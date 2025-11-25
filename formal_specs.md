Let’s treat this as v0.1 of a real spec.

I will:
	•	Give the language a working name: CertiJSON.
	•	Write a compact but formal-ish specification: syntax (JSON + abstract), typing, evaluation, repr and extern_c, and extraction-to-C obligations.

You can later copy this into a spec.md and extend.

⸻

CertiJSON v0.1 — Core Specification

0. Design goals

CertiJSON is a proof-and-programming language designed for use by LLM agents, not humans. Its primary goals:
	1.	Logical soundness
	•	Curry–Howard: types = propositions, terms = proofs/programs.
	•	If a module is accepted by the kernel, all theorem declarations are valid theorems in the core logic.
	2.	Deterministic, total core
	•	Pure, total, dependently typed λ-calculus with inductive types.
	•	Evaluation (normalization) is deterministic and terminating.
	3.	C interop with representation-level guarantees
	•	All C-visible values have explicit representation descriptors (repr) describing their ABI layout.
	•	extern_c declarations are checked against these representations.
	•	Extraction produces C code in a small, UB-free, deterministic subset.
	4.	LLM-oriented concrete syntax
	•	Concrete syntax is JSON with a small, fixed set of node kinds.
	•	The kernel uses abstract syntax derived from JSON; typing and evaluation rules are stated on the abstract syntax.

⸻

1. Concrete syntax: JSON structure

1.1 Module

A CertiJSON module is a single JSON object:

{
  "module": "ModuleName",
  "declarations": [ Decl, Decl, ... ]
}

Each Decl is one of:
	•	inductive declaration
	•	def declaration
	•	theorem declaration
	•	repr declaration
	•	extern_c declaration

Example (shape, not full content):

{ "inductive": { ... } }
{ "def":       { ... } }
{ "theorem":   { ... } }
{ "repr":      { ... } }
{ "extern_c":  { ... } }

1.2 Term JSON nodes

Terms and types share the same JSON node space.

Canonical node forms (abstracting away optional fields):
	•	Variable:

{ "var": "x" }


	•	Universe:

{ "universe": "Type0" }

For v0.1 we may only use "Type" or "Type0".

	•	Dependent function type (Π):

{
  "pi": {
    "arg": { "name": "x", "type": Term },
    "result": Term
  }
}


	•	Forall (sugar for pi):

{
  "forall": {
    "arg": { "name": "x", "type": Term },
    "result": Term
  }
}


	•	Lambda abstraction:

{
  "lambda": {
    "arg": { "name": "x", "type": Term },
    "body": Term
  }
}


	•	Application:

{ "app": [ Term, Term, ... ] }


	•	Equality type:

{
  "eq": {
    "type": Term,
    "lhs":  Term,
    "rhs":  Term
  }
}


	•	Reflexivity proof:

{
  "refl": {
    "eq": {
      "type": Term,
      "lhs":  Term,
      "rhs":  Term
    }
  }
}

(With the requirement that lhs and rhs are definitionally equal.)

	•	Match / elimination:

{
  "match": {
    "scrutinee": Term,
    "motive": Term,           // generally a function from scrutinee to Type
    "cases": [
      {
        "pattern": {
          "ctor": "ConstructorName",
          "args": [ { "name": "x" }, ... ]
        },
        "body": Term
      },
      ...
    ]
  }
}



Optionally, for inductive hypotheses, pattern args may carry "is_hypothesis": true.

You can add literals ("nat": 0, "int32": 5, "float64": 0.5) as additional node forms in the abstract syntax.

⸻

2. Abstract syntax

We define an abstract syntax over meta-variables:
	•	Variables: x, y, f, g, ...
	•	Type-level terms: A, B, C, ...
	•	Terms: t, u, v, ...
	•	Inductive type names: I, J, ...
	•	Constructors: c, d, ...

2.1 Terms

The abstract term grammar:
	•	t ::= x                             (variable)
	•	   | Type_i                         (universe; for v0.1: Type)
	•	   | Π(x : A). B                    (dependent function type)
	•	   | λ (x : A). t                   (lambda)
	•	   | t u                            (application)
	•	   | Eq_A(t, u)                     (intensional equality)
	•	   | refl_A(t)                      (reflexivity proof)
	•	   | C                              (constant / defined symbol)
	•	   | c                              (constructor)
	•	   | match t as x return P with ... (pattern match; with cases)

Inductives and constructors are part of the global signature (see below).

2.2 Declarations
	•	Inductive type:
Inductive I (x₁ : A₁) ... (xₙ : Aₙ) : Type_i := c₁ : C₁ | ... | c_k : C_k
	•	Definition:
def f : A := t
with optional role annotation role ∈ {runtime, proof-only, both}.
	•	Theorem:
theorem p : A := t
Semantically same as def with role = proof-only.
	•	Repr:
repr R describing ABI layout; see §4.
	•	Extern C:
extern_c f : A with representation-level signature; see §5.

All of these are encoded in JSON as described in the previous messages; here we only define their logical meaning.

⸻

3. Static semantics (typing)

3.1 Contexts and signatures
	•	A context Γ is a finite sequence of bindings:
	•	Γ ::= · | Γ, x : A
	•	A global signature Σ contains:
	•	Inductive type declarations
	•	Constructors with their types
	•	Definitions (constants)
	•	Repr descriptors
	•	Extern C declarations

We write Σ; Γ ⊢ t : A for the typing judgment.

We assume a standard, predicative cumulative hierarchy of universes, but v0.1 may collapse this to a single universe Type and ignore cumulativity.

3.2 Selected typing rules

I will state representative rules; you can extend with more connectives later.

(Var)
If (x : A) ∈ Γ, then:
	•	Σ; Γ ⊢ x : A

(Universe)
	•	Σ; Γ ⊢ Type : Type
(or Type₀ : Type₁ in a multi-universe system)

(Pi)
If
	•	Σ; Γ ⊢ A : Type
	•	Σ; Γ, x : A ⊢ B : Type

then
	•	Σ; Γ ⊢ Π(x : A). B : Type

(Lambda)
If
	•	Σ; Γ, x : A ⊢ t : B

then
	•	Σ; Γ ⊢ λ(x : A). t : Π(x : A). B

(App)
If
	•	Σ; Γ ⊢ f : Π(x : A). B
	•	Σ; Γ ⊢ u : A

then
	•	Σ; Γ ⊢ f u : B[x := u]

(Eq formation)
If
	•	Σ; Γ ⊢ A : Type
	•	Σ; Γ ⊢ t : A
	•	Σ; Γ ⊢ u : A

then
	•	Σ; Γ ⊢ Eq_A(t, u) : Type

(Eq intro – refl)
If
	•	Σ; Γ ⊢ A : Type
	•	Σ; Γ ⊢ t : A

then
	•	Σ; Γ ⊢ refl_A(t) : Eq_A(t, t)

(Eq elimination / rewrite)
You may axiomatize J (identity type eliminator) or give a primitive rewrite construct; for spec brevity, we assume the existence of standard equality elimination that preserves definitional equality.

⸻

3.3 Inductive types

A (monomorphic) inductive declaration in abstract form:
	•	Inductive I (x₁ : A₁) ... (xₙ : Aₙ) : Type :=
	•	c₁ : C₁
	•	…
	•	c_k : C_k

Constraints:
	1.	Well-formed parameter telescope:
For each i,
	•	Σ; Γ, x₁ : A₁, ..., x_{i-1} : A_{i-1} ⊢ A_i : Type
	2.	Constructors well-typed:
Each constructor type C_j is of the form:
	•	Π(y₁ : B₁)...(y_m : B_m). I x₁ ... xₙ
where all occurrences of I in C_j are strictly positive.

The typing rules give:
	•	Σ; Γ ⊢ I : Π(x₁ : A₁)...(xₙ : Aₙ). Type
	•	For each constructor c_j:
	•	Σ; Γ ⊢ c_j : Π(x₁ : A₁)...(xₙ : Aₙ). (Π(y₁ : B₁)...(y_m : B_m). I x₁ ... xₙ)

3.4 Pattern matching

Abstract form (single-scrutinee match):
	•	match t as z return P with
	•	| c₁ (y₁¹, ..., y_{m₁}¹) ⇒ u₁
	•	…
	•	| c_k (y₁ᵏ, ..., y_{m_k}ᵏ) ⇒ u_k

Typing rule (simplified):

Assume:
	•	Σ; Γ ⊢ t : I a₁ ... aₙ
	•	Σ; Γ, z : I a₁ ... aₙ ⊢ P : Type
	•	For each constructor c_j of I with type (after parameter application):
c_j : Π(y₁ : B₁)...(y_m : B_m). I a₁ ... aₙ
we require:
	•	Σ; Γ, y₁ : B₁, ..., y_m : B_m ⊢ u_j : P[z := c_j y₁ ... y_m]

Then:
	•	Σ; Γ ⊢ match t as z return P with ... : P[z := t]

Termination: CertiJSON enforces that pattern matching is structural recursion when used recursively (see below).

⸻

4. Dynamic semantics (core evaluation)

We define a deterministic, total evaluation relation:
	•	t ⇓ v  (“t evaluates to value v”), with values:
	•	v ::= λ(x : A). t | c v₁ ... v_m | other canonical forms

Evaluation follows β-reduction and unfolding of global definitions, but:
	•	No infinite reduction is possible in well-typed terms thanks to the termination/structural recursion restriction on definitions.

Key clauses (sketch):
	•	(λ(x : A). t) u ⇓ t[x := u'] where u ⇓ u'.
	•	match (c v₁ ... v_m) as z return P with ... reduces to the corresponding case body with variables substituted.

Definitions (def f : A := t) may be unfolded during normalization as needed.

⸻

5. Termination / totality

To ensure the “if it compiles, it terminates and is deterministic” property:
	•	Every recursive definition must be structurally recursive on at least one argument of an inductive type, or use a later well-founded recursion mechanism.
	•	The kernel checks that in every recursive call:
	•	The structurally decreasing argument is a direct subterm of the original (e.g. pattern variable in a constructor).

Formally specifying the termination checker is a separate sub-spec, but the requirement is that:

For all def f : A := t accepted by the kernel, t is strongly normalizing under the evaluation relation.

⸻

6. Representation layer (repr)

6.1 Purpose

repr declarations describe how logical types are represented in memory for C interop and extraction. They are not part of the core logic per se, but are checked for internal consistency.

6.2 Abstract notion

A representation descriptor R describes:
	1.	A C-level type or layout (R.c_type or R.c_struct).
	2.	Size and alignment constraints.
	3.	For composite values: field names, types, and offsets.
	4.	A correspondence between logical values and C-level bit patterns.

6.3 JSON shape

Informally:

{
  "repr": {
    "name": "Int32Repr",
    "kind": "primitive",
    "c_type": "int32_t",
    "size_bits": 32,
    "signed": true
  }
}

{
  "repr": {
    "name": "Point2DRepr",
    "kind": "struct",
    "c_struct_name": "Point2D",
    "size_bytes": 8,
    "align_bytes": 4,
    "fields": [
      { "name": "x", "repr": "Int32Repr", "offset_bytes": 0 },
      { "name": "y", "repr": "Int32Repr", "offset_bytes": 4 }
    ]
  }
}

6.4 Linking logical types to representations

A def for a logical type may reference a repr:

{
  "def": {
    "name": "Point2D",
    "role": "both",
    "type": { "universe": "Type" },
    "body": {
      "logical_struct": {
        "fields": [
          { "name": "x", "type": { "var": "Int32" } },
          { "name": "y", "type": { "var": "Int32" } }
        ]
      }
    },
    "repr": "Point2DRepr"
  }
}

The compiler must enforce:
	•	Field count and ordering match.
	•	Logical types used in the struct have associated reprs compatible with the C layout.

A future version of the spec can define logical encode/decode functions and require proofs like decode(encode(v)) = v.

⸻

7. FFI and extern_c

7.1 Purpose

extern_c defines functions implemented in C with a specified ABI and a logical type in CertiJSON.

7.2 JSON shape

Informally:

{
  "extern_c": {
    "name": "c_sin",                // logical name
    "c_name": "sin",                // C symbol
    "header": "<math.h>",           // included in generated C
    "signature": {
      "return": { "repr": "Float64Repr" },
      "args": [
        { "name": "x", "repr": "Float64Repr" }
      ]
    },
    "type": {
      "pi": {
        "arg": { "name": "_", "type": { "var": "Float64" } },
        "result": { "var": "Float64" }
      }
    },
    "safety": "pure",               // or "impure"
    "axioms": [ /* optional logical axioms about c_sin */ ]
  }
}

Well-formedness requirements:
	1.	All repr names used in signature must refer to valid representation descriptors.
	2.	The logical type must erase to the same C-level argument/return structure defined by signature.
	3.	For safety = "pure", the function is assumed side-effect free at the logical level.
	4.	For safety = "impure", the function typically returns an IO A-like type and effects are reasoned about separately or not at all.

The kernel treats extern_c as primitive constants with the declared type; any axioms attached must be checked for well-typedness but are assumed logically, not derived.

⸻

8. Extraction to C (obligations, sketch)

Extraction is not part of the logical kernel but is specified to guarantee correct C interop.

8.1 Erasure

The erasure function erase(t) removes all proof-only parts:
	•	Erase terms whose type lives in Prop/TypeProp (or is marked proof-only).
	•	Erase implicit arguments not needed at runtime.
	•	Erase equality proofs, logical connectives not used at runtime, etc.

Definitions and theorems with role = "proof-only" are erased from output entirely.

8.2 Translation
	•	Inductive types with repr are mapped to C structs/enums according to their repr descriptor.
	•	Pure, total def with role = "runtime" are mapped to C functions in a small, well-defined C subset.
	•	Calls to extern_c are emitted as C calls using the signature and conversions defined by repr.

The extracted C must satisfy:
	•	No undefined behavior in the C standard sense (under a specified safe subset).
	•	Deterministic semantics matching the core evaluation semantics extended with FFI axioms.

The exact small-step semantics of the C subset and the proof of correctness of extraction are out of scope for v0.1, but this section specifies the goal.

⸻

9. Soundness and safety theorems (to be proved)

The spec implies a set of core meta-theorems you aim to prove about CertiJSON:
	1.	Progress and Preservation (Type Soundness)
	•	If Σ; Γ ⊢ t : A and t is closed, then either t is a value or there exists t' such that t → t', and Σ; Γ ⊢ t' : A.
	2.	Strong Normalization (Totality)
	•	Every well-typed, closed term normalizes: for all t, if Σ; · ⊢ t : A, then there exists a value v such that t ⇓ v.
	3.	Logical Soundness
	•	If a theorem p : P := t is accepted in a well-formed signature, then P is valid under the intended model of the core type theory.
	4.	FFI ABI Correctness
	•	Given well-formed repr and extern_c declarations, any call from extracted C to a C function respects the ABI described by repr.
	5.	Extraction Correctness
	•	For all closed runtime terms t of type A with repr A, evaluating t in the core and running the corresponding extracted C code produce observationally equivalent results, assuming the external C environment behaves according to its axioms.

⸻

This is a reasonably compact “formal spec skeleton” for the language.

If you want, next I can:
	•	Turn this into a tighter, more Coq/Agda-style spec (with full inference rules and an explicit definition of the JSON → abstract syntax mapping), or
	•	Start from this and write a JSON Schema that enforces the structural constraints for modules/terms as much as possible on the concrete level.

Alright, let’s turn this into a more formal spec you could actually implement or even mechanize later.

I’ll refine what we already have into a core formal spec for the language (I’ll keep the working name CertiJSON), with:
	1.	Abstract syntax (math-level, not JSON)
	2.	JSON → AST mapping
	3.	Typing rules (inference rules)
	4.	Evaluation semantics
	5.	Sketch of totality constraint
	6.	Repr / extern layer as a separate (non-logical) layer

You can drop this into a spec.md and iterate.

⸻

CertiJSON Core Formal Specification (v0.2)

0. Informal overview

CertiJSON is a pure, total, dependently typed language with:
	•	Inductive types and pattern matching
	•	Intensional equality
	•	Universes (Type₀, Type₁, …) — v0.2: just Type₀ (a.k.a. Type)
	•	JSON as the concrete syntax, but all rules are stated on an abstract syntax.

The spec here covers the logical core. repr and extern_c are specified as an additional layer on top.

⸻

1. Names and meta-variables
	•	Variable names: x, y, f, g, ...
	•	Type-level terms: A, B, C, ...
	•	Terms: t, u, v, ...
	•	Inductive type names: I, J, ...
	•	Constructors: c, d, ...
	•	Universes: Type_i (v0.2: just Type₀, usually written Type)

We assume an infinite supply of variable names and alpha-equivalence (renaming bound variables) as usual.

⸻

2. Abstract syntax

2.1 Terms

We define terms t by the following grammar:
	•	Variables
t ::= x
	•	Universes
t ::= Type_i (v0.2: Type₀)
	•	Dependent function type (Π / forall)
t ::= Π(x : A). B
	•	Lambda abstraction
t ::= λ(x : A). t
	•	Application
t ::= t u (left-associative: t u v = (t u) v)
	•	Equality type
t ::= Eq_A(u, v)
where A, u, v are terms.
	•	Equality reflexivity
t ::= refl_A(u)
	•	Constant / global name
t ::= cst
where cst is a globally defined constant or constructor name.
	•	Pattern match / elimination
For a single scrutinee on an inductive type I:
t ::= match t₀ as z return P with (c₁(⃗y¹) ⇒ u₁ | ... | c_k(⃗yᵏ) ⇒ u_k)
where:
	•	t₀ is the scrutinee,
	•	z is the match-as variable,
	•	P is the motive (a term possibly depending on z),
	•	each c_j is a constructor of I,
	•	⃗yʲ is a vector of pattern-bound variables.

We regard forall (x : A). B as syntactic sugar for Π(x : A). B.

You can extend the grammar with literals (nat n, int32 n, etc.) as base forms; I omit them here to keep the core small.

⸻

3. JSON → AST mapping (concrete syntax)

The concrete syntax is JSON, but the kernel first parses JSON into the abstract syntax above.

Here is the canonical mapping:
	•	Variable:

{ "var": "x" }

↦ abstract term x.

	•	Universe:

{ "universe": "Type0" }

↦ Type₀.

	•	Π (dependent function type):

{
  "pi": {
    "arg": { "name": "x", "type": A_json },
    "result": B_json
  }
}

↦ Π(x : A). B where A = ⟦A_json⟧, B = ⟦B_json⟧.

	•	Forall (sugar for Π):

{
  "forall": {
    "arg": { "name": "x", "type": A_json },
    "result": B_json
  }
}

↦ Π(x : A). B.

	•	Lambda:

{
  "lambda": {
    "arg": { "name": "x", "type": A_json },
    "body": t_json
  }
}

↦ λ(x : A). t.

	•	Application:

{ "app": [ t_json, u1_json, u2_json, ... ] }

↦ (((t u₁) u₂) ...) where t = ⟦t_json⟧, uᵢ = ⟦ui_json⟧.

	•	Equality type:

{
  "eq": {
    "type": A_json,
    "lhs":  u_json,
    "rhs":  v_json
  }
}

↦ Eq_A(u, v).

	•	Reflexivity:

{
  "refl": {
    "eq": {
      "type": A_json,
      "lhs":  u_json,
      "rhs":  v_json
    }
  }
}

↦ refl_A(u) with a side condition at type-checking time that u and v are definitionally equal.

	•	Match:

{
  "match": {
    "scrutinee": t0_json,
    "motive": P_json,
    "as": "z",                 // optional; if missing, a fresh name is chosen
    "cases": [
      {
        "pattern": {
          "ctor": "C1",
          "args": [ { "name": "y1" }, { "name": "y2" } ]
        },
        "body": u1_json
      },
      ...
    ]
  }
}

↦ match t₀ as z return P with (C1(y1, y2) ⇒ u₁ | ...), where:
	•	t₀ = ⟦t0_json⟧
	•	P = ⟦P_json⟧
	•	each u_j = ⟦uj_json⟧.

	•	Global constants / constructors (Nat, zero, succ, plus, etc.) are encoded as:

{ "var": "Nat" }
{ "var": "zero" }
{ "var": "succ" }

and mapped to the corresponding cst names in the global environment.

We assume a well-formedness predicate on JSON that ensures a valid mapping to the abstract syntax; malformed JSON (wrong tags, missing fields) is rejected before type checking.

⸻

4. Global environment and declarations

A global environment or signature Σ is a finite mapping containing:
	•	Inductive definitions
	•	Constructor types
	•	Constant definitions
	•	(Later) repr and extern_c, which do not affect the core logic directly.

4.1 Inductive declaration (abstract)

An inductive block is:

Inductive I (x₁ : A₁) ... (xₙ : Aₙ) : Type_i := c₁ : C₁ | ... | c_k : C_k

We require:
	1.	Parameter telescope well-formed:
For each i:
Σ; x₁ : A₁, ..., x_{i-1} : A_{i-1} ⊢ A_i : Type_j for some universe index (v0.2: Type₀).
	2.	Each constructor type C_j has the form:
Π(x₁ : A₁)...(xₙ : Aₙ). Π(y₁ : B₁)...(y_m : B_m). I x₁ ... xₙ
with strict positivity for I in C_j (standard positivity condition).

When this is accepted, Σ is extended with:
	•	I : Π(x₁ : A₁)...(xₙ : Aₙ). Type_i
	•	For each c_j:
c_j : Π(x₁ : A₁)...(xₙ : Aₙ). Π(y₁ : B₁)...(y_m : B_m). I x₁ ... xₙ

4.2 Constant definition

A constant definition:

def f : A := t

is accepted if:
	•	Σ; · ⊢ A : Type_i (v0.2: Type₀)
	•	Σ; · ⊢ t : A
	•	Termination checker accepts t as total (see §6).

Then we extend Σ with f : A and an unfolding rule f ≝ t.

4.3 Theorem

A theorem is syntactic sugar:

theorem p : P := t

is treated exactly as def p : P := t with an external convention that role = proof-only (for erasure later).

⸻

5. Typing rules

We define a judgment Σ; Γ ⊢ t : A.

5.1 Context formation
	•	· is a valid context.
	•	If Σ; Γ ⊢ A : Type_i, then Γ, x : A is a valid context (with x fresh).

5.2 Selected rules

I’ll write them in inference-rule style.

(Var)
If (x : A) ∈ Γ, then

————————————
Σ; Γ ⊢ x : A

(Universe)
————————————
Σ; Γ ⊢ Type₀ : Type₀

(You may want Type₀ : Type₁ in a multi-universe system; v0.2 can be impredicative or leave this as is.)

(Pi)
If
	•	Σ; Γ ⊢ A : Type₀
	•	Σ; Γ, x : A ⊢ B : Type₀

then

——————————————————————————————
Σ; Γ ⊢ Π(x : A). B : Type₀

(Lambda)
If
	•	Σ; Γ, x : A ⊢ t : B

then

——————————————————————————————
Σ; Γ ⊢ λ(x : A). t : Π(x : A). B

(App)
If
	•	Σ; Γ ⊢ f : Π(x : A). B
	•	Σ; Γ ⊢ u : A

then

——————————————————————————————
Σ; Γ ⊢ f u : B[x := u]

(Conversion / Definitional equality)
We assume a judgment of definitional equality Σ; Γ ⊢ A ≡ B (β + unfolding).

If
	•	Σ; Γ ⊢ t : A
	•	Σ; Γ ⊢ A ≡ B

then

————————————————
Σ; Γ ⊢ t : B

(Equality formation)
If
	•	Σ; Γ ⊢ A : Type₀
	•	Σ; Γ ⊢ u : A
	•	Σ; Γ ⊢ v : A

then

————————————————————————
Σ; Γ ⊢ Eq_A(u, v) : Type₀

(Equality introduction: refl)
If
	•	Σ; Γ ⊢ A : Type₀
	•	Σ; Γ ⊢ u : A

then

————————————————————————————
Σ; Γ ⊢ refl_A(u) : Eq_A(u, u)

(Equality elimination – J) (sketch)
We do not introduce a dedicated syntax node; instead we assume a primitive eliminator J. For the spec:
	•	Introduce a constant J with the usual type:
J : Π(A : Type₀). Π(x : A). Π(P : Π(y : A). Eq_A(x, y) → Type₀).
     P x (refl_A(x)) → Π(y : A). Π(e : Eq_A(x, y)). P y e

Typing/evaluation of J follow the standard identity type eliminator. For practical use, you can give a higher-level rewrite form that compiles down to J. For now, we just require:
	•	The kernel implements equality elimination in a sound, standard way.

(Inductive type and constructors)
If Inductive I ... is in Σ (well-formed), and I : Π(⃗x : ⃗A). Type₀, then:

———————————————
Σ; Γ ⊢ I : Π(⃗x : ⃗A). Type₀

If c_j is a constructor with type C_j in Σ, then:

———————————————
Σ; Γ ⊢ c_j : C_j

(Match)
Let I be an inductive type in Σ with parameters ⃗A and constructors c₁, ..., c_k:
	•	Suppose Σ; Γ ⊢ t₀ : I ⃗a
	•	Suppose Σ; Γ, z : I ⃗a ⊢ P : Type₀

Each constructor c_j has (after parameter specialization) type:

c_j : Π(y₁ : B₁)...(y_m : B_m). I ⃗a

For each case c_j(⃗yʲ) ⇒ u_j we require:
	•	Σ; Γ, y₁ : B₁, ..., y_m : B_m ⊢ u_j : P[z := c_j(⃗y)]

Then the match has type:
	•	Σ; Γ ⊢ match t₀ as z return P with (c₁(⃗y¹) ⇒ u₁ | ... | c_k(⃗yᵏ) ⇒ u_k) : P[z := t₀]

⸻

6. Evaluation (dynamic semantics)

You can define big-step evaluation t ⇓ v with values:
	•	v ::= λ(x : A). t  | c v₁ ... v_m | Type₀ | Π(x : A). B | Eq_A(u, v) | ...

Key rules (sketch):
	•	Beta-reduction:
If t₁ ⇓ λ(x : A). t and t₂ ⇓ v₂ and t[x := v₂] ⇓ v, then
t₁ t₂ ⇓ v.
	•	Match on constructor:
If t₀ ⇓ c_j(v₁, ..., v_m) and the j-th case is c_j(⃗yʲ) ⇒ u_j, then u_j[⃗y := ⃗v] ⇓ v implies
match t₀ as z return P with ... ⇓ v.
	•	Constants:
If f ≝ t in Σ and t ⇓ v, then f ⇓ v.

You can equivalently specify a small-step relation t → t' and define ⇓ as its reflexive transitive closure to values.

⸻

7. Termination / totality (informal spec)

CertiJSON requires totality for all accepted definitions:

For every def f : A := t accepted by the kernel, and for every closed argument v of appropriate type, evaluation of f v terminates.

To achieve this, the kernel runs a termination checker on each definition:
	•	Structural recursion:
	•	f may only recurse on an argument of inductive type.
	•	In each recursive call, the argument is a structurally smaller subterm of the original (e.g. a constructor field).
	•	No general recursion without a well-founded proof (which could be added later).

For v0.2, you can specify:
	•	“A def is accepted only if all recursive calls are guarded and structurally decreasing on an inductive argument.”

The full formalization of this checker can be added as a separate document.

⸻

8. Repr and extern_c (interface layer)

These are not part of the logical core (typing/evaluation), but part of the C-interoperable backend spec. They do not affect the judgments Σ; Γ ⊢ t : A, only the extraction.

8.1 Repr (representation descriptors)
	•	A repr describes a C-level layout (struct, primitive type, enum, etc.).
	•	There is a mapping repr_of_type : Σ × Type → option ReprName which is defined when a logical type has a C representation.

Well-formedness constraints (informal):
	•	Primitive repr:
	•	Has a valid C type name, size, and signedness.
	•	Struct repr:
	•	Fields do not overlap.
	•	Offsets are within [0, size_bytes).
	•	Field reprs are themselves well-formed.

For a type T with repr R, it should be possible (and intended) to prove:
	•	encode_T : T → Bytes(size_bytes(R))
	•	decode_T : Bytes(size_bytes(R)) → Option T
	•	decode_T (encode_T v) = Some v  (round-trip property)

These proofs live in the core language and justify correctness of the representation.

8.2 extern_c

An extern_c declaration:
	•	Binds a logical constant f with type A in the core.
	•	Associates it with a C symbol and a signature that uses reprs for arguments and result.

Well-formedness:
	•	All repr names used in signature are valid.
	•	A erases to a function type compatible with signature:
	•	For example, if signature is (Point2DRepr, Point2DRepr) → Float64Repr, then
A should be (up to definitional equality) something like:
Π(p1 : Point2D). Π(p2 : Point2D). Float64
where both Point2D and Float64 have the corresponding reprs.
	•	axioms attached to extern_c are required to be well-typed theorems in the core (their truth is assumed, not proved).

Extraction ensures:
	•	Calls to f in core terms become calls to the C symbol with correctly encoded arguments/return values according to the repr descriptors.
	•	No raw or inconsistent ABI usage is generated.

⸻

9. Meta-theoretic goals (to be proven about the spec)

Given the above, the intended metatheory for CertiJSON’s core is:
	1.	Type soundness (progress + preservation):
If Σ; · ⊢ t : A and t is closed, then either t is a value or there exists t' such that t → t', and if t → t' then Σ; · ⊢ t' : A.
	2.	Normalization / totality:
For all closed, well-typed terms t, there exists a value v such that t ⇓ v.
	3.	Logical soundness:
If a theorem p : P := t is accepted by the kernel in some well-formed Σ, then P holds in the standard model of the type theory.
	4.	FFI representation soundness:
Given well-formed repr and extern_c declarations and correct encode/decode proofs, the runtime C representation of values of type T is consistent with the core logical semantics of T.
	5.	Extraction correctness (future work):
Extracted C code (in a restricted UB-free subset) simulates the evaluation semantics of the core, modulo the assumed axioms for extern_c functions.

⸻

If you want, I can next:
	•	Reshape this into an actual spec.md with headings and numbered definitions (ready to drop into a repo), or
	•	Start defining a minimal standard library spec (Nat, Bool, List, Eq, basic lemmas) so the LLM has a canonical universe of symbols to use.

Alright, let’s turn this into a more formal spec you could actually implement or even mechanize later.

I’ll refine what we already have into a core formal spec for the language (I’ll keep the working name CertiJSON), with:
	1.	Abstract syntax (math-level, not JSON)
	2.	JSON → AST mapping
	3.	Typing rules (inference rules)
	4.	Evaluation semantics
	5.	Sketch of totality constraint
	6.	Repr / extern layer as a separate (non-logical) layer

You can drop this into a spec.md and iterate.

⸻

CertiJSON Core Formal Specification (v0.2)

0. Informal overview

CertiJSON is a pure, total, dependently typed language with:
	•	Inductive types and pattern matching
	•	Intensional equality
	•	Universes (Type₀, Type₁, …) — v0.2: just Type₀ (a.k.a. Type)
	•	JSON as the concrete syntax, but all rules are stated on an abstract syntax.

The spec here covers the logical core. repr and extern_c are specified as an additional layer on top.

⸻

1. Names and meta-variables
	•	Variable names: x, y, f, g, ...
	•	Type-level terms: A, B, C, ...
	•	Terms: t, u, v, ...
	•	Inductive type names: I, J, ...
	•	Constructors: c, d, ...
	•	Universes: Type_i (v0.2: just Type₀, usually written Type)

We assume an infinite supply of variable names and alpha-equivalence (renaming bound variables) as usual.

⸻

2. Abstract syntax

2.1 Terms

We define terms t by the following grammar:
	•	Variables
t ::= x
	•	Universes
t ::= Type_i (v0.2: Type₀)
	•	Dependent function type (Π / forall)
t ::= Π(x : A). B
	•	Lambda abstraction
t ::= λ(x : A). t
	•	Application
t ::= t u (left-associative: t u v = (t u) v)
	•	Equality type
t ::= Eq_A(u, v)
where A, u, v are terms.
	•	Equality reflexivity
t ::= refl_A(u)
	•	Constant / global name
t ::= cst
where cst is a globally defined constant or constructor name.
	•	Pattern match / elimination
For a single scrutinee on an inductive type I:
t ::= match t₀ as z return P with (c₁(⃗y¹) ⇒ u₁ | ... | c_k(⃗yᵏ) ⇒ u_k)
where:
	•	t₀ is the scrutinee,
	•	z is the match-as variable,
	•	P is the motive (a term possibly depending on z),
	•	each c_j is a constructor of I,
	•	⃗yʲ is a vector of pattern-bound variables.

We regard forall (x : A). B as syntactic sugar for Π(x : A). B.

You can extend the grammar with literals (nat n, int32 n, etc.) as base forms; I omit them here to keep the core small.

⸻

3. JSON → AST mapping (concrete syntax)

The concrete syntax is JSON, but the kernel first parses JSON into the abstract syntax above.

Here is the canonical mapping:
	•	Variable:

{ "var": "x" }

↦ abstract term x.

	•	Universe:

{ "universe": "Type0" }

↦ Type₀.

	•	Π (dependent function type):

{
  "pi": {
    "arg": { "name": "x", "type": A_json },
    "result": B_json
  }
}

↦ Π(x : A). B where A = ⟦A_json⟧, B = ⟦B_json⟧.

	•	Forall (sugar for Π):

{
  "forall": {
    "arg": { "name": "x", "type": A_json },
    "result": B_json
  }
}

↦ Π(x : A). B.

	•	Lambda:

{
  "lambda": {
    "arg": { "name": "x", "type": A_json },
    "body": t_json
  }
}

↦ λ(x : A). t.

	•	Application:

{ "app": [ t_json, u1_json, u2_json, ... ] }

↦ (((t u₁) u₂) ...) where t = ⟦t_json⟧, uᵢ = ⟦ui_json⟧.

	•	Equality type:

{
  "eq": {
    "type": A_json,
    "lhs":  u_json,
    "rhs":  v_json
  }
}

↦ Eq_A(u, v).

	•	Reflexivity:

{
  "refl": {
    "eq": {
      "type": A_json,
      "lhs":  u_json,
      "rhs":  v_json
    }
  }
}

↦ refl_A(u) with a side condition at type-checking time that u and v are definitionally equal.

	•	Match:

{
  "match": {
    "scrutinee": t0_json,
    "motive": P_json,
    "as": "z",                 // optional; if missing, a fresh name is chosen
    "cases": [
      {
        "pattern": {
          "ctor": "C1",
          "args": [ { "name": "y1" }, { "name": "y2" } ]
        },
        "body": u1_json
      },
      ...
    ]
  }
}

↦ match t₀ as z return P with (C1(y1, y2) ⇒ u₁ | ...), where:
	•	t₀ = ⟦t0_json⟧
	•	P = ⟦P_json⟧
	•	each u_j = ⟦uj_json⟧.

	•	Global constants / constructors (Nat, zero, succ, plus, etc.) are encoded as:

{ "var": "Nat" }
{ "var": "zero" }
{ "var": "succ" }

and mapped to the corresponding cst names in the global environment.

We assume a well-formedness predicate on JSON that ensures a valid mapping to the abstract syntax; malformed JSON (wrong tags, missing fields) is rejected before type checking.

⸻

4. Global environment and declarations

A global environment or signature Σ is a finite mapping containing:
	•	Inductive definitions
	•	Constructor types
	•	Constant definitions
	•	(Later) repr and extern_c, which do not affect the core logic directly.

4.1 Inductive declaration (abstract)

An inductive block is:

Inductive I (x₁ : A₁) ... (xₙ : Aₙ) : Type_i := c₁ : C₁ | ... | c_k : C_k

We require:
	1.	Parameter telescope well-formed:
For each i:
Σ; x₁ : A₁, ..., x_{i-1} : A_{i-1} ⊢ A_i : Type_j for some universe index (v0.2: Type₀).
	2.	Each constructor type C_j has the form:
Π(x₁ : A₁)...(xₙ : Aₙ). Π(y₁ : B₁)...(y_m : B_m). I x₁ ... xₙ
with strict positivity for I in C_j (standard positivity condition).

When this is accepted, Σ is extended with:
	•	I : Π(x₁ : A₁)...(xₙ : Aₙ). Type_i
	•	For each c_j:
c_j : Π(x₁ : A₁)...(xₙ : Aₙ). Π(y₁ : B₁)...(y_m : B_m). I x₁ ... xₙ

4.2 Constant definition

A constant definition:

def f : A := t

is accepted if:
	•	Σ; · ⊢ A : Type_i (v0.2: Type₀)
	•	Σ; · ⊢ t : A
	•	Termination checker accepts t as total (see §6).

Then we extend Σ with f : A and an unfolding rule f ≝ t.

4.3 Theorem

A theorem is syntactic sugar:

theorem p : P := t

is treated exactly as def p : P := t with an external convention that role = proof-only (for erasure later).

⸻

5. Typing rules

We define a judgment Σ; Γ ⊢ t : A.

5.1 Context formation
	•	· is a valid context.
	•	If Σ; Γ ⊢ A : Type_i, then Γ, x : A is a valid context (with x fresh).

5.2 Selected rules

I’ll write them in inference-rule style.

(Var)
If (x : A) ∈ Γ, then

————————————
Σ; Γ ⊢ x : A

(Universe)
————————————
Σ; Γ ⊢ Type₀ : Type₀

(You may want Type₀ : Type₁ in a multi-universe system; v0.2 can be impredicative or leave this as is.)

(Pi)
If
	•	Σ; Γ ⊢ A : Type₀
	•	Σ; Γ, x : A ⊢ B : Type₀

then

——————————————————————————————
Σ; Γ ⊢ Π(x : A). B : Type₀

(Lambda)
If
	•	Σ; Γ, x : A ⊢ t : B

then

——————————————————————————————
Σ; Γ ⊢ λ(x : A). t : Π(x : A). B

(App)
If
	•	Σ; Γ ⊢ f : Π(x : A). B
	•	Σ; Γ ⊢ u : A

then

——————————————————————————————
Σ; Γ ⊢ f u : B[x := u]

(Conversion / Definitional equality)
We assume a judgment of definitional equality Σ; Γ ⊢ A ≡ B (β + unfolding).

If
	•	Σ; Γ ⊢ t : A
	•	Σ; Γ ⊢ A ≡ B

then

————————————————
Σ; Γ ⊢ t : B

(Equality formation)
If
	•	Σ; Γ ⊢ A : Type₀
	•	Σ; Γ ⊢ u : A
	•	Σ; Γ ⊢ v : A

then

————————————————————————
Σ; Γ ⊢ Eq_A(u, v) : Type₀

(Equality introduction: refl)
If
	•	Σ; Γ ⊢ A : Type₀
	•	Σ; Γ ⊢ u : A

then

————————————————————————————
Σ; Γ ⊢ refl_A(u) : Eq_A(u, u)

(Equality elimination – J) (sketch)
We do not introduce a dedicated syntax node; instead we assume a primitive eliminator J. For the spec:
	•	Introduce a constant J with the usual type:
J : Π(A : Type₀). Π(x : A). Π(P : Π(y : A). Eq_A(x, y) → Type₀).
     P x (refl_A(x)) → Π(y : A). Π(e : Eq_A(x, y)). P y e

Typing/evaluation of J follow the standard identity type eliminator. For practical use, you can give a higher-level rewrite form that compiles down to J. For now, we just require:
	•	The kernel implements equality elimination in a sound, standard way.

(Inductive type and constructors)
If Inductive I ... is in Σ (well-formed), and I : Π(⃗x : ⃗A). Type₀, then:

———————————————
Σ; Γ ⊢ I : Π(⃗x : ⃗A). Type₀

If c_j is a constructor with type C_j in Σ, then:

———————————————
Σ; Γ ⊢ c_j : C_j

(Match)
Let I be an inductive type in Σ with parameters ⃗A and constructors c₁, ..., c_k:
	•	Suppose Σ; Γ ⊢ t₀ : I ⃗a
	•	Suppose Σ; Γ, z : I ⃗a ⊢ P : Type₀

Each constructor c_j has (after parameter specialization) type:

c_j : Π(y₁ : B₁)...(y_m : B_m). I ⃗a

For each case c_j(⃗yʲ) ⇒ u_j we require:
	•	Σ; Γ, y₁ : B₁, ..., y_m : B_m ⊢ u_j : P[z := c_j(⃗y)]

Then the match has type:
	•	Σ; Γ ⊢ match t₀ as z return P with (c₁(⃗y¹) ⇒ u₁ | ... | c_k(⃗yᵏ) ⇒ u_k) : P[z := t₀]

⸻

6. Evaluation (dynamic semantics)

You can define big-step evaluation t ⇓ v with values:
	•	v ::= λ(x : A). t  | c v₁ ... v_m | Type₀ | Π(x : A). B | Eq_A(u, v) | ...

Key rules (sketch):
	•	Beta-reduction:
If t₁ ⇓ λ(x : A). t and t₂ ⇓ v₂ and t[x := v₂] ⇓ v, then
t₁ t₂ ⇓ v.
	•	Match on constructor:
If t₀ ⇓ c_j(v₁, ..., v_m) and the j-th case is c_j(⃗yʲ) ⇒ u_j, then u_j[⃗y := ⃗v] ⇓ v implies
match t₀ as z return P with ... ⇓ v.
	•	Constants:
If f ≝ t in Σ and t ⇓ v, then f ⇓ v.

You can equivalently specify a small-step relation t → t' and define ⇓ as its reflexive transitive closure to values.

⸻

7. Termination / totality (informal spec)

CertiJSON requires totality for all accepted definitions:

For every def f : A := t accepted by the kernel, and for every closed argument v of appropriate type, evaluation of f v terminates.

To achieve this, the kernel runs a termination checker on each definition:
	•	Structural recursion:
	•	f may only recurse on an argument of inductive type.
	•	In each recursive call, the argument is a structurally smaller subterm of the original (e.g. a constructor field).
	•	No general recursion without a well-founded proof (which could be added later).

For v0.2, you can specify:
	•	“A def is accepted only if all recursive calls are guarded and structurally decreasing on an inductive argument.”

The full formalization of this checker can be added as a separate document.

⸻

8. Repr and extern_c (interface layer)

These are not part of the logical core (typing/evaluation), but part of the C-interoperable backend spec. They do not affect the judgments Σ; Γ ⊢ t : A, only the extraction.

8.1 Repr (representation descriptors)
	•	A repr describes a C-level layout (struct, primitive type, enum, etc.).
	•	There is a mapping repr_of_type : Σ × Type → option ReprName which is defined when a logical type has a C representation.

Well-formedness constraints (informal):
	•	Primitive repr:
	•	Has a valid C type name, size, and signedness.
	•	Struct repr:
	•	Fields do not overlap.
	•	Offsets are within [0, size_bytes).
	•	Field reprs are themselves well-formed.

For a type T with repr R, it should be possible (and intended) to prove:
	•	encode_T : T → Bytes(size_bytes(R))
	•	decode_T : Bytes(size_bytes(R)) → Option T
	•	decode_T (encode_T v) = Some v  (round-trip property)

These proofs live in the core language and justify correctness of the representation.

8.2 extern_c

An extern_c declaration:
	•	Binds a logical constant f with type A in the core.
	•	Associates it with a C symbol and a signature that uses reprs for arguments and result.

Well-formedness:
	•	All repr names used in signature are valid.
	•	A erases to a function type compatible with signature:
	•	For example, if signature is (Point2DRepr, Point2DRepr) → Float64Repr, then
A should be (up to definitional equality) something like:
Π(p1 : Point2D). Π(p2 : Point2D). Float64
where both Point2D and Float64 have the corresponding reprs.
	•	axioms attached to extern_c are required to be well-typed theorems in the core (their truth is assumed, not proved).

Extraction ensures:
	•	Calls to f in core terms become calls to the C symbol with correctly encoded arguments/return values according to the repr descriptors.
	•	No raw or inconsistent ABI usage is generated.

⸻

9. Meta-theoretic goals (to be proven about the spec)

Given the above, the intended metatheory for CertiJSON’s core is:
	1.	Type soundness (progress + preservation):
If Σ; · ⊢ t : A and t is closed, then either t is a value or there exists t' such that t → t', and if t → t' then Σ; · ⊢ t' : A.
	2.	Normalization / totality:
For all closed, well-typed terms t, there exists a value v such that t ⇓ v.
	3.	Logical soundness:
If a theorem p : P := t is accepted by the kernel in some well-formed Σ, then P holds in the standard model of the type theory.
	4.	FFI representation soundness:
Given well-formed repr and extern_c declarations and correct encode/decode proofs, the runtime C representation of values of type T is consistent with the core logical semantics of T.
	5.	Extraction correctness (future work):
Extracted C code (in a restricted UB-free subset) simulates the evaluation semantics of the core, modulo the assumed axioms for extern_c functions.

⸻

If you want, I can next:
	•	Reshape this into an actual spec.md with headings and numbered definitions (ready to drop into a repo), or
	•	Start defining a minimal standard library spec (Nat, Bool, List, Eq, basic lemmas) so the LLM has a canonical universe of symbols to use.


# CertiJSON Core Language Specification (v0.3)

_Working name_: **CertiJSON**  
_Goal_: A pure, total, dependently typed language with JSON concrete syntax, designed for LLM agents. All accepted modules are logically sound, and runtime terms can be extracted to UB-free C with representation-level guarantees.

---

## 0. Version 0.3 Overview

This document describes **CertiJSON v0.3**.

Changes from v0.2:

1. Introduces a **Prop vs Type** distinction:
   - `Type` = computational types (data, functions).
   - `Prop` = proof-only types (propositions).
   - Erasure is defined primarily on `Prop`.

2. Clarifies **definition roles**:
   - `runtime`, `proof-only`, `both`.

3. Defines a **C-safe type subset** for FFI and extraction:
   - Primitive and struct-like types with explicit `repr`.
   - Only C-safe types may appear at the FFI boundary and as final extracted entrypoints.

4. Tightens `repr` and `extern_c` well-formedness:
   - Formal link between logical type, representation, and C signature.

---

## 1. Design Goals

**G1. Logical soundness**

- Curry–Howard:
  - `Prop` terms are propositions.
  - Terms inhabiting `P : Prop` are proofs.
  - Terms inhabiting `A : Type` are computational values.
- If a module is accepted by the kernel, every `theorem` is a valid theorem in the underlying type theory.

**G2. Total, deterministic core**

- No general recursion.
- Only structurally (or otherwise proven) terminating definitions are accepted.
- Evaluation is deterministic and terminating for all well-typed closed terms.

**G3. Clean separation of logic and computation**

- `Prop` is proof-only.
- `Type` is for runtime data.
- Extraction erases everything living purely in `Prop` and all `proof-only` definitions.

**G4. Safe and deterministic C interop**

- Explicit `repr` (representation descriptors) for all C-visible types.
- `extern_c` declarations tie logical functions to C functions via these representations.
- Extracted C is restricted to a small, UB-free subset.

**G5. LLM-optimized syntax**

- Concrete syntax is JSON.
- No precedence or layout rules.
- Small, fixed set of node kinds with canonical formatting.

---

## 2. Abstract Syntax

The type theory is defined at the level of **abstract syntax**. JSON is a serialization of these terms.

### 2.1 Universes

We distinguish:

- `Type` – universe of computational types.
- `Prop` – universe of propositions (proof-only).

We may later extend to a hierarchy (`Type0`, `Type1`, …); v0.3 keeps a single `Type`.

### 2.2 Names and Meta-Variables

- Term variables: `x, y, z, f, g, ...`
- Types: `A, B, C, ...`
- Terms: `t, u, v, ...`
- Inductive type names: `I, J, ...`
- Constructors: `c, d, ...`
- Global constants: `cst`

### 2.3 Terms

Abstract term grammar:

1. **Variables**

   - `t ::= x`

2. **Universes**

   - `t ::= Type`
   - `t ::= Prop`

3. **Dependent function types**

   - `t ::= Π(x : A). B`

   Where:
   - If `A : Type` and `B : Type`, then `Π(x : A). B : Type`.
   - If either `A` or `B` is in `Prop` (and consistent), it may live in `Prop` as a logical function type.
   - Exact universe rules given in §4.

4. **Lambda abstraction**

   - `t ::= λ(x : A). t`

5. **Application**

   - `t ::= t u` (left-associative).

6. **Equality type (in Prop)**

   - `t ::= Eq_A(u, v)` where `A : Type` or `A : Prop`.

7. **Reflexivity**

   - `t ::= refl_A(u)`.

8. **Global constants / constructors**

   - `t ::= cst`.

9. **Pattern match**

   - `t ::= match t₀ as z return P with (c₁(⃗y¹) ⇒ u₁ | ... | c_k(⃗yᵏ) ⇒ u_k)`.

10. **(Optional) Literals**

   - Implementation-defined base literals (e.g. `nat n`, `int32 n`, `float64 f`) are allowed as extensions and must be given explicit typing and evaluation rules.

### 2.4 Derived Forms

- Universal quantification:
  - `forall (x : A). B` ≜ `Π(x : A). B`.

- Non-dependent function types:
  - `A → B` ≜ `Π(_ : A). B`.

---

## 3. JSON Concrete Syntax

### 3.1 Module Structure

A CertiJSON module is a JSON object:

```json
{
  "module": "ModuleName",
  "declarations": [ Decl, ... ]
}

# CertiJSON Core Language Specification (v0.3)

_Working name_: **CertiJSON**  
_Goal_: A pure, total, dependently typed language with JSON concrete syntax, designed for LLM agents. All accepted modules are logically sound, and runtime terms can be extracted to UB-free C with representation-level guarantees.

---

## 0. Version 0.3 Overview

This document describes **CertiJSON v0.3**.

Changes from v0.2:

1. Introduces a **Prop vs Type** distinction:
   - `Type` = computational types (data, functions).
   - `Prop` = proof-only types (propositions).
   - Erasure is defined primarily on `Prop`.

2. Clarifies **definition roles**:
   - `runtime`, `proof-only`, `both`.

3. Defines a **C-safe type subset** for FFI and extraction:
   - Primitive and struct-like types with explicit `repr`.
   - Only C-safe types may appear at the FFI boundary and as final extracted entrypoints.

4. Tightens `repr` and `extern_c` well-formedness:
   - Formal link between logical type, representation, and C signature.

---

## 1. Design Goals

**G1. Logical soundness**

- Curry–Howard:
  - `Prop` terms are propositions.
  - Terms inhabiting `P : Prop` are proofs.
  - Terms inhabiting `A : Type` are computational values.
- If a module is accepted by the kernel, every `theorem` is a valid theorem in the underlying type theory.

**G2. Total, deterministic core**

- No general recursion.
- Only structurally (or otherwise proven) terminating definitions are accepted.
- Evaluation is deterministic and terminating for all well-typed closed terms.

**G3. Clean separation of logic and computation**

- `Prop` is proof-only.
- `Type` is for runtime data.
- Extraction erases everything living purely in `Prop` and all `proof-only` definitions.

**G4. Safe and deterministic C interop**

- Explicit `repr` (representation descriptors) for all C-visible types.
- `extern_c` declarations tie logical functions to C functions via these representations.
- Extracted C is restricted to a small, UB-free subset.

**G5. LLM-optimized syntax**

- Concrete syntax is JSON.
- No precedence or layout rules.
- Small, fixed set of node kinds with canonical formatting.

---

## 2. Abstract Syntax

The type theory is defined at the level of **abstract syntax**. JSON is a serialization of these terms.

### 2.1 Universes

We distinguish:

- `Type` – universe of computational types.
- `Prop` – universe of propositions (proof-only).

We may later extend to a hierarchy (`Type0`, `Type1`, …); v0.3 keeps a single `Type`.

### 2.2 Names and Meta-Variables

- Term variables: `x, y, z, f, g, ...`
- Types: `A, B, C, ...`
- Terms: `t, u, v, ...`
- Inductive type names: `I, J, ...`
- Constructors: `c, d, ...`
- Global constants: `cst`

### 2.3 Terms

Abstract term grammar:

1. **Variables**

   - `t ::= x`

2. **Universes**

   - `t ::= Type`
   - `t ::= Prop`

3. **Dependent function types**

   - `t ::= Π(x : A). B`

   Where:
   - If `A : Type` and `B : Type`, then `Π(x : A). B : Type`.
   - If either `A` or `B` is in `Prop` (and consistent), it may live in `Prop` as a logical function type.
   - Exact universe rules given in §4.

4. **Lambda abstraction**

   - `t ::= λ(x : A). t`

5. **Application**

   - `t ::= t u` (left-associative).

6. **Equality type (in Prop)**

   - `t ::= Eq_A(u, v)` where `A : Type` or `A : Prop`.

7. **Reflexivity**

   - `t ::= refl_A(u)`.

8. **Global constants / constructors**

   - `t ::= cst`.

9. **Pattern match**

   - `t ::= match t₀ as z return P with (c₁(⃗y¹) ⇒ u₁ | ... | c_k(⃗yᵏ) ⇒ u_k)`.

10. **(Optional) Literals**

   - Implementation-defined base literals (e.g. `nat n`, `int32 n`, `float64 f`) are allowed as extensions and must be given explicit typing and evaluation rules.

### 2.4 Derived Forms

- Universal quantification:
  - `forall (x : A). B` ≜ `Π(x : A). B`.

- Non-dependent function types:
  - `A → B` ≜ `Π(_ : A). B`.

---

## 3. JSON Concrete Syntax

### 3.1 Module Structure

A CertiJSON module is a JSON object:

```json
{
  "module": "ModuleName",
  "declarations": [ Decl, ... ]
}

Yes, let’s roll to 0.4.

I’ll treat v0.4 as an incremental refinement of 0.3 with a focus on things that matter for actually implementing this:
	•	Explicit syntax and rules for equality elimination via a rewrite term.
	•	A clearer, explicit notion of structural recursion at the term level.
	•	A more concrete list of primitive literals and C-safe types.
	•	A minimal but explicit module/import mechanism (LLM-friendly, trivial semantics).
	•	Slightly sharper wording around repr correctness requirements.

Here is a ready-to-drop spec-0.4.md:

⸻


# CertiJSON Core Language Specification (v0.4)

_Working name_: **CertiJSON**  
_Goal_: A pure, total, dependently typed language with JSON concrete syntax, designed for LLM agents. All accepted modules are logically sound, and runtime terms can be extracted to UB-free C with representation-level guarantees.

---

## 0. Version 0.4 Overview

This document describes **CertiJSON v0.4**.

Changes from v0.3:

1. Introduces an explicit **`rewrite` term** for equality elimination (instead of relying on an implicit `J`).
2. Specifies **structural recursion** more concretely by adding a `rec_args` annotation to recursive `def`s and restricting recursive calls syntactically.
3. Defines a small, fixed set of **primitive literals and primitive types** (e.g. `Int32`, `Int64`, `Float64`, `Bool`) and marks them as **C-safe** by default.
4. Adds a minimal **module/import system**:
   - Modules have `module` and optional `imports`.
   - Names from imports are available in the global environment in a flat way.
5. Tightens the description of `repr` correctness and notes that encode/decode functions are expected and should be provable in the core language.

---

## 1. Design Goals (unchanged in spirit)

**G1. Logical soundness**

- `Prop` is the universe of propositions.
- `Type` is the universe of computational types.
- If a module is accepted, every `theorem` is a valid theorem in the underlying type theory.

**G2. Total, deterministic core**

- No general recursion; only total functions (structural recursion for v0.4).
- Evaluation is deterministic and strongly normalizing for well-typed closed terms.

**G3. Clean separation of computation and proof**

- `Type` for data and computations.
- `Prop` for proofs and propositions.
- Erasure removes `Prop`-only terms and `proof-only` definitions.

**G4. Safe C interop**

- Explicit `repr` describe ABI layouts.
- `extern_c` uses `repr` to define the boundary precisely.
- Extracted C code is within a small, UB-free subset.

**G5. LLM-optimized JSON syntax**

- Concrete syntax is JSON only.
- Fixed, small set of node kinds.
- No precedence rules, no layout rules.

---

## 2. Abstract Syntax

The core type theory is defined at the level of **abstract syntax**.

### 2.1 Universes

- `Type` – universe of computational types (values).
- `Prop` – universe of propositions (proofs).

### 2.2 Names and Meta-Variables

- Variables: `x, y, z, f, g, ...`
- Types: `A, B, C, ...`
- Terms: `t, u, v, ...`
- Inductive names: `I, J, ...`
- Constructors: `c, d, ...`
- Global constants: `cst`

### 2.3 Primitive Types and Literals

v0.4 fixes a minimal primitive set:

- Primitive types (all in `Type`):
  - `Int32`, `Int64`, `Float64`, `Bool`, `Size`
- Literals (abstract view):
  - `int32(n)` for `n ∈ ℤ` in the range of 32-bit signed int.
  - `int64(n)` for 64-bit.
  - `float64(f)` for 64-bit IEEE.
  - `bool(b)` where `b ∈ {true, false}`.

These primitives are **C-safe** and have canonical `repr` (see §8).

### 2.4 Terms

Abstract term grammar:

1. Variable  
   `t ::= x`

2. Universes  
   `t ::= Type | Prop`

3. Dependent function type (Π)  
   `t ::= Π(x : A). B`

4. Lambda abstraction  
   `t ::= λ(x : A). t`

5. Application  
   `t ::= t u` (left-associative)

6. Equality type  
   `t ::= Eq_A(u, v)`

7. Equality reflexivity  
   `t ::= refl_A(u)`

8. Equality elimination **(new explicit form)**  
   `t ::= rewrite e in t_body`  
   where `e : Eq_A(u, v)` and `t_body` is a term whose type depends on `u`. See §4.4.

9. Global constants / constructors  
   `t ::= cst`

10. Pattern match  
   `t ::= match t₀ as z return P with (c₁(⃗y¹) ⇒ u₁ | ... | c_k(⃗yᵏ) ⇒ u_k)`

11. Primitive literals  
   `t ::= int32(n) | int64(n) | float64(f) | bool(b)`  

(Concrete forms for literals are defined in JSON; this is the abstract view.)

### 2.5 Derived Forms

- `forall (x : A). B` ≜ `Π(x : A). B`.
- `A → B` ≜ `Π(_ : A). B`.

---

## 3. JSON Concrete Syntax

### 3.1 Module and Imports

A CertiJSON module is a JSON object:

```json
{
  "module": "ModuleName",
  "imports": [ "OtherModule1", "OtherModule2" ],
  "declarations": [ Decl, ... ]
}

	•	imports is optional. If present, it is a list of module names whose public declarations are added to the global environment Σ for this module.
	•	The import mechanism is flat: no namespaces. Name collisions must be rejected by the implementation or disambiguated via pre-processing; v0.4 assumes modules are combined into a single global signature without clashes.

3.2 Terms (JSON → Abstract)

Let ⟦·⟧ map JSON nodes to abstract terms.
	1.	Variable

{ "var": "x" }

⟦·⟧ = x.

	2.	Universes

{ "universe": "Type" }
{ "universe": "Prop" }

⟦·⟧ = Type, Prop.

	3.	Π-type

{
  "pi": {
    "arg": { "name": "x", "type": A_json },
    "result": B_json
  }
}

⟦·⟧ = Π(x : ⟦A_json⟧). ⟦B_json⟧.

	4.	Forall (sugar)

{
  "forall": {
    "arg": { "name": "x", "type": A_json },
    "result": B_json
  }
}

⟦·⟧ = Π(x : ⟦A_json⟧). ⟦B_json⟧.

	5.	Lambda

{
  "lambda": {
    "arg": { "name": "x", "type": A_json },
    "body": t_json
  }
}

⟦·⟧ = λ(x : ⟦A_json⟧). ⟦t_json⟧.

	6.	Application

{ "app": [ t_json, u1_json, u2_json, ... ] }

⟦·⟧ = (((⟦t_json⟧ ⟦u1_json⟧) ⟦u2_json⟧) ...).

	7.	Equality

{
  "eq": {
    "type": A_json,
    "lhs":  u_json,
    "rhs":  v_json
  }
}

⟦·⟧ = Eq_⟦A_json⟧(⟦u_json⟧, ⟦v_json⟧).

	8.	Reflexivity

{
  "refl": {
    "eq": {
      "type": A_json,
      "lhs":  u_json,
      "rhs":  v_json
    }
  }
}

⟦·⟧ = refl_⟦A_json⟧(⟦u_json⟧) with the usual side condition (lhs ≡ rhs at type-check time).

	9.	rewrite (new)

{
  "rewrite": {
    "proof": e_json,
    "in": t_json
  }
}

⟦·⟧ = rewrite ⟦e_json⟧ in ⟦t_json⟧.

	10.	Match

{
  "match": {
    "scrutinee": t0_json,
    "motive": P_json,
    "as": "z",
    "cases": [
      {
        "pattern": {
          "ctor": "C1",
          "args": [ { "name": "y1" }, { "name": "y2" } ]
        },
        "body": u1_json
      }
    ]
  }
}

⟦·⟧ =
match ⟦t0_json⟧ as z return ⟦P_json⟧ with (C1(y1, y2) ⇒ ⟦u1_json⟧ | ...).
	11.	Literals

{ "int32": 123 }
{ "int64": 1234567890 }
{ "float64": 3.14 }
{ "bool": true }

map to int32(123), int64(1234567890), float64(3.14), bool(true).
	12.	Global names

{ "var": "Nat" }
{ "var": "succ" }
{ "var": "plus" }

map to constants/constructors in Σ.

Invalid nodes or missing fields are rejected before type checking.

3.3 Inductive Declarations (JSON)

Same as v0.3:

{
  "inductive": {
    "name": "I",
    "params": [
      { "name": "x1", "type": A1_json },
      ...
    ],
    "universe": "Type",
    "constructors": [
      {
        "name": "C1",
        "args": [
          { "name": "y1", "type": B11_json },
          ...
        ]
      },
      ...
    ]
  }
}

3.4 def / theorem Declarations, with Recursion Annotation

def

{
  "def": {
    "name": "f",
    "role": "runtime",      // "runtime" | "proof-only" | "both" (default "both")
    "type": A_json,
    "body": t_json,
    "rec_args": [0]         // NEW: indices of structurally recursive arguments (optional)
  }
}

	•	rec_args:
	•	A list of 0-based argument indices which are designated as structurally decreasing arguments for recursion.
	•	Empty or omitted means the definition is non-recursive.
	•	The termination checker uses rec_args to enforce structural recursion (see §7).

Abstractly: def f : ⟦A_json⟧ := ⟦t_json⟧.

theorem

{
  "theorem": {
    "name": "p",
    "type": P_json,
    "proof": t_json
  }
}

Abstractly: def p : ⟦P_json⟧ := ⟦t_json⟧ with role = proof-only.

⸻

4. Typing

Same basic judgment as 0.3:

Σ; Γ ⊢ t : A

with A : Type or A : Prop.

4.1 Contexts and Definitional Equality
	•	Contexts Γ are sequences of bindings x : A.
	•	Σ; Γ ⊢ A ≡ B is definitional equality (β, unfolding, α, congruence).

4.2 Core Typing Rules

These are as in v0.3, but summarized:
	•	(Var), (Universe), (Pi), (Lambda), (App), (Conversion), (Eq-Form), (Eq-Refl), (Inductive), (Constructor), (Match) remain unchanged.
	•	Literal typing:
	•	Σ; Γ ⊢ int32(n) : Int32
	•	Σ; Γ ⊢ int64(n) : Int64
	•	Σ; Γ ⊢ float64(f) : Float64
	•	Σ; Γ ⊢ bool(b) : Bool

4.3 Universe Rule for Π

Exactly as in 0.3:
	•	If Σ; Γ ⊢ A : Type and Σ; Γ, x : A ⊢ B : Type then Σ; Γ ⊢ Π(x : A). B : Type.
	•	If A : Type or Prop, and B : Prop, then Π(x : A). B : Prop.

4.4 Typing Rule for rewrite (explicit equality elimination)

We introduce an explicit rewrite construct:

Abstract form: rewrite e in t_body.

Intuition:
	•	e : Eq_A(u, v).
	•	t_body is typed in a context where some occurrences refer to u.
	•	After rewriting, those occurrences are replaced by v.

We formalize this as the standard transport along equality (like Coq’s eq_rect / J), in a simplified form:

Let P be a family P : A → Type or P : A → Prop.

We define the typing rule:

If
	1.	Σ; Γ ⊢ A : Type or Prop.
	2.	Σ; Γ ⊢ u : A.
	3.	Σ; Γ ⊢ v : A.
	4.	Σ; Γ ⊢ e : Eq_A(u, v).
	5.	Σ; Γ, x : A ⊢ P : U where U ∈ {Type, Prop}.
	6.	Σ; Γ ⊢ t_body : P[x := u].

then:

Σ; Γ ⊢ rewrite e in t_body : P[x := v]

Concretely, in JSON, rewrite carries only proof and in fields. The motive P and distinguished variable x are inferred by the kernel from the type of t_body and the equality e (like Coq’s rewrite tactic). Implementation details are left to the checker; the rule above specifies the intended typing relation.

⸻

5. Global Declarations

Same as v0.3, plus recursion annotations.

5.1 Inductive

As before: well-formedness of parameters and strict positivity.

5.2 def + Roles

Same: def f : A := t with role ∈ {runtime, proof-only, both} accepted if:
	1.	Σ; · ⊢ A : Type or Prop.
	2.	Σ; · ⊢ t : A.
	3.	Termination checker accepts t given rec_args (see §7).

5.3 theorem

As before: sugar for def with role = proof-only.

⸻

6. Evaluation

Big-step evaluation t ⇓ v as in v0.3.
	•	Values: λs, constructors applied to values, universes, Π-types, equality types, literals.
	•	Key rules: unfolding of def, β-reduction, match on constructors, plus appropriate rules for literals.

For rewrite, we require that evaluation is proof-irrelevant:
	•	rewrite e in t_body evaluates by leaving t_body as-is up to definitional equality; the runtime effect of rewrite is erased at extraction.
	•	In other words, rewrite is logically meaningful but computationally a no-op (it reduces to t_body or its normalized counterpart).

⸻

7. Termination and Structural Recursion (concretized)

v0.4 requires structural recursion for all recursive definitions.

Given:

{
  "def": {
    "name": "f",
    "type": A_json,
    "body": t_json,
    "rec_args": [i1, i2, ...]
  }
}

Let the abstract type of f be:

f : Π(a₀ : A₀). Π(a₁ : A₁)... Π(a_n : A_n). R

	•	Each index ij in rec_args refers to an argument a_ij of inductive type (or a structurally equivalent type).
	•	In the body t, every recursive call f u₀ ... u_n must satisfy:
	•	For at least one ij in rec_args, u_ij is a structural subterm of a_ij (e.g. a pattern variable bound by matching on a_ij).
	•	No recursive call may use an argument that is not strictly smaller on all designated structural positions.

The exact structural-subterm relation is:
	•	t is a structural subterm of itself (for pattern bindings).
	•	If a is of an inductive type I, and in a pattern c(… , x, …), then each x bound in the pattern is a structural subterm of c(…).

The termination checker is allowed to be conservative (rejecting some terminating definitions) but must be sound: any definition it accepts is strongly normalizing.

⸻

8. C-Safe Types and repr

8.1 Primitive C-Safe Types (fixed set)

The following logical types are C-safe with canonical repr (predefined):
	•	Int32 ↔ int32_t
	•	Int64 ↔ int64_t
	•	Float64 ↔ double
	•	Bool ↔ uint8_t (0 = false, 1 = true)
	•	Size ↔ size_t

Each has a predefined repr descriptor in the standard library.

8.2 C-Safe Type Predicate

We say CType(T) holds if:
	1.	T is a primitive C-safe type, or
	2.	T is a struct-like type with a repr that:
	•	Uses only fields whose types are C-safe.
	•	Has a finite, fixed layout.

Any type used:
	•	As an argument or result of extern_c.
	•	As the final type of a function intended for C entrypoints.

must satisfy CType.

8.3 repr Declarations

Same shape as v0.3, but with normative requirements:
	•	A repr describes:
	•	Either a primitive c_type or a struct with fields.
	•	Size and alignment (primitive or computed).
	•	For each repr R and logical type T linked to it, we require the existence (in the standard library) of:

encode_T : T → Bytes(size_bytes(R))
decode_T : Bytes(size_bytes(R)) → Option T

and a theorem:

theorem decode_encode_roundtrip :
  ∀(v : T), decode_T (encode_T v) = Some v.


	•	These functions and theorem are not part of the kernel but are expected to be provable in CertiJSON itself; they serve as the link between logic and representation.

⸻

9. extern_c Declarations

Same idea as v0.3, with the primitive C-safe set now explicit.

Shape:

{
  "extern_c": {
    "name": "c_sin",
    "c_name": "sin",
    "header": "<math.h>",
    "signature": {
      "return": { "repr": "Float64Repr" },
      "args": [
        { "name": "x", "repr": "Float64Repr" }
      ]
    },
    "type": {
      "pi": {
        "arg": { "name": "_", "type": { "var": "Float64" } },
        "result": { "var": "Float64" }
      }
    },
    "safety": "pure",
    "axioms": [ /* optional theorems as specs */ ]
  }
}

Well-formedness as in 0.3, plus:
	•	Every repr used must correspond to a type that satisfies CType.
	•	The logical type must be first-order in terms of C-safe types (no higher-order arguments crossing the boundary).

⸻

10. Extraction (Intent)

Extraction behavior is the same as 0.3 but with rewrite explicitly erased:
	•	Erasure removes:
	•	All Prop terms and proof-only definitions.
	•	rewrite constructs (they reduce to their in term at runtime).
	•	Translation to C uses only:
	•	CType-conformant types and repr.
	•	Functions with role = runtime or both.

The ultimate goal remains:

Extracted C code is observationally equivalent to CertiJSON evaluation for all runtime-typed terms, modulo assumed extern_c axioms.

⸻

11. Meta-Theoretic Targets (unchanged, restated)

For the core language (ignoring repr and extern_c):
	1.	Type Soundness
	2.	Strong Normalization
	3.	Logical Soundness

For the representation and FFI layer:
	4.	Representation Soundness (via encode/decode proofs).
	5.	FFI ABI Safety (via repr and extern_c well-formedness).
	6.	Extraction Correctness (future mechanized result).

⸻

Appendix A: Minimal Predefined Entities

Non-normative but recommended:
	•	Bool : Type, with constructors true, false, and repr linking it to uint8_t.
	•	Nat : Type, with constructors zero, succ (not C-safe by default).
	•	Int32, Int64, Float64, Size : Type with primitive reprs.
	•	List (A : Type) : Type with constructors nil, cons (not C-safe by default).

These provide a minimal working environment for LLM agents.

⸻


If you want to push this one step further for 0.5, we could either (a) add a tiny *formal* small-step semantics for the C-subset and outline a proof sketch for extraction correctness, or (b) start specifying a JSON Schema for modules so that syntactic well-formedness is machine-checked even before type checking.

# CertiJSON Core Language Specification (v0.5)

_Working name_: **CertiJSON**  
_Goal_: A pure, total, dependently typed language with JSON concrete syntax, designed for LLM agents. All accepted modules are logically sound, and runtime terms can be extracted to a small, UB-free C-subset with representation-level guarantees.

---

## 0. Version 0.5 Overview

This document describes **CertiJSON v0.5**.

Changes from v0.4:

1. Introduces a **formal erasure function** `erase : Term → Term` (from full core to runtime core).
2. Defines a tiny, explicit C-like target language **Cmini**:
   - Syntax, typing, small-step semantics.
   - Only features needed by extraction.
3. Specifies an **extraction function** `E : RuntimeTerm → CminiProgram`.
4. States a precise **simulation theorem** (extraction correctness, at least for closed programs without FFI).
5. Tightens and clarifies how `extern_c` hooks into Cmini (via external declarations).

Everything else from 0.4 (Prop/Type, rewrite, structural recursion, JSON concrete syntax, repr/extern_c) is kept and referenced.

---

## 1. Design Goals (summary)

**G1. Logical soundness**

- `Prop` = propositions, `Type` = computational types.
- `theorem` declarations and proof terms live in the core type theory.

**G2. Total, deterministic core**

- Only structurally terminating `def`s.
- Evaluation is deterministic and strongly normalizing.

**G3. Proof/compute separation**

- `Prop` and `proof-only` definitions are erased for runtime.
- Only `Type`-typed, `runtime`/`both` definitions survive into runtime core and extraction.

**G4. Verified extraction target**

- Extraction targets **Cmini**, a small, UB-free C-like language.
- `repr` and `extern_c` describe how CertiJSON values map to C data and C functions.

---

## 2. Core Language (unchanged from 0.4)

The logical core (CertiJSON terms, types, inductives, typing, evaluation, `rewrite`, structural recursion, `repr`, `extern_c`) is as in **v0.4**.

We do not repeat all of v0.4; instead we refine and extend with:

- A formal **erasure** (Section 3).
- Target language **Cmini** (Sections 4–5).
- Extraction and correctness (Section 6).

Assumption: We have:

- Typing judgment: `Σ; Γ ⊢ t : A` with `A : Type` or `A : Prop`.
- Big-step evaluation: `t ⇓ v` on fully elaborated core terms.

---

## 3. Erasure: From Full Core to Runtime Core

Erasure removes all proof-only and `Prop`-only parts, leaving a **runtime core** that has no `Prop`, no `rewrite`, and no proof-only constants.

### 3.1 Runtime Core Language

Runtime terms `tr` are a subset of full terms:

- Variables: `x`
- Universes: `Type` (but not `Prop` in types at runtime)
- Π-types: `Π(x : A). B` with `A, B : Type`
- Lambdas: `λ(x : A). t`
- Applications: `t u`
- Inductive types and constructors whose types live in `Type`
- Pattern match: `match ...` where motive returns `Type`
- Primitive literals: `int32(n)`, `int64(n)`, `float64(f)`, `bool(b)`
- No `Prop`, no `Eq`, no `refl`, no `rewrite` at runtime

Runtime contexts and types refer only to `Type`-inhabited types.

### 3.2 Erasure Function

We define a partial function:

> `erase : Term → RuntimeTerm`

which may be undefined if the term is purely propositional or clearly non-runtime. For well-typed closed terms of `Type`, `erase` is defined.

We write `|t|` for `erase(t)`.

Definition by cases (informal, but precise enough):

1. **Variables**

   - `erase(x) = x`.

2. **Universes**

   - `erase(Type) = Type`.
   - `erase(Prop)` is undefined as a runtime type (values of type `Prop` are not runtime).

3. **Π-type**

   - If `Σ; Γ ⊢ Π(x : A). B : Type` then:

     ```text
     erase(Π(x : A). B) = Π(x : erase(A)). erase(B)
     ```

   - If the result type lives in `Prop` (function producing proofs), its erasure is not used as a runtime type; such functions are not extracted.

4. **Lambda**

   - For `λ(x : A). t` with `A, t` runtime-meaningful:

     ```text
     erase(λ(x : A). t) = λ(x : erase(A)). erase(t)
     ```

5. **Application**

   - `erase(t u) = erase(t) erase(u)`.

6. **Equality and Proof Terms**

   - `erase(Eq_A(u, v))` is undefined as runtime.
   - `erase(refl_A(u))` is undefined.
   - `erase(rewrite e in t_body) = erase(t_body)`.

   These never appear in runtime positions; they are used only in `Prop` and `proof-only` definitions.

7. **Inductive Types and Constructors**

   - If `I : Π(⃗x : ⃗A). Type`:

     ```text
     erase(I) = I
     erase(c) = c
     ```

     (Names are kept; their types have been erased accordingly.)

8. **Pattern Match**

   - `erase(match t₀ as z return P with cases)`
   - If `P` is a motive returning `Type`, `erase` applies recursively:

     ```text
     erase(match t₀ as z return P with (c₁(⃗y¹) ⇒ u₁ | ...)) =
       match erase(t₀) as z return erase(P) with (c₁(⃗y¹) ⇒ erase(u₁) | ...)
     ```

   - If `P` returns `Prop`, such matches are `Prop`-only and will not appear in runtime; `erase` is not needed there.

9. **Primitive Literals**

   - `erase(int32(n)) = int32(n)` (and similarly for others).

10. **Global Constants**

   For a definition:

   - `def f : A := t` with `role = runtime` or `both` and `A : Type`:

     - `erase(f) = f` (we keep the name).
     - `erase(t)` is defined; `f`’s runtime body is `erase(t)`.

   For `role = proof-only` or `A : Prop`: `f` is erased; `erase(f)` is undefined (or mapped to a special symbol that must not appear at runtime).

### 3.3 Erasure Properties (Intended)

For any well-typed, closed `t : A` with `A : Type` and `role` allowing runtime:

- `erase(t)` is a well-typed runtime term of some erased type `erase(A)` in the runtime core.
- Evaluation in full core and runtime core coincide on observable values (modulo proofs), i.e.:

  ```text
  t ⇓ v  ⇒  erase(t) ⇓ erase(v)

# CertiJSON Core Language Specification (v0.5)

_Working name_: **CertiJSON**  
_Goal_: A pure, total, dependently typed language with JSON concrete syntax, designed for LLM agents. All accepted modules are logically sound, and runtime terms can be extracted to a small, UB-free C-subset with representation-level guarantees.

---

## 0. Version 0.5 Overview

This document describes **CertiJSON v0.5**.

Changes from v0.4:

1. Introduces a **formal erasure function** `erase : Term → Term` (from full core to runtime core).
2. Defines a tiny, explicit C-like target language **Cmini**:
   - Syntax, typing, small-step semantics.
   - Only features needed by extraction.
3. Specifies an **extraction function** `E : RuntimeTerm → CminiProgram`.
4. States a precise **simulation theorem** (extraction correctness, at least for closed programs without FFI).
5. Tightens and clarifies how `extern_c` hooks into Cmini (via external declarations).

Everything else from 0.4 (Prop/Type, rewrite, structural recursion, JSON concrete syntax, repr/extern_c) is kept and referenced.

---

## 1. Design Goals (summary)

**G1. Logical soundness**

- `Prop` = propositions, `Type` = computational types.
- `theorem` declarations and proof terms live in the core type theory.

**G2. Total, deterministic core**

- Only structurally terminating `def`s.
- Evaluation is deterministic and strongly normalizing.

**G3. Proof/compute separation**

- `Prop` and `proof-only` definitions are erased for runtime.
- Only `Type`-typed, `runtime`/`both` definitions survive into runtime core and extraction.

**G4. Verified extraction target**

- Extraction targets **Cmini**, a small, UB-free C-like language.
- `repr` and `extern_c` describe how CertiJSON values map to C data and C functions.

---

## 2. Core Language (unchanged from 0.4)

The logical core (CertiJSON terms, types, inductives, typing, evaluation, `rewrite`, structural recursion, `repr`, `extern_c`) is as in **v0.4**.

We do not repeat all of v0.4; instead we refine and extend with:

- A formal **erasure** (Section 3).
- Target language **Cmini** (Sections 4–5).
- Extraction and correctness (Section 6).

Assumption: We have:

- Typing judgment: `Σ; Γ ⊢ t : A` with `A : Type` or `A : Prop`.
- Big-step evaluation: `t ⇓ v` on fully elaborated core terms.

---

## 3. Erasure: From Full Core to Runtime Core

Erasure removes all proof-only and `Prop`-only parts, leaving a **runtime core** that has no `Prop`, no `rewrite`, and no proof-only constants.

### 3.1 Runtime Core Language

Runtime terms `tr` are a subset of full terms:

- Variables: `x`
- Universes: `Type` (but not `Prop` in types at runtime)
- Π-types: `Π(x : A). B` with `A, B : Type`
- Lambdas: `λ(x : A). t`
- Applications: `t u`
- Inductive types and constructors whose types live in `Type`
- Pattern match: `match ...` where motive returns `Type`
- Primitive literals: `int32(n)`, `int64(n)`, `float64(f)`, `bool(b)`
- No `Prop`, no `Eq`, no `refl`, no `rewrite` at runtime

Runtime contexts and types refer only to `Type`-inhabited types.

### 3.2 Erasure Function

We define a partial function:

> `erase : Term → RuntimeTerm`

which may be undefined if the term is purely propositional or clearly non-runtime. For well-typed closed terms of `Type`, `erase` is defined.

We write `|t|` for `erase(t)`.

Definition by cases (informal, but precise enough):

1. **Variables**

   - `erase(x) = x`.

2. **Universes**

   - `erase(Type) = Type`.
   - `erase(Prop)` is undefined as a runtime type (values of type `Prop` are not runtime).

3. **Π-type**

   - If `Σ; Γ ⊢ Π(x : A). B : Type` then:

     ```text
     erase(Π(x : A). B) = Π(x : erase(A)). erase(B)
     ```

   - If the result type lives in `Prop` (function producing proofs), its erasure is not used as a runtime type; such functions are not extracted.

4. **Lambda**

   - For `λ(x : A). t` with `A, t` runtime-meaningful:

     ```text
     erase(λ(x : A). t) = λ(x : erase(A)). erase(t)
     ```

5. **Application**

   - `erase(t u) = erase(t) erase(u)`.

6. **Equality and Proof Terms**

   - `erase(Eq_A(u, v))` is undefined as runtime.
   - `erase(refl_A(u))` is undefined.
   - `erase(rewrite e in t_body) = erase(t_body)`.

   These never appear in runtime positions; they are used only in `Prop` and `proof-only` definitions.

7. **Inductive Types and Constructors**

   - If `I : Π(⃗x : ⃗A). Type`:

     ```text
     erase(I) = I
     erase(c) = c
     ```

     (Names are kept; their types have been erased accordingly.)

8. **Pattern Match**

   - `erase(match t₀ as z return P with cases)`
   - If `P` is a motive returning `Type`, `erase` applies recursively:

     ```text
     erase(match t₀ as z return P with (c₁(⃗y¹) ⇒ u₁ | ...)) =
       match erase(t₀) as z return erase(P) with (c₁(⃗y¹) ⇒ erase(u₁) | ...)
     ```

   - If `P` returns `Prop`, such matches are `Prop`-only and will not appear in runtime; `erase` is not needed there.

9. **Primitive Literals**

   - `erase(int32(n)) = int32(n)` (and similarly for others).

10. **Global Constants**

   For a definition:

   - `def f : A := t` with `role = runtime` or `both` and `A : Type`:

     - `erase(f) = f` (we keep the name).
     - `erase(t)` is defined; `f`’s runtime body is `erase(t)`.

   For `role = proof-only` or `A : Prop`: `f` is erased; `erase(f)` is undefined (or mapped to a special symbol that must not appear at runtime).

### 3.3 Erasure Properties (Intended)

For any well-typed, closed `t : A` with `A : Type` and `role` allowing runtime:

- `erase(t)` is a well-typed runtime term of some erased type `erase(A)` in the runtime core.
- Evaluation in full core and runtime core coincide on observable values (modulo proofs), i.e.:

  ```text
  t ⇓ v  ⇒  erase(t) ⇓ erase(v)

(We will refine this when defining simulation.)

⸻

4. Target Language Cmini: Syntax

Cmini is a tiny, structured, C-like language used as extraction target.

4.1 High-Level Overview

Cmini features:
	•	First-order functions (no function pointers).
	•	Base types matching C-safe types: int32, int64, double, u8, size.
	•	Struct types with named fields.
	•	Locals, assignments, if-then-else, while loops (though extraction may not need all).
	•	Statements and expressions are separate (C-style).
	•	No undefined behavior by construction (we define semantics only for in-bounds, initialized operations).

4.2 Types (Cmini)

τ (Cmini types):
	•	Primitive:

τ ::= int32 | int64 | double | u8 | size


	•	Struct:

τ ::= struct S

where S is a struct name.

4.3 Expressions

e (expressions):
	•	Variables: x
	•	Integer / float / bool literals:
	•	n32, n64, f64, b (where b ∈ {true, false})
	•	Field access:
	•	e.f
	•	Binary operations:
	•	e1 + e2, e1 - e2, e1 * e2, etc. (exact set minimal, e.g. just + for Nat-like extraction).
	•	Function call:
	•	f(e1, ..., en)

4.4 Statements

s (statements):
	•	skip
	•	Sequential composition: s1; s2
	•	Local variable declaration: τ x = e;
	•	Assignment: x = e;
	•	Return: return e;
	•	Conditionals:

if (e) { s1 } else { s2 }


	•	(Optional) while loops:

while (e) { s }

Extraction of structurally recursive functions can be expressed without explicit loops, but we may allow them for future optimization.

4.5 Functions and Programs

A function:

func f(τ1 x1, ..., τn xn) : τret {
  s
}

A program:

Program ::= (StructDecl)* (ExternDecl)* (FuncDecl)*

	•	StructDecl defines struct S { τ1 f1; ...; τk fk; };
	•	ExternDecl defines extern τ f(τ1, ..., τn); (used for extern_c).
	•	FuncDecl defines func f(...) : τ { ... }.

⸻

5. Cmini Semantics

We give a small-step operational semantics for Cmini.

5.1 Runtime Configuration

A configuration is:
	•	⟨P, F, s, σ, ρ⟩ where:
	•	P is the program (fixed).
	•	F is the current function name.
	•	s is the current statement (rest of body).
	•	σ is the store: a mapping from variable names to values (primitives or structs).
	•	ρ is the call stack: a stack of frames.
	•	A frame contains: return address (F', s'), variable environment snapshot for the caller, and the destination variable for the return value (or “top-level return”).

Values v in Cmini are:
	•	Primitive constants: n32, n64, f64, b, sz.
	•	Struct values: (S, {f1 = v1, ..., fk = vk}).

For simplicity, we assume no heap; structs are stored by value in locals.

5.2 Expression Evaluation

We define an evaluation judgment:

P; σ ⊢ e ⇓ v

for expressions e without side effects (Cmini expressions are pure). For example:
	•	P; σ ⊢ x ⇓ σ(x)
	•	P; σ ⊢ n32 ⇓ n32
	•	P; σ ⊢ e1 + e2 ⇓ v3
if P; σ ⊢ e1 ⇓ v1, P; σ ⊢ e2 ⇓ v2, and v3 is the integer sum (computed in defined range).
	•	P; σ ⊢ e.f ⇓ v_f
if P; σ ⊢ e ⇓ (S, { ..., f = v_f, ... }).

Function calls in expressions are not allowed; they appear only as a statement form return f(e1,...,en) (or as call statements). For simplicity, our expressions are side-effect free.

5.3 Statement Small-Step Semantics

We define small-step transitions:

⟨P, F, s, σ, ρ⟩ → ⟨P, F', s', σ', ρ'⟩

Selected rules:
	•	Seq-Skip

⟨P, F, skip; s2, σ, ρ⟩ → ⟨P, F, s2, σ, ρ⟩


	•	Decl
For τ x = e; s2:
If P; σ ⊢ e ⇓ v, then:

⟨P, F, τ x = e; s2, σ, ρ⟩ → ⟨P, F, s2, σ[x ↦ v], ρ⟩


	•	Assign
For x = e; s2:
If P; σ ⊢ e ⇓ v, then:

⟨P, F, x = e; s2, σ, ρ⟩ → ⟨P, F, s2, σ[x ↦ v], ρ⟩


	•	If-True / If-False
If P; σ ⊢ e ⇓ bool(true):

⟨P, F, if (e) { s1 } else { s2 }, σ, ρ⟩ → ⟨P, F, s1, σ, ρ⟩

If P; σ ⊢ e ⇓ bool(false):

⟨P, F, if (e) { s1 } else { s2 }, σ, ρ⟩ → ⟨P, F, s2, σ, ρ⟩


	•	Return (no caller)
For top-level main function returning value:
If P; σ ⊢ e ⇓ v and ρ is empty:

⟨P, F, return e;, σ, []⟩ → ⟨P, F, done, σ, []⟩

with the returned value implicitly recorded as the result of the program.

	•	Function Call (modeled via call/return)
Extraction uses explicit function calls modeled as:

call f(e1,...,en); s_rest

(or as x = f(e1,...,en); s_rest; either way we translate them to stack operations.)
	•	Evaluate arguments: P; σ ⊢ ei ⇓ vi.
	•	Push frame (F, s_rest, x, σ) onto ρ.
	•	Initialize new σ' with parameters bound to vi.
	•	Set F' = f, s' = body_f.
On return e; in f, we:
	•	Evaluate e to v.
	•	Pop frame (F_caller, s_rest, x_ret, σ_caller).
	•	Set σ_caller[x_ret ↦ v].
	•	Continue in caller:

⟨P, f, return e;, σ, ρ :: (F_caller, s_rest, x_ret, σ_caller)⟩
→
⟨P, F_caller, s_rest, σ_caller[x_ret ↦ v], ρ⟩



Exact details can be tuned, but the key is: no UB, values always initialized, and semantics is deterministic.

⸻

6. Extraction: From Runtime Core to Cmini

We now specify an extraction function:

E : RuntimeTerm → CminiProgram

For v0.5, we concentrate on fully applied, closed, first-order functions:
	•	Closed runtime definition:

def main : A := t

with A a C-safe type (CType(A)).

We assume all runtime definitions f are:
	•	First-order.
	•	Only take and return C-safe types (after repr resolution).
	•	Finite, structurally recursive, and total.

6.1 Types Translation

We define a mapping:

T ⟦·⟧ : Type → τ  (CertiJSON runtime type → Cmini type)

	•	For primitive C-safe types:

T⟦Int32⟧   = int32
T⟦Int64⟧   = int64
T⟦Float64⟧ = double
T⟦Bool⟧    = u8
T⟦Size⟧    = size


	•	For struct-like types linked to repr:
	•	For logical type Point2D with repr Point2DRepr defining struct Point2D { int32 x; int32 y; }; we set:

T⟦Point2D⟧ = struct Point2D


The extraction tool generates the corresponding StructDecl in Cmini.

Complex inductives not used at C boundary may be compiled into internal structs and tagged unions; v0.5 does not fully specify that encoding; we assume only C-safe (finite struct-like) types cross the boundary.

6.2 Term Translation (High-Level)

We define a family of translations:
	•	E_fun(f) : FuncDecl for each runtime function f.
	•	E_term(t) : CminiExpr/CminiStmt depending on context.

Sketch:
	1.	Functions
For a definition:

def f : Π(a₁ : A₁)...(a_n : A_n). R := t

with all Aᵢ, R C-safe:
	•	Generate a Cmini function:

func f(T⟦A₁⟧ a₁, ..., T⟦A_n⟧ a_n) : T⟦R⟧ {
  s_body
}


	•	s_body is obtained from E_stmt(t_return) where t_return is a core term representing t with explicit arguments; we translate pattern matches into if/switch, etc.

	2.	Pattern Matches
	•	Inductives that are C-safe and struct-like become structs with finite tags; pattern matches are compiled to:
	•	A tag inspection (if needed) plus field extraction into local variables (τ yi = x.f_i;).
	•	Nested if/switch for constructors.
	3.	Literals and Arithmetic
	•	Direct mapping: int32(n) → n32, etc.
	•	Primitive operations (like plus for Nat or arithmetic on primitives) become arithmetic expressions e1 + e2. For more complex operations, we introduce library functions.
	4.	Recursion
	•	Structural recursion in core becomes function recursion in Cmini, matching the call rules above. Because the core is total, recursion in Cmini is total (no UB, no divergence).

6.3 Program Extraction

Given a module M with runtime definitions f1, ..., fk and a chosen entrypoint main:
	•	E(M) constructs:
	•	Struct declarations for all repr-annotated C-safe types used in M.
	•	Extern declarations for each extern_c.
	•	Function declarations for each runtime function fᵢ.
	•	Marks main as the top-level function (or generates a thin wrapper).

Result: a Cmini program P.

⸻

7. Extraction Correctness (Simulation)

We now specify the correctness property we want extraction to satisfy.

7.1 Core vs Cmini Results

Let:
	•	t be a closed CertiJSON term of type T with T : Type, CType(T).
	•	v be its CertiJSON value: t ⇓ v.
	•	P = E(t) be the extracted Cmini program (with main calling the compiled t).
	•	P ⇓ v_c mean: running P under Cmini semantics yields final value v_c.

We define a value correspondence:

V⟦T⟧(v, v_c) meaning “CertiJSON value v of type T corresponds to Cmini value v_c of type T⟦T⟧”.

This is defined via repr/encode/decode:
	•	If T is primitive (e.g. Int32), then V⟦Int32⟧(int32(n), n32) is true iff they share the same numeric value.
	•	If T is struct-like with repr R, then V⟦T⟧(v, v_c) holds iff:
	•	encode_T(v) equals the byte sequence encoding of v_c, or equivalently,
	•	decode_T applied to the byte representation of v_c yields Some v.

7.2 Simulation Theorem (No FFI)

Theorem 1 (Extraction correctness without extern_c, sketch).

Assume:
	•	No extern_c calls are used in the program (pure CertiJSON).
	•	t is a closed term with Σ; · ⊢ t : T and T : Type.
	•	CType(T) holds.
	•	t ⇓ v.

Let P = E(t) be the extracted Cmini program, and let P ⇓ v_c.

Then:
	•	V⟦T⟧(v, v_c) holds.

Moreover, evaluation traces correspond:
	•	For each step of Cmini execution, there exists a sequence of evaluation steps in CertiJSON runtime core such that the observable parts of the configurations (values of variables mapped from core variables) correspond.

(Full proof is left for mechanization; the spec states this as intended property.)

7.3 Simulation with FFI

If extern_c is used:
	•	Each extern_c has:
	•	A logical type A1 → ... → An → B.
	•	A repr for all Ai and B.
	•	A Cmini extern declaration extern τB f(τ1,...,τn) with τi = T⟦Ai⟧.
	•	We assume an external specification:
For each extern_c f and each call with arguments (v1,...,vn) in CertiJSON and corresponding Cmini values (v_c1,...,v_cn), if V⟦Ai⟧(vi, v_ci) for all i, then the C environment returns a value v_c such that there exists a logical result v with V⟦B⟧(v, v_c) and the logical axioms about f hold.

Under that assumption, the same simulation theorem extends to programs calling extern_c.

⸻

8. Summary of v0.5 Additions
	1.	Erasure from full core to runtime core:
	•	Removes Prop, rewrite, proofs, and proof-only definitions.
	2.	Cmini: Explicit, small, C-like target language with:
	•	Pure expressions, structured statements, no UB.
	3.	Type translation T⟦·⟧ and term extraction E.
	4.	Value correspondence V⟦T⟧ via repr+encode/decode.
	5.	Simulation theorem stating that extracted Cmini programs faithfully implement CertiJSON runtime semantics.

⸻

9. Next Directions (beyond 0.5)

Not part of this spec, but natural next steps:
	•	Formal Coq/Agda definition of:
	•	CertiJSON core syntax, typing, and semantics.
	•	Cmini syntax, typing, and semantics.
	•	Erasure and extraction functions.
	•	Proof of Theorem 1.
	•	JSON Schema definitions to enforce syntactic well-formedness of modules pre-kernel.
	•	Extensions for:
	•	Effects modeled via monadic types in Type.
	•	More expressive FFI (buffers, arrays) with verified ownership/borrowing discipline.

⸻


# CertiJSON Core Language Specification (v0.6)

_Working name_: **CertiJSON**  
_Goal_: A pure, total, dependently typed language with JSON concrete syntax, designed for LLM agents. All accepted modules are logically sound, and runtime terms can be extracted to a small, UB-free C-subset with representation-level guarantees.

---

## 0. Version 0.6 Overview

This document describes **CertiJSON v0.6**.

Relative to **v0.5**, v0.6 adds:

1. **Formal pattern-matching safety**:
   - Exhaustiveness and non-overlap conditions for `match`.
   - JSON-level annotation for pattern coverage hints (optional, for LLM guidance).

2. **Name resolution and modules**:
   - Explicit specification of how `imports` work.
   - Rules for name qualification and collision detection.

3. **JSON structural well-formedness layer**:
   - Machine-checkable, schema-style constraints for:
     - Modules
     - Declarations
     - Terms

4. **Definitional equality clarified**:
   - Explicit β/δ/ι rules, and an optional η-rule toggle.
   - A “kernel mode” flag: `eta = on | off`.

5. **Agent-facing constraints**:
   - A small **“Agent Profile”** section that constrains what shape of code LLMs should emit to maximize success (purely conventional, but part of the spec).

All other components from v0.5 remain as-is:

- Prop / Type split
- Equality and `rewrite`
- Inductives and structural recursion (`rec_args`)
- Erasure
- Cmini target
- `repr` + `extern_c`
- Extraction and simulation theorem (sketch)

---

## 1. Core Design Summary

**G1. Logic**

- `Prop` – propositions (proof-only).
- `Type` – computational types (values).
- Curry–Howard: terms inhabiting `P : Prop` are proofs; terms inhabiting `A : Type` are programs/data.

**G2. Totality and determinism**

- Only structural recursion (v0.6) is allowed.
- All accepted `def` are total; evaluation always terminates.

**G3. Proof / compute separation**

- `Prop` and `proof-only` definitions are erased.
- Only `Type` and `runtime`/`both` definitions survive into runtime core and extraction.

**G4. Safe C interop**

- `repr` describes ABI layout.
- `extern_c` binds logical constants to C functions via `repr`.
- Extraction produces Cmini, a UB-free target.

**G5. LLM-oriented JSON**

- Concrete syntax is JSON.
- Strict schema-like constraints (no partial data, no implicit defaults except where explicitly defined).

---

## 2. Core Abstract Syntax (as in v0.4/v0.5)

### 2.1 Universes

- `Type` – universe of computational types.
- `Prop` – universe of propositions.

### 2.2 Primitive Types and Literals

Primitive types (all in `Type`):

- `Int32`, `Int64`, `Float64`, `Bool`, `Size`.

Primitive literals:

- `int32(n)` – 32-bit signed integer.
- `int64(n)` – 64-bit signed integer.
- `float64(f)` – 64-bit float.
- `bool(b)` – boolean.

### 2.3 Terms

Abstract term grammar:

- Variables: `x`
- Universes: `Type | Prop`
- Π-type: `Π(x : A). B`
- Lambda: `λ(x : A). t`
- Application: `t u`
- Equality: `Eq_A(u, v)` (in `Prop`)
- Reflexivity: `refl_A(u)`
- Equality elimination: `rewrite e in t_body`
- Global constant / constructor: `cst`
- Pattern match:

  ```text
  match t₀ as z return P with
    c₁(⃗y¹) ⇒ u₁
  | ...
  | c_k(⃗yᵏ) ⇒ u_k


# CertiJSON Core Language Specification (v0.6)

_Working name_: **CertiJSON**  
_Goal_: A pure, total, dependently typed language with JSON concrete syntax, designed for LLM agents. All accepted modules are logically sound, and runtime terms can be extracted to a small, UB-free C-subset with representation-level guarantees.

---

## 0. Version 0.6 Overview

This document describes **CertiJSON v0.6**.

Relative to **v0.5**, v0.6 adds:

1. **Formal pattern-matching safety**:
   - Exhaustiveness and non-overlap conditions for `match`.
   - JSON-level annotation for pattern coverage hints (optional, for LLM guidance).

2. **Name resolution and modules**:
   - Explicit specification of how `imports` work.
   - Rules for name qualification and collision detection.

3. **JSON structural well-formedness layer**:
   - Machine-checkable, schema-style constraints for:
     - Modules
     - Declarations
     - Terms

4. **Definitional equality clarified**:
   - Explicit β/δ/ι rules, and an optional η-rule toggle.
   - A “kernel mode” flag: `eta = on | off`.

5. **Agent-facing constraints**:
   - A small **“Agent Profile”** section that constrains what shape of code LLMs should emit to maximize success (purely conventional, but part of the spec).

All other components from v0.5 remain as-is:

- Prop / Type split
- Equality and `rewrite`
- Inductives and structural recursion (`rec_args`)
- Erasure
- Cmini target
- `repr` + `extern_c`
- Extraction and simulation theorem (sketch)

---

## 1. Core Design Summary

**G1. Logic**

- `Prop` – propositions (proof-only).
- `Type` – computational types (values).
- Curry–Howard: terms inhabiting `P : Prop` are proofs; terms inhabiting `A : Type` are programs/data.

**G2. Totality and determinism**

- Only structural recursion (v0.6) is allowed.
- All accepted `def` are total; evaluation always terminates.

**G3. Proof / compute separation**

- `Prop` and `proof-only` definitions are erased.
- Only `Type` and `runtime`/`both` definitions survive into runtime core and extraction.

**G4. Safe C interop**

- `repr` describes ABI layout.
- `extern_c` binds logical constants to C functions via `repr`.
- Extraction produces Cmini, a UB-free target.

**G5. LLM-oriented JSON**

- Concrete syntax is JSON.
- Strict schema-like constraints (no partial data, no implicit defaults except where explicitly defined).

---

## 2. Core Abstract Syntax (as in v0.4/v0.5)

### 2.1 Universes

- `Type` – universe of computational types.
- `Prop` – universe of propositions.

### 2.2 Primitive Types and Literals

Primitive types (all in `Type`):

- `Int32`, `Int64`, `Float64`, `Bool`, `Size`.

Primitive literals:

- `int32(n)` – 32-bit signed integer.
- `int64(n)` – 64-bit signed integer.
- `float64(f)` – 64-bit float.
- `bool(b)` – boolean.

### 2.3 Terms

Abstract term grammar:

- Variables: `x`
- Universes: `Type | Prop`
- Π-type: `Π(x : A). B`
- Lambda: `λ(x : A). t`
- Application: `t u`
- Equality: `Eq_A(u, v)` (in `Prop`)
- Reflexivity: `refl_A(u)`
- Equality elimination: `rewrite e in t_body`
- Global constant / constructor: `cst`
- Pattern match:

  ```text
  match t₀ as z return P with
    c₁(⃗y¹) ⇒ u₁
  | ...
  | c_k(⃗yᵏ) ⇒ u_k

	•	Primitive literals: int32(n), int64(n), float64(f), bool(b).

Derived:
	•	forall (x : A). B ≜ Π(x : A). B.
	•	A → B ≜ Π(_ : A). B.

⸻

3. JSON Concrete Syntax and Schema-Like Constraints

v0.6 introduces a schema-style layer. We do not define a complete JSON Schema file, but the rules below are equivalent.

3.1 Module Structure

A module is:

{
  "module": "ModuleName",
  "imports": [ "OtherModule1", "OtherModule2" ],
  "declarations": [ Decl, ... ]
}

Constraints:
	•	"module": required, non-empty string, must be a valid identifier (ASCII letters, digits, underscore, not starting with digit).
	•	"imports": optional array of non-empty strings; default is empty array if omitted.
	•	"declarations": required array, length ≥ 0; each element is one of the declaration shapes below.

3.2 Declaration Shapes

Each Decl is exactly one of:
	•	Inductive:

{
  "inductive": {
    "name": "I",
    "params": [ { "name": "x", "type": A_json }, ... ],
    "universe": "Type",
    "constructors": [
      {
        "name": "C1",
        "args": [ { "name": "y", "type": B_json }, ... ]
      },
      ...
    ]
  }
}


	•	Def:

{
  "def": {
    "name": "f",
    "role": "runtime",      // "runtime" | "proof-only" | "both" (default if omitted: "both")
    "type": A_json,
    "body": t_json,
    "rec_args": [0, 1, ...] // optional, array of non-negative integers
  }
}


	•	Theorem:

{
  "theorem": {
    "name": "p",
    "type": P_json,
    "proof": t_json
  }
}


	•	repr:

{
  "repr": {
    "name": "Point2DRepr",
    "kind": "primitive" | "struct",
    // primitive:
    "c_type": "int32_t",       // if kind == "primitive"
    "size_bits": 32,
    "signed": true,
    // OR struct:
    "c_struct_name": "Point2D",
    "size_bytes": 8,
    "align_bytes": 4,
    "fields": [
      { "name": "x", "repr": "Int32Repr", "offset_bytes": 0 },
      { "name": "y", "repr": "Int32Repr", "offset_bytes": 4 }
    ]
  }
}


	•	extern_c:

{
  "extern_c": {
    "name": "c_sin",
    "c_name": "sin",
    "header": "<math.h>",
    "signature": {
      "return": { "repr": "Float64Repr" },
      "args": [
        { "name": "x", "repr": "Float64Repr" }
      ]
    },
    "type": A_json,
    "safety": "pure",    // "pure" | "impure"
    "axioms": [ /* optional theorem names or inline specs */ ]
  }
}



Constraints:
	•	Every declaration object must have exactly one of these top-level keys: "inductive", "def", "theorem", "repr", "extern_c".
	•	"name" fields: same identifier format as module names; must be unique per module (no duplicates across any declarations in declarations).
	•	"role": if omitted, treated as "both".

3.3 Term JSON Nodes

We keep the v0.4/v0.5 forms, adding some schema constraints.

3.3.1 Variables

{ "var": "x" }

Constraints: "var" is a non-empty string; actual binding validity is checked in typing.

3.3.2 Universes

{ "universe": "Type" }
{ "universe": "Prop" }

Only these two strings are allowed.

3.3.3 Π-type / forall

{
  "pi": {
    "arg": { "name": "x", "type": A_json },
    "result": B_json
  }
}

{
  "forall": {
    "arg": { "name": "x", "type": A_json },
    "result": B_json
  }
}

Fields:
	•	"arg.name": identifier string.
	•	"arg.type": term JSON.
	•	"result": term JSON.

3.3.4 Lambda

{
  "lambda": {
    "arg": { "name": "x", "type": A_json },
    "body": t_json
  }
}

3.3.5 Application

{ "app": [ t_json, u1_json, u2_json, ... ] }

	•	Array length ≥ 2.
	•	First element: function term.
	•	Remaining elements: arguments.

3.3.6 Equality and Refl

{
  "eq": {
    "type": A_json,
    "lhs":  u_json,
    "rhs":  v_json
  }
}

{
  "refl": {
    "eq": {
      "type": A_json,
      "lhs":  u_json,
      "rhs":  v_json
    }
  }
}

3.3.7 rewrite

{
  "rewrite": {
    "proof": e_json,
    "in": t_json
  }
}

No extra fields allowed.

3.3.8 match

{
  "match": {
    "scrutinee": t0_json,
    "motive": P_json,
    "as": "z",
    "cases": [
      {
        "pattern": {
          "ctor": "C1",
          "args": [ { "name": "y1" }, { "name": "y2" } ]
        },
        "body": u1_json
      }
    ],
    "coverage_hint": "complete"  // NEW, optional: "unknown" | "complete"
  }
}

	•	"as" optional; if absent, implementation may generate a fresh name.
	•	"coverage_hint" optional, "complete" means the agent claims exhaustiveness; kernel still verifies coverage independently.

3.3.9 Literals

{ "int32": 123 }
{ "int64": 1234567890 }
{ "float64": 3.14 }
{ "bool": true }

Constraints:
	•	Values must be valid JSON numbers/booleans.
	•	Range constraints for int32/int64 are checked by implementation; out-of-range is rejected.

⸻

4. Name Resolution and Modules

v0.6 makes the module/import behavior explicit.

4.1 Global Signature

The kernel maintains a global signature Σ that includes:
	•	Declarations from the current module.
	•	Declarations from all imported modules.

Each declared name must be unique within its module. Imports are:
	•	Flat: importing module M adds all exported names from M directly into the current module’s lookup scope.

4.2 Import Semantics

Given:

{
  "module": "A",
  "imports": [ "B", "C" ],
  "declarations": [ ... ]
}

Resolution steps:
	1.	Load module "B" and "C" (transitively resolving their imports).
	2.	Construct Σ_A as:
	•	Σ_B ∪ Σ_C ∪ Decl_A, where:
	•	Σ_B, Σ_C contain public names from B and C.
	•	Decl_A are declarations from A.

Collisions:
	•	If the same identifier (e.g. "plus") is exported by two imported modules and/or A declares it again, this is a name collision.
	•	v0.6: collisions are rejected at load time; there is no namespacing or qualification mechanism in the core spec.

4.3 Scope Rules
	•	Term-level variables:
	•	Bound by lambda, pi/forall, and match patterns.
	•	Standard lexical scoping; innermost binding wins.
	•	Type- and constant-level names:
	•	Resolved from Σ (current module + imports).
	•	Must be defined before use in the same module or appear in an imported module.

⸻

5. Typing and Definitional Equality

Typing judgment (as in v0.4/v0.5):

Σ; Γ ⊢ t : A

with A : Type or A : Prop.

5.1 Definitional Equality

We define a judgment:

Σ; Γ ⊢ t ≡ u

Definitional equality is the least congruence generated by:
	•	β-rule:

(λ(x : A). t) u ≡ t[x := u]


	•	δ-rule (unfold def):
If def f : A := t ∈ Σ then:

f ≡ t


	•	ι-rule (for match):
If we have:

match c_j(⃗v) as z return P with ... | c_j(⃗y) ⇒ u_j | ...

then:

match c_j(⃗v) as z return P with ... ≡ u_j[⃗y := ⃗v]


	•	α-rule:
α-equivalent terms (differing only by bound variable names) are equal.
	•	Congruence:
If parts of a compound term are equal, the compound terms are equal (for λ, Π, app, Eq, etc.).

Optional η-Rule
The kernel can be implemented in two modes:
	•	eta = off (default, simpler kernel):
No η for functions.
	•	eta = on:
Add:

f ≡ λ(x : A). f x

when x not free in f and f : Π(x : A). B.

This flag is a kernel configuration; it does not affect well-typedness, only definitional equality.

5.2 Typing Rules

The typing rules from v0.4/v0.5 are unchanged:
	•	(Var), (Universe), (Pi), (Lambda), (App), (Conversion)
	•	(Eq-Form), (Eq-Refl), (Inductive), (Constructor), (Match), rewrite rule
	•	Literal typing rules (primitives).

⸻

6. Pattern Matching: Safety and Coverage

New in v0.6: coverage and non-overlap conditions.

6.1 Non-Overlap

Given a match:

match t₀ as z return P with
  c₁(⃗y¹) ⇒ u₁
| ...
| c_k(⃗yᵏ) ⇒ u_k

Let I be the inductive type of t₀.
	•	For a given constructor c_j, there must be at most one case with head c_j.
	•	That ensures non-overlap (no two branches match the same constructor).

If two cases share the same constructor name c in the same match, the program is rejected.

6.2 Exhaustiveness

Let I have constructors c₁, ..., c_m.

A match is exhaustive if:
	•	For every constructor c_j of I, there exists a case whose pattern uses c_j.

If any c_j is missing, the match is non-exhaustive.

v0.6:
	•	Requires exhaustiveness for all match expressions in runtime terms.
	•	Allows non-exhaustive matches in Prop-only contexts (e.g. proofs) if they are not used in runtime code; however, for simplicity, an implementation may just require exhaustiveness everywhere.

The kernel must check this statically from the inductive declaration in Σ.

6.3 coverage_hint

The JSON field "coverage_hint": "complete" is advisory:
	•	If "coverage_hint": "complete" is present, the kernel still checks exhaustiveness.
	•	If the hint is wrong (missing constructors), the match is rejected as non-exhaustive.

This field exists to help LLM agents generate exhaustive matches more reliably.

⸻

7. Structural Recursion (re-stated with v0.6 clarity)

The rec_args field in def declarations is used to enforce structural recursion.

Given:

{
  "def": {
    "name": "f",
    "type": A_json,
    "body": t_json,
    "rec_args": [i0, i1, ...]
  }
}

Assume:

Σ; · ⊢ f : Π(a₀ : A₀)...(a_n : A_n). R

with each i_k referring to a parameter a_{i_k} whose type is an inductive type.

Constraints:
	1.	Every recursive call f u₀ ... u_n in the body must:
	•	Appear syntactically inside a match that deconstructs at least one of the rec_args parameters (or their descendants).
	•	For each i_k in rec_args, the corresponding argument u_{i_k} must be structurally smaller than the original a_{i_k} (i.e. one of the pattern variables bound by deconstructing a_{i_k} or a structural subterm thereof).
	2.	No recursive call may use any u_{i_k} that is not derived from such pattern variables (no “cycling back”).

The exact subterm relation is:
	•	If a variable x is bound in a pattern c(..., x, ...) for an inductive type I, then x is a strict subterm of the matched value c(...).
	•	If y is a field of x via nested patterns, y is a strict subterm of x.

The termination checker may be conservative; if it is unsure whether a call is decreasing, it must reject the definition.

⸻

8. Erasure and Cmini (from v0.5, unchanged)

v0.6 keeps:
	•	Erasure erase : Term → RuntimeTerm.
	•	Runtime core (no Prop, rewrite, proofs).
	•	Cmini target language:
	•	Types: int32, int64, double, u8, size, struct S.
	•	Expressions, statements, functions, programs.
	•	Small-step semantics for Cmini.
	•	Type translation T⟦·⟧.
	•	Extraction E from runtime functions to Cmini.
	•	Value correspondence V⟦T⟧ via repr + encode/decode.
	•	Simulation theorem (no-FFI + FFI cases) as intended property.

(No changes are made here; v0.6 just builds on v0.5.)

⸻

9. Agent Profile (LLM-Oriented Constraints)

This section is non-normative for the kernel, but normative for agent tooling that generates CertiJSON.

To maximize success:
	1.	Explicit, simple patterns
	•	Always name all bound variables in pi, lambda, and match.
	•	Avoid very long chains of nested applications; use JSON app with a small number of arguments.
	2.	Exhaustive matches with coverage_hint
	•	When matching on an inductive I with constructors C1,...,Ck, always include every constructor exactly once.
	•	Set "coverage_hint": "complete" on every match you intend to be exhaustive.
	3.	Role discipline
	•	Use "role": "proof-only" for lemmas and theorems.
	•	Use "role": "runtime" or "both" only for actual executable code.
	4.	Recursion discipline
	•	Always specify rec_args for recursive functions.
	•	Structure recursive definitions as:
	•	match on a structurally decreasing argument.
	•	Recursive calls only in the branches, on immediate subterms (pattern variables or field extractions).
	5.	Avoid unused features
	•	Do not use Prop in types meant for extraction.
	•	Do not attempt higher-order extern_c (no function-valued arguments or results).
	6.	Equality handling
	•	Use rewrite only in proofs (Prop).
	•	For runtime code, prefer pattern matching or primitive operations instead of equality reasoning.

⸻

10. Meta-Theoretic Targets (as in v0.5)

For the core:
	1.	Type Soundness:
	•	Well-typed terms do not go wrong.
	•	Preservation + progress for the core language.
	2.	Strong Normalization:
	•	All well-typed closed terms terminate.
	3.	Logical Soundness:
	•	Every theorem p : P := t represents a valid proof of P : Prop.

For representation and FFI:
	4.	Representation Soundness:
	•	repr + encode/decode + roundtrip theorem ensure ABI correctness.
	5.	FFI Safety:
	•	Well-formed extern_c and correct C implementations ensure UB-free interaction.
	6.	Extraction Correctness:
	•	Extracted Cmini programs simulate CertiJSON runtime evaluation modulo assumed axioms for extern_c.

⸻

11. Summary of v0.6
	•	Tightens the surface of the language for LLMs (JSON constraints and module rules).
	•	Tightens pattern-match safety (coverage + non-overlap).
	•	Makes definitional equality explicit (β/δ/ι (+ optional η)).
	•	Leaves the core logic, erasure, Cmini, and extraction from v0.5 intact.

This version is intended to be stable enough for:
	•	Implementing an initial kernel.
	•	Building an LLM agent that emits CertiJSON modules.
	•	Beginning formalization in Coq/Agda if desired.

If you like, the obvious “0.7” step would be to start carving out a **minimal standard library spec** in a separate document (`stdlib-0.7.md`) with fully specified types and signatures for `Nat`, `List`, `Option`, plus some core lemmas (associativity, commutativity, etc.) that the agent can rely on.

# CertiJSON Standard Library Specification (v0.7)

This document specifies a **minimal standard library** for **CertiJSON v0.6**.

- Language core: see `spec-0.6.md`.
- This file defines:
  - Core data types: `Nat`, `List`, `Option`, `Pair`, `Result`.
  - Basic operations and recursion schemes.
  - A few canonical theorems (equational properties).
- Everything is given in **abstract form** (Core / Typing). JSON shapes are sketched in an appendix.

The standard library modules are **pure CertiJSON**; no `extern_c` here.

---

## 1. Module Layout

We define a collection of logical modules:

- `Std.Bool`
- `Std.Nat`
- `Std.List`
- `Std.Option`
- `Std.Pair`
- `Std.Result`
- `Std.Eq` (basic equality theorems)

Implementations may physically put them into separate files or a single bundle, but these module names and exported identifiers are reserved for the standard library.

Each module:

```json
{
  "module": "Std.Nat",
  "imports": [ "Std.Bool", "Std.Eq" ],
  "declarations": [ ... ]
}

Here’s a stdlib-0.7.md you can drop alongside spec-0.6.md.

# CertiJSON Standard Library Specification (v0.7)

This document specifies a **minimal standard library** for **CertiJSON v0.6**.

- Language core: see `spec-0.6.md`.
- This file defines:
  - Core data types: `Nat`, `List`, `Option`, `Pair`, `Result`.
  - Basic operations and recursion schemes.
  - A few canonical theorems (equational properties).
- Everything is given in **abstract form** (Core / Typing). JSON shapes are sketched in an appendix.

The standard library modules are **pure CertiJSON**; no `extern_c` here.

---

## 1. Module Layout

We define a collection of logical modules:

- `Std.Bool`
- `Std.Nat`
- `Std.List`
- `Std.Option`
- `Std.Pair`
- `Std.Result`
- `Std.Eq` (basic equality theorems)

Implementations may physically put them into separate files or a single bundle, but these module names and exported identifiers are reserved for the standard library.

Each module:

```json
{
  "module": "Std.Nat",
  "imports": [ "Std.Bool", "Std.Eq" ],
  "declarations": [ ... ]
}

Names must be unique across the entire combined signature.

⸻

2. Std.Bool

2.1 Inductive

Inductive Bool : Type :=
  | true  : Bool
  | false : Bool

In practice Bool is usually treated as a primitive with repr to u8; this inductive form is the logical interface.

2.2 Basic functions
	1.	if_then_else

def if_then_else :
  ∀(A : Type), Bool → A → A → A
:= λ(A : Type). λ(b : Bool). λ(x : A). λ(y : A).
     match b as z return A with
     | true  ⇒ x
     | false ⇒ y

Role: runtime.

(You can also treat this as syntactic sugar in higher layers.)

⸻

3. Std.Eq

Basic equality utilities. Recall Eq_A(u,v) : Prop and refl_A(u) : Eq_A(u,u) are in the core.

3.1 Symmetry

theorem eq_sym :
  ∀(A : Type)(x y : A), Eq_A(x, y) → Eq_A(y, x)
:= λ(A : Type). λ(x : A). λ(y : A). λ(p : Eq_A(x,y)).
     (* proof using rewrite / J-style eliminator *)

3.2 Transitivity

theorem eq_trans :
  ∀(A : Type)(x y z : A),
    Eq_A(x, y) → Eq_A(y, z) → Eq_A(x, z)
:= ...

3.3 Congruence (unary)

theorem eq_congr1 :
  ∀(A B : Type)(f : A → B)(x y : A),
    Eq_A(x, y) → Eq_B(f x, f y)
:= ...

Exported:
	•	eq_sym, eq_trans, eq_congr1.

Role: proof-only.

⸻

4. Std.Nat

4.1 Inductive

Inductive Nat : Type :=
  | zero : Nat
  | succ : Nat → Nat

4.2 Recursor / eliminator

We define the usual non-dependent recursor:

def nat_rec :
  ∀(A : Type),
    A → (Nat → A → A) → Nat → A
:= λ(A : Type). λ(a0 : A). λ(step : Nat → A → A). λ(n : Nat).
     (* structural recursion on n *)
     match n as z return A with
     | zero   ⇒ a0
     | succ k ⇒ step k (nat_rec A a0 step k)

	•	role = runtime
	•	rec_args = [2] (0 = A, 1 = a0, 2 = step, 3 = n; structural recursion is on n → index 3; but we can choose to define a curried version where nat_rec is fully applied, so details may vary—here we just signal “recursive argument is Nat”).

4.3 Addition

def plus :
  Nat → Nat → Nat
:= λ(n : Nat). λ(m : Nat).
     nat_rec Nat
       m
       (λ(k : Nat). λ(acc : Nat). succ acc)
       n

	•	role = runtime, rec_args = [] (we use nat_rec internally; the kernel only checks nat_rec’s recursion).

4.4 Multiplication

def mult :
  Nat → Nat → Nat
:= λ(n : Nat). λ(m : Nat).
     nat_rec Nat
       zero
       (λ(_ : Nat). λ(acc : Nat). plus acc m)
       n

4.5 Comparison (≤ as inductive Prop)

We define a standard “less or equal” relation:

Inductive le (n : Nat) : Nat → Prop :=
  | le_refl  : le n n
  | le_succ  : ∀(m : Nat), le n m → le n (succ m)

Often written le n m.

4.6 Basic theorems (sketch)
	•	plus_zero_right:

theorem plus_zero_right :
  ∀(n : Nat), Eq_Nat(plus n zero, n)
:= ...


	•	plus_zero_left:

theorem plus_zero_left :
  ∀(n : Nat), Eq_Nat(plus zero n, n)
:= ...


	•	plus_succ_right:

theorem plus_succ_right :
  ∀(n m : Nat),
    Eq_Nat(plus n (succ m), succ (plus n m))
:= ...


	•	Commutativity and associativity can be added later; they’re not strictly required for a minimal stdlib but are natural.

All these are role = proof-only.

⸻

5. Std.List

We define standard polymorphic lists.

5.1 Inductive

Inductive List (A : Type) : Type :=
  | nil  : List A
  | cons : A → List A → List A

5.2 Length

def length :
  ∀(A : Type), List A → Nat
:= λ(A : Type). λ(xs : List A).
     match xs as z return Nat with
     | nil        ⇒ zero
     | cons x xs' ⇒ succ (length A xs')

	•	role = runtime
	•	rec_args = [1] (index 1: the xs argument).

5.3 Append

def append :
  ∀(A : Type), List A → List A → List A
:= λ(A : Type). λ(xs : List A). λ(ys : List A).
     match xs as z return List A with
     | nil        ⇒ ys
     | cons x xs' ⇒ cons x (append A xs' ys)

	•	role = runtime
	•	rec_args = [1] (recursive on xs argument).

5.4 map

def map :
  ∀(A B : Type), (A → B) → List A → List B
:= λ(A : Type). λ(B : Type). λ(f : A → B). λ(xs : List A).
     match xs as z return List B with
     | nil        ⇒ nil B
     | cons x xs' ⇒ cons (f x) (map A B f xs')

	•	role = runtime
	•	rec_args = [3] (structural recursion on xs).

5.5 fold_right

def fold_right :
  ∀(A B : Type), (A → B → B) → B → List A → B
:= λ(A : Type). λ(B : Type). λ(f : A → B → B). λ(z : B). λ(xs : List A).
     match xs as t return B with
     | nil        ⇒ z
     | cons x xs' ⇒ f x (fold_right A B f z xs')

	•	role = runtime
	•	rec_args = [4] (on xs).

5.6 Theorems (examples)
	•	length_nil:

theorem length_nil :
  ∀(A : Type), Eq_Nat(length A (nil A), zero)
:= ...


	•	length_cons:

theorem length_cons :
  ∀(A : Type)(x : A)(xs : List A),
    Eq_Nat(length A (cons A x xs), succ (length A xs))
:= ...


	•	length_append:

theorem length_append :
  ∀(A : Type)(xs ys : List A),
    Eq_Nat(length A (append A xs ys),
           plus (length A xs) (length A ys))
:= ...



Role: all proof-only.

⸻

6. Std.Option

An option type, parameterized over A : Type.

6.1 Inductive

Inductive Option (A : Type) : Type :=
  | none : Option A
  | some : A → Option A

6.2 map

def option_map :
  ∀(A B : Type), (A → B) → Option A → Option B
:= λ(A : Type). λ(B : Type). λ(f : A → B). λ(o : Option A).
     match o as z return Option B with
     | none      ⇒ none B
     | some x    ⇒ some B (f x)

	•	role = runtime, non-recursive (rec_args = []).

6.3 default

def option_default :
  ∀(A : Type), A → Option A → A
:= λ(A : Type). λ(def : A). λ(o : Option A).
     match o as z return A with
     | none   ⇒ def
     | some x ⇒ x


⸻

7. Std.Pair

A binary product type.

7.1 Inductive

Inductive Pair (A B : Type) : Type :=
  | pair : A → B → Pair A B

7.2 Projections

def fst :
  ∀(A B : Type), Pair A B → A
:= λ(A : Type). λ(B : Type). λ(p : Pair A B).
     match p as z return A with
     | pair x y ⇒ x

def snd :
  ∀(A B : Type), Pair A B → B
:= λ(A : Type). λ(B : Type). λ(p : Pair A B).
     match p as z return B with
     | pair x y ⇒ y

Both role = runtime.

⸻

8. Std.Result

A simple error type with two branches.

8.1 Inductive

Inductive Result (E A : Type) : Type :=
  | ok    : A → Result E A
  | error : E → Result E A

8.2 map

def result_map :
  ∀(E A B : Type), (A → B) → Result E A → Result E B
:= λ(E A B : Type). λ(f : A → B). λ(r : Result E A).
     match r as z return Result E B with
     | ok a    ⇒ ok E B (f a)
     | error e ⇒ error E B e

8.3 bind (monadic)

def result_bind :
  ∀(E A B : Type), Result E A → (A → Result E B) → Result E B
:= λ(E A B : Type). λ(r : Result E A). λ(k : A → Result E B).
     match r as z return Result E B with
     | ok a    ⇒ k a
     | error e ⇒ error E B e

role = runtime.

⸻

9. JSON Sketches for Standard Library Terms

This appendix gives indicative JSON forms for key definitions. Exact formatting may vary; only the shape matters.

9.1 Nat (inductive) – Std.Nat

{
  "inductive": {
    "name": "Nat",
    "params": [],
    "universe": "Type",
    "constructors": [
      { "name": "zero", "args": [] },
      {
        "name": "succ",
        "args": [
          { "name": "n", "type": { "var": "Nat" } }
        ]
      }
    ]
  }
}

9.2 plus (sketch, core idea only)

{
  "def": {
    "name": "plus",
    "role": "runtime",
    "type": {
      "pi": {
        "arg": { "name": "n", "type": { "var": "Nat" } },
        "result": {
          "pi": {
            "arg": { "name": "m", "type": { "var": "Nat" } },
            "result": { "var": "Nat" }
          }
        }
      }
    },
    "body": {
      "lambda": {
        "arg": { "name": "n", "type": { "var": "Nat" } },
        "body": {
          "lambda": {
            "arg": { "name": "m", "type": { "var": "Nat" } },
            "body": {
              "app": [
                { "var": "nat_rec" },
                { "var": "Nat" },
                { "var": "m" },
                {
                  "lambda": {
                    "arg": { "name": "_k", "type": { "var": "Nat" } },
                    "body": {
                      "lambda": {
                        "arg": { "name": "acc", "type": { "var": "Nat" } },
                        "body": {
                          "app": [
                            { "var": "succ" },
                            { "var": "acc" }
                          ]
                        }
                      }
                    }
                  }
                },
                { "var": "n" }
              ]
            }
          }
        }
      }
    },
    "rec_args": []
  }
}

9.3 List (inductive) – Std.List

{
  "inductive": {
    "name": "List",
    "params": [
      { "name": "A", "type": { "universe": "Type" } }
    ],
    "universe": "Type",
    "constructors": [
      {
        "name": "nil",
        "args": []
      },
      {
        "name": "cons",
        "args": [
          { "name": "x", "type": { "var": "A" } },
          { "name": "xs", "type": {
              "app": [
                { "var": "List" },
                { "var": "A" }
              ]
            }
          }
        ]
      }
    ]
  }
}


⸻

10. Properties and Expectations

The standard library is designed so that:
	•	All inductives satisfy strict positivity.
	•	All runtime defs are structurally recursive or non-recursive.
	•	All theorems live in Prop (role = proof-only) and are fully checkable by the core.
	•	The library is total: no non-terminating recursion.
	•	All names and modules obey the name resolution rules from spec-0.6.md.

This forms the minimal base that an LLM agent can rely on to write and prove basic functional programs in CertiJSON.

⸻


# CertiJSON Core Language Specification (v0.7)

_Working name_: **CertiJSON**  
_Goal_: A pure, total, dependently typed language with JSON concrete syntax, designed for LLM agents. All accepted modules are logically sound, and runtime terms can be extracted to a small, UB-free C-subset with representation-level guarantees.

This version **extends v0.6** and assumes the separate standard library spec `stdlib-0.7.md`.

---

## 0. Version 0.7 Overview

This document describes **CertiJSON v0.7**.

Relative to **v0.6**, v0.7 adds:

1. A precise **compilation pipeline**:
   - JSON → Elaborated core → Runtime core → Cmini → C.
   - Explicit intermediate artifacts and invariants at each stage.

2. A clear separation between:
   - **Declarative** typing and equality (spec-level).
   - **Algorithmic** typing and equality (implementation-level), with constraints that guarantee soundness.

3. A definition of the **Trusted Computing Base (TCB)**:
   - Which components must be trusted for correctness.
   - What can be untrusted and fuzzed/rewritten by LLM tooling.

4. An explicit notion of **profiles**:
   - **Kernel Profile**: what the kernel must implement.
   - **Agent Profile**: what code LLMs should emit (building on the v0.6 “Agent Profile” section, formalized here).

5. A normative reference to the minimal standard library (`stdlib-0.7`) as the base environment.

The core logic, syntax, semantics, `repr`/`extern_c`, erasure, pattern safety, and Cmini from **v0.6** remain **unchanged**.

---

## 1. Relation to Previous Versions

- **v0.4–0.6** defined:
  - Abstract syntax (Prop/Type, Π, inductives, equality, `rewrite`).
  - JSON concrete syntax and schema constraints.
  - Pattern-matching safety (exhaustive, non-overlapping).
  - Structural recursion via `rec_args`.
  - Erasure and a C-like target language Cmini.
  - Extraction and a simulation theorem sketch.

- **v0.7** does **not** change the core calculus.  
  Instead, it:
  - Organizes the language into compilation phases.
  - Specifies algorithmic behavior (type checking, equality checking).
  - Defines TCB and profiles.

Everything defined in **v0.6** is still valid in v0.7; this document is additive.

---

## 2. Compilation Pipeline

The CertiJSON toolchain is defined as a pipeline of phases:

1. **JSON Parsing & Structural Validation**
2. **Elaboration to Core**
3. **Declarative Typing / Well-formedness**
4. **Erasure to Runtime Core**
5. **Extraction to Cmini**
6. **Lowering Cmini to C**

Each phase takes a well-defined input artifact and produces an output artifact under explicit invariants.

### 2.1 Phase 1 – JSON Parsing & Structural Validation

Input: JSON file representing a module.  
Output: **Raw AST** with the same structure, but now as internal data structures.

Checks:

- Structural constraints from `spec-0.6` §3:
  - Required fields are present.
  - Only known node kinds are used.
  - All `"name"` fields are syntactically valid identifiers.
  - `role` belongs to `{ "runtime", "proof-only", "both" }`.
  - `coverage_hint`, if present, is in `{ "unknown", "complete" }`.
  - `rec_args` contains non-negative integers.

If any structural rule fails, the module is rejected before any type checking.

### 2.2 Phase 2 – Elaboration to Core

Input: Raw AST.  
Output: **Elaborated Core AST** for each module, with:

- Bound variable names resolved and renamed to avoid captures (α-normalized or locally nameless).
- Inferred implicit motives for `match` and `rewrite` (if implementation chooses to allow partial specification).
- Optional: expansion of syntactic sugar (`forall`, `A → B`) into primitive Π-forms.

This phase must preserve the JSON structure up to sugar, i.e. no new logical constructs are introduced beyond those in the spec.

### 2.3 Phase 3 – Declarative Typing and Well-Formedness

Input: Elaborated Core AST.  
Output: Accepted signature `Σ` with proofs of:

- For each module `M`:
  - All `imports` have been resolved into a consistent global signature.
  - Each declaration is well-formed:

    - Inductives: strict positivity, universe correctness.
    - Defs: `Σ; · ⊢ t : A` and termination (structural recursion).
    - Theorems: `Σ; · ⊢ proof : Prop` (or at least `Σ; · ⊢ proof : P` where `P : Prop`).
    - repr/extern_c: satisfy all well-formedness rules from v0.6.

- Pattern matches:
  - Non-overlapping.
  - Exhaustive (for runtime code; optional stricter policy for Prop).

This is specified using the **declarative typing rules** from v0.6.

Artifacts:

- A checked signature `Σ` (possibly serialized as a compiled interface file).
- A set of **core terms** annotated with their types.

Guarantee:

> If Phase 3 succeeds, any subsequently derived artifacts (erasure, extraction, etc.) are based on a logically sound and total core.

### 2.4 Phase 4 – Erasure to Runtime Core

Input: Checked core signature `Σ`.  
Output: **Runtime Core Program**:

- All terms/types in `Prop` are removed.
- All `proof-only` definitions are removed.
- `rewrite` is removed (replaced by its body).
- Only `Type`-typed definitions with `role ∈ {runtime, both}` remain.

Invariants:

- For every runtime definition `f : A`, `A : Type`.
- Runtime core has no reference to `Prop`, `Eq`, `refl`, or `rewrite`.

Phase 4 uses the erasure function specified in v0.5/v0.6.

### 2.5 Phase 5 – Extraction to Cmini

Input: Runtime Core Program + `repr` and `extern_c` metadata.  
Output: **Cmini Program** `P_cmini`.

Steps:

1. Map runtime types `T` to Cmini types `T⟦T⟧` where `CType(T)` holds.
2. Generate:
   - Cmini `struct` declarations from `repr`.
   - `extern` declarations for each `extern_c`.
   - Cmini functions for each runtime `def`.

Invariants:

- Type soundness: Cmini program is well-typed in its own (simple) type system.
- No UB by construction (no uninitialized variables, no invalid accesses, no wild pointers).

### 2.6 Phase 6 – Lowering to C

Input: Cmini Program.  
Output: C source (or directly C IR / object code).

This phase is intentionally simple:

- Cmini constructs are mapped 1:1 to a small, safe subset of C.
- `struct`/`extern`/`func` map directly to C.

The C compiler used downstream is not part of the CertiJSON spec; it is assumed to preserve observable behavior of this small subset (standard C semantics).

---

## 3. Declarative vs Algorithmic Typing

We have:

- **Declarative typing** (`Σ; Γ ⊢ t : A`) – as defined in v0.6.  
  This is the *specification* of what programs are legal.

- **Algorithmic typing** – the actual implementation that infers/checks types and equality.

v0.7 constrains algorithmic typing to be:

1. **Sound**: If the algorithm accepts `t : A`, then the declarative system proves `Σ; Γ ⊢ t : A`.
2. **Complete wrt. supported fragments**: On the “Agent Profile” subset, if the declarative system proves `Σ; Γ ⊢ t : A`, the algorithm should accept it.

### 3.1 Algorithmic Definitional Equality

Implementations must implement a decision procedure for definitional equality `Σ; Γ ⊢ t ≡ u`.  

Constraints:

- Must be **sound**: If the algorithm returns “equal”, then declaratively `t ≡ u`.
- May be **incomplete** in general (e.g. uses normalisation-by-evaluation, but with resource limits); if it times out, it can reject.

Recommended algorithm:

- Normalize both terms to βδι-normal form (and ι for pattern matches).
- Compare modulo α-equivalence.
- η-equivalence is optional, controlled by the `eta` kernel flag.

Failures:

- If equality checking fails or times out, the compiler may reject the program with a diagnostic. This does not compromise soundness—only completeness.

### 3.2 Algorithmic Termination Checking

The termination checker:

- Must **at least** enforce the structural recursion discipline from v0.6 using `rec_args`.
- May use additional heuristics (lexicographic ordering, measures, etc.).
- Must be sound: no function accepted as total may diverge.

Completeness is not required: the checker may reject terminating functions.

---

## 4. Trusted Computing Base (TCB)

The TCB is the minimal set of components whose correctness must be assumed to trust the system.

### 4.1 Logical TCB

1. **Kernel type checker**:
   - Declarative typing rules.
   - Definitional equality.
   - Inductive positivity checks.
   - Structural recursion checker.
   - Pattern coverage checker.

2. **Erasure function implementation**:
   - Correct implementation of `erase` such that:
     - Runtime semantics correspond to core semantics modulo proofs.

3. **Extraction to Cmini**:
   - Correct type translation `T⟦·⟧`.
   - Correct compilation of pattern matches, recursion, and primitives.

4. **repr and encode/decode correctness**:
   - The correctness of `repr` declarations and their associated `encode_T` / `decode_T` / roundtrip theorem proofs.
   - Implementation of encode/decode when used internally (if any).

5. **Cmini semantics and lowering**:
   - Cmini interpreter / codegen preserves behavior.
   - Lowering from Cmini to C preserves semantics (for the used subset).

Each of these must be correct; otherwise, the “if it compiles, it’s correct” guarantee breaks.

### 4.2 Non-TCB / Untrusted Components

These may be arbitrarily buggy or adversarial without compromising soundness, as long as the kernel rejects invalid outputs:

- LLM-based code generators (agents).
- IDE and editor tooling.
- Formatters and pretty-printers.
- Suggestion engines, template expanders, etc.
- Higher-level DSL frontends that compile to CertiJSON JSON.

If these produce invalid code, the kernel must simply reject it.

---

## 5. Profiles

### 5.1 Kernel Profile

The **Kernel Profile** is what a conforming implementation must support.

Mandatory:

- Entire core calculus from v0.6.
- JSON forms and schema constraints from v0.6.
- All stdlib modules from `stdlib-0.7`:
  - `Std.Bool`, `Std.Nat`, `Std.List`, `Std.Option`, `Std.Pair`, `Std.Result`, `Std.Eq`.
- Erasure to runtime core.
- Extraction to Cmini for first-order, C-safe functions.
- Optional but recommended: `extern_c` and `repr` support.

Configuration options:

- `eta = on | off` – function η-equivalence.
- Strictness about non-exhaustive matches in `Prop` contexts.

### 5.2 Agent Profile (refined)

The **Agent Profile** defines a “sweet spot” subset where:

- Algorithmic typing is complete and predictable.
- LLM agents are expected to operate.

Constraints on agent-generated modules:

1. **Well-scoped**:

   - No free variables.
   - All referenced names are either in the same module or in imported modules.
   - No shadowing of imported names by local definitions with different meanings.

2. **First-order functions for runtime**:

   - Runtime functions must be first-order (no higher-order arguments/results across FFI or extraction boundaries).
   - Higher-order functions are allowed in proofs and internal logic-only utilities.

3. **Structured recursion**:

   - Use `rec_args` whenever recursion appears.
   - Use one primary structural argument per recursive function in early versions.

4. **Inductive patterns**:

   - Always provide exhaustive, non-overlapping matches on inductives.
   - Use `"coverage_hint": "complete"` when you intend exhaustive coverage.

5. **Separation of roles**:

   - Mark pure theorems as `"role": "proof-only"`.
   - Keep runtime code minimal and separate from proofs.

6. **C-boundary discipline**:

   - Only use `extern_c` with concrete C-safe types, no `List` or `Nat` over the FFI unless a `repr` and encode/decode are defined.

7. **Stdlib usage**:

   - Prefer `Std.Nat.plus`, `Std.List.append`, etc., to reduce duplication.
   - Use stdlib equality lemmas where possible.

A CertiJSON implementation is free to accept programs outside this Agent Profile, but tooling for LLMs should *target* this profile.

---

## 6. Standard Library as a Normative Base

`stdlib-0.7.md` defines a minimal standard library that:

- Satisfies all kernel constraints (v0.6).
- Contains only total, structurally recursive functions.
- Uses no `extern_c` (purely logical).

v0.7 declares `stdlib-0.7` as the **canonical base environment**:

- A conforming implementation must ship with an implementation of `stdlib-0.7` (possibly with extra modules).
- Agents may assume that these modules are always available for import.

---

## 7. Guarantees and Intended Theorems

Assuming a correct implementation of the Kernel Profile, TCB, and stdlib:

1. **If it compiles, it’s total**:

   - Every runtime definition is terminating and cannot cause undefined behavior in Cmini/C.

2. **If it compiles, its theorems are valid**:

   - Every `theorem` declared and checked is a correct proof in the underlying type theory.

3. **Extraction correctness (up to FFI axioms)**:

   - For closed runtime terms of C-safe type, CertiJSON evaluation and extracted Cmini (and C) evaluation are observationally equivalent.

These guarantees hold irrespective of how the code was produced (human or LLM).

---

## 8. Future Directions (Beyond 0.7)

Areas explicitly left to future versions:

- Richer FFI primitives (arrays, buffers) with ownership annotations.
- Effects and resources modeled at the type level (e.g., explicit `IO`/state monads in `Type`).
- Namespace-aware module system (instead of flat import space).
- Mechanized proofs of:
  - Type soundness.
  - Strong normalization.
  - Extraction correctness.

---


Nice, let’s level it up.

Here’s a core spec v0.7 that sits on top of spec-0.6.md and assumes stdlib-0.7.md exists as the canonical stdlib.

You can save this as spec-0.7.md.

⸻


# CertiJSON Core Language Specification (v0.7)

_Working name_: **CertiJSON**  
_Goal_: A pure, total, dependently typed language with JSON concrete syntax, designed for LLM agents. All accepted modules are logically sound, and runtime terms can be extracted to a small, UB-free C-subset with representation-level guarantees.

This version **extends v0.6** and assumes the separate standard library spec `stdlib-0.7.md`.

---

## 0. Version 0.7 Overview

This document describes **CertiJSON v0.7**.

Relative to **v0.6**, v0.7 adds:

1. A precise **compilation pipeline**:
   - JSON → Elaborated core → Runtime core → Cmini → C.
   - Explicit intermediate artifacts and invariants at each stage.

2. A clear separation between:
   - **Declarative** typing and equality (spec-level).
   - **Algorithmic** typing and equality (implementation-level), with constraints that guarantee soundness.

3. A definition of the **Trusted Computing Base (TCB)**:
   - Which components must be trusted for correctness.
   - What can be untrusted and fuzzed/rewritten by LLM tooling.

4. An explicit notion of **profiles**:
   - **Kernel Profile**: what the kernel must implement.
   - **Agent Profile**: what code LLMs should emit (building on the v0.6 “Agent Profile” section, formalized here).

5. A normative reference to the minimal standard library (`stdlib-0.7`) as the base environment.

The core logic, syntax, semantics, `repr`/`extern_c`, erasure, pattern safety, and Cmini from **v0.6** remain **unchanged**.

---

## 1. Relation to Previous Versions

- **v0.4–0.6** defined:
  - Abstract syntax (Prop/Type, Π, inductives, equality, `rewrite`).
  - JSON concrete syntax and schema constraints.
  - Pattern-matching safety (exhaustive, non-overlapping).
  - Structural recursion via `rec_args`.
  - Erasure and a C-like target language Cmini.
  - Extraction and a simulation theorem sketch.

- **v0.7** does **not** change the core calculus.  
  Instead, it:
  - Organizes the language into compilation phases.
  - Specifies algorithmic behavior (type checking, equality checking).
  - Defines TCB and profiles.

Everything defined in **v0.6** is still valid in v0.7; this document is additive.

---

## 2. Compilation Pipeline

The CertiJSON toolchain is defined as a pipeline of phases:

1. **JSON Parsing & Structural Validation**
2. **Elaboration to Core**
3. **Declarative Typing / Well-formedness**
4. **Erasure to Runtime Core**
5. **Extraction to Cmini**
6. **Lowering Cmini to C**

Each phase takes a well-defined input artifact and produces an output artifact under explicit invariants.

### 2.1 Phase 1 – JSON Parsing & Structural Validation

Input: JSON file representing a module.  
Output: **Raw AST** with the same structure, but now as internal data structures.

Checks:

- Structural constraints from `spec-0.6` §3:
  - Required fields are present.
  - Only known node kinds are used.
  - All `"name"` fields are syntactically valid identifiers.
  - `role` belongs to `{ "runtime", "proof-only", "both" }`.
  - `coverage_hint`, if present, is in `{ "unknown", "complete" }`.
  - `rec_args` contains non-negative integers.

If any structural rule fails, the module is rejected before any type checking.

### 2.2 Phase 2 – Elaboration to Core

Input: Raw AST.  
Output: **Elaborated Core AST** for each module, with:

- Bound variable names resolved and renamed to avoid captures (α-normalized or locally nameless).
- Inferred implicit motives for `match` and `rewrite` (if implementation chooses to allow partial specification).
- Optional: expansion of syntactic sugar (`forall`, `A → B`) into primitive Π-forms.

This phase must preserve the JSON structure up to sugar, i.e. no new logical constructs are introduced beyond those in the spec.

### 2.3 Phase 3 – Declarative Typing and Well-Formedness

Input: Elaborated Core AST.  
Output: Accepted signature `Σ` with proofs of:

- For each module `M`:
  - All `imports` have been resolved into a consistent global signature.
  - Each declaration is well-formed:

    - Inductives: strict positivity, universe correctness.
    - Defs: `Σ; · ⊢ t : A` and termination (structural recursion).
    - Theorems: `Σ; · ⊢ proof : Prop` (or at least `Σ; · ⊢ proof : P` where `P : Prop`).
    - repr/extern_c: satisfy all well-formedness rules from v0.6.

- Pattern matches:
  - Non-overlapping.
  - Exhaustive (for runtime code; optional stricter policy for Prop).

This is specified using the **declarative typing rules** from v0.6.

Artifacts:

- A checked signature `Σ` (possibly serialized as a compiled interface file).
- A set of **core terms** annotated with their types.

Guarantee:

> If Phase 3 succeeds, any subsequently derived artifacts (erasure, extraction, etc.) are based on a logically sound and total core.

### 2.4 Phase 4 – Erasure to Runtime Core

Input: Checked core signature `Σ`.  
Output: **Runtime Core Program**:

- All terms/types in `Prop` are removed.
- All `proof-only` definitions are removed.
- `rewrite` is removed (replaced by its body).
- Only `Type`-typed definitions with `role ∈ {runtime, both}` remain.

Invariants:

- For every runtime definition `f : A`, `A : Type`.
- Runtime core has no reference to `Prop`, `Eq`, `refl`, or `rewrite`.

Phase 4 uses the erasure function specified in v0.5/v0.6.

### 2.5 Phase 5 – Extraction to Cmini

Input: Runtime Core Program + `repr` and `extern_c` metadata.  
Output: **Cmini Program** `P_cmini`.

Steps:

1. Map runtime types `T` to Cmini types `T⟦T⟧` where `CType(T)` holds.
2. Generate:
   - Cmini `struct` declarations from `repr`.
   - `extern` declarations for each `extern_c`.
   - Cmini functions for each runtime `def`.

Invariants:

- Type soundness: Cmini program is well-typed in its own (simple) type system.
- No UB by construction (no uninitialized variables, no invalid accesses, no wild pointers).

### 2.6 Phase 6 – Lowering to C

Input: Cmini Program.  
Output: C source (or directly C IR / object code).

This phase is intentionally simple:

- Cmini constructs are mapped 1:1 to a small, safe subset of C.
- `struct`/`extern`/`func` map directly to C.

The C compiler used downstream is not part of the CertiJSON spec; it is assumed to preserve observable behavior of this small subset (standard C semantics).

---

## 3. Declarative vs Algorithmic Typing

We have:

- **Declarative typing** (`Σ; Γ ⊢ t : A`) – as defined in v0.6.  
  This is the *specification* of what programs are legal.

- **Algorithmic typing** – the actual implementation that infers/checks types and equality.

v0.7 constrains algorithmic typing to be:

1. **Sound**: If the algorithm accepts `t : A`, then the declarative system proves `Σ; Γ ⊢ t : A`.
2. **Complete wrt. supported fragments**: On the “Agent Profile” subset, if the declarative system proves `Σ; Γ ⊢ t : A`, the algorithm should accept it.

### 3.1 Algorithmic Definitional Equality

Implementations must implement a decision procedure for definitional equality `Σ; Γ ⊢ t ≡ u`.  

Constraints:

- Must be **sound**: If the algorithm returns “equal”, then declaratively `t ≡ u`.
- May be **incomplete** in general (e.g. uses normalisation-by-evaluation, but with resource limits); if it times out, it can reject.

Recommended algorithm:

- Normalize both terms to βδι-normal form (and ι for pattern matches).
- Compare modulo α-equivalence.
- η-equivalence is optional, controlled by the `eta` kernel flag.

Failures:

- If equality checking fails or times out, the compiler may reject the program with a diagnostic. This does not compromise soundness—only completeness.

### 3.2 Algorithmic Termination Checking

The termination checker:

- Must **at least** enforce the structural recursion discipline from v0.6 using `rec_args`.
- May use additional heuristics (lexicographic ordering, measures, etc.).
- Must be sound: no function accepted as total may diverge.

Completeness is not required: the checker may reject terminating functions.

---

## 4. Trusted Computing Base (TCB)

The TCB is the minimal set of components whose correctness must be assumed to trust the system.

### 4.1 Logical TCB

1. **Kernel type checker**:
   - Declarative typing rules.
   - Definitional equality.
   - Inductive positivity checks.
   - Structural recursion checker.
   - Pattern coverage checker.

2. **Erasure function implementation**:
   - Correct implementation of `erase` such that:
     - Runtime semantics correspond to core semantics modulo proofs.

3. **Extraction to Cmini**:
   - Correct type translation `T⟦·⟧`.
   - Correct compilation of pattern matches, recursion, and primitives.

4. **repr and encode/decode correctness**:
   - The correctness of `repr` declarations and their associated `encode_T` / `decode_T` / roundtrip theorem proofs.
   - Implementation of encode/decode when used internally (if any).

5. **Cmini semantics and lowering**:
   - Cmini interpreter / codegen preserves behavior.
   - Lowering from Cmini to C preserves semantics (for the used subset).

Each of these must be correct; otherwise, the “if it compiles, it’s correct” guarantee breaks.

### 4.2 Non-TCB / Untrusted Components

These may be arbitrarily buggy or adversarial without compromising soundness, as long as the kernel rejects invalid outputs:

- LLM-based code generators (agents).
- IDE and editor tooling.
- Formatters and pretty-printers.
- Suggestion engines, template expanders, etc.
- Higher-level DSL frontends that compile to CertiJSON JSON.

If these produce invalid code, the kernel must simply reject it.

---

## 5. Profiles

### 5.1 Kernel Profile

The **Kernel Profile** is what a conforming implementation must support.

Mandatory:

- Entire core calculus from v0.6.
- JSON forms and schema constraints from v0.6.
- All stdlib modules from `stdlib-0.7`:
  - `Std.Bool`, `Std.Nat`, `Std.List`, `Std.Option`, `Std.Pair`, `Std.Result`, `Std.Eq`.
- Erasure to runtime core.
- Extraction to Cmini for first-order, C-safe functions.
- Optional but recommended: `extern_c` and `repr` support.

Configuration options:

- `eta = on | off` – function η-equivalence.
- Strictness about non-exhaustive matches in `Prop` contexts.

### 5.2 Agent Profile (refined)

The **Agent Profile** defines a “sweet spot” subset where:

- Algorithmic typing is complete and predictable.
- LLM agents are expected to operate.

Constraints on agent-generated modules:

1. **Well-scoped**:

   - No free variables.
   - All referenced names are either in the same module or in imported modules.
   - No shadowing of imported names by local definitions with different meanings.

2. **First-order functions for runtime**:

   - Runtime functions must be first-order (no higher-order arguments/results across FFI or extraction boundaries).
   - Higher-order functions are allowed in proofs and internal logic-only utilities.

3. **Structured recursion**:

   - Use `rec_args` whenever recursion appears.
   - Use one primary structural argument per recursive function in early versions.

4. **Inductive patterns**:

   - Always provide exhaustive, non-overlapping matches on inductives.
   - Use `"coverage_hint": "complete"` when you intend exhaustive coverage.

5. **Separation of roles**:

   - Mark pure theorems as `"role": "proof-only"`.
   - Keep runtime code minimal and separate from proofs.

6. **C-boundary discipline**:

   - Only use `extern_c` with concrete C-safe types, no `List` or `Nat` over the FFI unless a `repr` and encode/decode are defined.

7. **Stdlib usage**:

   - Prefer `Std.Nat.plus`, `Std.List.append`, etc., to reduce duplication.
   - Use stdlib equality lemmas where possible.

A CertiJSON implementation is free to accept programs outside this Agent Profile, but tooling for LLMs should *target* this profile.

---

## 6. Standard Library as a Normative Base

`stdlib-0.7.md` defines a minimal standard library that:

- Satisfies all kernel constraints (v0.6).
- Contains only total, structurally recursive functions.
- Uses no `extern_c` (purely logical).

v0.7 declares `stdlib-0.7` as the **canonical base environment**:

- A conforming implementation must ship with an implementation of `stdlib-0.7` (possibly with extra modules).
- Agents may assume that these modules are always available for import.

---

## 7. Guarantees and Intended Theorems

Assuming a correct implementation of the Kernel Profile, TCB, and stdlib:

1. **If it compiles, it’s total**:

   - Every runtime definition is terminating and cannot cause undefined behavior in Cmini/C.

2. **If it compiles, its theorems are valid**:

   - Every `theorem` declared and checked is a correct proof in the underlying type theory.

3. **Extraction correctness (up to FFI axioms)**:

   - For closed runtime terms of C-safe type, CertiJSON evaluation and extracted Cmini (and C) evaluation are observationally equivalent.

These guarantees hold irrespective of how the code was produced (human or LLM).

---

## 8. Future Directions (Beyond 0.7)

Areas explicitly left to future versions:

- Richer FFI primitives (arrays, buffers) with ownership annotations.
- Effects and resources modeled at the type level (e.g., explicit `IO`/state monads in `Type`).
- Namespace-aware module system (instead of flat import space).
- Mechanized proofs of:
  - Type soundness.
  - Strong normalization.
  - Extraction correctness.

---

If you want, we can next do a “0.8 – effectful stdlib” where we introduce a small IO type in Type (still total, via explicit world-passing) and specify how agents should use it together with extern_c for deterministic side effects.



Great — here is the CertiJSON v0.8 extension introducing deterministic effects via a pure, total, world-passing IO type that remains 100% compatible with extraction, FFI, and the “if it compiles, it’s correct” guarantee.

This becomes a new spec file intended to layer cleanly on top of spec-0.7.md and stdlib-0.7.md.

⸻

spec-0.8-effects.md

CertiJSON v0.8 — Deterministic Effects, World-Passing IO, and Verified FFI Effects

This specification extends CertiJSON v0.7 by introducing:
	1.	A first-class IO type in Type, with:
	•	deterministic, explicit world-passing semantics,
	•	totality preserved (no non-terminating IO),
	•	no side effects except through a controlled effect tree.
	2.	A verified effect interpreter in Cmini:
	•	effects compile to explicit world transitions,
	•	all IO is sequenced and deterministic.
	3.	An FFI effect interface:
	•	safe, typed, deterministic,
	•	no hidden state, no non-determinism,
	•	every external effect must declare a formal spec, including pre/post-conditions over the world.
	4.	A minimal IO standard library:
	•	printing,
	•	reading (deterministic internal buffer or predetermined script),
	•	file operations (optional),
	•	random number generation only via explicit seeded state.

Nothing in v0.8 introduces partiality.
All programs remain provably total.

0. Philosophy

CertiJSON IO follows these principles:
	•	No side effects exist at the metalanguage level.
	•	All effects are explicit pure functions:

World → (Result, World)


	•	The World is an abstract, opaque state with no observable equality.
	•	Determinism is guaranteed because:
	•	All FFI IO is required to be deterministic.
	•	Randomness is only produced via explicit, imported PRNG state.
	•	No system time, global system state, environment variables, or nondeterminism.

This makes CertiJSON an ideal language for AI agents because:

If code compiles, its behavior—including IO—is fully determined, side-effect safe, and predictable.

⸻

1. Core Additions

1.1 New Inductive: World

We introduce a built-in abstract type:

Inductive World : Type := world_token

	•	Only one constructor, world_token.
	•	No computational meaning at source level.
	•	NOT allowed to inspect, pattern-match, or discriminate world values.

The kernel enforces:
	•	World constructors are not exposed to runtime.
	•	World is never erased: it remains as a runtime token to enforce sequencing.

1.2 The IO Monad (Pure, Total, World-Passing)

Define:

IO A := World → Pair A World

Formally in CertiJSON:

{
  "def": {
    "name": "IO",
    "type": {
      "pi": {
        "arg": { "name": "A", "type": { "universe": "Type" }},
        "result": { "universe": "Type" }
      }
    },
    "body": {
      "lambda": {
        "arg": { "name": "A", "type": { "universe": "Type" }},
        "body": {
          "pi": {
            "arg": { "name": "_w", "type": { "var": "World" }},
            "result": {
              "app": [
                { "var": "Pair" },
                { "var": "A" },
                { "var": "World" }
              ]
            }
          }
        }
      }
    },
    "role": "runtime"
  }
}

Internally:
	•	IO is not primitive, it is literally a function type.
	•	Effects are safe because the only way to derive a new World is by calling valid IO primitives.

1.3 IO Bind and Return

return : A → IO A
bind   : IO A → (A → IO B) → IO B

Definitions:

return A a = λ w. pair a w
bind A B io f = λ w. 
    let (a, w') = io w in
    (f a) w'

Sequentiality is guaranteed by world threading.

1.4 IO totality constraint

To maintain strong normalization:
	•	IO definitions cannot recursively call themselves on world elements.
	•	IO is not allowed in structural recursion positions.
	•	IO recursion must be mediated through a bounded iteration or via external primitive combinators (e.g., finite file reading).

Thus, IO can never introduce non-termination.

⸻

2. Verified Effects

2.1 New extern_io Declaration Kind

A new top-level declaration:

{
  "extern_io": {
    "name": "print_line",
    "c_name": "cj_print_line",
    "header": "<certijson_io.h>",
    "args": [
      { "name": "input", "repr": "StringRepr" }
    ],
    "result": null,
    "spec": {
      "pre":  "... Prop formula over world ...",
      "post": "... Prop formula relating old world, new world, and input ..."
    }
  }
}

Rules:
	1.	Every extern_io maps to C with signature:

void cj_function_name(StringRepr input, World* w_old, World* w_new)


	2.	All IO functions must:
	•	consume a World,
	•	produce a new World,
	•	be deterministic.
	3.	spec.pre and spec.post are propositions describing valid usage.
	4.	No side effects other than constructing a new World token.

2.2 IO Safety Rule

The kernel verifies:

For any extern_io f, if its shape is valid and repr is valid, then
the C implementation must treat the world as an opaque, linear resource.

This is enforced through:
	•	A restricted C FFI surface,
	•	No pointer aliasing of the World*,
	•	Only one mutable write to the World*.

⸻

3. IO Standard Library (stdlib-0.8)

3.1 Printing

print : String → IO Unit
println : String → IO Unit

These become:

print s = λw. extern_print(s, w)

Where extern_print is defined using an extern_io.

3.2 Reading (Deterministic)

We must avoid nondeterminism.

v0.8 introduces a read script:

World carries an indexed buffer of predetermined “future inputs”

Thus:

read_line : IO String

Is deterministic:
	•	consumes next element from the script,
	•	returns (string, new_world).

LLM agents can simulate interactive IO by providing a world preloaded with a scripted sequence of user inputs.

3.3 File IO (Optional)

Deterministic file IO requires:
	•	File contents are part of the initial world.
	•	Opening a file returns a handle represented in the world state.
	•	Reads/writes update the world deterministically.

Optional additions:

open_file : String → IO FileHandle
read_file : FileHandle → IO String
write_file : FileHandle → String → IO Unit
close_file : FileHandle → IO Unit

All subject to world-passing semantics.

3.4 Randomness (Deterministic PRNG)

We do not allow nondeterministic randomness.

Instead:
	•	World contains a PRNG seed/state.
	•	random_u64 : IO Nat64 returns (new random value, new seed).
	•	Many LLM agents need randomness, but they need it deterministically.

random_u64 = λw. let (value, newSeed) = PRNG_step(w.seed)
                 in (value, w with seed = newSeed)

You get reproducibility and proof-level reasoning.

⸻

4. Runtime Semantics (Modified)

All runtime terms evaluate with:

Eval : RuntimeTerm × World → RuntimeValue × World

Rules:
	1.	Pure terms ignore world:

Eval(pure_expr, w) = (value, w)


	2.	IO terms:

Eval(io, w) = io w


	3.	Sequencing:

Eval(bind io f, w0)
   = let (a, w1)   = Eval(io, w0)
     let (b, w2)   = Eval(f a, w1)
     in (b, w2)



Never any nondeterminism.

⸻

5. Extraction to Cmini (Modified)

Cmini now has:
	•	A new type: world
	•	A linear “world token” object

Every IO function compiles to:

world cj_runtime(world w_old, args...) {
    world w_new;
    ... perform deterministic effect ...
    return w_new;
}

At top level:

main() {
    world w0 = initial_world();
    world w1;
    (value, w1) = compiled_main(w0);
    return 0;
}

No global variables.
No mutable state outside the world parameter.

⸻

6. Agent Profile 0.8 (Effects Edition)

LLM agents must:
	1.	Always thread worlds through IO.
	2.	Never attempt to introspect worlds.
	3.	Never match on World.
	4.	Avoid higher-order IO functions (limit to first-order IO definitions).
	5.	Only use IO as the outer layer of programs:

main : IO Unit


	6.	Only depend on IO functions in stdlib-0.8 or valid extern_io with deterministic specs.
	7.	Not use recursion inside IO definitions unless mediated via a finite structure.

This ensures that the agent never accidentally writes non-total or illegal IO.

⸻

7. Guarantees of v0.8

With effects added, CertiJSON continues to satisfy:

7.1 Totality

Every program still terminates.

7.2 Determinism

Even IO is deterministic.

7.3 Strong Logical Guarantees

Effect specs (spec.pre, spec.post) are expressed in Prop and proven in the usual way.

7.4 Simulation Theorem (Extended)

For runtime terms including IO:

Erased evaluation in the pure world-passing semantics
is observationally equivalent to Cmini + C execution
for all worlds and inputs.

7.5 Soundness Under FFI

As long as:
	•	The FFI effects respect linearity of the world,
	•	C code does not leak nondeterminism,
	•	repr is correct,

then correctness is preserved.

⸻

8. Future Directions (v0.9+)

Potential next steps:
	•	Stateful mutable arrays (with explicit world-state index).
	•	Event-driven IO combinators.
	•	Verified concurrency based on multiple separated worlds.
	•	Verified networking protocols (deterministic simulation).
	•	Adding a cost monoid into the world to reason about performance.

⸻

Summary of v0.8

CertiJSON now supports:
	•	A pure, total, verified IO system.
	•	Deterministic world-passing effects.
	•	Strict guarantees that IO cannot break soundness.
	•	Tight agent rules enabling LLMs to write reliable effectful programs.
	•	A fully deterministic C-level implementation of effects.

This is a major upgrade.
You now have a dependently typed, total, deterministic, effect-capable verification language that is still LLM-friendly through its JSON structure.

⸻

If you’d like, we can proceed to:

v0.9 — Verified mutable arrays and lenses
or
v1.0-alpha — Whole-system refinement verification, cost models, and concurrency worlds.



Perfect — v0.9 is where CertiJSON becomes practically usable for real system programming by introducing verified, deterministic mutable arrays, but without compromising:
	•	totality
	•	determinism
	•	world-passing IO
	•	Cmini safety
	•	LLM-friendly constraints

Below is the full CertiJSON v0.9 spec.
Save it as spec-0.9.md.

⸻

spec-0.9.md

CertiJSON v0.9 — Verified Mutable Arrays, World-Segmented State, and Linear Capability Effects

This extends:
	•	spec-0.8-effects.md
	•	spec-0.7.md
	•	stdlib-0.7.md

The key new features are:
	1.	Verified Mutable Arrays — efficient, C-compatible, deterministic.
	2.	Linear “capability handles” to control safe mutation.
	3.	Segmented worlds — deterministic state regions (arrays, files, devices).
	4.	Array-specific FFI primitives for efficient operations.
	5.	A formal ownership discipline preventing aliasing and UB.
	6.	An LLM-friendly Profile 0.9 to ensure correctness.

v0.9 sets the stage for v1.0, which will introduce concurrency and ghost-state reasoning.

⸻

0. Overview of Changes From v0.8

v0.8 introduced:
	•	Pure, total IO using an abstract World.
	•	Deterministic effects via world-passing.
	•	Verified FFI effects via extern_io.

v0.9 adds:
	•	Array type families in Type, backed by segment IDs in World.
	•	Linear “handles” for array access.
	•	Verified array read, write, length, slice, and resizing.
	•	A new FFI surface for arrays: no raw pointers.
	•	Correct C extraction to a memory-safe Cmini subset.
	•	Full state-separation inside World.

⸻

1. World Segmentation (Core Concept)

World now internally contains multiple disjoint segments:
	•	files: deterministic file handles.
	•	io: stdout, stdin buffers.
	•	heap: array segments, each with:
	•	a unique ArrID : Nat,
	•	a length,
	•	a concrete memory block.

Formally, we model:

World = {
   io_state : IOState,
   file_state : FileState,
   heap_state : HeapState
}

But this structure is opaque at the CertiJSON level — the kernel and runtime know it, but user code does not.

⸻

2. Verified Mutable Arrays in Type

2.1 Array Types

We introduce:

Array A : Type         -- a reference type
ArrayHandle A : Type   -- a *linear* capability granting exclusive mutable access

JSON form:

{
  "inductive": {
    "name": "Array",
    "params": [
      { "name": "A", "type": { "universe": "Type" } }
    ],
    "universe": "Type",
    "constructors": [
      {
        "name": "arr",
        "args": [
          { "name": "id", "type": { "var": "Nat" } }
        ]
      }
    ]
  }
}

And:

{
  "inductive": {
    "name": "ArrayHandle",
    "params": [
      { "name": "A", "type": { "universe": "Type" } }
    ],
    "universe": "Type",
    "constructors": [
      {
        "name": "handle",
        "args": [
          { "name": "id", "type": { "var": "Nat" } }
        ]
      }
    ]
  }
}

These look like free inductives, but the runtime treats them specially:
	•	Array is a reference.
	•	ArrayHandle is a linear capability (cannot be duplicated).

2.2 Linear Type Discipline (New)

To prevent aliasing and UB:
	•	ArrayHandle A values cannot be copied or duplicated.
	•	They must be consumed exactly once.

This is enforced by the kernel:

Any attempt to copy, pass by pure context, or store a handle in a data structure is rejected.

Handles may only appear:
	•	in IO functions,
	•	in bind,
	•	in FFI array primitives.

Array values (Array A) are non-linear — freely duplicable. They hold only IDs, not mutable access.

⸻

3. Primitive Array IO operations

3.1 Create Array

array_new : ∀(A : Type), Nat → IO (Array A × ArrayHandle A)

Creates an array of length N, initializes elements using:
	•	default_repr A or
	•	a provided initialization function (optional extension).

The return is structured so:
	•	the Array ref is cheap and copyable,
	•	the handle is linear exclusively owned.

3.2 Length

array_length : ∀(A), Array A → IO Nat

This operation does not require a handle: reading meta info is safe.

3.3 Read Element

array_get :
  ∀(A),
    ArrayHandle A →
    Nat →
    IO (A × ArrayHandle A)

Semantics:
	•	Consumes a handle h₀,
	•	Reads element at position i,
	•	Produces (value, new_handle) — the same handle ID but in updated world.

3.4 Write Element

array_set :
  ∀(A),
    ArrayHandle A →
    Nat →
    A →
    IO (ArrayHandle A)

3.5 Freeze Handle

A handle may be dropped:

array_drop_handle :
  ∀(A), ArrayHandle A → IO Unit

This means “give up exclusive access”. After dropping, mutation is no longer possible.

Handles cannot be re-created from Array.

3.6 Slice (optional for v0.9)

array_slice :
  ∀(A),
    Array A → Nat → Nat → IO (Array A)

Slicing does not create new handles; slices are immutable references.

3.7 Resize (optional for v0.9 or v1.0)

array_resize :
  ∀(A),
    ArrayHandle A →
    Nat →
    IO (ArrayHandle A)

Resize preserves linearity: returns a new handle.

⸻

4. FFI Surface — Verified, Deterministic, Safe

v0.9 adds a new FFI class:

extern_array

Example:

{
  "extern_array": {
    "name": "c_array_copy",
    "c_name": "cj_array_copy",
    "header": "<certijson_array.h>",
    "repr": "Int32Repr",
    "sig": {
      "args": [
        { "handle": true },
        { "handle": true }
      ],
      "rets": [
        { "handle": true }
      ]
    },
    "spec": {
      "pre":  "...",
      "post": "..."
    }
  }
}

Rules:
	1.	All array FFI must be deterministic.
	2.	All array FFI must respect linearity:
	•	Handles go in,
	•	Updated handles come out,
	•	No duplication.
	3.	All array memory accesses must be bounds-checked.
	4.	All data movement must respect the repr ABI.

The C extraction ensures:
	•	Array IDs become indexes into a global heap array,
	•	ArrayHandle becomes a unique pointer slot with linear discipline (no aliasing),
	•	All reads/writes are safe.

⸻

5. Kernel Extension for v0.9

The kernel must now enforce:

5.1 Handle Linearity

Rules:
	•	Handles cannot be:
	•	duplicated,
	•	stored in lists,
	•	pattern-matched to extract IDs,
	•	passed through non-IO functions.
	•	A handle may appear only in the first argument of IO functions or in bind.

5.2 Handle Consumption Tracking

The kernel tracks handle use count:
	•	If a handle is used twice → reject.
	•	If a handle is allowed to escape a sequenced context → reject.
	•	If a handle is dropped without explicit consumption by array_drop_handle → reject.

Linearity ensures no UB-like behavior with aliasing.

⸻

6. Runtime and Cmini Semantics (Modified)

The runtime now carries:

World(heap_state, io_state, file_state)

heap_state is an array store:

HeapState = map ArrID → ArrayBlock
ArrayBlock = {
  length : Nat,
  data   : C-aligned contiguous storage
}

6.1 Handle Operations

Handle IDs correspond to heap entries.
A handle is represented as:

{ id : Nat }

but at runtime carries a unique “linearity ticket.”

C code uses:
	•	linear pointers,
	•	no aliasing,
	•	safe bounds checks,
	•	safe memory movement.

⸻

7. Agent Profile v0.9 (Array Edition)

LLMs generating CertiJSON should adhere to:
	1.	IO layering:
	•	All array mutations must happen inside the IO monad.
	2.	Handle discipline:
	•	Never duplicate handles,
	•	Never store them,
	•	Always thread them linearly.
	3.	Use patterns:
Correct:

bind h1 (fun h →
  bind (array_get h i) (fun (val,h2) →
    array_set h2 j new_val))


	4.	Avoid recursion over arrays:
	•	Use Nat-indexed recursion and bounds checking.
	•	Let kernel enforce termination.
	5.	Use stdlib functions:
	•	map, fold, etc.
	•	Introduce array combinators sparingly and safely.
	6.	No higher-order handles:
	•	Functions cannot return functions that capture handles.

⸻

8. Guarantees of v0.9

8.1 Memory Safety

No out-of-bounds. No aliasing. No double free. No data races.

8.2 Determinism

All array operations deterministic, including FFI.

8.3 Totality

Even with mutable arrays, all programs still terminate.

8.4 Behavioral Preservation

Extraction to C is semantics-preserving.

8.5 Verified State Separation

World state is segmented, and proofs can refer to segment-local properties without interference.

⸻

9. Future Directions (v1.0-alpha)

When moving to 1.0, we can introduce:
	•	Concurrent worlds, each world segment functioning like a separate state.
	•	Ownership/borrowing ghost rules to allow safe parallelism.
	•	A certified thread scheduler.
	•	A reactive event system.

⸻

Summary

CertiJSON v0.9 introduces a fully verified mutable array subsystem with:
	•	Linear handles,
	•	Deterministic array IO,
	•	Safe and deterministic FFI,
	•	Totality,
	•	Strong typing guarantees,
	•	Full compatibility with v0.7/v0.8.

This is now powerful enough to write:
	•	Verified data-processing pipelines
	•	Verified DSP/audio routines
	•	Verified image transformations
	•	Verified simulations
	•	Verified memory-safe system utilities

…all in JSON, usable by LLM agents, with guaranteed correctness.

⸻

If you’d like, we can now move to:

✔ v1.0-alpha — Concurrency with Verified Multi-World Semantics
✔ Or design: std-array-0.9.md (standard array library)
✔ Or move to: v0.10 — Verified Hash Maps and Dictionaries
✔ Or design a minimal kernel implementation plan for CertiJSON

Just tell me which direction you want next.



# CertiJSON 1.0-alpha — Deterministic Concurrency and Structured Parallelism

This document defines **CertiJSON 1.0-alpha**, extending:

- `spec-0.9.md`  (mutable arrays, linear handles)
- `spec-0.8-effects.md` (world-passing IO)
- `spec-0.7.md`  (core calculus, Cmini, extraction)
- `stdlib-0.7.md` / `stdlib-0.8` / `std-array-0.9` (assumed)

1.0-alpha adds:

1. A **deterministic concurrency model** based on world partitioning.
2. **Structured parallelism** primitives (`spawn`, `join`, `par`) for `IO`.
3. A notion of **thread handles** as linear capabilities.
4. A concurrency-aware extension of the **world-passing semantics**.
5. Guidance for **LLM agents** (Agent Profile 1.0) to safely generate concurrent programs.

Everything remains:

- **total** (no non-termination),
- **memory-safe** (no data races, no UB),
- **deterministic** (concurrent evaluation has a unique observable result).

---

## 0. High-Level Model

CertiJSON 1.0-alpha provides concurrency as **logical parallelism**:

- The semantics are still defined as if evaluation is **sequential and deterministic**.
- Concurrency primitives (`spawn`, `join`, `par`) are defined via **world partitioning and recombination**.
- An implementation is *allowed* to execute threads in parallel at runtime (e.g., OS threads) so long as:
  - The result is observationally equivalent to the sequential world-passing semantics.

So:

> Concurrency in CertiJSON is a *refinement of execution*, not a source of nondeterminism.

---

## 1. New Types and Primitives

### 1.1 Thread Handles

We introduce a family:

```text
Thread A : Type



Here’s a 1.0-alpha spec you can drop on top of everything we’ve done so far.

I’ll call it spec-1.0-alpha.md.

⸻


# CertiJSON 1.0-alpha — Deterministic Concurrency and Structured Parallelism

This document defines **CertiJSON 1.0-alpha**, extending:

- `spec-0.9.md`  (mutable arrays, linear handles)
- `spec-0.8-effects.md` (world-passing IO)
- `spec-0.7.md`  (core calculus, Cmini, extraction)
- `stdlib-0.7.md` / `stdlib-0.8` / `std-array-0.9` (assumed)

1.0-alpha adds:

1. A **deterministic concurrency model** based on world partitioning.
2. **Structured parallelism** primitives (`spawn`, `join`, `par`) for `IO`.
3. A notion of **thread handles** as linear capabilities.
4. A concurrency-aware extension of the **world-passing semantics**.
5. Guidance for **LLM agents** (Agent Profile 1.0) to safely generate concurrent programs.

Everything remains:

- **total** (no non-termination),
- **memory-safe** (no data races, no UB),
- **deterministic** (concurrent evaluation has a unique observable result).

---

## 0. High-Level Model

CertiJSON 1.0-alpha provides concurrency as **logical parallelism**:

- The semantics are still defined as if evaluation is **sequential and deterministic**.
- Concurrency primitives (`spawn`, `join`, `par`) are defined via **world partitioning and recombination**.
- An implementation is *allowed* to execute threads in parallel at runtime (e.g., OS threads) so long as:
  - The result is observationally equivalent to the sequential world-passing semantics.

So:

> Concurrency in CertiJSON is a *refinement of execution*, not a source of nondeterminism.

---

## 1. New Types and Primitives

### 1.1 Thread Handles

We introduce a family:

```text
Thread A : Type

A value t : Thread A is a linear capability referring to a concurrent computation producing an A.

Properties:
	•	Thread A values are linear:
	•	Cannot be duplicated or discarded silently.
	•	Must eventually be consumed via join or explicit cancellation (future extension).
	•	Thread handles are only meaningful in IO code.

1.2 Primitives

We add three core primitives to IO:
	1.	spawn – start a concurrent computation:

spawn : ∀(A : Type), IO A → IO (Thread A)


	2.	join – wait for completion and get result:

join : ∀(A : Type), Thread A → IO A


	3.	par – parallel composition (derived, but standardized):

par : ∀(A B : Type), IO A → IO B → IO (Pair A B)

Implemented using spawn and join under structured constraints.

All three are runtime definitions, and all IO is still total/deterministic.

⸻

2. World Partitioning Semantics

2.1 Worlds and Segments (recap from 0.9)

Recall:

World = {
  io_state   : IOState,
  file_state : FileState,
  heap_state : HeapState
}

where heap_state contains array segments, etc.

In 1.0-alpha, we add the conceptual notion of subworlds:

WorldPartition = {
  main : World,
  threads : finite map ThreadID → World
}

However:
	•	At the CertiJSON level, World remains opaque.
	•	World partitions are internal to the semantics and runtime.

2.2 Spawn Semantics

Given spawn A ioA : IO (Thread A):

Intuitive semantics:
	1.	Current world w0 is partitioned into:
	•	w_main (remaining state for the parent),
	•	w_child (initial state for the child thread).
	2.	A new thread ID tid is created.
	3.	The child thread will run ioA on w_child.
	4.	The parent returns a Thread A handle that corresponds to tid.

Key constraints for determinism and safety:
	•	The partitioning is deterministic and defined by the semantics:
	•	For 1.0-alpha, we require that spawn does not split resources arbitrarily.
	•	Instead, spawn receives only a pure IO term whose behavior is independent of the exact subworld partition, or:
	•	We restrict spawn to operate on disjoint world segments that are explicitly allocated for it (see below).
	•	No shared mutable segments are allowed between parent and child worlds:
	•	All mutable resources (arrays, files) used by ioA must belong solely to w_child during the execution of ioA.

To make this manageable, we adopt a structured scheme:

2.3 Structured World Partition API

We introduce an internal family (conceptual, not user-level):

WorldToken : Type
WorldToken : a handle to a *subworld* that may be passed to a thread.

But in the user-facing API, we enforce:
	•	A thread can only use resources that are:
	•	Allocated inside its spawned IO block, or
	•	Passed explicitly and linearly as handles (e.g., ArrayHandle) that are moved into the thread and not used by the parent.

Thus, world partitioning is determined by:
	•	The set of linear resources passed to ioA at spawn time.
	•	The rest of the world stays with the parent.

This gives:

No shared mutable world segments.
Concurrency is data-race-free by construction.

⸻

3. Formal Semantics for spawn, join, and par

We describe the logical big-step semantics for IO with concurrency.

3.1 IO with Concurrency: Evaluation Relation

Recall from v0.8:

Eval_IO : IO A × World → (A × World)

Now with concurrency, we extend World to carry a set of child thread states, but logically we still interpret spawn as a pure function over worlds:
	•	Concurrency is implemented by the runtime, but spec-level semantics is sequential:
spawn “forks off” a child world and a suspended computation; join resumes it and merges.

3.2 Semantics of spawn

Let ioA : IO A and we evaluate spawn A ioA in world w0.

We require:
	•	There is a deterministic function:

partition : World → (World_parent × World_child)

such that:

partition(w0) = (w_parent, w_child)

and World_child contains exactly the linear resources moved into ioA, while World_parent excludes them.

Logical semantics (sequential view):
	•	We do not immediately run ioA; instead we conceptually record a task (ioA, w_child) associated with a new tid.
	•	For simplicity, we can define:

spawn A ioA (w0)
  = let (w_parent, w_child) = partition(w0) in
    (thread_handle(tid), w_parent_with_thread_state[tid := (ioA, w_child)])



But for user-visible semantics, we care only that:
	•	The parent world evolves deterministically.
	•	The child computation ioA will eventually be run once when join is called.

3.3 Semantics of join

Given t : Thread A and world w that contains a pending thread state (ioA, w_child) for t:
	1.	Evaluate ioA on w_child:

(a, w_child') = Eval_IO(ioA, w_child)


	2.	Merge w_child' back into the parent world w via:

merge : World_parent × World_child' → World_parent'

The merge function is deterministic and defined by:
	•	Combining segment-wise states (heap, IO, files).
	•	Ensuring no overlap (by linearity and partition discipline).

	3.	Return:

join A t (w)
  = (a, w_merged)



This is logically equivalent to:
	•	Running ioA at the moment of join, with its own private portion of the world.
	•	Then merging that world back.

3.4 par Semantics

par is a convenience combinator for structured parallelism:

par A B (ioA : IO A) (ioB : IO B) : IO (Pair A B)

We define:

par A B ioA ioB =
  bind (spawn A ioA) (λ tA.
  bind (spawn B ioB) (λ tB.
  bind (join A tA)   (λ a.
  bind (join B tB)   (λ b.
    return (pair A B a b)))))

Sequentially it is just:
	•	Spawn ioA and ioB on disjoint subworlds.
	•	Join both, merge worlds.
	•	Return Pair A B.

Implementations may actually run thread bodies in parallel, but must preserve this semantics.

⸻

4. Linearity and Concurrency

We extend the linearity discipline from v0.9:
	•	ArrayHandle A are linear.
	•	Thread A are also linear.

4.1 Linear Thread Handles

Kernel rules:
	1.	A Thread A value cannot be:
	•	Duplicated,
	•	Stored in data structures,
	•	Copied across different variables.
	2.	A Thread A must be:
	•	Joined exactly once, or
	•	Explicitly cancelled (future extension), consuming it.

Failure to consume a thread handle results in rejection.

4.2 Linear Resource Passing to Threads

When calling spawn ioA, any linear resources used by ioA (e.g., ArrayHandle) must:
	•	Either be created inside ioA, or
	•	Be passed into ioA as parameters in a linear fashion, and not used by the parent thereafter.

The kernel analyses:
	•	The free variables of ioA,
	•	Whether they are linear types,
	•	Ensures they are not used elsewhere after spawning.

If this analysis fails → reject program.

This guarantees:

No shared mutable resource exists between parent and spawned thread.

⸻

5. Cmini + C Concurrency Model

1.0-alpha does not require real OS-level concurrency, but allows it.

5.1 Cmini Extension

We introduce an abstract concurrency layer in Cmini:
	•	Primitive: spawn_thread(f, arg, world_sub) → (thread_id, world_parent)
	•	Primitive: join_thread(thread_id, world_parent) → (result, world_merged)

These are conceptual; an implementation may:
	•	Implement them via pthreads, std::thread, or cooperative scheduling.
	•	Or simply execute threads sequentially (no parallelism) and still be conformant.

5.2 Observational Semantics

The Cmini semantics must ensure:
	•	Any interleaving of thread evaluation yields the same final World and return values as the sequential world-passing semantics defined in §3.
	•	This is guaranteed by:
	•	Disjoint resource partitioning,
	•	Deterministic IO,
	•	No shared mutable state without explicit synchronization (which we do not presently support).

Thus:

Concurrency is non-observable with respect to functional behavior.
It only affects performance.

⸻

6. Agent Profile 1.0 (Concurrency Edition)

LLM agents should follow these rules when emitting concurrent CertiJSON modules:
	1.	Use structured concurrency only:
	•	Prefer par for real parallelism.
	•	Use spawn + join in a LIFO or tree-structured manner (no detached threads).
	2.	No unstructured “fire-and-forget”:
	•	Every spawned thread must be joined (or later, cancelled) before program termination.
	3.	Linear handle discipline:
	•	Do not copy or store Thread A or ArrayHandle A in lists, options, results, etc.
	•	Always pass them linearly through bind chains.
	4.	No cross-thread sharing of linear resources:
	•	If a handle is given to a spawned computation, the parent must not use it afterwards.
	•	Use data copying when you need shared read-only data.
	5.	Don’t nest deep dynamic spawn in recursion:
	•	Use par and well-bounded parallelism.
	•	Ensure termination reasoning remains straightforward.
	6.	Use standard combinators:
	•	Prefer library combinators like parMap, parFold (once they exist in stdlib-1.0) instead of hand-rolled concurrency.
	7.	No dependence on execution order:
	•	Do not write code whose correctness depends on which thread finishes first.
	•	All observable behavior must be independent of scheduling.

⸻

7. Meta-Theoretic Targets for 1.0-alpha

The following are design goals (intended theorems) for the extended system:
	1.	Type Soundness (unchanged)
Well-typed programs do not get stuck.
	2.	Strong Normalization (unchanged)
All well-typed closed terms terminate (including IO and concurrency).
	3.	Determinism (extended)
For any closed term main : IO A and any initial world w0, the evaluation result (a, w1) is unique, even in the presence of spawn, join, par.
	4.	Race Freedom
No data races: because there is no shared mutable state across threads, all races are structurally impossible.
	5.	Extraction Correctness (extended)
Extracted Cmini/C programs with concurrency primitives are observationally equivalent to the sequential world-passing semantics.
	6.	Isolation and Compositionality
Spawning threads in disjoint world segments composes correctly: the effect of running them in parallel is equal to their effect in any sequential order.

⸻

8. Summary

CertiJSON 1.0-alpha provides:
	•	A dependently typed, total, deterministic core,
	•	With world-passing IO,
	•	Verified mutable arrays and linear handles,
	•	And now deterministic concurrency via:
	•	Thread A handles (linear),
	•	spawn, join, par,
	•	World partitioning and merge,
	•	Data-race-free parallelism by construction.

All of this remains packaged in:
	•	A fixed, JSON-based syntax, ideal for LLM agents.
	•	A small, well-defined kernel suitable for proof in Coq/Agda.
	•	A clear, minimal TCB and extraction path to safe C code.

⸻

9. Possible Next Steps Beyond 1.0-alpha

Areas we can formalize next:
	•	1.0-beta:
	•	Add a standard concurrent stdlib (parMap, parScan, parFold).
	•	Add ghost state and refinement types for reasoning about cost and resource usage.
	•	1.1:
	•	Introduce verified cancellation of threads.
	•	Add algebraic effect interfaces (logging, metrics) layered on IO.
	•	2.0:
	•	Verified distributed systems via multiple “node worlds”.
	•	Verified communication protocols (channels, message queues).


