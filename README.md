# CertiJSON

**A proof-based programming language for agentic LLMs**

[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![Status: Alpha](https://img.shields.io/badge/Status-Alpha-orange.svg)]()

---

## What is CertiJSON?

CertiJSON is a pure, total, dependently typed programming language designed **exclusively for use by AI coding agents**. It solves a fundamental problem in AI-assisted software development:

> **LLMs can generate code, but they cannot guarantee its correctness.**

CertiJSON shifts the burden of correctness from the code generator (the LLM) to the code verifier (the kernel). An LLM can propose any code it wants; if it's wrong, the kernel rejects it. If a CertiJSON module compiles, its theorems are mathematically valid and its runtime code is guaranteed to terminate without undefined behavior.

## Key Features

| Feature | Description |
|---------|-------------|
| 🔧 **JSON Syntax** | All programs are valid JSON—trivial parsing, no ambiguity |
| 🔒 **Proof-Based** | Curry–Howard correspondence: types = propositions, terms = proofs |
| ⚡ **C Interop** | Compiles to a safe C subset for real-world deployment |
| ⏱️ **Total** | All programs terminate—no infinite loops, no crashes |
| 🎯 **Deterministic** | Same inputs always produce same outputs |

## Quick Example

A simple natural number addition function in CertiJSON:

```json
{
  "module": "Example",
  "imports": ["Std.Nat"],
  "declarations": [
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
                  "match": {
                    "scrutinee": { "var": "n" },
                    "motive": { "var": "Nat" },
                    "as": "z",
                    "cases": [
                      {
                        "pattern": { "ctor": "zero", "args": [] },
                        "body": { "var": "m" }
                      },
                      {
                        "pattern": { "ctor": "succ", "args": [{ "name": "k" }] },
                        "body": {
                          "app": [
                            { "var": "succ" },
                            { "app": [{ "var": "plus" }, { "var": "k" }, { "var": "m" }] }
                          ]
                        }
                      }
                    ],
                    "coverage_hint": "complete"
                  }
                }
              }
            }
          }
        },
        "rec_args": [0]
      }
    }
  ]
}
```

## Why JSON?

Traditional programming languages have complex grammars with precedence rules, layout sensitivity, and ambiguous syntax. For LLMs:

- **Parsing is error-prone** — minor syntax errors break everything
- **Formatting varies** — style choices add noise to training
- **Ambiguity exists** — same text can mean different things

CertiJSON eliminates these issues:

- ✅ JSON is unambiguous and universally parsed
- ✅ Single canonical representation
- ✅ No precedence or layout rules to memorize
- ✅ Trivial for LLMs to generate and validate

## Architecture

```
┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐
│   JSON   │───▶│   Core   │───▶│ Runtime  │───▶│    C     │
│   File   │    │  Terms   │    │   Core   │    │  Source  │
└──────────┘    └──────────┘    └──────────┘    └──────────┘
            Parse &         Type Check &      Erase &        Extract &
            Elaborate       Verify            Optimize       Lower
```

### Compilation Pipeline

1. **Parse** — JSON → Raw AST
2. **Elaborate** — Raw AST → Core terms
3. **Type Check** — Verify types, termination, proofs
4. **Erase** — Remove proof-only terms
5. **Extract** — Core → Cmini (safe C subset)
6. **Lower** — Cmini → C source code

## Type System

CertiJSON features a dependently typed core with:

- **Two universes**: `Type` (computational) and `Prop` (logical)
- **Dependent functions**: `Π(x : A). B`
- **Inductive types**: Natural numbers, lists, options, etc.
- **Propositional equality**: `Eq_A(x, y)` with `refl` and `rewrite`
- **Structural recursion**: Guaranteed termination

## C Interoperability

CertiJSON provides safe FFI through explicit representation descriptors:

```json
{
  "repr": {
    "name": "Int32Repr",
    "kind": "primitive",
    "c_type": "int32_t",
    "size_bits": 32,
    "signed": true
  }
}
```

```json
{
  "extern_c": {
    "name": "c_sin",
    "c_name": "sin",
    "header": "<math.h>",
    "signature": {
      "return": { "repr": "Float64Repr" },
      "args": [{ "name": "x", "repr": "Float64Repr" }]
    },
    "type": { "pi": { "arg": { "name": "_", "type": { "var": "Float64" } }, "result": { "var": "Float64" } } },
    "safety": "pure"
  }
}
```

## Effects and Concurrency

- **World-passing IO**: Deterministic effects via `IO A = World → (A, World)`
- **Linear arrays**: Mutable arrays with ownership tracking
- **Structured concurrency**: `spawn`, `join`, `par` with deterministic semantics

## Documentation

- 📖 [Full Specification](formal_specs.md) — Complete language specification
- 🔧 [Standard Library](formal_specs.md#19-standard-library) — Bool, Nat, List, Option, Pair, Result
- 🤖 [Agent Profile](formal_specs.md#18-agent-profile) — Guidelines for LLM code generation

## Design Goals

| Goal | Description |
|------|-------------|
| **G1. Logical Soundness** | Types are propositions, terms are proofs |
| **G2. Totality** | All programs terminate |
| **G3. Separation** | Clear split between proofs (`Prop`) and code (`Type`) |
| **G4. Safe C Interop** | Explicit memory layouts, no undefined behavior |
| **G5. LLM-Optimized** | JSON syntax, no ambiguity |

## Status

CertiJSON is currently in **alpha** stage. The specification is stable, but the reference implementation is under development.

### Roadmap

- [x] Core type theory specification
- [x] JSON concrete syntax
- [x] C interop design (repr, extern_c)
- [x] Effects and IO model
- [x] Concurrency primitives
- [ ] Reference compiler implementation
- [ ] Standard library implementation
- [ ] IDE tooling
- [ ] Mechanized metatheory proofs

## Contributing

Contributions are welcome! Areas of interest:

- Reference compiler (F#)
- Standard library modules
- Example programs and proofs
- Documentation improvements
- Mechanized proofs (Coq/Agda)

## License

MIT License — see [LICENSE](LICENSE) for details.

## Acknowledgments

CertiJSON draws inspiration from:

- [Coq](https://coq.inria.fr/) — Dependent types and proof assistants
- [Lean](https://leanprover.github.io/) — Modern proof assistant design
- [Idris](https://www.idris-lang.org/) — Dependently typed programming
- [CompCert](https://compcert.org/) — Verified C compilation

---

<p align="center">
  <em>Making LLM-generated code provably correct.</em>
</p>
