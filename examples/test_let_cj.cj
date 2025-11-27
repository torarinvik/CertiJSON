import Std.Nat
import Std.Bool

# Test let binding as statement (body is the rest)
def double_let(n: Nat) -> Nat:
    let x: Nat = n
    return add_nat(x, x)

# Test exists in type position - using a simpler example
# This creates the type: exists m: Nat, True
def ExistsNat() -> Prop:
    return exists m: Nat, True
