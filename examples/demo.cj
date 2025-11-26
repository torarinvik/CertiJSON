import Std.Nat

def add_one(n: Nat) -> Nat:
    one: Nat = succ(zero)
    return add_nat(n, one)
