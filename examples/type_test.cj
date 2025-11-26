import Std.Pointer
import Std.Vec
import Std.Nat

class MyList(A: Type):
    nil
    cons(head: A, tail: MyList(A))

def length(A: Type, l: MyList(A)) -> Std.Nat.Nat:
    match l:
        case nil:
            return Std.Nat.zero
        case cons(h, t):
            return Std.Nat.succ(length(A, t))

def safe_head(A: Type, l: MyList(A)) -> Std.Pointer.Pointer(A):
    match l:
        case nil:
            return Std.Pointer.Nullpointer(A)
        case cons(h, t):
            return Std.Pointer.Some(A, h)

def vec_zero() -> Std.Vec.Vec(Std.Nat.Nat, Std.Nat.zero):
    return Std.Vec.vnil(Std.Nat.Nat)

def dep_id(A: Type, x: A) -> A:
    return x

def pos_nat(n: { x: Std.Nat.Nat | Std.Nat.le(Std.Nat.succ(Std.Nat.zero), x) }) -> Std.Nat.Nat:
    return n.value
