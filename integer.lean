import .natural

inductive integer: Type
| zero : integer
| pos_succ : natural → integer
| neg_succ : natural → integer

namespace integer

open integer

def succ : integer → integer
| zero := pos_succ natural.zero
| (pos_succ n) := pos_succ (natural.succ n)
| (neg_succ n) := natural.rec_on n (
    zero
) (
    assume m : natural, -- n = natural.succ m
    assume prev : integer, -- prev = succ (neg_succ m)
    neg_succ m
)

def pred : integer → integer
| zero := neg_succ natural.zero
| (neg_succ n) := neg_succ (natural.succ n)
| (pos_succ n) := natural.rec_on n (
    zero
) (
    assume m : natural, -- n = natural.succ m
    assume prev : integer, -- prev = succ (pos_succ m)
    pos_succ m
)

instance integer_has_zero: has_zero integer := ⟨zero⟩
instance integer_has_one: has_one integer := ⟨succ zero⟩

def add: integer → integer → integer
| 0            y            := y
| x            0            := x
| (pos_succ n) (pos_succ m) := pos_succ (n + m + 1)
| (pos_succ n) (neg_succ m) := if h: n ≤ m then (
    succ (neg_succ (m - n))
) else (
    pred (pos_succ (n - m))
)
| (neg_succ n) (pos_succ m) := if n ≤ m then (
    pred (pos_succ (m - n))
) else (
    succ (neg_succ (n - m))
)
| (neg_succ n) (neg_succ m) := neg_succ (n + m + 1)

instance integer_has_add: has_add integer := ⟨add⟩

def neg: integer → integer
| 0            := 0
| (pos_succ a) := neg_succ a
| (neg_succ a) := pos_succ a

instance integer_has_neg: has_neg integer := ⟨neg⟩

def sub : integer → integer → integer :=
    λ x y, x + (-y)

instance integer_has_sub: has_sub integer := ⟨sub⟩

end integer