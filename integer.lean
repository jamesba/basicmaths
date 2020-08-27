import .natural


-- So having constructed the natural numbers I'm now going to construct the integers
-- I'm not sure if this is the best way to construct them, I've considered an
-- asynmmetric embedding, and even a single embedding of the naturals, but this
-- seems to work
inductive integer: Type
| zero : integer
| pos_succ : natural → integer
| neg_succ : natural → integer

namespace integer

open integer

-- The successor, which is similar to the natural successor
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

-- The predecessor
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

-- Addition, defined using natural addition and subtraction
def add: integer → integer → integer
| x 0            := x
| x (pos_succ n) :=
    match x with
    | 0 := pos_succ n
    | (pos_succ m) := pred (pos_succ (m + n))
    | (neg_succ m) := _
    end
| x (neg_succ n) := _

instance integer_has_add: has_add integer := ⟨add⟩

-- negation is very simple
def neg: integer → integer
| 0            := 0
| (pos_succ a) := neg_succ a
| (neg_succ a) := pos_succ a

instance integer_has_neg: has_neg integer := ⟨neg⟩

-- And that makes subtraction even simpler
def sub (x y : integer): integer := x + (-y)

instance integer_has_sub: has_sub integer := ⟨sub⟩


-- Which brings us to multiplication
def mult: integer → integer → integer
| x 0 := 0
| 0 y := 0
| (pos_succ a) (pos_succ b) := pos_succ (a*b + a + b)
| (pos_succ a) (neg_succ b) := neg_succ (a*b + a + b)
| (neg_succ a) (pos_succ b) := neg_succ (a*b + a + b)
| (neg_succ a) (neg_succ b) := pos_succ (a*b + a + b)

instance integer_has_mul: has_mul integer := ⟨mult⟩

end integer