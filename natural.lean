-- This is an example of how to construct the natural numbers in lean,
-- and how to build up results on them from the most basic of logical
-- postulates.
--
-- As part of lean's built in logic engine I have access to the following
-- operations and axioms:
--
-- Propositions:
--   any proposition has type Prop,
--   any proposiyion p is itself a type
--   a member of the type p is a proof of p
--
-- Implication:
--   given propositions p and q, (p → q) is also a proposition
--   given a proof hp: p, and a proof hpq: p → q then (hpq hp) is a proof
--   of q
--
-- Or:
--   given propositions p,q, (p ∨ q) is also a proposition
--   given a proof hp of p, (or.intro_left q hp) is a proof of (p ∨ q)
--   given a proof hq of q, (or.intro_right p hq) is a proof of (p ∨ q)
--   given a proof hpq of (p ∨ q), a proof hpr of (p → r) and a proof hqr
--     of (q → r) then (or.elim hpq hpr hqr) is a proof of ((p ∨ q) → r)
--
-- And:
--   given propositions p,q, (p ∧ q) is also a proposition
--   given a proof hp of p, and a proof hq or q, (and.intro hp hq) is a proof
--     of (p ∧ q)
--   given a proof hpq of (p ∧ q), (and.elim_left hpq) is a proof of p
--   given a proof hpq of (p ∧ q), (and.elim_right hpq) is a proof of q
--
-- Not:
--   given a proposition p, ¬p is shorthand for the proposition (p → false)
--   given a proof hp of p and a proof hnp of ¬p, (absurd hp hnp) is a proof of any proposition
--
-- Exists:
--   given a type α, and a function p: α → Prop, (∃ x : α, p x) is a proposition
--   given an entity x of type α and a proof hpx of p x, ⟨x, hpx⟩ is a proof of
--     (∃ x : α, p x)
--   given a proof hxp of (∃ x : α, p x) we can bind hxp to get x:α and a proof of p x
--
-- Forall:
--   given a type α and a function p: α → Prop, (∀ x : α, p x) is a proposition
--   a proof of (∀ x : α, p x) is a function hxpx: (α → p x) (ie. a function that
--     maps any element x of α to a proof of p x)
--
-- Assume:
--   given propositions p, q, (assume hp:p, hq) is a proof of p → q provided that hq is a
--     proof of q, which may include references to hp in its definition.
--
-- inductive:
--   We can define a type inductively by definining a number of specific constructors that
--     may or may not themselves take parameters. Any instance of the type must have been
--     constructed using one of the constructors, and if the comnstructor takes parameters
--     then the unique combination of constructor and parameter values is considered to define
--     the element
--   All inductive constructors are injective, so given a proof h: con x = con y we then
--     injection h is a proof that x = y
--   Given any inductive type α and a proof h that two elements constructed using different
--     constructors are equal (α.no_confusion h) is a proof of false
--
-- rec_on:
--   given any inductive type α we may use the function α.rec_on which takes a number of
--     parameters one greater than the number of constructors α has. The first parameter
--     is of type α, the remaining are each of the same type as the constructor they correspond
--     to in order (eg. if a constructor takes no pareters then its corresponding parameter here
--     is of type α, whilst if it takes one then it is a function returnimng α, etc ...)
--     the value of a call to rec_on is then the same as a call to the parameter corresponding to
--     the constructor that constructed the input value with the same parameters as were passed
--     to the constructor.
--
-- equality:
--   for any type α the operator = is already defined, and (a = b) is a proposition.axioms
--   for any type α and any element x : α, rfl is a proof of (x = x).
--   for any type α and any elements x, y: α, eq.sym is a proof of (x = y → y = x)
--   for any type α, elements x y : α, and function p : α → Prop if hxy is a proof that x = y,
--     and hpx is a proof of p x then (eq.subst hxy hpx) is a proof of p y
--   for any type α, elements x y : α, and function p : α → Prop if hxy is a proof that x = y,
--     then (congr.arg p hxy) is a proof that (p x = p y)


-- We begin by defining a new type, natural. (nat is the builtin type, so we want a different
-- name)
inductive natural : Type
| zero : natural
| succ : natural → natural

namespace natural

open natural

instance natural_has_zero : has_zero natural := ⟨zero⟩
instance natural_has_one : has_one natural := ⟨succ zero⟩

-- euqality is already defined for all types, and includes some of the properties we want for
-- peano's axioms, so I'll quickly prove them.
lemma eq_refl (n : natural): n = n := rfl
lemma eq_sym (x y : natural): x = y → y = x := eq.symm
lemma eq_trans (x y z : natural) (h1: x = y) (h2: y = z): (x = z) := eq.trans ‹x = y› ‹y = z›
-- Peano's 5th is implicit in how = is defined

lemma succ_inj (x y : natural): x = y ↔ succ x = succ y :=
    iff.intro (
        assume :x = y,
        congr_arg succ ‹x = y›
    ) (
        assume h: succ x = succ y,
        show x = y, by injection h
    )

lemma zero_not_succ  (x : natural):  (succ x ≠ 0) :=
    assume h,
    natural.no_confusion h


-- Now we define addition
-- I originally defined addition the other way round with the first
-- parameter as 0 or succ a, but this is unfortunate. If you do it
-- this way round then (a + 1) = a + succ 0 = succ a + 0 = succ a is
-- definitional, and so can be used in unfolding future definitions
def add : natural → natural → natural
    | a  0        := a
    | a  (succ b) := succ (add a b)

instance natural_has_add : has_add natural := ⟨add⟩

-- And prove some standard additive properties
lemma zero_add_ (x : natural): 0 + x = x :=
    natural.rec_on x (
        show (0 : natural) + 0 = 0, by refl
    ) (
        assume n: natural,
        assume h: 0 + n = n,
        calc
            0 + succ n = succ (0 + n) : by refl
            ...        = succ n       : by rw h
    )
lemma add_zero_ (x : natural): x + 0 = x := by refl

lemma one_add (x : natural): 1 + x = succ x :=
    natural.rec_on x (
        show 1 + 0 = succ 0, by refl
    ) (
        assume n : natural,
        assume h : 1 + n = succ n,
        calc
            1 + (succ n) = succ (1 + n)  : by refl
            ...          = succ (succ n) : by rw h
    )
lemma add_one (x : natural): x + 1 = succ x := by refl

lemma add_asoc (x y z : natural): (x + y) + z = x + (y + z) :=
    natural.rec_on z (
        show (x + y) + 0 = x + (y + 0), by refl
    ) (
        assume n : natural,
        assume h : (x + y) + n = x + (y + n),
        calc
            (x + y) + succ n = succ ((x + y) + n)   : by refl
            ...              = succ (x + (y + n))   : by rw h
            ...              = x + succ (y + n)     : by refl
    )
lemma add_com (x y : natural): x + y = y + x :=
    natural.rec_on y (
        show x + 0 = 0 + x, by rwa [add_zero_, zero_add_]
    ) (
        assume n: natural,
        assume h : x + n = n + x,
        calc
            x + succ n = x + (n + 1)    : by rw add_one
            ...        = (x + n) + 1    : by rw add_asoc
            ...        = (n + x) + 1    : by rw h
            ...        = n + (x + 1)    : by rw add_asoc
            ...        = n + (1 + x)    : by rw [add_one, one_add]
            ...        = (n + 1) + x    : by rw add_asoc
            ...        = (succ n) + x   : by rw add_one
    )

@[simp]
lemma add_rearrange (x y z : natural): (x + y) + z = (x + z) + y := (
    calc
        (x + y) + z = x + (y + z)   : by rw add_asoc
        ...         = x + (z + y)   : by rw add_com y
        ...         = (x + z) + y   : by rw add_asoc
)



-- Now define multiplication
def mult : natural → natural → natural
    | a 0       := 0
    | a (b + 1) := a + (mult a b)

instance natural_has_mult : has_mul natural := ⟨mult⟩


-- And prove some useful results about multiplication
lemma mult_zero (x : natural): x * 0 = 0 := by refl

lemma zero_mult (x : natural): 0 * x = 0 :=
    natural.rec_on x (
        show (0 : natural) * 0 = 0, by refl
    ) (
        assume n : natural,
        assume h : 0 * n = 0,
        calc
            0 * (n + 1) = 0 + 0 * n : by refl
            ...         = 0 + 0     : by rw h
            ...         = 0         : by refl
    )


lemma mult_one (x : natural): x * 1 = x := by refl

lemma one_mult (x : natural): 1 * x = x :=
    natural.rec_on x (
        show (1 : natural) * 0 = 0, by refl
    ) (
        assume n : natural,
        assume h : 1 * n = n,
        calc
            1 * (n + 1) = 1 + (1 * n)  : by refl
            ...         = 1 + n        : by rw h
            ...         = n + 1        : by rw add_com
    )

lemma add_dist_mult (x y z : natural): (x + y) * z = (x * z) + (y * z) :=
    natural.rec_on z (
        show (x + y) * 0 = (x * 0) + (y * 0), by refl
    ) (
        assume n: natural,
        assume h: (x + y) * n = (x * n) + (y * n),
        calc
            (x + y) * (n + 1) = (x + y) + ((x + y) * n)        : by refl
            ...               = (x + y) + ((x * n) + (y * n))  : by rw h
            ...               = (x + (x * n)) + (y + (y * n))  : by rw [←add_asoc (x + y) (x * n), add_asoc x y, add_com y (x * n), ←add_asoc, add_asoc]
    )

lemma mult_dist_add (x y z : natural): x * (y + z) = (x * y) + (x * z) :=
    natural.rec_on z (
        show x * (y + 0) = (x * y) + (x * 0), by refl
    ) (
        assume n: natural,
        assume h: x * (y + n) = (x * y) + (x * n),
        calc
            x * (y + (n + 1)) = x * ((y + n) + 1)        : by rw add_asoc
            ...               = x + (x * (y + n))        : by refl
            ...               = (x * y) + x + (x * n)    : by rw [h, ←add_asoc, add_com (x*y)]
            ...               = (x * y) + (x + (x * n))  : by rw add_asoc
            ...               = (x * y) + (x * (n + 1))  : by refl
    )

lemma mult_asoc (x y z : natural): (x * y) * z = x * (y * z) :=
    natural.rec_on z (
        calc
            (x * y) * 0 = x * (y * 0)  : by refl
    ) (
        assume n: natural,
        assume h: (x * y) * n = x * (y * n),
        calc
            (x * y) * (n + 1) = (x * y) + ((x * y) * n)    : by refl
            ...               = x * (y + (y * n))          : by rw [h, mult_dist_add]
            ...               = x * (y * (n + 1))          : by refl
    )

lemma mult_com (x y : natural): x * y = y * x :=
    natural.rec_on x (
        show 0 * y = y * 0, by rw [zero_mult, mult_zero]
    ) (
        assume n : natural,
        assume h : n * y = y * n,
        calc
            (n + 1) * y = (y * n) + (y * 1)   : by rw [add_dist_mult, one_mult, h, mult_one]
            ...         = y * (n + 1)         : by rw mult_dist_add
    )

-- equality is decidable
lemma succ_ne_zero (n : natural): (n + 1) ≠ 0 :=
    assume h : succ n = 0,
    natural.no_confusion h

lemma zero_ne_succ (n : natural): 0 ≠ (n + 1) :=
    assume h :  0 = succ n,
    natural.no_confusion h

@[reducible]
instance natural_decidable_eq: decidable_eq natural
| 0       0       := is_true (by refl)
| (x + 1) 0       := is_false (succ_ne_zero x)
| 0       (y + 1) := is_false (zero_ne_succ y)
| (x + 1) (y + 1) :=
    match natural_decidable_eq x y with
    | is_true h  := is_true (by rw h)
    | is_false _ := is_false (assume h: succ x = succ y, have x = y, by injection h, absurd ‹x = y› ‹x ≠ y›)
    end

-- inequalities
def le (x y : natural): Prop := ∃ z : natural, z + x = y
instance natural_has_le: has_le natural := ⟨le⟩

def lt (x y : natural): Prop := (x ≤ y) ∧ (x ≠ y)
instance natural_has_lt: has_lt natural := ⟨lt⟩

lemma succ_le_succ {x y : natural}: x ≤ y → (x + 1) ≤ (y + 1) :=
    assume ⟨z, (h: z + x = y)⟩,
    suffices z + (x + 1) = y + 1, from ⟨z, this⟩,
    show z + (x + 1) = y + 1, by rw [←add_asoc z x 1, h]

instance le_decidable: ∀ a b : natural, decidable (a ≤ b)
| 0       y        := is_true ⟨y, by refl⟩
| (x + 1) 0        := is_false (
    assume ⟨z, h⟩,
    have (z + x) + 1 = 0, by rw [add_asoc, h],
    have (z + x) + 1 ≠ 0, from succ_ne_zero (z + x),
    absurd ‹(z + x) + 1 = 0› ‹(z + x) + 1 ≠ 0›
)
|  (x+1) (y+1)    :=
    match le_decidable x y with
        | is_true xley := is_true (succ_le_succ xley)
        | is_false xgty := is_false (
            assume ⟨z, (h: z + x + 1 = y + 1)⟩,
            have x ≤ y, from ⟨z, by injection h⟩,
            absurd ‹x ≤ y› xgty
        )
    end


-- subtraction, of a sort
def pred: natural → natural
| 0       := 0
| (a + 1) := a

def sub:  natural → natural → natural
| a 0       := a
| a (b + 1) := pred (sub a b)

instance natural_has_sub: has_sub natural := ⟨sub⟩

-- And essentially that's the natural numbers

end natural
