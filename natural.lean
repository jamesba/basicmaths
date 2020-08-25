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
def add : natural → natural → natural
    | 0        := λ x, x
    | (succ n) := λ x, succ (add n x)

instance natural_has_add : has_add natural := ⟨add⟩


-- And prove some standard additive properties
@[simp, pattern]
lemma zero_add_ (x : natural): 0 + x = x := by refl

@[simp, pattern]
lemma add_zero_ (x : natural): x + 0 = x :=
    natural.rec_on x (
        show (0 : natural) + 0 = 0, by refl
    ) (
        assume n : natural,
        assume h : n + 0 = n,
        calc
            succ n + 0 = succ (n + 0)   :by refl
            ...        = succ n         :by rw h
    )

@[simp, pattern]
lemma one_add (x : natural): 1 + x = succ x := by refl

@[simp, pattern]
lemma add_one (x : natural): x + 1 = succ x :=
    natural.rec_on x (
        show 0 + 1 = succ 0, by refl
    ) (
        assume n : natural,
        assume h : n + 1 = succ n,
        calc
            (succ n) + 1 = succ (n + 1)  : by refl
            ...          = succ (succ n) : by rw h
    )

@[simp]
lemma add_asoc (x y z : natural): (x + y) + z = x + (y + z) :=
    natural.rec_on x (
        show ((0: natural) + y) + z = (0: natural) + (y + z), by refl
    ) (
        assume n : natural,
        assume h : (n + y) + z = n + (y + z),
        calc
            ((succ n) + y) + z = succ (n + y) + z     : by refl
            ...                = succ ((n + y) + z)   : by refl
            ...                = succ (n + (y + z))   : by rw h
            ...                = (succ n) + (y + z)   : by refl
    )

@[simp]
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
    | 0 := λ x, 0
    | (succ n) := λ x, (mult n x) + x

instance natural_has_mult : has_mul natural := ⟨mult⟩


-- And prove some useful results about multiplication
lemma zero_mult (x : natural): 0 * x = 0 := by refl

lemma mult_zero (x : natural): x * 0 = 0 :=
    natural.rec_on x (
        show (0 : natural) * 0 = 0, by refl
    ) (
        assume n : natural,
        assume h : n * 0 = 0,
        calc
            (succ n) * 0 = (n * 0) + 0   : by refl
            ...          = (n * 0)       : by rw add_zero_
            ...          = 0             : by rw h
    )

lemma one_mult (x : natural): 1 * x = x := by refl

lemma mult_one (x : natural): x * 1 = x :=
    natural.rec_on x (
        show (0 : natural) * 1 = 0, by refl
    ) (
        assume n : natural,
        assume h : n * 1 = n,
        calc
            (succ n) * 1 = (n * 1) + 1   : by refl
            ...          = n + 1         : by rw h
            ...          = succ n        : by rw add_one
    )

lemma add_dist_mult (x y z : natural): (x + y) * z = (x * z) + (y * z) :=
    natural.rec_on x (
        show (0 + y) * z = (0 * z) + (y * z), by refl
    ) (
        assume n : natural,
        assume h : (n + y) * z = (n * z) + (y * z),
        calc
            (succ n + y) * z = (succ (n + y)) * z         : by refl
            ...              = ((n + y) * z) + z          : by refl
            ...              = (n * z) + (y * z) + z      : by rw h
            ...              = (n * z) + ((y * z) + z)    : by rw add_asoc
            ...              = (n * z) + (z + (y * z))    : by rw [←add_com (y * z) z]
            ...              = ((n * z) + z) + (y * z)    : by rw add_asoc
            ...              = ((succ n) * z) + (y * z)   : by refl
    )

lemma mult_dist_add (x y z : natural): x * (y + z) = (x * y) + (x * z) :=
    natural.rec_on x (
        show 0 * (y + z) = (0 * y) + (0 * z), by refl
    ) (
        assume n : natural,
        assume h : n * (y + z) = (n * y) + (n * z),
        calc
            (succ n) * (y + z) = (n * (y + z)) + (y + z)           : by refl
            ...                = ((n * y) + (n * z)) + (y + z)     : by rw h
            ...                = (n * y) + ((n * z) + (y + z))     : by rw add_asoc
            ...                = (n * y) + (((n * z) + y) + z)     : by rw add_asoc
            ...                = (n * y) + ((y + (n * z)) + z)     : by rw [add_com (n * z) y]
            ...                = (n * y) + (y + ((n * z) + z))     : by rw add_asoc
            ...                = ((n * y) + y) + ((n * z) + z)     : by rw add_asoc
            ...                = ((succ n) * y) + ((succ n) * z)   : by refl
    )

lemma mult_asoc (x y z : natural): (x * y) * z = x * (y * z) :=
    natural.rec_on x (
        calc
            (0 * y) * z = 0 * z        : by rw zero_mult
            ...         = 0            : by rw zero_mult
            ...         = 0 * (y * z)  : by rw [zero_mult (y * z)]
    ) (
        assume n : natural,
        assume h : (n * y) * z = n * (y * z),
        calc
            (succ n * y) * z = (n * y + y) * z           : by refl
            ...              = ((n * y) * z) + (y * z)   : by rw add_dist_mult
            ...              = n * (y * z) + (y * z)     : by rw h
            ...              = (succ n) * (y * z)        : by refl
    )

lemma mult_com (x y : natural): x * y = y * x :=
    natural.rec_on x (
        calc
            0 * y = 0       : by rw zero_mult
            ...   = y * 0   : by rw mult_zero
    ) (
        assume n : natural,
        assume h : n * y = y * n,
        calc
            (succ n) * y = (n + 1) * y         : by rw add_one
            ...          = (n * y) + (1 * y)   : by rw add_dist_mult
            ...          = (n * y) + y         : by rw one_mult
            ...          = (y * n) + y         : by rw h
            ...          = (y * n) + (y * 1)   : by rw mult_one
            ...          = y * (n + 1)         : by rw mult_dist_add
            ...          = y * (succ n)        : by rw add_one
    )

-- equality is decidable
lemma succ_ne_zero (n : natural): (succ n) ≠ 0 :=
    assume h : succ n = 0,
    natural.no_confusion h

lemma zero_ne_succ (n : natural): 0 ≠ (succ n) :=
    assume h :  0 = succ n,
    natural.no_confusion h

@[reducible]
instance natural_decidable_eq: decidable_eq natural
| 0        0        := is_true (by refl)
| (succ x) 0        := is_false (succ_ne_zero x)
| 0        (succ y) := is_false (zero_ne_succ y)
| (succ x) (succ y) :=
    match natural_decidable_eq x y with
    | is_true hxeqy  := is_true (
        calc
            succ x = succ x  : by rw [eq.refl (succ x)]
            ...    = succ y  : by rw [hxeqy]
    )
    | is_false hxney := is_false (
        assume h: succ x = succ y,
        have x = y, by injection h,
        absurd ‹x = y› ‹x ≠ y›
    )
    end

-- inequalities
def le (x y : natural): Prop := ∃ z : natural, x + z = y
instance natural_has_le: has_le natural := ⟨le⟩

def lt (x y : natural): Prop := (x ≤ y) ∧ (x ≠ y)
instance natural_has_lt: has_lt natural := ⟨lt⟩

instance le_decidable: ∀ a b : natural, decidable (a ≤ b)
| 0        0        := is_true ⟨0, by refl⟩
| (succ x) 0        := is_false (
    assume ⟨c, (h : succ x + c = 0)⟩,
    have succ (x + c) = 0, from (
        calc
            succ (x + c) = (x + c) + 1  : by simp
            ...          = (x + 1) + c  : by rw add_rearrange
            ...          = (succ x) + c : by rw add_one
            ...          = 0            : by rw h
    ),
    absurd ‹succ (x + c) = 0› (succ_ne_zero (x + c))
)
| 0        (succ y) := is_true ⟨(succ y), by refl⟩
| (succ x) (succ y) :=
    match le_decidable x y with
        | is_true xley  := is_true (
            let ⟨z, (h : x + z = y)⟩ := xley in (
                ⟨z, calc
                    (succ x) + z = (x + 1) + z  : by rw add_one
                    ...          = x + z + 1    : by rw add_rearrange
                    ...          = y + 1        : by rw h
                    ...          = succ y       : by rw add_one
                ⟩
            )
        )
        | is_false xgty := is_false (
            assume ⟨z, (h : succ x + z = succ y)⟩,
            suffices x ≤ y, from absurd this xgty,
            ⟨z, (
                suffices succ (x + z) = succ y, by injection this,
                calc
                    succ (x + z) = (x + z) + 1  : by rw add_one
                    ...          = (x + 1) + z  : by rw add_rearrange
                    ...          = (succ x) + z : by rw add_one
                    ...          = succ y       : by rw h
            )⟩
        )
    end


-- subtraction, of a sort
def pred: natural → natural
| 0        := 0
| (succ a) := a

def sub:  natural → natural → natural
| 0 b        := 0
| a 0        := a
| a (succ b) := pred (sub a b)

instance natural_has_sub: has_sub natural := ⟨sub⟩

-- And essentially that's the natural numbers

end natural
