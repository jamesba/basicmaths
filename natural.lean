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
--   given propositions p and q and a proof h of p → q, (mt h) is a proof of ¬q → ¬p
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


-- equality is already defined for all types, and includes some of the properties we want for
-- peano's axioms, so I'll quickly prove them.
lemma eq_refl (n : natural): n = n := rfl
lemma eq_sym (x y : natural): x = y → y = x := eq.symm
lemma eq_trans (x y z : natural) (h1: x = y) (h2: y = z): (x = z) := eq.trans ‹x = y› ‹y = z›
-- Peano's 5th is implicit in how = is defined

lemma succ_inj {x y : natural}: x = y ↔ succ x = succ y :=
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

lemma zero_sum {x y : natural}: x + y = 0 → x = 0 :=
    match y with
    | 0 := assume h, show x=0, by rw [←add_zero_ x, h]
    | (a+1) := assume h, (
        have (x + a) + 1 = 0, by rw [add_asoc, h],
        absurd this (zero_not_succ (x+a))
    )
    end

lemma add_unchanged_implies_zero {x y : natural}: x + y = y → x = 0 :=
    natural.rec_on y (
        assume h : x + 0 = 0,
        show x = 0, by rw [←add_zero_ x, h]
    ) (
        assume a : natural,
        assume hr: x + a = a → x = 0,
        assume h: x + (a+1) = a+1,
        have (x + a)+1 = a+1, by rw [add_asoc x a 1, h],
        have x + a = a, from iff.elim_right succ_inj this,
        show x = 0, from hr this
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

-- This is needed to allow us to represent natural numbers sensibly
-- in messages. It's primarily a convenience for the programmer.
-- This is based on what's done for ℕ in the lean core library

def digit_char (n: natural) : char :=
if n = 0 then '0' else
if n = 1 then '1' else
if n = 2 then '2' else
if n = 3 then '3' else
if n = 4 then '4' else
if n = 5 then '5' else
if n = 6 then '6' else
if n = 7 then '7' else
if n = 8 then '8' else
if n = 9 then '9' else
if n = 0xa then 'a' else
if n = 0xb then 'b' else
if n = 0xc then 'c' else
if n = 0xd then 'd' else
if n = 0xe then 'e' else
if n = 0xf then 'f' else
'*'

def digit_succ (b : natural): list natural → list natural
| [] := [1]
| (d::ds) :=
    if (d+1) = b then
        0 :: digit_succ ds
    else
        (d+1) :: ds

def to_digits (b : natural): natural → list natural
| 0     := [0]
| (n+1) := digit_succ b (to_digits n)

def repr (n: natural): string :=
    ((to_digits 10 n).map digit_char).reverse.as_string

instance natural_has_repr: has_repr natural := ⟨repr⟩

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

instance lt_decidable: ∀ a b : natural, decidable (a < b) :=
assume a b,
match natural.natural_decidable_eq a b with
| is_true h  := is_false (assume :a < b, absurd h this.right)
| is_false h := (
    match natural.le_decidable a b with
    | is_true hle  := is_true ⟨hle, h⟩
    | is_false hle := is_false (assume :a < b, absurd this.left hle)
    end
)
end


lemma le_zero {x: natural}: x ≤ 0 → x = 0 :=
    match x with
    | 0     := assume h, by refl
    | (a+1) := (
        assume ⟨y, h⟩,
        suffices y + (a+1) ≠ 0, from absurd h this,
        calc
             y + (a+1) = (y + a) + 1 :by rw add_asoc
             ...       ≠ 0           :by apply succ_ne_zero
    )
    end

lemma zero_le (x:natural): 0 ≤ x :=
    match x with
    | 0 := ⟨0, by refl⟩
    | (a+1) := ⟨a+1, add_zero_ (a+1)⟩
    end

lemma le_refl (x: natural): x ≤ x := ⟨0, zero_add_ x⟩

lemma le_trans {x y z: natural}: x ≤ y → y ≤ z → x ≤ z :=
    assume ⟨a, _⟩,
    assume ⟨b, _⟩,
    ⟨b+a, show b + a + x = z, by rw [add_asoc, ‹a + x = y›, ‹b + y = z›]⟩

lemma lt_trans {x y z: natural}: x < y → y < z → x < z :=
    assume hxy: x < y,
    assume hyz: y < z,
    suffices x ≠ z, from ⟨le_trans hxy.left hyz.left, this⟩,
    assume h: x = z,
    suffices z = y, from absurd (eq.symm this) hyz.right,
    let ⟨a, (_: a+x=y)⟩ := hxy.left in (
        let ⟨b, (_: b+y=z)⟩ := hyz.left in (
            suffices b = 0, from (
                calc
                    z   = b + y  : by rw ‹b+y=z›
                    ... = 0 + y  : by rw this
                    ... = y      : by rw zero_add_
            ),
            suffices (b + a) = 0, from zero_sum this,
            suffices  x = (b + a) + x, from  add_unchanged_implies_zero (eq.symm this),
            calc
                x   = z            : by assumption
                ... = b + y        : by rw ‹b + y = z›
                ... = b + (a + x)  : by rw ‹a + x = y›
                ... = (b + a) + x  : by rw add_asoc
        )
    )

lemma le_sym_implies_eq {x y :natural}: x ≤ y → y ≤ x → x = y :=
    assume ⟨a, _⟩,
    assume ⟨b, _⟩,
    suffices a = 0, from (
    calc
        x          = 0 + x          : by rw zero_add_
        ...        = a + x          : by rw this
        ...        = y              : by rw [‹a + x = y›]
    ),
    suffices a + b = 0, from (zero_sum this),
    suffices (a + b) + x = x, from add_unchanged_implies_zero this,
    calc
        (a + b) + x = (b + a) + x   : by rw add_com a b
        ...         = b + (a + x)   : by rw add_asoc
        ...         = b + y         : by rw [‹a+x = y›]
        ...         = x             : by rw [‹b+y = x›]

lemma le_implies_not_succ {x y : natural}: x ≤ y → x ≠ y+1 :=
    assume h: x ≤ y,
    assume :x = y + 1,
    have y+1 ≤ y, from ‹x = y+1› ▸ ‹x ≤ y›,
    let ⟨z, (_: z + (y + 1) = y)⟩ := this in (
        have (z + 1) + y = y, by rw [add_com, ←add_asoc, add_com y, add_asoc, ‹z + (y+1) = y›],
        have z+1 = 0, from add_unchanged_implies_zero this,
        have z+1 ≠ 0, from succ_ne_zero z,
        absurd ‹z+1 = 0› ‹z+1 ≠ 0›
    )

lemma nz_implies_succ {x : natural}: x ≠ 0 → ∃ y: natural, x = y+1 :=
    match x with
    | 0     := assume :0 ≠ 0, absurd (eq.refl 0) this
    | n + 1 := assume :n + 1 ≠ 0, ⟨n, eq.refl (n+1)⟩
    end

lemma le_implies_lt_succ {x y: natural}: x ≤ y → x < y + 1 :=
    assume ⟨z, (h: z + x = y)⟩,
    suffices z + 1 + x = y + 1, from ⟨⟨z+1, this⟩, le_implies_not_succ ‹x ≤ y›⟩,
    suffices (z + x) + 1 = y + 1, by rw [add_asoc, add_com 1 x, ←add_asoc z x 1, this],
    show (z + x) + 1 = y + 1, from iff.elim_left succ_inj ‹z + x = y›

lemma lt_succ_implies_le {x y: natural}: x < y+1 → x ≤ y :=
    assume ⟨(hle: x ≤ y+1), hne⟩,
    let ⟨z, (h: z + x = y + 1)⟩ := hle in
        if hz: z = 0 then
            have x = y + 1, by rw [←zero_add_ x, ←hz, h],
            absurd this hne
        else
            let ⟨n, (_: z = n+1)⟩ := nz_implies_succ hz in (
                suffices n + x = y, from ⟨n, this⟩,
                suffices n + x + 1 = y + 1, from iff.elim_right succ_inj this,
                calc
                    n + x + 1 = (n + 1) + x   : by simp
                    ...       = y + 1         : by rwa ←‹z = n+1›
            )

lemma gt_implies_succ_gt {x y: natural}: x > y → x+1 > y :=
    assume ⟨(_: y ≤ x), (_: y ≠ x)⟩,
    if h: y = (x+1)
    then
        absurd ‹y = x+1› (le_implies_lt_succ ‹y ≤ x›).right
    else
        ⟨(le_implies_lt_succ ‹y ≤ x›).left, ‹y ≠ x + 1›⟩

lemma ne_succ (x: natural): x ≠ x+1 :=
    natural.rec_on x (
        assume h: 0 = 1,
        natural.no_confusion h
    ) (
        assume n: natural,
        assume h: n ≠ n + 1,
        assume : (n+1) = (n+1) + 1,
        have n = n + 1, from (iff.elim_right succ_inj) this,
        absurd ‹n = n +1› ‹n ≠ n + 1›
    )

lemma lt_implies_succ_le {x y: natural}: x < y → (x+1) ≤ y :=
    assume ⟨⟨z,(_:z+x=y)⟩,(_:x≠y)⟩,
    if h:z = 0 then
        have x = y, by rwa [←zero_add_ x, ←h],
        absurd ‹x = y› ‹x ≠ y›
    else
        let ⟨n, (_: z=n+1)⟩ := (nz_implies_succ h) in (
            have n + 1 + x = y, from ‹z=n+1› ▸ ‹z+x=y›,
            suffices n + (x + 1) = y, from ⟨n, this⟩,
            show n + (x + 1) = y, by rwa [add_com x, ←add_asoc n 1 x]
        )

lemma succ_gt (x : natural): (x+1) > x := ⟨⟨1, add_com 1 x⟩, ne_succ x⟩

lemma lt_succ (x : natural): x < (x+1) := succ_gt x

lemma le_iff_not_gt {x y: natural}: x ≤ y ↔ ¬ (x > y) :=
    iff.intro (
        assume : x≤y,
        assume ⟨(_:y ≤ x), (_: y ≠ x)⟩,
        suffices y = x, from absurd this ‹y≠x›,
        show y = x, from le_sym_implies_eq ‹y ≤ x› ‹x ≤ y›
    ) (
        natural.rec_on x (
            assume h: ¬(0 > y),
            show 0 ≤ y, from zero_le y
        ) (
            assume n: natural,
            assume h: (¬n > y → n ≤ y),
            assume :¬(n+1 > y),
            suffices (n+1)≤y, from (add_one n) ▸ this,
            have ¬n > y, from mt (gt_implies_succ_gt) this,
            have n ≤ y, from h this,
            have n ≠ y, from (
                assume :n = y,
                have n+1 > y, from this ▸ (succ_gt n),
                absurd this ‹¬n+1 > y›
            ),
            lt_implies_succ_le ⟨‹n ≤ y›, ‹n ≠ y›⟩
        )
    )


-- subtraction, of a sort
def pred: natural → natural
| 0       := 0
| (a + 1) := a

def sub:  natural → natural → natural
| a 0       := a
| a (b + 1) := pred (sub a b)

instance natural_has_sub: has_sub natural := ⟨sub⟩

lemma sub_zero (x: natural): x - 0 = x := by refl

lemma zero_sub (x: natural): 0 - x = 0 :=
    natural.rec_on x (
        by refl
    ) (
        assume n: natural,
        assume h: 0 - n = 0,
        calc
            0 - (n+1) = pred (0 - n)  : by refl
            ...       = pred 0        : by rw h
            ...       = 0             : by refl
    )

lemma succ_sub_one (x: natural): (x+1) - 1 = x :=
calc
    (x+1) - 1 = (x+1) - (0+1)     : by rw zero_add_
    ...       = pred ((x+1) - 0)  : by refl
    ...       = pred (x+1)        : by refl
    ...       = x                 : by refl

lemma pred_zero {x : natural}: pred x = 0 → x ≠ 0 → x = 1 :=
    assume h: pred x = 0,
    assume hz: x ≠ 0,
    if hh: x = 0 then
        absurd hh hz
    else
        let ⟨n, (_: x = n + 1)⟩ := nz_implies_succ hz in (
            calc
                x   = n + 1             : by assumption
                ... = (pred (n+1)) + 1  : by refl
                ... = (pred x) + 1      : by rw ‹x = n+1›
                ... = 0 + 1             : by rw h
                ... = 1                 : by rw zero_add_
        )

lemma succ_pred {x: natural}: x ≠ 0 → (pred x) + 1 = x :=
    assume h,
    let ⟨a, h⟩ := nz_implies_succ h in calc
        (pred x) + 1 = (pred (a+1)) + 1   : by rw h
        ...          = a + 1              : by refl
        ...          = x                  : by rw h

lemma pred_add {x y: natural}: x ≠ 0 → (pred x) + y = pred (x + y) :=
    assume h: x ≠ 0,
    let ⟨a, (h: x = a+1)⟩ := nz_implies_succ h in (
        calc
            pred x + y = pred (a+1) + y   : by rw h
            ...        = a + y            : by refl
            ...        = pred (a + y + 1) : by refl
            ...        = pred ((a+1) + y) : by simp
            ...        = pred (x + y)     : by rw h
    )

lemma eq_implies_le {x y: natural}: x = y → x ≤ y := assume h, ⟨0, h ▸ (zero_add_ x)⟩

lemma not_le {x y: natural}: ¬(x ≤ y) ↔ (y < x) :=
    iff.intro (
        natural.rec_on y (
            assume h,
            have x ≠ 0, from assume :x=0, absurd (eq_implies_le this) h,
            suffices 0 ≤ x, from ⟨this, ne.symm ‹x≠0›⟩,
            zero_le x
        ) (
            assume a: natural,
            assume hr: ¬x ≤ a → a < x,
            assume : ¬x ≤ a+1,
            have x ≠ a+1, from assume :x=a+1, absurd (eq_implies_le this) ‹¬x ≤ a+1›,
            suffices a+1 ≤ x, from ⟨this, ne.symm ‹x≠a+1›⟩,
            have x ≤ a → x ≤ a+1, from assume :x≤ a, (le_implies_lt_succ this).left,
            have a < x, from hr (mt ‹x ≤ a → x ≤ a+1› ‹¬(x ≤ a+1)›),
            lt_implies_succ_le ‹a < x›
        )
    ) (
        assume ⟨⟨a, (_: a+y=x)⟩, (_: y ≠ x)⟩,
        assume ⟨b, (_: b+x=y)⟩,
        suffices y=x, from absurd this ‹y≠x›,
        suffices b=0, by rw [←‹b+x=y›, this, zero_add_ x],
        suffices b+a=0, from zero_sum this,
        suffices y = b+a+y, from  add_unchanged_implies_zero (eq.symm this),
        calc
            y   = b+x     : by rw ‹b+x=y›
            ... = b+(a+y) : by rw ‹a+y=x›
            ... = b+a+y   : by rw add_asoc b a y
    )

lemma succ_le_implies_lt {x y: natural}:  (x+1) ≤ y → x < y :=
    assume ⟨z, (h: z + (x+1) = y)⟩,
    have (z + 1) + x = y, by rw [add_asoc z, add_com 1, h],
    suffices x ≠ y, from ⟨⟨(z+1), ‹(z + 1) + x = y›⟩, this⟩,
    assume hc: x = y,
    have y < x+1, from hc ▸ lt_succ x,
    absurd ‹x+1 ≤ y› (iff.elim_right not_le ‹y < x+1›)

lemma diff_zero_can_cancel {x y : natural}: x - y ≠ 0 → (x - y) + y = x :=
    natural.rec_on y (
        assume h: x ≠ 0,
        by refl
    ) (
        assume a: natural,
        assume hr: x - a ≠ 0 → x - a + a = x,
        assume h: x - (a+1) ≠ 0,
        have x - (a+1) = pred (x - a), by refl,
        if hxa: x - a = 0 then
            suffices x - (a+1) = 0, from absurd this h,
            calc
                x - (a+1)  = pred (x - a)  : by refl
                ...        = pred 0        : by rw hxa
                ...        = 0             : by refl
        else
            have hr: x - a + a = x, from hr hxa,
            calc
                x - (a+1) + (a+1) = (pred (x - a)) + (a + 1) : by refl
                ...               = (pred (x - a)) + (1 + a) : by rw add_com a
                ...               = (pred (x - a) + 1) + a   : by rw add_asoc
                ...               = x - a + a                : by rw succ_pred hxa
                ...               = x                        : by assumption
    )

lemma pred_nz {x: natural}: pred x ≠ 0 → x ≠ 0 :=
    assume h: pred x ≠ 0,
    assume hc: x = 0,
    suffices pred x = 0, from absurd this h,
    calc
        pred x = pred 0  : by rw hc
        ...    = 0       : by refl

lemma diff_nz_succ_sub {x y: natural}: x - y ≠ 0 → (x+1) - y = (x - y) + 1 :=
    natural.rec_on y (
        assume :x ≠ 0,
        by refl
    ) (
        assume b,
        assume hr: x - b ≠ 0 → x + 1 - b = x - b + 1,
        assume h: pred (x - b) ≠ 0,
        have h: x - b ≠ 0, from pred_nz h,
        have hr: (x+1) - b = (x - b) + 1, from hr h,
        calc
            (x+1) - (b+1) = pred ((x+1) - b)    : by refl
            ...           = pred ((x - b) + 1)  : by rw hr
            ...           = x - b               : by refl
            ...           = (pred (x - b)) + 1  : by rw succ_pred h
            ...           = (x - (b+1)) + 1     : by refl
    )

lemma diff_zero_of_successors {x y : natural}: (x+1) - (y+1) = 0 → x - y = 0 :=
    assume h: pred ((x+1) - y) = 0,
    if hxy: x - y = 0 then
        hxy
    else
        have hx1: (x+1) - y = (x - y) + 1, from diff_nz_succ_sub hxy,
        suffices pred ((x+1) - y) = x - y, from absurd h ((eq.symm this) ▸ hxy),
        calc
            pred ((x+1) - y) = pred ((x - y) + 1)  : by rw hx1
            ...              = x - y               : by refl

lemma both_diffs_zero_implies_equal {x : natural}: (∀ y : natural, x - y = 0 → y - x = 0 → x = y) :=
    natural.rec_on x (
        assume y: natural,
        assume h1: 0-y=0,
        assume h2: y=0,
        eq.symm h2
    ) (
        assume a: natural,
        assume hr: ∀ (y : natural), a - y = 0 → y - a = 0 → a = y,
        assume y: natural,
        assume h1: (a+1) - y = 0,
        assume h2: y - (a+1) = 0,
        if hyz: y = 0 then
            suffices a+1 = 0, from absurd this (succ_ne_zero a),
            calc
                a+1 = (a+1) - 0   : by refl
                ... = (a+1) - y   : by rw hyz
                ... = 0           : by rw h1
        else
            let ⟨b, (_:y=b+1)⟩ := nz_implies_succ hyz in (
                suffices (a+1) = (b+1), from (eq.symm ‹y=b+1›) ▸ this,
                suffices a = b, from congr_arg succ this,
                have h1: (a+1) - (b+1) = 0, from ‹y=b+1› ▸ h1,
                have h2: (b+1) - (a+1) = 0, from ‹y=b+1› ▸ h2,
                have h1: a - b = 0, from diff_zero_of_successors h1,
                have h2: b - a = 0, from diff_zero_of_successors h2,
                hr b h1 h2
            )
    )

lemma diff_zero {x y : natural}: x - y = 0 → x ≤ y :=
    assume h: x - y = 0,
    if hi: y - x = 0 then
        have x = y, from both_diffs_zero_implies_equal y h hi,
        eq_implies_le ‹x = y›
    else
        suffices (y - x) + x = y, from ⟨y-x, this⟩,
        diff_zero_can_cancel hi


lemma lt_sub_nz {x y: natural}: x < y → y - x ≠ 0 :=
    assume h: x < y,
    assume hc: y - x = 0,
    suffices y ≤ x, from absurd this (iff.elim_right not_le h),
    diff_zero hc


lemma sub_cancel_same {x y : natural}: y ≤ x → (x-y)+y = x :=
    natural.rec_on y (
        assume h: 0 ≤ x,
        by refl
    ) (
        assume n: natural,
        assume hr: n ≤ x → x - n + n = x,
        assume h: n+1 ≤ x,
        have x≠0, from assume :x=0,
            have n+1=0, from le_zero (‹x=0› ▸ h),
            absurd ‹n+1=0› (succ_ne_zero n),
        have n < x, from succ_le_implies_lt h,
        calc
            (x - (n+1)) + (n+1) = (x - (n+1) + n) + 1       : by refl
            ...                 = ((pred (x - n)) + n) + 1  : by refl
            ...                 = (pred ((x - n) + n)) + 1  : by rw pred_add (lt_sub_nz ‹n<x›)
            ...                 = (pred x) + 1              : by rw hr ‹n<x›.left
            ...                 = x                         : by rw succ_pred ‹x≠0›
    )

lemma lt_anti_sym {x y: natural}: x < y ↔ y > x :=
    iff.intro (assume ⟨h,g⟩, ⟨h,g⟩) (assume ⟨h,g⟩, ⟨h,g⟩)

lemma succ_sub {x y: natural}: y ≤ x → (x+1) - y = (x - y) + 1 :=
    natural.rec_on y (
        assume h,
        show (x+1) - 0 = x + 1, by refl
    ) (
        assume a: natural,
        assume h: a ≤ x → (x + 1) - a = (x - a) + 1,
        assume ⟨z,(_:z + (a+1) = x)⟩,
        have a ≤ x, from ⟨z+1, by rwa [add_asoc, add_com 1]⟩,
        have ¬ a > x, from (iff.elim_left le_iff_not_gt) ‹a ≤ x›,
        have ¬ x < a, from mt (iff.elim_left lt_anti_sym) ‹¬a > x›,
        have x ≠ a, from (
            assume :x = a,
            suffices z+1 = 0, from absurd this (succ_ne_zero z),
            suffices (z+1) + a = a, from add_unchanged_implies_zero this,
            calc
                (z+1) + a = z + (1+a)  : by rw add_asoc
                ...       = z + (a+1)  : by rw add_com 1
                ...       = x          : by assumption
                ...       = a          : by assumption
        ),
        have ¬ x ≤ a, from (
            assume :x ≤ a,
            suffices x < a, from absurd this ‹¬x < a›,
            ⟨‹x ≤ a›, ‹x ≠ a›⟩
        ),
        have x - a ≠ 0, from (mt diff_zero) ‹¬x ≤ a›,
        have h: (x + 1) - a = (x - a) + 1, from h ‹a ≤ x›,
        have (x + 1) - (a + 1) = x - a, from
        (
            calc
                (x + 1) - (a + 1) = pred ((x+1) - a)    : by refl
                ...               = pred ((x - a) + 1)  : by rw h
                ...               = x - a               : by refl
        ),
        suffices (x - (a + 1)) + 1 = x - a, from (eq.symm this) ▸ ‹(x + 1) - (a + 1) = x - a›,
        calc
            (x - (a + 1)) + 1 = pred(x - a) + 1   : by refl
            ...               = x - a             : by rw (succ_pred ‹x-a ≠ 0›)
    )

lemma sub_self_zero (x: natural): x - x = 0 :=
    natural.rec_on x (
        by refl
    ) (
        assume n: natural,
        assume h: n - n = 0,
        have n ≤ n, from le_refl n,
        calc
            (n+1) - (n+1) = pred ((n+1) - n)   : by refl
            ...           = pred ((n - n) + 1) : by rw (succ_sub ‹n ≤ n›)
            ...           = pred (0 + 1)       : by rw h
            ...           = pred 1             : by rw zero_add_
            ...           = 0                  : by refl
    )

lemma le_sub_zero {x y: natural}: x ≤ y → x - y = 0 :=
    natural.rec_on y (
        assume h,
        have x - 0 = x, by refl,
        suffices x = 0, from ‹x = 0› ▸ ‹x-0=x›,
        le_zero h
    ) (
        assume n: natural,
        assume hr: x ≤ n → x - n = 0,
        assume h: x ≤ n+1,
        if hh: x=n+1 then
            have (n+1) - (n+1) = 0, from sub_self_zero (n+1),
            show x - (n+1) = 0, from (eq.symm hh) ▸ this
        else
            have h: x ≤ n, from lt_succ_implies_le ⟨h, hh⟩,
            have hr: x - n = 0, from hr h,
            calc
                x - (n+1) = pred (x - n)   : by refl
                ...       = pred 0         : by rw hr
                ...       = 0              : by refl
    )

lemma diff_nz {x y : natural}: x - y ≠ 0 → y < x :=
    assume h: x - y ≠ 0,
    if hle: x ≤ y then
        absurd (le_sub_zero hle) h
    else
        iff.elim_left not_le hle

lemma succ_sub_self_one (x : natural): (x+1) - x = 1 :=
    calc
        (x+1) - x = (x - x) + 1  : by rw succ_sub (eq_implies_le (eq.refl x))
        ...       = 0 + 1        : by rw sub_self_zero
        ...       = 1            : by rw zero_add_

lemma sub_nz_implies_anti_sum_zero {x y : natural}: x - y ≠ 0 → y - x = 0 :=
    assume h: x - y ≠ 0,
    le_sub_zero (diff_nz h).left

lemma le_implies_le_sum {x y z: natural}: x ≤ y → x ≤ z + y :=
    assume ⟨a, (h: a+x = y)⟩,
    suffices z+a+x = z + y, from ⟨z+a, this⟩,
    calc
        z + a + x = z + (a + x)  : by rw add_asoc
        ...       = z + y        : by rw h

lemma add_sub_asoc {x y z : natural}: natural.sub z y = 0 → x + (y - z) = (x + y) - z :=
    assume h: z - y = 0,
    natural.rec_on x (
        calc
            0 + (y - z) = y - z       : by rw zero_add_
            ...         = (0 + y) - z : by rw zero_add_
    ) (
        assume a: natural,
        assume hr: a + (y-z) = (a+y) - z,
        have z ≤ y, from diff_zero h,
        have z ≤ a+y, from le_implies_le_sum ‹z ≤ y›,
        calc
            (a+1) + (y-z) = (a + (y-z)) + 1  : by simp
            ...           = ((a+y) - z) + 1  : by rw hr
            ...           = ((a+y)+1) - z    : by rw succ_sub ‹z ≤ a+y›
            ...           = ((a+1)+y) - z    : by simp
    )

lemma add_cancel_right {x y z : natural}: x + y = z + y → x = z :=
    natural.rec_on y (
        assume h, by assumption
    ) (
        assume b: natural,
        assume hr: x + b = z + b → x = z,
        assume h: x + (b+1) = z + (b+1),
        have h: (x + b) + 1 = (z + b) + 1, by rw [add_asoc x b 1, h, ←add_asoc z b 1],
        have h: x + b = z + b, from iff.elim_right succ_inj h,
        show x = z, from hr h
    )

lemma add_cancel_left {x y z: natural}: x + y = x + z → y = z :=
    assume h: x + y = x + z,
    have h: y + x = z + x, by rw [←add_com x y, h, add_com x z],
    show y = z, from add_cancel_right h

lemma le_add_cancel_left {x y z: natural}:  x + y ≤ x + z ↔ y ≤ z :=
    iff.intro (
        assume ⟨a, (h: a + (x + y) = x + z)⟩,
        suffices a+y = z, from ⟨a, this⟩,
        suffices a+y+x = z+x, from add_cancel_right this,
        show a + y + x = z + x, by rw [add_asoc, ←add_com x y, h, add_com x z]
    ) (
        assume ⟨a, (h: a + y = z)⟩,
        suffices a + (x + y) = (x + z), from ⟨a, this⟩,
        show a + (x + y) = x + z, by rw [add_com x y, ←add_asoc a y x, h, add_com z x]
    )

lemma le_add_cancel_right {x y z: natural}:  x + y ≤ z + y ↔ x ≤ z :=
    iff.intro (
        assume h: x + y ≤ z + y,
        have h: y + x ≤ y + z, from (add_com z y) ▸ (add_com x y) ▸ h,
        iff.elim_left le_add_cancel_left h
    ) (
        assume h: x ≤ z,
        (add_com y z) ▸ (add_com y x) ▸ (iff.elim_right le_add_cancel_left h)
    )

lemma lt_add_cancel_left {x y z: natural}:  x + y < x + z ↔ y < z :=
    iff.intro (
        assume h: x + y < x + z,
        suffices y ≠ z, from ⟨iff.elim_left le_add_cancel_left h.left, this⟩,
        assume hc: y = z,
        suffices x + y = x + z, from absurd this h.right,
        show x + y = x + z, by rw hc
    ) (
        assume h: y < z,
        suffices x + y ≠ x + z, from ⟨iff.elim_right le_add_cancel_left h.left, this⟩,
        assume hc: x + y = x + z,
        suffices y = z, from absurd this h.right,
        add_cancel_left hc
    )

lemma lt_add_cancel_right {x y z: natural}:  x + y < z + y ↔ x < z :=
    iff.intro (
        assume h: x + y < z + y,
        have h: y + x < y + z, from (add_com z y) ▸ (add_com x y) ▸ h,
        iff.elim_left lt_add_cancel_left h
    ) (
        assume h: x < z,
        (add_com y z) ▸ (add_com y x) ▸ (iff.elim_right lt_add_cancel_left h)
    )

lemma sub_cancel_right (x y z: natural): (x+z) - (y+z) = x - y :=
    if hxy: x - y = 0 then
        have h: x ≤ y, from diff_zero hxy,
        have h: x+z ≤ y+z, from iff.elim_right le_add_cancel_right h,
        show (x+z) - (y+z) = x - y, by rw [le_sub_zero h, hxy]
    else
        natural.rec_on z (
            by refl
        ) (
            assume c: natural,
            assume hr: (x + c) - (y + c) = x - y,
            have y < x, from diff_nz hxy,
            have y+c < x+c, from iff.elim_right lt_add_cancel_right ‹y < x›,
            have (x+c) - (y+c) ≠ 0, from lt_sub_nz ‹y+c < x+c›,
            calc
                (x + (c+1)) - (y + (c+1)) = ((x+c) + 1) - ((y+c) + 1)   : by refl
                ...                       = pred (((x+c) + 1) - (y+c))  : by refl
                ...                       = pred (((x+c) - (y+c)) + 1)  : by rw diff_nz_succ_sub ‹(x+c)-(y+c)≠0›
                ...                       = (x+c) - (y+c)               : by refl
                ...                       = x - y                       : by assumption
        )

lemma sub_of_sub (x y z: natural): (x-y)-z = x-(y+z) :=
    natural.rec_on z (
        by refl
    ) (
        assume c: natural,
        assume hr: x - y - c = x - (y + c),
        calc
            (x - y) - (c+1) = pred ((x - y) - c)  : by refl
            ...             = pred (x - (y + c))  : by rw hr
            ...             = x - (y+c+1)         : by refl
    )


lemma mult_nz {x y: natural}: x≠0 → y≠0 → (x*y)≠0 :=
    natural.rec_on y (
        assume hx,
        assume hy,
        absurd (eq.refl 0) hy
    ) (
        assume b: natural,
        assume hr: x ≠ 0 → b ≠ 0 → x * b ≠ 0,
        assume hx: x ≠ 0,
        assume hy: b+1 ≠ 0,
        assume hc: x*(b+1) = 0,
        absurd (zero_sum hc) hx
    )

-- And essentially that's the natural numbers

end natural
