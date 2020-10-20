import .group

universe u

-- A ring is a standard construction in algebra, almost as fundemental as a group
--
-- Of course the lean standard library includes Rings, but I choose to create my own
-- probably because I'm bloody minded like that

def LeftDistrib {α: Type} (add: α → α → α) (mul: α → α → α) := ∀ a b c : α, mul c (add a b) = add (mul c a) (mul c b)
def RightDistrib {α: Type} (add: α → α → α) (mul: α → α → α) := ∀ a b c : α, mul (add a b) c = add (mul a c) (mul b c)
def NoZeroDivisors (α: Type) [has_add α] [has_mul α] [has_zero α] := ∀ a b : α, a * b = 0 → a ≠ 0 → b = 0
def NonZero (α: Type) [has_zero α]: Type := {a: α // a ≠ 0}
def ExcludedMiddle (α: Type) := ∀ a b : α, a = b ∨ a ≠ b

postfix `ˣ`:1025 := NonZero

def NZLeftInverse {α: Type} (zero: α) (one: α) (mul: α → α → α) (inv : α → α) := ∀ a : α, (a ≠ zero → mul (inv a) a = one)

class Ring (α: Type) extends has_zero α, has_add α, has_neg α, has_mul α:=
(is_set: ExcludedMiddle α)
(add_assoc: Associative add)
(add_comm: Commutative add)
(left_zero: LeftIdentity add 0)
(left_neg: LeftInverse add 0 neg)
(mul_assoc: Associative mul)
(left_distrib: LeftDistrib add mul)
(right_distrib: RightDistrib add mul)

instance RingHasSub {α: Type} [r: Ring α]: has_sub α := ⟨λ a b : α, a + -b⟩

-- Given a Ring we can also construct subrings

structure SubRing { α : Type} (r: Ring α) (p : α → Prop) :=
(pd: ∀ a : α, decidable (p a))
(inc_zero: p 0)
(cu_add: ∀ a b : α, p a → p b → p (a + b))
(cu_mul: ∀ a b : α, p a → p b → p (a*b))
(cu_neg: ∀ a : α, p a → p (-a))

-- This lets us construct a Commutative Ring

class CommRing (α: Type) extends has_zero α, has_add α, has_neg α, has_mul α :=
(is_set: ExcludedMiddle α)
(add_assoc: Associative add)
(add_comm: Commutative add)
(left_zero: LeftIdentity add 0)
(left_neg: LeftInverse add 0 neg)
(mul_assoc: Associative mul)
(mul_comm: Commutative mul)
(left_distrib: LeftDistrib add mul)
def CommRing.to_Ring {α: Type} (cr: CommRing α): Ring α :=
{
    is_set        := cr.is_set,
    add_assoc     := cr.add_assoc,
    add_comm      := cr.add_comm,
    left_zero     := cr.left_zero,
    left_neg      := cr.left_neg,
    mul_assoc     := cr.mul_assoc,
    left_distrib  := cr.left_distrib,
    right_distrib := assume a b c: α, by rw [cr.mul_comm, cr.left_distrib, CommRing.mul_comm α c, CommRing.mul_comm α c]
}
instance CommRingIsRing {α: Type} [cr: CommRing α]: Ring α := cr.to_Ring


-- And a Unit Ring
class UnitRing (α: Type) extends Ring α, has_one α := (left_one: LeftIdentity mul one) (right_one: RightIdentity mul one)

-- An NZDRing is a Ring without zero divisors
class NZDRing (α: Type) extends Ring α := (nzd: NoZeroDivisors α)

-- A Commutative Unit Ring
class CommUnitRing (α: Type) extends CommRing α, has_one α := (left_one: LeftIdentity mul one)
def CommUnitRing.to_UnitRing {α: Type} (cur: CommUnitRing α): UnitRing α :=
{
    is_set        := cur.is_set,
    add_assoc     := cur.add_assoc,
    add_comm      := cur.add_comm,
    left_zero     := cur.left_zero,
    left_neg      := cur.left_neg,
    mul_assoc     := cur.mul_assoc,
    left_distrib  := cur.left_distrib,
    right_distrib := cur.to_CommRing.to_Ring.right_distrib,
    left_one      := cur.left_one,
    right_one     := assume a : α, by rw [cur.mul_comm, CommUnitRing.left_one α a]
}
instance CommUnitRingIsUnitRing {α: Type} [cur: CommUnitRing α]: UnitRing α := cur.to_UnitRing

-- A Commutative NZDRing
class CommNZDRing (α: Type) extends CommRing α := (nzd: NoZeroDivisors α)
def CommNZDRing.to_Ring {α : Type} (cnzdr: CommNZDRing α): Ring α := cnzdr.to_CommRing.to_Ring
def CommNZDRing.to_NZDRing {α: Type} (cnzdr: CommNZDRing α): NZDRing α :=
{
    is_set        := cnzdr.is_set,
    add_assoc     := cnzdr.add_assoc,
    add_comm      := cnzdr.add_comm,
    left_zero     := cnzdr.left_zero,
    left_neg      := cnzdr.left_neg,
    mul_assoc     := cnzdr.mul_assoc,
    left_distrib  := cnzdr.left_distrib,
    right_distrib := cnzdr.to_Ring.right_distrib,
    nzd           := cnzdr.nzd
}
instance CommNZDRingIsNZDRing {α: Type} [cnzdr: CommNZDRing α]: NZDRing α := cnzdr.to_NZDRing

-- NZDUnitRing
class NZDUnitRing (α : Type) extends UnitRing α := (zero_ne_one: zero ≠ one) (nzd: NoZeroDivisors α)
def NZDUnitRing.to_NZDRing {α: Type} (nzdur: NZDUnitRing α): NZDRing α :=
{
    is_set        := nzdur.is_set,
    add_assoc     := nzdur.add_assoc,
    add_comm      := nzdur.add_comm,
    left_zero     := nzdur.left_zero,
    left_neg      := nzdur.left_neg,
    mul_assoc     := nzdur.mul_assoc,
    left_distrib  := nzdur.left_distrib,
    right_distrib := nzdur.right_distrib,
    nzd           := nzdur.nzd
}
instance NZDUnitRingIsNZDRing {α: Type} [nzdur: NZDUnitRing α]: NZDRing α := nzdur.to_NZDRing

-- An Integral Domain
class IntegralDomain (α: Type) extends CommUnitRing α := (nzd: NoZeroDivisors α)
def IntegralDomain.to_UnitRing {α: Type} (intd: IntegralDomain α): UnitRing α := intd.to_CommUnitRing.to_UnitRing
def IntegralDomain.to_CommNZDRing {α: Type} (intd: IntegralDomain α): CommNZDRing α :=
{
    is_set        := intd.is_set,
    add_assoc     := intd.add_assoc,
    add_comm      := intd.add_comm,
    left_zero     := intd.left_zero,
    left_neg      := intd.left_neg,
    mul_assoc     := intd.mul_assoc,
    left_distrib  := intd.left_distrib,
    mul_comm      := intd.mul_comm,
    nzd           := intd.nzd
}
instance IntegralDomainIsCommNZDRing {α: Type} [intd: IntegralDomain α]: CommNZDRing α := intd.to_CommNZDRing
def IntegralDomain.to_NZDRing {α: Type } (intd: IntegralDomain α): NZDRing α := intd.to_CommNZDRing.to_NZDRing
def IntegralDomain.to_Ring {α: Type } (intd: IntegralDomain α): Ring α := intd.to_UnitRing.to_Ring

-- Division Ring
-- For convenience we will define inv: α → α even though this is strictly speaking wrong.
-- We thus require that inv : α → α can be projected onto αˣ
class DivisionRing (α: Type) extends UnitRing α, has_inv α :=
(inv_nz_is_nz: ∀ a : α, a ≠ 0 → a⁻¹ ≠ 0)
(left_inv: NZLeftInverse zero one mul inv)
(zero_ne_one: zero ≠ one)


-- Field
class Field (α: Type) extends IntegralDomain α, has_inv α :=
(inv_nz_is_nz: ∀ a : α, a ≠ 0 → a⁻¹ ≠ 0)
(left_inv: NZLeftInverse zero one mul inv)
(zero_ne_one: zero ≠ one)
def Field.to_UnitRing {α: Type} (f: Field α): UnitRing α := f.to_IntegralDomain.to_UnitRing
def Field.to_Ring {α: Type} (f: Field α): Ring α := f.to_UnitRing.to_Ring
def Field.to_DivisionRing {α: Type} (f: Field α): DivisionRing α :=
{
    is_set        := f.is_set,
    add_assoc     := f.add_assoc,
    add_comm      := f.add_comm,
    left_zero     := f.left_zero,
    left_neg      := f.left_neg,
    mul_assoc     := f.mul_assoc,
    left_distrib  := f.left_distrib,
    right_distrib := f.to_Ring.right_distrib,
    left_one      := f.left_one,
    right_one     := f.to_UnitRing.right_one,
    inv_nz_is_nz  := f.inv_nz_is_nz,
    left_inv      := f.left_inv,
    zero_ne_one   := f.zero_ne_one
}
instance FieldIsDivisionRing {α: Type} [f: Field α]: DivisionRing α := f.to_DivisionRing

-- And subfields

class SubField {α: Type} (f: Field α) (p: α → Prop) :=
(pd: ∀ a : α, decidable (p a))
(inc_zero: p 0)
(inc_one: p 1)
(cu_add: ∀ a b : α, p a → p b → p (a + b))
(cu_mul: ∀ a b : α, p a → p b → p (a*b))
(cu_neg: ∀ a : α, p a → p (-a))
(cu_inv: ∀ a : α, p a → p (a⁻¹))


-- And now some results on these various ringoids!

namespace Ring
variable {α: Type}
variable (r: Ring α)
include r

lemma zero_add (a : α): 0 + a = a := Ring.left_zero α a
lemma add_zero (a : α): a + 0 = a := by rw [r.add_comm, r.zero_add]

lemma neg_add (a : α): -a + a = 0 := Ring.left_neg α a
lemma add_neg (a : α): a  + -a = 0 := by rw [r.add_comm, r.neg_add]

lemma add_mul (a b c: α): (a + b)*c = a*c + b*c := Ring.right_distrib α a b c
lemma mul_add (a b c: α): c*(a + b) = c*a + c*b := Ring.left_distrib α a b c

def to_AdditiveAbelianGroup {α: Type} (r: Ring α): AdditiveAbelianGroup α :=
{
    assoc := r.add_assoc,
    left_id := r.left_zero,
    right_id := r.add_zero,
    left_inv := r.left_neg,
    right_inv := r.add_neg,
    comm := r.add_comm
}

instance RingIsAdditiveAbelianGroup {α: Type} [r: Ring α]: AdditiveAbelianGroup α := r.to_AdditiveAbelianGroup

lemma zero_unique (z: α): LeftIdentity r.add z → z = 0 := r.to_AdditiveAbelianGroup.to_Group.id_unique
lemma neg_unique {a b : α}: a + b = 0 → a = -b := r.to_AdditiveAbelianGroup.to_Group.inv_unique

lemma zero_mul (a : α): 0 * a = 0 :=
    suffices 0*a + 0*a = 0 + 0*a, from iff.elim_left r.to_AdditiveAbelianGroup.to_Group.cancel_right this,
    calc
        0*a + 0*a = 0 + (0*a + 0*a)  : by rw r.zero_add
        ...       = 0 + (0 + 0)*a    : by rw r.right_distrib
        ...       = 0 + 0*a          : by rw r.zero_add 0
lemma mul_zero (a : α): a * 0 = 0 :=
    suffices a*0 + a*0 = 0 + a*0, from iff.elim_left r.to_AdditiveAbelianGroup.to_Group.cancel_right this,
    calc
        a*0 + a*0 = 0 + (a*0 + a*0)  : by rw r.zero_add
        ...       = 0 + a*(0 + 0)    : by rw r.left_distrib
        ...       = 0 + a*0          : by rw r.zero_add 0

lemma neg_neg (a: α): -(-a) = a := r.to_AdditiveAbelianGroup.to_Group.inv_inv a

lemma neg_mul (a b : α): (-a) * b = -(a * b) :=
    suffices ((-a) * b) + (a * b) = 0, from r.neg_unique this,
    calc
        ((-a) * b) + (a * b) = (-a + a) * b  : by rw r.right_distrib
        ...                  = 0 * b         : by rw r.neg_add
        ...                  = 0             : by rw r.zero_mul

lemma mul_neg (a b : α): a * (-b) = -(a * b) :=
    suffices (a * -b) + (a * b) = 0, from r.neg_unique this,
    calc
        (a * -b) + (a * b) = a * (-b + b)  : by rw r.left_distrib
        ...                = a * 0         : by rw r.neg_add
        ...                = 0             : by rw r.mul_zero

lemma neg_mul_neg (a b : α): -a * -b = a * b :=
calc
    -a * -b = -(a * -b)   : by rw r.neg_mul
    ...     = -(-(a * b)) : by rw r.mul_neg
    ...     = a * b       : by rw r.neg_neg

lemma add_cancel_left {a b c : α}: a + b = a + c ↔ b = c := r.to_AdditiveAbelianGroup.to_Group.cancel_left
lemma add_cancel_right {a b c : α}: a + b = c + b ↔ a = c := r.to_AdditiveAbelianGroup.to_Group.cancel_right

lemma left_transfer_to_rhs {a b c : α}: a + b = c ↔ b = -a + c :=
calc
    a + b = c ↔ -a + (a + b) = -a + c : by rw r.add_cancel_left
    ...       ↔ (-a + a) + b = -a + c : by rw r.add_assoc
    ...       ↔ 0 + b = -a + c        : by rw r.neg_add
    ...       ↔ b = -a + c            : by rw r.zero_add

lemma right_transfer_to_rhs {a b c : α}: a + b = c ↔ a = c + -b :=
calc
    a + b = c ↔ (a + b) + -b = c + -b : by rw r.add_cancel_right
    ...       ↔ a + (b + -b) = c + -b : by rw r.add_assoc
    ...       ↔ a + 0 = c + -b        : by rw r.add_neg
    ...       ↔ a = c + -b            : by rw r.add_zero

lemma neg_zero: -(0 : α) = 0 :=
suffices (0: α) + 0 = 0, from eq.symm (r.neg_unique this),
r.add_zero 0

lemma left_distrib_neg (a b c : α): c*(a - b) = c*a - c*b :=
calc
    c*(a - b) = c*(a + -b)    : by refl
    ...       = c*a + c*-b    : by rw r.left_distrib
    ...       = c*a + -(c*b)  : by rw r.mul_neg
    ...       = c*a - c*b     : by refl

lemma diff_zero {a b : α}: a = b ↔ a - b = 0 :=
iff.intro (
    assume h: a = b,
    calc
        a - b = a - a  : by rw h
        ...   = a + -a : by refl
        ...   = 0      : by rw r.add_neg
) (
    assume h: a - b = 0,
    calc
        a   = a + 0         : by rw r.add_zero
        ... = a + (-b + b)  : by rw r.neg_add
        ... = (a + -b) + b  : by rw r.add_assoc
        ... = (a - b) + b   : by refl
        ... = 0 + b         : by rw h
        ... = b             : by rw r.zero_add
)

end Ring




namespace SubRing
variable {α : Type}
variable [r: Ring α]
variable {p: α → Prop}
variable (sr: SubRing r p)

include α
include r
include p
include sr

def add (a b : {x: α // p x}): {x: α // p x} := ⟨a.val + b.val,(sr.cu_add) a.val b.val a.property b.property⟩
def mul (a b : {x: α // p x}): {x: α // p x} := ⟨a.val * b.val, (sr.cu_mul) a.val b.val a.property b.property⟩
def neg (a : {x: α // p x}): {x: α // p x} := ⟨-a.val, (sr.cu_neg) a.val a.property⟩
def zero : {x: α // p x} := ⟨(0 : α), sr.inc_zero⟩
def is_set: ExcludedMiddle {x: α // p x} :=
    assume ⟨a, ha⟩ ⟨b, hb⟩,
    or.elim (Ring.is_set α a b) (
        assume h: a = b,
        or.intro_left _ (subtype.eq h)
    ) (
        assume h: a ≠ b,
        or.intro_right _ (assume hc: (⟨a, ha⟩: {x:α // p x}) = ⟨b, hb⟩, absurd (by injection hc) h)
    )

lemma add_sr (a b : {x: α // p x}): (sr.add a b).val = a.val + b.val := let ⟨a, ha⟩ := a in (let ⟨b, hb⟩ := b in (rfl))
lemma mul_sr (a b : {x: α // p x}): (sr.mul a b).val = a.val * b.val := let ⟨a, ha⟩ := a in (let ⟨b, hb⟩ := b in (rfl))

instance SubRingHasAdd {α: Type} [r: Ring α] {p : α → Prop} [sr: SubRing r p]: has_add {x: α // p x} := ⟨sr.add⟩
instance SubRingHasMul {α: Type} [r: Ring α] {p : α → Prop} [sr: SubRing r p]: has_mul {x: α // p x} := ⟨sr.mul⟩
instance SubRingHasZero {α: Type} [r: Ring α] {p : α → Prop} [sr: SubRing r p]: has_zero {x: α // p x} := ⟨sr.zero⟩
instance SubRingHasNeg {α: Type} [r: Ring α] {p : α → Prop} [sr: SubRing r p]: has_neg {x: α // p x} := ⟨sr.neg⟩

lemma add_assoc: Associative sr.add := assume a b c : {x: α // p x}, suffices (sr.add (sr.add a b) c).val = (sr.add a (sr.add b c)).val, from subtype.eq this, by rw [sr.add_sr, sr.add_sr, r.add_assoc, ←sr.add_sr, ←sr.add_sr]
lemma add_comm: Commutative sr.add := assume a b : {x: α // p x}, suffices (sr.add a b).val = (sr.add b a).val, from subtype.eq this, by rw [sr.add_sr, r.add_comm, ←sr.add_sr]
lemma left_zero: LeftIdentity sr.add sr.zero := assume a: {x: α // p x}, suffices (sr.add sr.zero a).val = a.val, from subtype.eq this, calc
    (sr.add sr.zero a).val = sr.zero.val + a.val  : by rw sr.add_sr
    ...                    = 0 + a.val            : by refl
    ...                    = a.val                : by rw r.zero_add
lemma left_neg: LeftInverse sr.add sr.zero sr.neg := assume a : {x: α // p x}, suffices (sr.add (sr.neg a) a).val = 0, from subtype.eq this, calc
    (sr.add (sr.neg a) a).val = (sr.neg a).val + a.val  : by rw sr.add_sr
    ...                       = -(a.val) + a.val        : by refl
    ...                       = 0                       : by rw r.neg_add
lemma mul_assoc: Associative sr.mul := assume a b c : {x:α // p x}, suffices (sr.mul (sr.mul a b) c).val = (sr.mul a (sr.mul b c)).val, from subtype.eq this, by rw [sr.mul_sr, sr.mul_sr, r.mul_assoc, sr.mul_sr, sr.mul_sr]
lemma left_distrib: LeftDistrib sr.add sr.mul := assume a b c : {x:α // p x}, suffices (sr.mul c (sr.add a b)).val = (sr.add (sr.mul c a) (sr.mul c b)).val, from subtype.eq this, calc
    (sr.mul c (sr.add a b)).val = c.val * (a.val + b.val)                 : by rw [sr.mul_sr, sr.add_sr]
    ...                         = c.val * a.val + c.val * b.val           : by rw r.left_distrib
    ...                         = (sr.add (sr.mul c a) (sr.mul c b)).val  : by rw [←sr.mul_sr, ←sr.mul_sr, ←sr.add_sr]
lemma right_distrib: RightDistrib sr.add sr.mul := assume a b c : {x:α // p x}, suffices (sr.mul (sr.add a b) c).val = (sr.add (sr.mul a c) (sr.mul b c)).val, from subtype.eq this, calc
    (sr.mul (sr.add a b) c).val = (a.val + b.val) * c.val                 : by rw [sr.mul_sr, sr.add_sr]
    ...                         = a.val * c.val + b.val * c.val           : by rw r.right_distrib
    ...                         = (sr.add (sr.mul a c) (sr.mul b c)).val  : by rw [←sr.mul_sr, ←sr.mul_sr, ←sr.add_sr]

def to_Ring: Ring {x: α // p x} :=
{
    add := sr.add,
    mul := sr.mul,
    neg := sr.neg,
    zero := sr.zero,
    is_set := sr.is_set,
    add_assoc := sr.add_assoc,
    add_comm := sr.add_comm,
    left_zero := sr.left_zero,
    left_neg := sr.left_neg,
    mul_assoc := sr.mul_assoc,
    left_distrib := sr.left_distrib,
    right_distrib := sr.right_distrib
}
instance {α: Type} [r: Ring α] {p : α → Prop} [sr: SubRing r p]: Ring {x:α // p x} := sr.to_Ring

end SubRing

namespace SubRing
private def decidable_and {α : Type} {p q : α → Prop} (pd: ∀ a : α, decidable (p a)) (qd: ∀ a : α, decidable (q a)): ∀ a : α, decidable (p a ∧ q a) :=
    assume a: α,
    match (pd a), (qd a) with
    | is_true hp,  is_true hq  := is_true (and.intro (hp) (hq))
    | is_false hp, _           := is_false (assume hc, absurd hc.left hp)
    | is_true hp,  is_false hq := is_false (assume hc, absurd hc.right hq)
    end

def intersection {α: Type} [r: Ring α] {p q: α → Prop} (srp: SubRing r p) (srq: SubRing r q): SubRing r (λ a, p a ∧ q a) :=
{
    pd:=decidable_and srp.pd srq.pd,
    inc_zero:=and.intro (srp.inc_zero) (srq.inc_zero),
    cu_add:=assume a b, assume ha hb, and.intro (srp.cu_add a b ha.left hb.left) (srq.cu_add a b ha.right hb.right),
    cu_mul:=assume a b, assume ha hb, and.intro (srp.cu_mul a b ha.left hb.left) (srq.cu_mul a b ha.right hb.right),
    cu_neg:=assume a, assume ha, and.intro (srp.cu_neg a ha.left) (srq.cu_neg a ha.right)
}

end SubRing



namespace UnitRing
variable {α: Type}
variable (ur: UnitRing α)
include ur

lemma one_mul (a: α): 1*a = a := UnitRing.left_one α a
lemma mul_one (a: α): a*1 = a := UnitRing.right_one α a

lemma neg_one_mul (a : α): -1 * a = -a :=
calc
    -1 * a = -(1*a)  : by rw ur.to_Ring.neg_mul
    ...    = -a      : by rw ur.one_mul
lemma mul_neg_one (a : α): a*(-1) = -a :=
calc
    a * -1 = -(a*1)  : by rw ur.to_Ring.mul_neg
    ...    = -a      : by rw ur.mul_one

lemma neg_one_mul_neg_one: (-1: α) * -1 = 1 :=
calc
    (-1: α) * -1 = -(-1)  : by rw ur.neg_one_mul
    ...          = 1      : by rw ur.to_Ring.neg_neg

end UnitRing





namespace NZDRing
variable {α : Type}
variable (nzdr: NZDRing α)
include nzdr

lemma no_zero_divisors {a b: α}: a * b = 0 → a ≠ 0 → b = 0 := NZDRing.nzd α a b

lemma mul_preserves_nz {a b : α}: a ≠ 0 → b ≠ 0 → a*b ≠ 0 :=
assume ha: a ≠ 0,
assume hb: b ≠ 0,
assume hc: a *b = 0,
absurd (nzdr.no_zero_divisors hc ha) hb

def mul_of_nz: αˣ → αˣ → αˣ := assume ⟨a, ha⟩, assume ⟨b, hb⟩, ⟨a*b, mul_preserves_nz nzdr ha hb⟩
instance NZHasMul [nzdr: NZDRing α]: has_mul αˣ := ⟨mul_of_nz nzdr⟩
lemma nz_mul (a b: αˣ): (a * b).val = a.val * b.val := let ⟨x, hx⟩ := a in (let ⟨y, hy⟩ := b in (rfl))

lemma mul_of_nz_assoc: Associative (mul_of_nz nzdr) :=
assume a b c,
suffices ((a * b) * c).val = (a * (b * c)).val, from subtype.eq this,
calc
    ((a * b) * c).val = (a * b).val * c.val  : by rw nz_mul nzdr
    ...               = (a.val * b.val) * c.val : by rw nz_mul nzdr
    ...               = a.val * (b.val * c.val) : by rw Ring.mul_assoc α a.val b.val c.val
    ...               = a.val * (b * c).val     : by rw nz_mul nzdr
    ...               = (a * (b * c)).val       : by rw nz_mul nzdr a

def multiplicative_semigroup_structure: MultiplicativeSemigroup αˣ := { mul_assoc_ := mul_of_nz_assoc nzdr }

instance {α : Type} [nzdr: NZDRing α]: MultiplicativeSemigroup αˣ := multiplicative_semigroup_structure nzdr

end NZDRing




namespace NZDUnitRing
variable {α : Type}
variable (nzdur: NZDUnitRing α)
include nzdur

lemma one_ne_zero: (1 : α) ≠ 0 := ne.symm (nzdur.zero_ne_one)

instance NZHasOne {α: Type} [nzdur: NZDUnitRing α]: has_one αˣ := ⟨⟨1, nzdur.one_ne_zero⟩⟩

lemma nonzero_one_mul (a : αˣ): 1 * a = a :=
suffices (1 * a).val = a.val, from subtype.eq this,
calc
    (1 * a).val = (1: αˣ).val * a.val  : by rw nzdur.to_NZDRing.nz_mul
    ...         = 1 * a.val            : by refl
    ...         = a.val                : by rw nzdur.to_UnitRing.one_mul

lemma nonzero_mul_one (a : αˣ): a * 1 = a :=
suffices (a * 1).val = a.val, from subtype.eq this,
calc
    (a * 1).val = a.val * (1: αˣ).val  : by rw nzdur.to_NZDRing.nz_mul
    ...         = a.val * 1            : by refl
    ...         = a.val                : by rw nzdur.to_UnitRing.mul_one

def multiplicative_monoid_structure: MultiplicativeMonoid αˣ :=
{
    assoc := nzdur.to_NZDRing.mul_of_nz_assoc,
    left_id := nzdur.nonzero_one_mul,
    right_id := nzdur.nonzero_mul_one
}
instance {α : Type} [nzdur: NZDUnitRing α]: MultiplicativeMonoid αˣ := nzdur.multiplicative_monoid_structure

lemma mul_cancel_left {a b c: α}: c ≠ 0 → c * a = c * b → a = b :=
assume hc: c ≠ 0,
assume h: c * a = c * b,
suffices a - b = 0, from iff.elim_right nzdur.to_Ring.diff_zero this,
suffices c*(a - b) = 0, from nzdur.to_NZDRing.no_zero_divisors this hc,
calc
    c*(a - b) = c*a - c*b  : by rw [nzdur.to_Ring.left_distrib_neg a b c, h]
    ...       = 0          : by rw iff.elim_left nzdur.to_Ring.diff_zero h

end NZDUnitRing




namespace IntegralDomain
variable {α : Type}
variable (intd: IntegralDomain α)
include intd

end IntegralDomain



namespace DivisionRing
variable {α : Type}
variable (dr: DivisionRing α)
include dr

lemma inv_mul {a : α}: a ≠ 0 → a⁻¹ * a = 1 := DivisionRing.left_inv α a
lemma inv_nz {a : α}: a ≠ 0 → a⁻¹ ≠ 0 := DivisionRing.inv_nz_is_nz a

lemma inv_inv {a : α}: a ≠ 0 → (a⁻¹)⁻¹ = a :=
assume hnz: a ≠ 0,
calc
    a⁻¹⁻¹ = a⁻¹⁻¹ * 1          : by rw dr.to_UnitRing.mul_one
    ...   = a⁻¹⁻¹ * (a⁻¹ * a)  : by rw dr.inv_mul hnz
    ...   = (a⁻¹⁻¹ * a⁻¹) * a  : by rw dr.to_Ring.mul_assoc
    ...   = 1 * a              : by rw dr.inv_mul (dr.inv_nz hnz)
    ...   = a                  : by rw dr.to_UnitRing.one_mul

lemma mul_inv {a : α}: a ≠ 0 → a * a⁻¹ = 1 :=
assume hnz: a ≠ 0,
calc
    a * a⁻¹ = a⁻¹⁻¹ * a⁻¹  : by rw dr.inv_inv hnz
    ...     = 1            : by rw dr.inv_mul (dr.inv_nz hnz)

def inv_of_nz: αˣ → αˣ := λ a : αˣ, ⟨a.val⁻¹, dr.inv_nz a.property⟩
instance {α : Type} [dr: DivisionRing α]: has_inv αˣ := ⟨dr.inv_of_nz⟩

lemma no_zero_divisors: NoZeroDivisors α :=
    assume a b : α,
    assume h: a * b = 0,
    assume ha: a ≠ 0,
    calc
        b   = 1*b          : by rw dr.to_UnitRing.one_mul
        ... = (a⁻¹ * a)*b  : by rw dr.inv_mul ha
        ... = a⁻¹ * (a*b)  : by rw dr.to_Ring.mul_assoc
        ... = a⁻¹ * 0      : by rw h
        ... = 0            : by rw dr.to_Ring.mul_zero

def to_NZDUnitRing {α: Type} (dr: DivisionRing α): NZDUnitRing α :=
{
    zero_ne_one := dr.zero_ne_one,
    nzd := dr.no_zero_divisors
}
instance {α: Type} [dr: DivisionRing α]: NZDUnitRing α := dr.to_NZDUnitRing
def to_NZDRing {α: Type} (dr: DivisionRing α): NZDRing α := dr.to_NZDUnitRing.to_NZDRing

lemma nz_inv_mul (a : αˣ): a⁻¹ * a = 1 :=
    suffices (a⁻¹ * a).val = 1, from subtype.eq this,
    calc
        (a⁻¹ * a).val = (a⁻¹).val * a.val  : by rw dr.to_NZDRing.nz_mul
        ...           = (a.val)⁻¹ * a.val  : by refl
        ...           = 1                  : by rw dr.inv_mul a.property
lemma nz_mul_inv (a : αˣ): a * a⁻¹ = 1 :=
    suffices (a * a⁻¹).val = 1, from subtype.eq this,
    calc
        (a * a⁻¹).val = a.val * (a⁻¹).val  : by rw dr.to_NZDRing.nz_mul
        ...           = a.val * (a.val)⁻¹  : by refl
        ...           = 1                  : by rw dr.mul_inv a.property

def multiplicative_group_structure: MultiplicativeGroup αˣ :=
{
    left_inv  := dr.nz_inv_mul,
    right_inv := dr.nz_mul_inv
}
instance {α : Type} [dr: DivisionRing α]: MultiplicativeGroup αˣ := dr.multiplicative_group_structure

end DivisionRing




namespace Field
variable {α : Type}
variable (f: Field α)
include f

def to_NZDUnitRing {α: Type} (f: Field α): NZDUnitRing α := f.to_DivisionRing.to_NZDUnitRing
def to_NZDRing: NZDRing α := f.to_DivisionRing.to_NZDRing

lemma nz_mul_comm (a b : αˣ): a * b = b * a :=
suffices (a * b).val = (b * a).val, from subtype.eq this,
calc
    (a * b).val = a.val * b.val   : by rw f.to_NZDRing.nz_mul
    ...         = b.val * a.val   : by rw f.mul_comm
    ...         = (b * a).val     : by rw f.to_NZDRing.nz_mul

def multiplicative_abelian_group_structure: MultiplicativeAbelianGroup αˣ :=
{
    comm := f.nz_mul_comm
}
instance {α: Type} [f: Field α]: MultiplicativeAbelianGroup αˣ := f.multiplicative_abelian_group_structure

end Field



namespace SubField

variable {α: Type}
variable [f: Field α]
variable {p : α → Prop}
variable (sf: SubField f p)

include α
include f
include p
include sf

def to_SubRing: SubRing f.to_Ring p :=
{
    pd:=sf.pd,
    inc_zero:=sf.inc_zero,
    cu_add:=sf.cu_add,
    cu_mul:=sf.cu_mul,
    cu_neg:=sf.cu_neg
}

instance: has_zero {x: α // p x} := ⟨sf.to_SubRing.zero⟩

def add: {x:α//p x} → {x:α//p x} → {x:α//p x} := sf.to_SubRing.add
def mul: {x:α//p x} → {x:α//p x} → {x:α//p x} := sf.to_SubRing.mul
def zero: {x:α//p x} := sf.to_SubRing.zero
def one: {x:α//p x} := ⟨1, sf.inc_one⟩
def neg: {x:α//p x} → {x:α//p x} := sf.to_SubRing.neg
def inv: {x:α//p x} → {x:α//p x} := λ ⟨a, ha⟩, ⟨a⁻¹, SubField.cu_inv f a ha⟩
lemma mul_comm: Commutative sf.mul := assume a b, suffices (sf.to_SubRing.mul a b).val = (sf.to_SubRing.mul b a).val, from subtype.eq this, by rw [sf.to_SubRing.mul_sr, f.mul_comm, ←sf.to_SubRing.mul_sr]
lemma left_one: LeftIdentity sf.to_SubRing.mul sf.one := assume a, suffices (SubRing.mul (to_SubRing sf) (one sf) a).val = a.val, from subtype.eq this, calc
    (SubRing.mul (to_SubRing sf) (one sf) a).val = sf.one.val * a.val   : by rw sf.to_SubRing.mul_sr
    ...                                          = 1 * a.val            : by refl
    ...                                          = a.val                : by rw f.to_UnitRing.one_mul
lemma nzd: ∀ a b : {x:α//p x}, sf.mul a b = sf.zero → a ≠ sf.zero → b = sf.zero :=
    assume a b,
    assume h: sf.to_SubRing.mul a b = sf.to_SubRing.zero,
    have h: (sf.to_SubRing.mul a b).val = sf.to_SubRing.zero.val, by injection h,
    have h: a.val * b.val = 0, from h,
    assume ha: a ≠ sf.to_SubRing.zero,
    have ha: a.val ≠ 0, from assume hc: a.val = sf.to_SubRing.zero.val, absurd (subtype.eq hc) ha,
    suffices b.val = 0, from subtype.eq this,
    f.to_NZDRing.no_zero_divisors h ha
lemma inv_nz_is_nz: ∀ a : {x:α//p x}, a ≠ sf.zero → sf.inv a ≠ sf.zero :=
    assume ⟨a, hp⟩,
    assume ha: (⟨a, hp⟩ : {x:α//p x}) ≠ sf.to_SubRing.zero,
    have ha: a ≠ 0, from assume hc: (⟨a,hp⟩ : {x:α//p x}).val = sf.to_SubRing.zero.val, absurd (subtype.eq hc) ha,
    assume hc: sf.inv ⟨a, hp⟩ = sf.to_SubRing.zero,
    have hc: (⟨a⁻¹, SubField.cu_inv f a hp⟩ : {x:α//p x}) = sf.to_SubRing.zero, from hc,
    have hc: a⁻¹ = 0, by injection hc,
    absurd hc (Field.inv_nz_is_nz a ha)

lemma left_inv: ∀ a : {x:α//p x}, a ≠ sf.zero → sf.mul (sf.inv a) a = sf.one :=
    assume ⟨a, hp⟩,
    assume h: (⟨a, hp⟩ : {x:α//p x}) ≠ sf.to_SubRing.zero,
    have h: a ≠ 0, from assume hc: (⟨a, hp⟩ : {x:α//p x}).val = sf.to_SubRing.zero.val, absurd (subtype.eq hc) h,
    suffices (sf.mul (sf.inv ⟨a, hp⟩) ⟨a, hp⟩).val = 1, from subtype.eq this,
    calc
        (sf.mul (sf.inv ⟨a, hp⟩) ⟨a, hp⟩).val = (sf.to_SubRing.mul ⟨a⁻¹, SubField.cu_inv f a hp⟩ ⟨a, hp⟩).val  : by refl
        ...                                   = a⁻¹ * a                                                        : by rw sf.to_SubRing.mul_sr
        ...                                   = 1                                                              : by rw f.to_DivisionRing.inv_mul h
lemma zero_ne_one: sf.zero ≠ sf.one := assume hc: sf.zero = sf.one, have hc: (0: α) = 1, by injection hc, absurd hc f.zero_ne_one


def to_Field: Field {x: α // p x} :=
{
    add := sf.add,
    mul := sf.mul,
    neg := sf.to_SubRing.neg,
    zero := sf.zero,
    one := sf.one,
    inv := sf.inv,
    is_set := sf.to_SubRing.is_set,
    add_assoc := sf.to_SubRing.add_assoc,
    add_comm := sf.to_SubRing.add_comm,
    left_zero := sf.to_SubRing.left_zero,
    left_neg := sf.to_SubRing.left_neg,
    mul_assoc := sf.to_SubRing.mul_assoc,
    left_distrib := sf.to_SubRing.left_distrib,
    mul_comm := sf.mul_comm,
    left_one := sf.left_one,
    nzd := sf.nzd,
    inv_nz_is_nz := sf.inv_nz_is_nz,
    left_inv := sf.left_inv,
    zero_ne_one := sf.zero_ne_one
}


end SubField
