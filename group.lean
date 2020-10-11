-- Groups, a fundemental structure of algebra.
--
-- Lean has them built in of course, but I'm going to redefine them
-- myself for the hell of it in keeping with my "from first principles"
-- approach


-- This is a technical element where we fix a 'universe' of types, so that we can
-- refer to the Type of a Type easily. Specifically in this notation if Type u is a type
-- then Type (u+1) is the Type of the Type itself.

-- The standard lean library uses lowercase names for all thse things, so to avoid confusion
-- let's use Camelcase

def Associative {α : Type} (f: α → α → α):= ∀ a b c : α, f (f a b) c = f a (f b c)

-- So we'll define our group as a class, so that it can be inferred when needed
--
-- We begin with the most basic of group-like objects, the semi-group
class Semigroup {α: Type} (op: α → α → α) := (assoc: (Associative op))

example {α : Type} [hm: has_mul α] [msg: Semigroup hm.mul] {a b c : α}: (a*b)*c = a*(b*c) := Semigroup.assoc _ a b c

namespace Semigroup

lemma add_assoc {α : Type} [ha: has_add α] [Semigroup ha.add] (a b c: α): (a+b)+c = a+(b+c) := Semigroup.assoc _ a b c
lemma mul_assoc {α : Type} [hm: has_mul α] [Semigroup hm.mul] (a b c: α): (a*b)*c = a*(b*c) := Semigroup.assoc _ a b c

end Semigroup

-- Right so from a Semigroup we can form a Monoid
class Monoid {α: Type} (op: α → α → α) (id: α) extends Semigroup op := (left_id: ∀ a : α, op id a = a) (right_id: ∀ a : α, op a id = a)

namespace Monoid

lemma add_zero {α: Type} [ha: has_add α] [hz: has_zero α] [Monoid ha.add hz.zero] (a: α): a + 0 = a := Monoid.right_id _ _ a
lemma mul_one {α: Type} [hm: has_mul α] [ho: has_one α] [Monoid hm.mul ho.one] (a: α): a*1 = a := Monoid.right_id _ _ a

lemma zero_add {α: Type} [ha: has_add α] [hz: has_zero α] [Monoid ha.add hz.zero] (a: α): 0 + a = a := Monoid.left_id _ _ a
lemma one_mul {α: Type} [hm: has_mul α] [ho: has_one α] [Monoid hm.mul ho.one] (a: α): 1*a = a := Monoid.left_id _ _ a

end Monoid

-- And from a monoid we can go to a full Group!
class Group {α: Type} (op: α → α → α) (id: α) (inv: α → α) extends Monoid op id := (left_inv: ∀ a : α, op (inv a) a = id) (right_inv: ∀ a : α, op a (inv a) = id)

namespace Group

lemma add_neg {α: Type} [ha: has_add α] [hz: has_zero α] [hn: has_neg α] [Group ha.add hz.zero hn.neg] (a: α): a + -a = 0 := Group.right_inv _ _ _ a
lemma mul_inv {α: Type} [hm: has_mul α] [ho: has_one α] [hi: has_inv α] [Group hm.mul ho.one hi.inv] (a: α): a*a⁻¹ = 1 := Group.right_inv _ _ _ a

lemma neg_add {α: Type} [ha: has_add α] [hz: has_zero α] [hn: has_neg α] [Group ha.add hz.zero hn.neg] (a: α): -a + a = 0 := Group.left_inv _ _ _ a
lemma inv_mul {α: Type} [hm: has_mul α] [ho: has_one α] [hi: has_inv α] [Group hm.mul ho.one hi.inv] (a: α): a⁻¹*a = 1 := Group.left_inv _ _ _ a

lemma neg_add_elm_add {α: Type} [ha: has_add α] [hz: has_zero α] [hn: has_neg α] [Group ha.add hz.zero hn.neg] (a b: α): a = -b + (b + a) :=
calc
    a   = 0 + a         : by rw Monoid.zero_add
    ... = -b + (b + a)  : by rw [←neg_add b, Semigroup.add_assoc]
lemma inv_mul_elm_mul {α: Type} [hm: has_mul α] [ho: has_one α] [hi: has_inv α] [Group hm.mul ho.one hi.inv] (a b: α): a = b⁻¹*(b*a) :=
calc
    a   = 1*a        : by rw Monoid.one_mul
    ... = b⁻¹*(b*a)  : by rw [←inv_mul b, Semigroup.mul_assoc]

lemma add_cancel_left {α: Type} [ha: has_add α] [hz: has_zero α] [hn: has_neg α] [Group ha.add hz.zero hn.neg] {a b c: α}: a + b = a + c ↔ b = c :=
    iff.intro (assume h: a + b = a + c, by rw [neg_add_elm_add b, h, ←neg_add_elm_add c]) (assume h: b = c, by rw h)
lemma mul_cancel_left {α: Type} [hm: has_mul α] [ho: has_one α] [hi: has_inv α] [Group hm.mul ho.one hi.inv] {a b c: α}: a*b = a*c ↔ b = c :=
    iff.intro (assume h: a*b = a*c, by rw [inv_mul_elm_mul b, h, ←inv_mul_elm_mul c]) (assume h: b = c, by rw h)

lemma add_elm_add_neg {α: Type} [ha: has_add α] [hz: has_zero α] [hn: has_neg α] [Group ha.add hz.zero hn.neg] (a b: α): a = (a + b) + -b :=
calc
    a   = a + 0         : by rw Monoid.add_zero
    ... = (a + b) + -b  : by rw [←add_neg b, Semigroup.add_assoc]
lemma mul_elm_mul_inv {α: Type} [hm: has_mul α] [ho: has_one α] [hi: has_inv α] [Group hm.mul ho.one hi.inv] (a b: α): a = (a*b)*b⁻¹ :=
calc
    a   = a*1        : by rw Monoid.mul_one
    ... = (a*b)*b⁻¹  : by rw [←mul_inv b, Semigroup.mul_assoc]

lemma add_cancel_right {α: Type} [ha: has_add α] [hz: has_zero α] [hn: has_neg α] [Group ha.add hz.zero hn.neg] {a b c: α}: a + c = b + c ↔ a = b :=
    iff.intro (assume h: a + c = b + c, by rw [add_elm_add_neg a, h, ←add_elm_add_neg b]) (assume h: a = b, by rw h)
lemma mul_cancel_right {α: Type} [hm: has_mul α] [ho: has_one α] [hi: has_inv α] [Group hm.mul ho.one hi.inv] {a b c: α}: a*c = b*c ↔ a = b :=
    iff.intro (assume h: a*c = b*c, by rw [mul_elm_mul_inv a, h, ←mul_elm_mul_inv b]) (assume h: a = b, by rw h)

end Group

-- And now a commutative group
class CommGroup {α: Type} (op: α → α → α) (id: α) (inv: α → α) extends Group op id inv := (comm: ∀ a b : α, op a b = op b a)

namespace CommGroup

lemma add_comm {α: Type} [ha: has_add α] [hz: has_zero α] [hn: has_neg α] [CommGroup ha.add hz.zero hn.neg] (a b: α): a + b = b + a := CommGroup.comm ha.add 0 hn.neg a b
lemma mul_comm {α: Type} [hm: has_mul α] [ho: has_one α] [hi: has_inv α] [CommGroup hm.mul ho.one hi.inv] (a b: α): a*b = b*a := CommGroup.comm hm.mul 1 hi.inv a b

end CommGroup
