-- Groups, a fundemental structure of algebra.
--
-- Lean has them built in of course, but I'm going to redefine them
-- myself for the hell of it in keeping with my "from first principles"
-- approach

-- These will be useful within this file
private variable {α : Type}
private variable {op : α → α → α}
private variable {id: α}
private variable {inv: α → α}
local infix `∘` := op
local postfix `⁻`:1025 := inv

-- The standard lean library uses lowercase names for all thse things, so to avoid confusion
-- let's use Camelcase

def Associative {α : Type} (f: α → α → α):= ∀ a b c : α, f (f a b) c = f a (f b c)
def Commutative {α : Type} (f: α → α → α):= ∀ a b : α, f a b = f b a
def LeftIdentity {α : Type} (f: α → α → α) (id: α) := ∀ a : α, f id a = a
def RightIdentity {α : Type} (f: α → α → α) (id: α) := ∀ a : α, f a id = a
def LeftInverse {α: Type} (f: α → α → α) (id: α) (inv: α → α) := ∀ a : α, f (inv a) a = id
def RightInverse {α: Type} (f: α → α → α) (id: α) (inv: α → α) := ∀ a : α, f a (inv a) = id

-- So we'll define our group as a class, so that it can be inferred when needed
-- I'll also create multiplicative and additive versions of the same, for convenience
--
-- We begin with the most basic of group-like objects, the semi-group
class Semigroup {α: Type} (op: α → α → α) := (assoc: (Associative op))

lemma Semigroup.op_assoc (s: Semigroup op) (a b c: α): (a∘b)∘c = a∘(b∘c) := Semigroup.assoc op a b c

-- And then the commutative semigroup
class CommSemigroup {α: Type} (op: α → α → α) extends Semigroup op := (comm: Commutative op)

def CommSemigroup.op_assoc (csg: CommSemigroup op) [s: Semigroup op] := s.op_assoc
lemma CommSemigroup.op_comm (csg: CommSemigroup op) (a b : α): a ∘ b = b ∘ a := CommSemigroup.comm op a b

-- Right so from a Semigroup we can form a Monoid
class Monoid {α: Type} (op: α → α → α) (id: α) extends Semigroup op := (left_id: LeftIdentity op id) (right_id: RightIdentity op id)

namespace Monoid
def op_assoc (m: Monoid op id) [s: Semigroup op] := s.op_assoc
lemma op_id (m:Monoid op id) (a: α): a∘id = a := Monoid.right_id op id a
lemma id_op (m: Monoid op id) (a: α): id∘a = a := Monoid.left_id op id a

lemma id_unique (m: Monoid op id) {e: α}: (∀ a:α, e∘a = a) → e = id :=
assume hl,
calc
    e   = e∘id  : by rw op_id m e
    ... = id    : by rw hl id


end Monoid

-- And a Commutative Monoid
class CommMonoid {α: Type} (op: α → α → α) (id: α) extends CommSemigroup op := (left_id: LeftIdentity op id)
instance CommMonoidIsMonoid {α: Type} (op: α → α → α) (id: α) [cm: CommMonoid op id]: Monoid op id := {assoc:=cm.assoc, left_id:=cm.left_id, right_id:=assume a, by rw [cm.comm, cm.left_id]}

def CommMonoid.op_assoc (m: CommMonoid op id) [m: Monoid op id] := m.op_assoc
def CommMonoid.op_comm (ag: CommMonoid op id) [csg: CommSemigroup op] := csg.op_comm
def CommMonoid.op_id (m: CommMonoid op id) [m: Monoid op id] := m.op_id
def CommMonoid.id_op (m: CommMonoid op id) [m: Monoid op id] := m.id_op

-- And from a monoid we can go to a full Group!
class Group {α: Type} (op: α → α → α) (id: α) (inv: α → α) extends Monoid op id := (left_inv: LeftInverse op id inv) (right_inv: RightInverse op id inv)

namespace Group
def op_assoc (g: Group op id inv) [s: Semigroup op] := s.op_assoc
def op_id (g: Group op id inv) [m: Monoid op id] := m.op_id
def id_op (g: Group op id inv) [m: Monoid op id] := m.id_op

lemma op_inv (g: Group op id inv) (a : α): a∘a⁻ = id := Group.right_inv op id inv a

lemma inv_op (g: Group op id inv) (a : α): a⁻∘a = id := Group.left_inv op id inv a

private lemma inv_op_elm_op (g: Group op id inv) (a b: α): a = b⁻ ∘ (b ∘ a) :=
calc
    a   = op id a       : by rw g.id_op
    ... = (b⁻∘b) ∘ a    : by rw g.inv_op
    ... = b⁻ ∘ (b ∘ a)  : by rw g.op_assoc
lemma cancel_left (g: Group op id inv) {a b c: α}: a∘b = a∘c ↔ b = c :=
iff.intro (
    assume h: a∘b = a∘c,
    by rw [inv_op_elm_op g b, h, ←inv_op_elm_op g c]
) (
    assume h: b = c,
    by rw h
)

private lemma op_elm_op_inv (g: Group op id inv) (a b: α): a = (a ∘ b) ∘ b⁻ :=
calc
    a   = a ∘ id        : by rw g.op_id
    ... = a ∘ (b ∘ b⁻)  : by rw g.op_inv
    ... = (a ∘ b) ∘ b⁻  : by rw g.op_assoc
lemma cancel_right (g: Group op id inv) {a b c: α}: b∘a = c∘a ↔ b = c :=
iff.intro (
    assume h: b∘a = c∘a,
    by rw [op_elm_op_inv g b, h, ←op_elm_op_inv g c]
) (
    assume h: b = c,
    by rw h
)

lemma id_unique (g: Group op id inv) [m: Monoid op id] {e: α}: (∀ a:α, e∘a = a) → e = id := m.id_unique

lemma inv_unique (g: Group op id inv) {a b: α}: b ∘ a = id → b = a⁻ :=
assume h: b ∘ a = id,
suffices b ∘ a = a⁻ ∘ a, from iff.elim_left (cancel_right g) this,
by rw [h, inv_op g]

lemma inv_inv (g: Group op id inv) (a : α): (a⁻)⁻ = a :=
calc
    (a⁻)⁻ = id ∘ (a⁻)⁻        : by rw g.id_op
    ...   = (a ∘ a⁻) ∘ (a⁻)⁻  : by rw g.op_inv
    ...   = a ∘ (a⁻ ∘ (a⁻)⁻)  : by rw g.op_assoc
    ...   = a ∘ id            : by rw g.op_inv
    ...   = a                 : by rw g.op_id

end Group

-- And now an abelian group
class AbelianGroup {α: Type} (op: α → α → α) (id: α) (inv: α → α) extends CommMonoid op id := (left_inv: LeftInverse op id inv)
def AbelianGroup.to_Group {α: Type} {op: α → α → α} {id: α} {inv: α → α} (ag: AbelianGroup op id inv): Group op id inv := {assoc:=ag.assoc, left_id:=ag.left_id, right_id:=assume a, by rw [ag.comm, ag.left_id], left_inv:=ag.left_inv, right_inv:=assume a, by rw [ag.comm, ag.left_inv]}
instance AbelianGroupIsGroup {α: Type} {op: α → α → α} {id: α} {inv: α → α} [ag: AbelianGroup op id inv]: Group op id inv := ag.to_Group

def AbelianGroup.op_assoc (ag: AbelianGroup op id inv) [s: Semigroup op] := s.op_assoc
def AbelianGroup.op_comm (ag: AbelianGroup op id inv) [cm: CommMonoid op id] := cm.op_comm
def AbelianGroup.op_id (ag: AbelianGroup op id inv) [m: Monoid op id] := m.op_id
def AbelianGroup.id_op (ag: AbelianGroup op id inv) [m: Monoid op id] := m.id_op
def AbelianGroup.op_inv (ag: AbelianGroup op id inv) [g: Group op id inv] := g.op_inv
def AbelianGroup.inv_op (ag: AbelianGroup op id inv) [g: Group op id inv] := g.inv_op
lemma AbelianGroup.cancel_left (ag: AbelianGroup op id inv) [g: Group op id inv] {a b c: α}: a∘b = a∘c ↔ b = c := g.cancel_left
lemma AbelianGroup.cancel_right (ag: AbelianGroup op id inv) [g: Group op id inv] {a b c: α}: b∘a = c∘a ↔ b = c := g.cancel_right

-- Some special versions for additive work
class AdditiveSemigroup (α: Type) extends has_add α := (add_assoc_: (Associative add))
instance AdditiveSemigroupIsSemigroup (α: Type) [asg: AdditiveSemigroup α]: Semigroup asg.add := {assoc := asg.add_assoc_}
lemma AdditiveSemigroup.add_assoc {α : Type} (asg: AdditiveSemigroup α) [sg: Semigroup asg.add] (a b c: α): (a+b)+c = a+(b+c) := sg.op_assoc a b c
class AdditiveMonoid (α: Type) extends has_zero α, has_add α := (assoc: Associative add) (left_id: LeftIdentity add 0) (right_id: RightIdentity add 0)
instance AdditiveMonoidIsMonoid (α: Type) [am: AdditiveMonoid α]: Monoid am.add am.zero := {assoc := am.assoc, left_id := am.left_id , right_id := am.right_id}
lemma AdditiveMonoid.add_zero {α: Type} (am: AdditiveMonoid α) [m: Monoid am.add am.zero] (a: α): a + 0 = a := m.op_id a
lemma AdditiveMonoid.zero_add {α: Type} (am: AdditiveMonoid α) [m: Monoid am.add am.zero] (a: α): 0 + a = a := m.id_op a
class AdditiveGroup (α: Type) extends AdditiveMonoid α, has_neg α := (left_inv: ∀ a : α, (-a) + a = 0) (right_inv: ∀ a : α, a  + (-a) = 0)
instance AdditiveGroupIsGroup (α: Type) [ag: AdditiveGroup α]: Group ag.add ag.zero ag.neg := {assoc:=ag.assoc, left_id:=ag.left_id, right_id:=ag.right_id, left_inv:=ag.left_inv, right_inv:=ag.right_inv}
lemma AdditiveGroup.add_neg {α: Type} (ag: AdditiveGroup α) [g: Group ag.add ag.zero ag.neg] (a: α): a + -a = 0 := g.op_inv a
lemma AdditiveGroup.neg_add {α: Type} (ag: AdditiveGroup α) [g: Group ag.add ag.zero ag.neg] (a: α): -a + a = 0 := g.inv_op a
lemma AdditiveGroup.cancel_left {α: Type} (ag: AdditiveGroup α) [g: Group ag.add ag.zero ag.neg] {a b c: α}: a + b = a + c ↔ b = c := g.cancel_left
lemma AdditiveGroup.cancel_right {α: Type} (ag: AdditiveGroup α) [g: Group ag.add ag.zero ag.neg] {a b c: α}: b + a = c + a ↔ b = c := g.cancel_right
class AdditiveAbelianGroup (α: Type) extends AdditiveGroup α := (comm: Commutative add)
def AdditiveAbelianGroup.to_AbelianGroup {α: Type} (aag: AdditiveAbelianGroup α): AbelianGroup aag.add aag.zero aag.neg := {assoc:=aag.assoc, left_id:=aag.left_id, left_inv:=aag.left_inv, comm:=aag.comm}
instance AdditiveAbelianGroupIsAbelianGroup {α: Type} [aag: AdditiveAbelianGroup α]: AbelianGroup aag.add aag.zero aag.neg := aag.to_AbelianGroup
def AdditiveAbelianGroup.to_Group {α: Type} (aag: AdditiveAbelianGroup α): Group aag.add aag.zero aag.neg := aag.to_AbelianGroup.to_Group
lemma AdditiveAbelianGroup.add_comm (aag: AdditiveAbelianGroup α) [ag: AbelianGroup aag.add aag.zero aag.neg] (a b : α): a + b = b + a := ag.op_comm a b

-- Some specialised versions for multiplicative work
class MultiplicativeSemigroup (α: Type) extends has_mul α := (mul_assoc_: (Associative mul))
instance MultiplicativeSemigroupIsSemigroup (α: Type) [msg: MultiplicativeSemigroup α]: Semigroup msg.mul := {assoc := msg.mul_assoc_}
lemma MultiplicativeSemigroup.mul_assoc {α : Type} (msg: MultiplicativeSemigroup α) [sg: Semigroup msg.mul] (a b c: α): (a*b)*c = a*(b*c) := sg.op_assoc a b c
class MultiplicativeMonoid (α: Type) extends has_one α, has_mul α := (assoc: Associative mul) (left_id: ∀ a : α, 1*a = a) (right_id: ∀ a : α, a*1 = a)
instance MultiplicativeMonoidIsMonoid (α: Type) [mm: MultiplicativeMonoid α]: Monoid mm.mul mm.one := {assoc := mm.assoc, left_id := mm.left_id, right_id := mm.right_id}
lemma MultiplicativeMonoid.mul_one {α: Type} (mm: MultiplicativeMonoid α) [m: Monoid mm.mul mm.one] (a: α): a*1 = a := m.op_id a
lemma MultiplicativeMonoid.one_mul {α: Type} (mm: MultiplicativeMonoid α) [m: Monoid mm.mul mm.one] (a: α): 1*a = a := m.id_op a
class MultiplicativeGroup (α: Type) extends MultiplicativeMonoid α, has_inv α := (left_inv: ∀ a : α, a⁻¹*a = 1) (right_inv: ∀ a : α, a*a⁻¹ = 1)
instance MultiplicativeGroupIsGroup (α: Type) [mg: MultiplicativeGroup α]: Group mg.mul mg.one mg.inv := {assoc:=mg.assoc, left_id:=mg.left_id, right_id:=mg.right_id, left_inv:=mg.left_inv, right_inv:=mg.right_inv}
lemma MultiplicativeGroup.mul_inv {α: Type} (mg: MultiplicativeGroup α) [g: Group mg.mul mg.one mg.inv] (a: α): a*a⁻¹ = 1 := g.op_inv a
lemma MultiplicativeGroup.inv_mul {α: Type} (mg: MultiplicativeGroup α) [g: Group mg.mul mg.one mg.inv] (a: α): a⁻¹*a = 1 := g.inv_op a
lemma MultiplicativeGroup.cancel_left {α: Type} (mg: MultiplicativeGroup α) [g: Group mg.mul mg.one mg.inv] {a b c: α}: a*b = a*c ↔ b = c := g.cancel_left
lemma MultiplicativeGroup.cancel_right {α: Type} (mg: MultiplicativeGroup α) [g: Group mg.mul mg.one mg.inv] {a b c: α}: b*a = c*a ↔ b = c := g.cancel_right
class MultiplicativeAbelianGroup (α: Type) extends MultiplicativeGroup α := (comm: Commutative mul)
instance MultiplicativeAbelianGroupIsAbelianGroup (α: Type) [mag: MultiplicativeAbelianGroup α]: AbelianGroup mag.mul mag.one mag.inv := {assoc:=mag.assoc, left_id:=mag.left_id, left_inv:=mag.left_inv, comm:=mag.comm}
lemma MultiplicativeAbelianGroup.mul_comm (mag: MultiplicativeAbelianGroup α) [ag: AbelianGroup mag.mul mag.one mag.inv] (a b : α): a * b = b * a := ag.op_comm a b
