import .natural
import .integer

--
-- So here we make use of two new features, quotients and subtypes
--
--  Given a type α an a property p: α → Prop we can define a new type
--  { a: α // p a }, which is a type where each element is of the form
--  ⟨a, h⟩, where a : α and h : p a.
--
--  Given a type α and a relation r: α → α → Prop we have new properties
--    * reflexive r := (∀ a : α, r a a)
--    * symmetric r := (∀ a b : α, r a b ↔ r b a)
--    * transitive r := (∀ a b c : α, r a b ∧ r b c → r a c)
--    * equivalence r := reflexive r ∧ symmetric r ∧ transitive r
--
--  Given a type α, a relation r: α → α → Prop and a proof h: equivalence r
--    * s: setoid α is an instance which can be defined as ⟨r, h⟩
--    * and this defines a new type quotient s
--    * given any a : α we have ⟦a⟧ : quotient s
--    * given any a b : α we have the notation a ≈ b := r a b
--    * given any a b : α quotient.sound is a proof a ≈ b → ⟦a⟧ = ⟦b⟧
--    * given any a b : α quotient.exact is a proof ⟦a⟧ = ⟦b⟧ → a ≈ b
--    * given any f: α → α and a proof h: ∀ a b : α, a ≈ b → f a ≈ f b then
--      given x : quotient s, then quotient.lift_on x f h : quotient s, defined
--      such that quotient.lift_on ⟦a⟧ f h = ⟦f a⟧
--    * given any p: (quotient s) → Prop and a proof h: ∀ a : α, p ⟦a⟧ then
--      for any x : (quotient s), quotient.induction_on x h is a proof of p x
--
--   quotient.lift_on₂ and quotient.lift_on₃ are shorthands for using quotient.lift_on
--   repeatedly on a function α → α → α or α → α → α → α respectively.
--

-- Here we go! Fractions!

structure int_nat_pair := (n: integer) (d: natural)

def fraction := {x: int_nat_pair // (x.d ≠ 0)}

namespace fraction

open fraction

def n: fraction → integer := λ x: fraction, x.val.n

def d: fraction → natural := λ x: fraction, x.val.d

def nz (x: fraction): (x.d ≠ 0) := x.2

protected lemma eq: ∀ {x y : fraction}, x.n = y.n → x.d = y.d → x = y
| ⟨⟨xn, xd⟩, hx⟩ ⟨⟨.(xn), .(xd)⟩, hy⟩ rfl rfl := rfl

def equiv (x y: fraction): Prop := x.n * y.d = y.n * x.d

lemma equiv_refl: reflexive equiv := assume x: fraction, eq.refl (x.n * x.d)

lemma equiv_symm: symmetric equiv :=
    assume x y: fraction,
    assume h: x.n * ↑y.d = y.n * ↑x.d,
    eq.symm h

lemma equiv_trans: transitive equiv :=
    assume x y z: fraction,
    assume hxy: x.n * ↑y.d = y.n * ↑x.d,
    assume hyz: y.n * ↑z.d = z.n * ↑y.d,
    have hnz: (integer.from_natural y.d) ≠ 0, from
        assume hc,
        have y.d = 0, by injection hc,
        absurd this y.nz,
    if hyn: y.n = 0 then
        have hxy: x.n * ↑y.d = 0 * ↑y.d, from calc
            x.n * ↑y.d = y.n * ↑x.d  : by rw hxy
            ...        = 0 * ↑x.d    : by rw hyn
            ...        = 0           : by rw integer.zero_mult
            ...        = 0 * ↑y.d    : by rw integer.zero_mult,
        have hyz: z.n * ↑y.d = 0 * ↑y.d, from calc
            z.n * ↑y.d = y.n * ↑z.d  : by rw hyz
            ...        = 0 * ↑z.d    : by rw hyn
            ...        = 0           : by rw integer.zero_mult
            ...        = 0 * ↑y.d    : by rw integer.zero_mult,
        have hxy: x.n = 0, from integer.mult_elim_right hnz hxy,
        have hyz: z.n = 0, from integer.mult_elim_right hnz hyz,
        calc
            x.n * ↑z.d = 0 * ↑z.d   : by rw hxy
            ...        = 0          : by rw integer.zero_mult
            ...        = 0 * ↑x.d   : by rw integer.zero_mult
            ...        = z.n * ↑x.d : by rw hyz
    else
        have y.n * ↑y.d ≠ 0, from
            assume hc: y.n * ↑y.d = 0,
            have hc: y.n * ↑y.d = 0 * ↑y.d, from
                calc
                    y.n * ↑y.d = 0        : by rw hc
                    ...        = ↑y.d * 0 : by rw integer.mult_zero ↑y.d
                    ...        = 0 * ↑y.d : by rw integer.mul_com ↑y.d,
            have y.n = 0, from integer.mult_elim_right hnz hc,
            absurd ‹y.n = 0› hyn,
        suffices (x.n * ↑z.d) * (y.n * ↑y.d) = (z.n * ↑x.d) * (y.n * ↑y.d), from integer.mult_elim_right ‹y.n * ↑y.d ≠ 0› this,
        calc
            (x.n * ↑z.d) * (y.n * ↑y.d) = (x.n * ↑y.d) * (y.n * ↑z.d)  : by rw [integer.mul_com y.n, integer.mul_asoc, ←integer.mul_asoc x.n, integer.mul_com (↑z.d), integer.mul_asoc, ←integer.mul_asoc, integer.mul_com (↑z.d)]
            ...                         = (y.n * ↑x.d) * (z.n * ↑y.d)  : by rw [hxy, hyz]
            ...                         = (z.n * ↑x.d) * (y.n * ↑y.d)  : by rw [integer.mul_asoc, ←integer.mul_asoc y.n, integer.mul_com (↑x.d), integer.mul_com y.n, integer.mul_asoc]

lemma equiv_equiv: equivalence equiv := ⟨equiv_refl, equiv_symm, equiv_trans⟩

instance fraction_setoid: setoid fraction := ⟨equiv, equiv_equiv⟩

instance equiv_decidable: ∀ x y: fraction, decidable (x ≈ y) :=
    assume x y: fraction,
    if h: x.n*y.d = y.n*x.d then
        is_true h
    else
        is_false h

def add (x y: fraction): fraction := ⟨⟨((x.n * y.d) + (y.n * x.d)), (x.d*y.d)⟩, natural.mult_nz x.nz y.nz⟩
instance fraction_has_add: has_add fraction  := ⟨add⟩

lemma add_asoc (x y z : fraction): (x + y) + z = x + (y + z) :=
have hn: ((x + y) + z).n = (x + (y + z)).n, from (
    calc
        ((x + y) + z).n = (x+y).n*z.d + z.n*(x+y).d                    : by refl
        ...             = (x.n*y.d + y.n*x.d)*z.d + z.n*(x.d*y.d)      : by refl
        ...             = x.n*y.d*z.d + y.n*x.d*z.d + z.n*x.d*y.d      : by simp only [integer.add_mult, integer.mul_asoc]
        ...             = x.n*(y.d*z.d) + (y.n*x.d*z.d + z.n*x.d*y.d)  : by rw [integer.add_asoc, integer.mul_asoc]
        ...             = x.n*(y.d*z.d) + (y.n*z.d*x.d + z.n*y.d*x.d)  : by rw [←integer.mul_asoc y.n, integer.mul_com x.d, integer.mul_asoc y.n, ←integer.mul_asoc z.n, integer.mul_com x.d, integer.mul_asoc z.n]
        ...             = x.n*(y.d*z.d) + (y.n*z.d + z.n*y.d)*x.d      : by rw integer.add_mult
        ...             = x.n*(y + z).d + (y + z).n*x.d                : by refl
        ...             = (x + (y + z)).n                              : by refl
),
have hd: ((x + y) + z).d = (x + (y + z)).d, from (show x.d*y.d*z.d = x.d*(y.d*z.d), by rw natural.mult_asoc),
fraction.eq hn hd


lemma add_com (x y : fraction): x + y = y + x :=
have hn: (x + y).n = (y + x).n, from (show x.n*y.d + y.n*x.d = y.n*x.d + x.n*y.d, by rw integer.add_com),
have hd: (x + y).d = (y + x).d, from (show x.d*y.d = y.d*x.d, by rw natural.mult_com),
fraction.eq hn hd

lemma add_invariant (x₁ y₁ x₂ y₂: fraction): x₁ ≈ x₂ → y₁ ≈ y₂ → ⟦x₁+y₁⟧ = ⟦x₂+y₂⟧ :=
    assume hx: x₁.n * x₂.d = x₂.n * x₁.d,
    assume hy: y₁.n * y₂.d = y₂.n * y₁.d,
    suffices (x₁+y₁).n * (x₂+y₂).d = (x₂+y₂).n * (x₁+y₁).d, from quotient.sound this,
    calc
        (x₁+y₁).n * (x₂+y₂).d = ((x₁.n * y₁.d) + (y₁.n * x₁.d)) * (x₂.d * y₂.d)            : by refl
        ...                   = (x₁.n * y₁.d)*(x₂.d * y₂.d) + (y₁.n * x₁.d)*(x₂.d * y₂.d)  : by rw integer.add_mult
        ...                   = (x₁.n * y₁.d)*(x₂.d * y₂.d) + (y₁.n * x₁.d)*(y₂.d * x₂.d)  : by rw integer.mul_com x₂.d
        ...                   = ((x₁.n * y₁.d)*x₂.d)*y₂.d + ((y₁.n * x₁.d)*y₂.d)*x₂.d      : by rw [integer.mul_asoc, integer.mul_asoc]
        ...                   = (x₁.n*(y₁.d*x₂.d))*y₂.d + (y₁.n*(x₁.d*y₂.d))*x₂.d          : by rw [integer.mul_asoc, integer.mul_asoc]
        ...                   = (x₁.n*(x₂.d*y₁.d))*y₂.d + (y₁.n*(y₂.d*x₁.d))*x₂.d          : by rw [integer.mul_com (y₁.d), integer.mul_com (x₁.d)]
        ...                   = (x₁.n*x₂.d)*(y₁.d*y₂.d) + (y₁.n*y₂.d)*(x₁.d*x₂.d)          : by rw [integer.mul_asoc, integer.mul_asoc, integer.mul_asoc, integer.mul_asoc]
        ...                   = (x₂.n*x₁.d)*(y₁.d*y₂.d) + (y₂.n*y₁.d)*(x₁.d*x₂.d)          : by rw [hx, hy]
        ...                   = (x₂.n*y₂.d)*(x₁.d*y₁.d) + (y₂.n*y₁.d)*(x₁.d*x₂.d)          : by rw [integer.mul_com y₁.d, integer.mul_asoc, ←integer.mul_asoc x₂.n, integer.mul_com x₁.d, integer.mul_asoc, ←integer.mul_asoc]
        ...                   = (x₂.n*y₂.d)*(x₁.d*y₁.d) + (y₂.n*y₁.d)*(x₂.d*x₁.d)          : by rw [←integer.mul_com x₁.d]
        ...                   = (x₂.n*y₂.d)*(x₁.d*y₁.d) + (y₂.n*x₂.d)*(x₁.d*y₁.d)          : by rw [integer.mul_asoc (y₂.n*y₁.d), ←integer.mul_asoc y₂.n, integer.mul_com y₁.d, integer.mul_asoc y₂.n, ←integer.mul_asoc (y₂.n*x₂.d), integer.mul_com y₁.d]
        ...                   = ((x₂.n*y₂.d)+(y₂.n*x₂.d))*(x₁.d*y₁.d)                      : by rw integer.add_mult
        ...                   = (x₂+y₂).n * (x₁+y₁).d                                      : by refl


def neg (x: fraction): fraction := ⟨⟨-x.n, x.d⟩, x.nz⟩
instance fraction_has_neg: has_neg fraction  := ⟨neg⟩

lemma neg_invariant (x y: fraction): x ≈ y → ⟦-x⟧ = ⟦-y⟧ :=
    assume h: x.n * y.d = y.n * x.d,
    suffices -x.n * y.d = -y.n * x.d, from quotient.sound this,
    calc
        -x.n * y.d = -(x.n * y.d)  : by rw integer.neg_mult
        ...        = -(y.n * x.d)  : by rw h
        ...        = -y.n * x.d    : by rw integer.neg_mult

lemma neg_neg (x: fraction): -(-x) = x :=
    suffices (-(-x)).n = x.n, from fraction.eq this rfl,
    show -(-x.n) = x.n, by rw ←integer.neg_neg x.n

def mult (x y: fraction): fraction := ⟨⟨x.n * y.n, x.d * y.d⟩, natural.mult_nz x.nz y.nz⟩
instance fraction_has_mult: has_mul fraction := ⟨mult⟩

lemma mult_invariant (x₁ y₁ x₂ y₂: fraction): x₁ ≈ x₂ → y₁ ≈ y₂ → ⟦x₁*y₁⟧ = ⟦x₂*y₂⟧ :=
    assume hx: x₁.n * x₂.d = x₂.n * x₁.d,
    assume hy: y₁.n * y₂.d = y₂.n * y₁.d,
    suffices (x₁.n*y₁.n)*(x₂.d*y₂.d) = (x₂.n*y₂.n)*(x₁.d*y₁.d), from quotient.sound this,
    calc
        (x₁.n*y₁.n)*(x₂.d*y₂.d) = (x₁.n*x₂.d)*(y₁.n*y₂.d)  : by simp
        ...                     = (x₂.n*x₁.d)*(y₂.n*y₁.d)  : by rw [hx, hy]
        ...                     = (x₂.n*y₂.n)*(x₁.d*y₁.d)  : by simp

lemma mult_asoc (x y z: fraction): (x * y) * z = x * (y * z) :=
    have hn: ((x*y)*z).n = (x*(y*z)).n, from (show (x.n*y.n)*z.n = x.n*(y.n*z.n), by rw integer.mul_asoc),
    have hd: ((x*y)*z).d = (x*(y*z)).d, from (show (x.d*y.d)*z.d = x.d*(y.d*z.d), by rw natural.mult_asoc),
    fraction.eq hn hd

lemma mult_com (x y: fraction): x * y = y * x :=
    have hn: (x*y).n = (y*x).n, from (show x.n*y.n = y.n*x.n, by rw integer.mul_com),
    have hd: (x*y).d = (y*x).d, from (show x.d*y.d = y.d*x.d, by rw natural.mult_com),
    fraction.eq hn hd

def non_zero_fraction := {f: fraction // (f.n ≠ 0)}
def inv (x: non_zero_fraction): non_zero_fraction :=
    have (integer.sgn x.val.n) * x.val.d ≠ 0, from integer.nz_mult_nz_nz (mt (iff.elim_right integer.sgn_zero) x.property) (integer.nz_impl_coe_nz x.val.nz),
    ⟨⟨⟨(integer.sgn x.val.n) * x.val.d, integer.abs x.val.n⟩, mt (iff.elim_right integer.abs_zero) x.property⟩, by assumption⟩

lemma inv_invariant {x y: non_zero_fraction}: x.val ≈ y.val → (inv x).val ≈ (inv y).val :=
    assume h: x.val.n*y.val.d = y.val.n*x.val.d,
    have hsgn: integer.sgn x.val.n = integer.sgn y.val.n, from (
        calc
            integer.sgn x.val.n = integer.sgn (x.val.n * y.val.d)   : by rw integer.sgn_mult_nat y.val.nz
            ...                 = integer.sgn (y.val.n * x.val.d)   : by rw h
            ...                 = integer.sgn y.val.n               : by rw ←integer.sgn_mult_nat x.val.nz
    ),
    calc
        (inv x).val.n*(inv y).val.d = (integer.sgn x.val.n * x.val.d)*(integer.abs y.val.n)  : by refl
        ...                         = (integer.sgn x.val.n * integer.abs y.val.n) * x.val.d  : by rw [←integer.mul_asoc, integer.mul_com (x.val.d), integer.mul_asoc]
        ...                         = (integer.sgn y.val.n * integer.abs y.val.n) * x.val.d  : by rw [hsgn]
        ...                         = y.val.n * x.val.d                                      : by rw integer.sgn_mult_abs
        ...                         = x.val.n * y.val.d                                      : by rw h
        ...                         = (integer.sgn x.val.n * integer.abs x.val.n) * y.val.d  : by rw integer.sgn_mult_abs
        ...                         = (integer.sgn y.val.n * integer.abs x.val.n) * y.val.d  : by rw hsgn
        ...                         = (integer.sgn y.val.n * y.val.d) * integer.abs x.val.n  : by rw [←integer.mul_asoc, ←integer.mul_com (y.val.d), integer.mul_asoc]
        ...                         = (inv y).val.n*(inv x).val.d                            : by refl

end fraction


def rational: Type := quotient fraction.fraction_setoid


namespace rational

open rational

notation n `÷` d := ⟦⟨⟨n, d⟩, (assume h, natural.no_confusion h)⟩⟧

instance has_coe_integer_rational: has_coe integer rational := ⟨assume n: integer, (n ÷ 1)⟩

def zero : rational := ↑(0: natural)
def one  : rational := ↑(1: natural)

instance rational_has_zero: has_zero rational := ⟨zero⟩
instance rational_has_one: has_one rational := ⟨one⟩
instance rational_has_zero_: has_zero (quotient fraction.fraction_setoid) := ⟨zero⟩
instance rational_has_one_: has_one (quotient fraction.fraction_setoid) := ⟨one⟩


instance rational_of_fraction_decidable_equality (x y : fraction): decidable (⟦x⟧ = ⟦y⟧) :=
    if h: x ≈ y then is_true (quotient.sound h) else is_false (mt quotient.exact h)

lemma eq_zero (x: fraction): ⟦x⟧ = 0 ↔ x.n = 0 :=
iff.intro (
    assume h: ⟦x⟧ = 0,
    have h: x ≈ ⟨⟨0, 1⟩, (assume h, natural.no_confusion h)⟩, from quotient.exact h,
    have h: x.n*1 = 0*x.d, from h,
    show x.n = 0, by rw [←integer.mult_one x.n, h, integer.zero_mult]
) (
    assume h: x.n = 0,
    suffices x ≈ ⟨⟨0, 1⟩, (assume h, natural.no_confusion h)⟩, from quotient.sound this,
    show x.n*1 = 0*x.d, by rw [integer.mult_one, h, integer.zero_mult]
)

-- addition

def add (x y: rational): rational := quotient.lift_on₂ x y (λ f g: fraction, ⟦f + g⟧) fraction.add_invariant
instance rational_has_add: has_add rational := ⟨add⟩
instance rational_has_add_: has_add (quotient fraction.fraction_setoid) := ⟨add⟩

lemma add_asoc (x y z: rational): (x + y) + z = x + (y + z) := quotient.induction_on₃ x y z (assume a b c: fraction, show ⟦(a+b)+c⟧ = ⟦a+(b+c)⟧, by rw fraction.add_asoc)
lemma add_com (x y: rational): x + y = y + x := quotient.induction_on₂ x y (assume a b: fraction, show ⟦a+b⟧ = ⟦b+a⟧, by rw fraction.add_com)

-- negation

def neg (x :rational): rational := quotient.lift_on x (λ f:fraction, ⟦-f⟧) fraction.neg_invariant
instance rational_has_neg: has_neg rational := ⟨neg⟩

lemma neg_neg (x :rational): -(-x) = x := quotient.induction_on x (assume a: fraction, show ⟦-(-a)⟧ = ⟦a⟧, by rw fraction.neg_neg)

-- subtraction

def sub (x y: rational): rational := x + -y

-- multiplication

def mult (x y: rational): rational := quotient.lift_on₂ x y (λ f g: fraction, ⟦f*g⟧) fraction.mult_invariant
instance rational_has_mult: has_mul rational := ⟨mult⟩

lemma mult_asoc (x y z: rational): (x*y)*z = x*(y*z) := quotient.induction_on₃ x y z (assume a b c: fraction, show ⟦(a*b)*c⟧ = ⟦a*(b*c)⟧, by rw fraction.mult_asoc)
lemma mult_com (x y: rational): x*y = y*x := quotient.induction_on₂ x y (assume a b: fraction, show ⟦a*b⟧ = ⟦b*a⟧, by rw fraction.mult_com)

-- inverse

private def inv_frac_rat (a: fraction) :rational :=
if h: a.n = 0 then
    (0: rational)
else
    ⟦(fraction.inv ⟨a, h⟩).val⟧

lemma inv_frac_rat_nz (x: fraction): (x.n ≠ 0) → inv_frac_rat x = ⟦(fraction.inv ⟨x, ‹x.n ≠ 0›⟩).val⟧ :=
match x with
| ⟨⟨0, d⟩, h⟩                          := assume h, absurd (eq.refl 0) h
| ⟨⟨integer.from_natural (n+1), d⟩, h⟩ := assume h, by refl
| ⟨⟨-[n+1], d⟩, h⟩                     := assume h, by refl
end

lemma inv_frac_rat_invariant (a b: fraction): a ≈ b → inv_frac_rat a = inv_frac_rat b :=
assume h: a.n*b.d = b.n*a.d,
if ha: a.n = 0 then
    have hb: b.n = 0, from (
        suffices b.n*a.d = 0, from integer.mult_nz_eq_z_imp_z this (integer.nz_impl_coe_nz a.nz),
        calc
            b.n*a.d = a.n*b.d  : by rw h
            ...     = 0*b.d    : by rw ha
            ...     = 0        : by rw integer.zero_mult
    ),
    calc
        inv_frac_rat a = inv_frac_rat ⟨⟨a.n, a.d⟩, a.nz⟩  : by refl
        ...            = inv_frac_rat ⟨⟨0, a.d⟩, a.nz⟩    : by rw ha
        ...            = 0                                : by refl
        ...            = inv_frac_rat ⟨⟨0, b.d⟩, b.nz⟩    : by refl
        ...            = inv_frac_rat ⟨⟨b.n, b.d⟩, b.nz⟩  : by rw hb
        ...            = inv_frac_rat b                   : by refl
else
    have hb: b.n ≠ 0, from (
        assume hc: b.n = 0,
        suffices a.n = 0, from absurd this ha,
        suffices a.n*b.d = 0, from integer.mult_nz_eq_z_imp_z this (integer.nz_impl_coe_nz b.nz),
        calc
            a.n*b.d = b.n*a.d : by rw h
            ...     = 0*a.d   : by rw hc
            ...     = 0       : by rw integer.zero_mult
    ),
    have hs: (fraction.inv ⟨a, ha⟩).val ≈ (fraction.inv ⟨b, hb⟩).val, from fraction.inv_invariant h,
    calc
        inv_frac_rat a = ⟦(fraction.inv ⟨a, ha⟩).val⟧  : by rw inv_frac_rat_nz a ha
        ...            = ⟦(fraction.inv ⟨b, hb⟩).val⟧  : by rw quotient.sound hs
        ...            = inv_frac_rat b                : by rw inv_frac_rat_nz b hb

def non_zero_rational := {f: rational // (f ≠ 0)}
def inv (x: non_zero_rational): non_zero_rational :=
⟨quotient.lift_on x.val inv_frac_rat inv_frac_rat_invariant,
(
    suffices ∀ a : rational, a ≠ 0 → quotient.lift_on (a) inv_frac_rat inv_frac_rat_invariant ≠ 0, from this x.val x.property,
    assume a: rational,
    quotient.induction_on a (
        assume f: fraction,
        assume h: ⟦f⟧ ≠ 0,
        have hn: f.n ≠ 0, from iff.elim_left (not_congr (eq_zero f)) h,
        assume hc: quotient.lift_on ⟦f⟧ inv_frac_rat inv_frac_rat_invariant = 0,
        have hc: inv_frac_rat f = 0, from hc,
        have h: inv_frac_rat f = ⟦(fraction.inv ⟨f, hn⟩).val⟧, by rw inv_frac_rat_nz f hn,
        have h: ⟦(fraction.inv ⟨f, hn⟩).val⟧ = 0, from h ▸ hc,
        have h: (fraction.inv ⟨f, hn⟩).val.n = 0, from iff.elim_left (eq_zero (fraction.inv ⟨f, hn⟩).val) h,
        have h: integer.sgn f.n * f.d = 0, from h,
        have h: integer.sgn f.n = 0, from integer.mult_nz_eq_z_imp_z h (integer.nz_impl_coe_nz f.nz),
        have h: f.n = 0, from iff.elim_right integer.sgn_zero h,
        absurd h hn
    )
)⟩

instance nzrational_has_inv: has_inv non_zero_rational := ⟨inv⟩

end rational