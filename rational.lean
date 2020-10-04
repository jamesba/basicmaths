import .natural
import .integer

-- Here we go! Fractions!

structure fraction := (n: integer) (d: natural) (nz: d≠0)

namespace fraction

open fraction

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

def add (x y: fraction): fraction := ⟨((x.n * y.d) + (y.n * x.d)), (x.d*y.d), natural.mult_nz x.nz y.nz⟩
instance fraction_has_add: has_add fraction  := ⟨add⟩

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

def neg (x: fraction): fraction := ⟨-x.n, x.d, x.nz⟩
instance fraction_has_neg: has_neg fraction  := ⟨neg⟩

lemma neg_invariant (x y: fraction): x ≈ y → ⟦-x⟧ = ⟦-y⟧ :=
    assume h: x.n * y.d = y.n * x.d,
    suffices -x.n * y.d = -y.n * x.d, from quotient.sound this,
    calc
        -x.n * y.d = -(x.n * y.d)  : by rw integer.neg_mult
        ...        = -(y.n * x.d)  : by rw h
        ...        = -y.n * x.d    : by rw integer.neg_mult

def mult (x y: fraction): fraction := ⟨x.n * y.n, x.d * y.d, natural.mult_nz x.nz y.nz⟩
instance fraction_has_mult: has_mul fraction := ⟨mult⟩

end fraction


def rational [s: setoid fraction]: Type := quotient s


namespace rational

open rational

notation n `÷` d := ⟦fraction.mk n d (assume h, natural.no_confusion h)⟧

instance has_coe_integer_rational: has_coe integer rational := ⟨assume n: integer, (n ÷ 1)⟩

def zero : rational := ↑(0: natural)
def one  : rational := ↑(1: natural)

instance rational_has_zero: has_zero rational := ⟨zero⟩
instance rational_has_one: has_one rational := ⟨one⟩


-- addition

def add (x y: rational): rational := quotient.lift_on₂ x y (λ f g: fraction, ⟦f + g⟧) fraction.add_invariant
instance rational_has_add: has_add rational := ⟨add⟩

-- negation

def neg (x :rational): rational := quotient.lift_on x (λ f:fraction, ⟦-f⟧) fraction.neg_invariant
instance rational_has_neg: has_neg rational := ⟨neg⟩


end rational