import .natural
import .integer

-- Here we go! Rational numbers!

structure rational := (n: integer) (d: natural) (nz: d≠0)

instance has_coe_integer_rational: has_coe integer rational := ⟨λ n, ⟨n, 1, (assume h, natural.no_confusion h)⟩⟩

namespace rational

open rational



notation n `÷` d := rational.mk n d (assume h, natural.no_confusion h)



def zero : rational := ↑(0: natural)
def one  : rational := ↑(1: natural)

instance rational_has_zero: has_zero rational := ⟨zero⟩
instance rational_has_one: has_one rational := ⟨one⟩


-- addition

def add (x y: rational): rational := ⟨((x.n * y.d) + (y.n * x.d)), (x.d*y.d), natural.mult_nz x.nz y.nz⟩
instance rational_has_add: has_add rational := ⟨add⟩

def neg (x: rational): rational := ⟨-x.n, x.d, x.nz⟩
instance rational_has_neg: has_neg rational := ⟨neg⟩

def sub (x y: rational): rational := x + -y
instance rational_has_sub: has_sub rational := ⟨sub⟩

def mult (x y: rational): rational := ⟨x.n * y.n, x.d * y.d, natural.mult_nz x.nz y.nz⟩
instance rational_has_mult: has_mul rational := ⟨mult⟩


end rational