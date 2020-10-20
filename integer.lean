import .natural
import .ring

-- So having constructed the natural numbers I'm now going to construct the integers
inductive integer: Type
| from_natural (n : 𝐍)
| neg_succ_to_natural (n : 𝐍)

notation `𝐙` := integer

-- Coercion from naturals

instance has_coe_natural_integer: has_coe 𝐍 integer := ⟨integer.from_natural⟩

namespace integer

open integer

-- Add some notation for them
notation `-[` n `+1]` := neg_succ_to_natural n
def zero: 𝐙 := from_natural 0
def one: 𝐙 := from_natural 1

instance integer_has_zero: has_zero integer := ⟨zero⟩
instance integer_has_one: has_one integer := ⟨one⟩

-- Add a representation

def repr: 𝐙 → string
| (from_natural n) := (natural.repr n)
| -[n+1] := "-" ++ (natural.repr (natural.succ n))

instance integer_has_repr: has_repr integer := ⟨repr⟩


-- negation
def sub_of_natural (x y : 𝐍): 𝐙 :=
match (natural.sub y x) with
| 0     := from_natural (natural.sub x y)
| (n+1) := -[n+1]
end

def neg: 𝐙 → 𝐙
| (from_natural 0)     := 0
| (from_natural (n+1)) := -[n+1]
| -[n+1]               := from_natural (n+1)

instance integer_has_neg: has_neg integer := ⟨neg⟩

-- addition
def add: 𝐙 → 𝐙 → 𝐙
| (from_natural n) (from_natural m) := from_natural (n + m)
| (from_natural n) -[m+1]           := sub_of_natural n (m+1)
| -[n+1]           (from_natural m) := sub_of_natural m (n+1)
| -[n+1]           -[m+1]           := -[(n+m+1)+1]

instance integer_has_add: has_add integer := ⟨add⟩
instance integer_has_sub: has_sub integer := ⟨λ x y, x + (-y)⟩

def succ: 𝐙 → 𝐙
| (from_natural a) := from_natural (a+1)
| -[0+1]           := from_natural 0
| -[(n+1)+1]       := -[n+1]

def pred: 𝐙 → 𝐙
| (from_natural (n+1)) := from_natural n
| (from_natural 0)     := -[0+1]
| -[n+1]               := -[(n+1)+1]

-- multiplication
def mult: 𝐙 → 𝐙 → 𝐙
| (from_natural n) (from_natural m) := from_natural (n*m)
| (from_natural n) -[m+1]           := -(from_natural (n*(m+1)))
| -[n+1]           (from_natural m) := -(from_natural ((n+1)*m))
| -[n+1]           -[m+1]           := from_natural ((n+1)*(m+1))

instance integer_has_mult : has_mul integer := ⟨mult⟩


-- properties
lemma neg_neg (x : 𝐙): x = -(-x) :=
match x with
| (from_natural 0)     := by refl
| (from_natural (n+1)) := by refl
| -[n+1]               := by refl
end

lemma sub_of_natural_sub_eq_zero {x y: 𝐍} (h: natural.sub y x = 0): sub_of_natural x y = from_natural (natural.sub x y) :=
begin
    unfold sub_of_natural,
    rw h,
    unfold sub_of_natural._match_1
end

lemma sub_of_natural_sub_ne_zero {x y: 𝐍} (h: natural.sub y x ≠ 0): sub_of_natural x y = -from_natural (natural.sub y x) :=
let ⟨z, (h: natural.sub y x = z+1)⟩ := natural.nz_implies_succ h in
begin
    unfold sub_of_natural,
    rw h,
    unfold sub_of_natural._match_1,
    refl
end

lemma succ_of_neg_succ_is_plus_one (n: 𝐍): succ (-[(n+1)+1]) = (-[(n+1)+1]) + 1 :=
have h: natural.sub ((n+1) + 1) 1 = n+1, from natural.succ_sub_one (n+1),
have nz: natural.sub ((n+1) + 1) 1 ≠ 0, from h ▸ (natural.succ_ne_zero n),
show -(from_natural (n+1)) = sub_of_natural 1 ((n+1) + 1), from  h ▸ (sub_of_natural_sub_ne_zero nz)

@[reducible, simp]
lemma succ_is_add_one (x: 𝐙): succ x = x + 1 :=
    match x with
    | (from_natural a) := by refl
    | -[0+1]           := by refl
    | -[(n+1)+1]       := succ_of_neg_succ_is_plus_one n
    end

lemma pred_succ_is_succ_sub_one (n: 𝐍): pred (from_natural (n+1)) = (from_natural (n+1)) - 1 :=
    have 1 ≤ (n+1), from ⟨n, by refl⟩,
    have natural.sub 1 (n+1) = 0, from natural.le_sub_zero ‹1 ≤ (n+1)›,
    suffices (from_natural (n+1)) - 1 = pred (from_natural (n+1)), from eq.symm this,
    show sub_of_natural (n+1) (0+1) = from_natural (natural.sub (n+1) 1), by rw [natural.zero_add_ 1, sub_of_natural_sub_eq_zero ‹natural.sub 1 (n+1) = 0›]

@[reducible, simp]
lemma pred_is_sub_one (x: 𝐙): pred x = x - 1 :=
    match x with
    | (from_natural (n+1)) := pred_succ_is_succ_sub_one n
    | (from_natural 0)     := by refl
    | -[n+1]               := by refl
    end

lemma sub_of_natural_zero (a: 𝐍): sub_of_natural a 0 = from_natural a := sub_of_natural_sub_eq_zero (natural.zero_sub a)

lemma coe_of_pred_is_pred {x: 𝐍}: x≠0 → from_natural (natural.pred x) = pred (from_natural x) :=
    assume h,
    let ⟨y, (h: x = y + 1)⟩ := natural.nz_implies_succ ‹x≠0› in (
        calc
            from_natural (natural.pred x) = from_natural (natural.pred (y+1))  : by rw h
            ...                           = pred (from_natural (y+1))          : by refl
            ...                           = pred (from_natural x)              : by rw h
    )

lemma coe_of_succ_is_succ (x: 𝐍):  from_natural (x+1) = from_natural x + 1 :=
    natural.rec_on x (by refl) (assume n: 𝐍, assume hr: from_natural (n + 1) = ↑n + 1, by refl)

lemma succ_of_neg_succ (x: 𝐍): -[x+1] + 1 = -(from_natural x) :=
    natural.rec_on x (
        by refl
    ) (
        assume n: 𝐍,
        assume hr: -[n+1] + 1 = -from_natural n,
        show -[(n+1)+1] + 1 = succ (-[(n+1)+1]), by rw succ_is_add_one
    )

lemma inv_succ_of_nat_is_pred (n: 𝐍): -(from_natural n + 1) = pred (-from_natural n) :=
    if h: n = 0 then
        suffices -(from_natural n + 1) = pred (-from_natural 0), by rw [this, h],
        show -(from_natural n + 1) = -(from_natural 0 + 1), by rw h
    else
        let ⟨m, (_: n = m+1)⟩ := natural.nz_implies_succ h in
            calc
                -(from_natural n + 1) = -(from_natural (m+1) + 1)  : by rw ‹n=m+1›
                ...                   = pred (-from_natural (m+1)) : by refl
                ...                   = pred (-from_natural n)     : by rw ‹n=m+1›

lemma inv_succ_of_neg_is_pred (n: 𝐍): -(-[n+1] + 1) = pred (-(-[n+1])) :=
    if h: n = 0 then
        calc
            -(-[n+1] + 1) = -(-[0+1] + 1)                   : by rw h
            ...           = pred (from_natural 1)           : by refl
            ...           = pred (from_natural (0+1))       : by rw natural.zero_add_
            ...           = pred (-(-[0+1]))                : by refl
            ...           = pred (- -[n+1])                 : by rw h
    else
        let ⟨m, (_: n = m+1)⟩ := natural.nz_implies_succ h in
            calc
                -(-[n+1] + 1) = -(-[(m+1)+1] + 1)               : by rw ‹n = m+1›
                ...           = -(-from_natural (m+1))          : by rw succ_of_neg_succ
                ...           = pred (-(-[(m+1)+1]))            : by refl
                ...           = pred (- -[n+1])                 : by rw ‹n = m+1›

lemma inv_succ_is_pred (x: 𝐙): -(x + 1) = pred (-x) :=
match x with
| from_natural n := inv_succ_of_nat_is_pred n
| -[n+1]         := inv_succ_of_neg_is_pred n
end

lemma inv_pred_is_succ (x: 𝐙): -(pred x) = -x + 1 :=
    calc
        -(pred x) = -(pred (-(-x)))  : by rw ←neg_neg x
        ...       = -(-(-x + 1))     : by rw inv_succ_is_pred
        ...       = -x + 1           : by rw ←neg_neg (-x + 1)

lemma zero_add_ (x: 𝐙): x = (from_natural 0) + x :=
match x with
| (from_natural n) := show from_natural n = from_natural (0+n), by rw natural.zero_add_
| -[n+1]           := by refl
end

lemma add_zero_ (x: 𝐙): x = x + (from_natural 0) :=
match x with
| (from_natural n) := by refl
| -[n+1]           := by refl
end

lemma pred_succ (x: 𝐙): pred (x+1) = x :=
match x with
| (from_natural n) := by refl
| -[0+1]           := by refl
| -[(n+1)+1]       := by refl
end

lemma succ_pred (x: 𝐙): (pred x) + 1 = x :=
match x with
| (from_natural (n+1)) := by refl
| (from_natural 0)     := by refl
| -[n+1]               := by refl
end

lemma pred_of_sum_is_sum_with_pred_nat_nat (a b : 𝐍): pred (from_natural a + from_natural b) = from_natural a + (pred (from_natural b)) :=
match b with
| 0    := show pred (a + from_natural 0) = a - 1, by rw [pred_is_sub_one, ←add_zero_ a]
| b+1  :=
calc
    pred (from_natural (a+(b+1))) = from_natural (natural.pred ((a+b)+1))                : by rw [←natural.add_asoc, coe_of_pred_is_pred (natural.succ_ne_zero (a+b))]
    ...                           = from_natural a + from_natural (natural.pred (b+1))   : by refl
    ...                           = from_natural a + pred (from_natural (b+1))           : by rw coe_of_pred_is_pred (natural.succ_ne_zero b)
end

lemma sub_of_natural_succ (a b : 𝐍): sub_of_natural (a+1) b = (sub_of_natural a b) + 1 :=
if hz: natural.sub b (a+1) = 0 then
    have b ≤ a+1, from natural.diff_zero hz,
    if h: b = a+1 then
        have natural.sub b a ≠ 0, from natural.lt_sub_nz ⟨⟨1, (natural.add_com a 1) ▸ (eq.symm h)⟩, (eq.symm h) ▸ (natural.ne_succ a)⟩,
        calc
            sub_of_natural (a+1) b = from_natural (natural.sub (a+1) b)    : by rw sub_of_natural_sub_eq_zero hz
            ...                    = from_natural ((a+1) - b)              : by refl
            ...                    = from_natural 0                        : by rw [h, natural.sub_self_zero]
            ...                    = -(from_natural 0)                     : by refl
            ...                    = -[0+1] + 1                            : by rw succ_of_neg_succ 0
            ...                    = -((from_natural (0)) + 1) + 1         : by refl
            ...                    = -(from_natural (b - a)) + 1           : by rw [←natural.sub_self_zero, ←coe_of_succ_is_succ, ←(natural.succ_sub (natural.le_refl a)), h]
            ...                    = -(from_natural (natural.sub b a)) + 1 : by refl
            ...                    = sub_of_natural a b + 1                : by rw sub_of_natural_sub_ne_zero ‹natural.sub b a ≠ 0›
    else
        have b < a+1, from ⟨natural.diff_zero hz, h⟩,
        have b ≤ a, from natural.lt_succ_implies_le this,
        calc
            sub_of_natural (a+1) b = from_natural (natural.sub (a+1) b)    : by rw sub_of_natural_sub_eq_zero hz
            ...                    = from_natural ((a+1) - b)              : by refl
            ...                    = from_natural ((a - b) + 1)            : by rw natural.succ_sub ‹b ≤ a›
            ...                    = from_natural ((natural.sub a b) + 1)  : by refl
            ...                    = (sub_of_natural a b) + 1              : by rw [coe_of_succ_is_succ, sub_of_natural_sub_eq_zero (natural.le_sub_zero ‹b ≤ a›)]
else
    have a+1 < b, from natural.diff_nz hz,
    have a < b, from natural.lt_trans (natural.lt_succ a) (‹a+1 < b›),
    calc
        sub_of_natural (a+1) b = -(from_natural (natural.sub b (a+1)))     : by rw sub_of_natural_sub_ne_zero hz
        ...                    = -(from_natural (natural.pred (b-a)))      : by refl
        ...                    = (-(from_natural (b-a))) + 1               : by rw [coe_of_pred_is_pred (natural.lt_sub_nz ‹a < b›), inv_pred_is_succ]
        ...                    = (-(from_natural (natural.sub b a))) + 1   : by refl
        ...                    = (sub_of_natural a b) + 1                  : by rw sub_of_natural_sub_ne_zero (natural.lt_sub_nz ‹a < b›)

lemma sub_of_natural_pred (a b : 𝐍): sub_of_natural a (b+1) = pred (sub_of_natural a b) :=
if hz: natural.sub (b+1) a = 0 then
    have b < a, from natural.succ_le_implies_lt (natural.diff_zero hz),
    have natural.sub a b ≠ 0, from natural.lt_sub_nz ‹b < a›,
    have natural.sub b a = 0, from natural.le_sub_zero ‹b < a›.left,
    calc
        sub_of_natural a (b+1) = from_natural (natural.sub a (b+1))                : by rw sub_of_natural_sub_eq_zero hz
        ...                    = from_natural (natural.pred (natural.sub a b))     : by refl
        ...                    = pred (sub_of_natural a b)                         : by rw [coe_of_pred_is_pred (‹natural.sub a b ≠ 0›), sub_of_natural_sub_eq_zero ‹natural.sub b a = 0›]
else
    have a ≤ b, from natural.lt_succ_implies_le (natural.diff_nz hz),
    suffices pred (-(from_natural (natural.sub b a))) = pred (sub_of_natural a b), from (
        calc
            sub_of_natural a (b+1) = -from_natural (natural.sub (b+1) a)           : by rw sub_of_natural_sub_ne_zero hz
            ...                    = -from_natural ((b+1) - a)                     : by refl
            ...                    = -from_natural ((b - a) + 1)                   : by rw natural.succ_sub ‹a ≤ b›
            ...                    = -from_natural ((natural.sub b a) + 1)         : by refl
            ...                    = pred (sub_of_natural a b)                     : by rwa [coe_of_succ_is_succ, inv_succ_is_pred]
    ),
    if hab: a = b then
        have natural.sub b a = 0, from hab ▸ (natural.sub_self_zero a),
        calc
            pred (-(from_natural (natural.sub b a))) = pred (-(from_natural (natural.sub a a)))  : by rw hab
            ...                                      = pred (-(from_natural (a - a)))            : by refl
            ...                                      = pred (-(from_natural 0))                  : by rw natural.sub_self_zero
            ...                                      = pred (from_natural 0)                     : by refl
            ...                                      = pred (from_natural (a - a))               : by rw ←natural.sub_self_zero
            ...                                      = pred (from_natural (natural.sub a a))     : by refl
            ...                                      = pred (from_natural (natural.sub a b))     : by rw hab
            ...                                      = pred (sub_of_natural a b)                 : by rw sub_of_natural_sub_eq_zero ‹natural.sub b a = 0›
    else
        have natural.sub b a ≠ 0, from natural.lt_sub_nz ⟨‹a ≤ b›, ‹a ≠ b›⟩,
        show pred (-(from_natural (natural.sub b a))) = pred (sub_of_natural a b), by rw sub_of_natural_sub_ne_zero ‹natural.sub b a ≠ 0›

lemma pred_of_sum_is_sum_with_pred_neg_nat (a b : 𝐍): pred (-[a+1] + from_natural b) = -[a+1] + pred (from_natural b) :=
match b with
| 0   := show pred (-[a+1] + from_natural 0) = pred (-[a+1]), by rw ←add_zero_ (-[a+1])
| b+1 :=
calc
    pred (sub_of_natural (b+1) (a+1))  = sub_of_natural b (a+1)                 : by rw [sub_of_natural_succ, pred_succ]
    ...                                = -[a+1] + from_natural b                : by refl
    ...                                = -[a+1] + (pred (from_natural (b+1)))   : by rw [←pred_succ (from_natural b), coe_of_succ_is_succ b]
end

lemma pred_of_sum_is_sum_with_pred_nat_neg (a b : 𝐍): pred (from_natural a + -[b+1]) = from_natural a + pred(-[b+1]) :=
show pred (sub_of_natural a (b+1)) = sub_of_natural a ((b+1)+1), by rw ←sub_of_natural_pred


lemma pred_of_sum_is_sum_with_pred_neg_neg (a b : 𝐍): pred (-[a+1] + -[b+1]) = -[a+1] + pred(-[b+1]) :=
show -[((a+b+1)+1)+1] = -[(a+(b+1)+1)+1], by rw natural.add_asoc a


lemma pred_of_sum_is_sum_with_pred (x y : 𝐙): pred (x + y) = x + (pred y) :=
match x, y with
| from_natural a, from_natural b := pred_of_sum_is_sum_with_pred_nat_nat a b
| -[a+1],         from_natural b := pred_of_sum_is_sum_with_pred_neg_nat a b
| from_natural a, -[b+1]         := pred_of_sum_is_sum_with_pred_nat_neg a b
| -[a+1],         -[b+1]         := pred_of_sum_is_sum_with_pred_neg_neg a b
end

lemma sub_of_natural_of_add_asoc (a b c: 𝐍): sub_of_natural (a + b) c = from_natural a + sub_of_natural b c :=
    natural.rec_on c (
        calc
            sub_of_natural (a + b) 0 = from_natural (a + b)                   : by rw sub_of_natural_zero
            ...                      = from_natural a + from_natural b        : by refl
            ...                      = from_natural a + (sub_of_natural b 0)  : by rw sub_of_natural_zero
    ) (
        assume n: 𝐍,
        assume hr: sub_of_natural (a + b) n = from_natural a + sub_of_natural b n,
        if habz: natural.sub (n+1) (a+b) = 0 then
            if hbz: natural.sub (n+1) b = 0 then
                calc
                    sub_of_natural (a + b) (n+1) = from_natural (natural.sub (a + b) (n+1))             : by rw sub_of_natural_sub_eq_zero habz
                    ...                          = from_natural ((a + b) - (n+1))                       : by refl
                    ...                          = from_natural (a + (b - (n+1)))                       : by rw natural.add_sub_asoc hbz
                    ...                          = from_natural a + from_natural (natural.sub b (n+1))  : by refl
                    ...                          = from_natural a + sub_of_natural b (n+1)              : by rw sub_of_natural_sub_eq_zero hbz
            else
                have n < a+b, from natural.succ_le_implies_lt (natural.diff_zero habz),
                have b ≤ n, from natural.lt_succ_implies_le (natural.diff_nz hbz),
                suffices from_natural a + pred (sub_of_natural b n)=from_natural a + sub_of_natural b (n+1), from (
                    calc
                        sub_of_natural (a + b) (n+1) = from_natural (natural.sub (a+b) (n+1))                    : by rw sub_of_natural_sub_eq_zero habz
                        ...                          = from_natural (natural.pred ((a+b) - n))                   : by refl
                        ...                          = pred (from_natural ((a+b) - n))                           : by rw [coe_of_pred_is_pred (natural.lt_sub_nz ‹n < a+b›)]
                        ...                          = pred (from_natural (natural.sub (a+b) n))                 : by refl
                        ...                          = from_natural a + sub_of_natural b (n+1)                   : by rwa [←sub_of_natural_sub_eq_zero (natural.le_sub_zero ‹n < a+b›.left), hr, pred_of_sum_is_sum_with_pred]
                ),
                suffices from_natural a + pred (sub_of_natural b n) = from_natural a + -(from_natural ((n - b) + 1)), from (
                    calc
                        from_natural a + pred (sub_of_natural b n) = from_natural a + -(from_natural ((n - b) + 1))            : by assumption
                        ...                                        = from_natural a + -(from_natural ((n+1) - b))              : by rw natural.succ_sub ‹b ≤ n›
                        ...                                        = from_natural a + -(from_natural (natural.sub (n+1) b))    : by refl
                        ...                                        = from_natural a + sub_of_natural b (n+1)                   : by rw sub_of_natural_sub_ne_zero hbz
                ),
                if hnb: b = n then
                    have natural.sub n b = 0, from (
                        calc
                            natural.sub n b = n - b : by refl
                            ...             = n - n : by rw hnb
                            ...             = 0     : by rw natural.sub_self_zero
                    ),
                    calc
                        from_natural a + pred (sub_of_natural b n) = from_natural a + pred (from_natural (natural.sub n n))    : by rw [sub_of_natural_sub_eq_zero ‹natural.sub n b = 0›, hnb]
                        ...                                        = from_natural a + pred (from_natural (n - n))              : by refl
                        ...                                        = from_natural a + pred (from_natural 0)                    : by rw natural.sub_self_zero
                        ...                                        = from_natural a + (-(from_natural 1))                      : by refl
                        ...                                        = from_natural a + (-(from_natural (0+1)))                  : by rw natural.zero_add_ 1
                        ...                                        = from_natural a + (-(from_natural ((n - b)+1)))            : by rw [←natural.sub_self_zero n, ←hnb]
                else
                    show from_natural a + pred (sub_of_natural b n) = from_natural a + -(from_natural ((natural.sub n b) + 1)),
                    by rw [sub_of_natural_sub_ne_zero (natural.lt_sub_nz ⟨‹b ≤ n›, hnb⟩), ←inv_succ_is_pred, coe_of_succ_is_succ]
        else
            have a+b ≤ n, from natural.lt_succ_implies_le (natural.diff_nz habz),
            suffices pred (-(from_natural (n - (a+b)))) = pred (sub_of_natural (a+b) n), from (
                calc
                    sub_of_natural (a+b) (n+1) = -(from_natural (natural.sub (n+1) (a+b)))             : by rw sub_of_natural_sub_ne_zero habz
                    ...                        = -(from_natural ((n+1) - (a+b)))                       : by refl
                    ...                        = from_natural a + sub_of_natural b (n+1)               : by rw [natural.succ_sub ‹a+b ≤ n›, coe_of_succ_is_succ, inv_succ_is_pred, this, hr, pred_of_sum_is_sum_with_pred, sub_of_natural_pred]
            ),
            if h:a+b = n then
                have natural.sub n (a+b) = 0, from h ▸ (natural.sub_self_zero (a+b)),
                calc
                    pred (-(from_natural (n - (a+b)))) = pred (-(from_natural 0))                      : by rw [h, natural.sub_self_zero]
                    ...                                = pred (from_natural 0)                         : by refl
                    ...                                = pred (from_natural ((a+b) - n))               : by rw [←natural.sub_self_zero, h]
                    ...                                = pred (from_natural (natural.sub (a+b) n))     : by refl
                    ...                                = pred (sub_of_natural (a+b) n)                 : by rw sub_of_natural_sub_eq_zero ‹natural.sub n (a+b) = 0›
            else
                have natural.sub n (a+b) ≠ 0, from natural.lt_sub_nz ⟨‹a+b ≤ n›, ‹a + b ≠ n›⟩,
                show pred (-(from_natural (natural.sub n (a+b)))) = pred (sub_of_natural (a+b) n), by rw sub_of_natural_sub_ne_zero ‹natural.sub n (a+b) ≠ 0›
    )

lemma add_com (x y : 𝐙): x + y = y + x :=
match x, y with
| from_natural a, from_natural b := show from_natural (a+b) = from_natural (b+a), by rw natural.add_com
| from_natural a, -[b+1]         := by refl
| -[a+1],         from_natural b := by refl
| -[a+1],         -[b+1]         := show -[(a+b+1)+1] = -[(b+a+1)+1], by rw natural.add_com a b
end

lemma sub_of_natural_of_add_right_asoc (a b c: 𝐍): sub_of_natural (a + b) c = sub_of_natural a c + from_natural b:=
calc
    sub_of_natural (a+b) c = sub_of_natural (b+a) c                 : by rw natural.add_com
    ...                    = from_natural b + sub_of_natural a c    : by rw sub_of_natural_of_add_asoc
    ...                    = (sub_of_natural a c) + from_natural b  : by rw add_com

lemma subnat_of_sub {a b : 𝐍}: natural.sub b a = 0 → (∀ c: 𝐍, sub_of_natural (a - b) c = sub_of_natural a (b+c)) :=
    assume h: natural.sub b a = 0,
    assume c: 𝐍,
    have b ≤ a, from natural.diff_zero h,
    if habc: b+c ≤ a then
        have c ≤ a-b, from (
            have b+c ≤ (a-b)+b, by rwa natural.sub_cancel_same ‹b ≤ a›,
            have b+c ≤ b+(a-b), from (natural.add_com (a-b) b) ▸ (‹b+c ≤ (a-b)+b›),
            iff.elim_left natural.le_add_cancel_left (‹b+c ≤ b+(a-b)›)
        ),
        calc
            sub_of_natural (a-b) c = from_natural (natural.sub (a-b) c)           : by rw sub_of_natural_sub_eq_zero (natural.le_sub_zero ‹c ≤ a - b›)
            ...                    = from_natural ((a-b)-c)                       : by refl
            ...                    = from_natural (a - (b+c))                     : by rw natural.sub_of_sub
            ...                    = from_natural (natural.sub a (b+c))           : by refl
            ...                    = sub_of_natural a (b+c)                       : by rw sub_of_natural_sub_eq_zero (natural.le_sub_zero habc)
    else
        have a < b+c, from (iff.elim_left natural.not_le) habc,
        have a-b < c, from (
            have (a-b)+b < b+c, by rwa natural.sub_cancel_same ‹b ≤ a›,
            have b+(a-b) < b+c, from (natural.add_com (a-b) b) ▸ ‹(a-b)+b < b+c›,
            iff.elim_left natural.lt_add_cancel_left ‹b+(a-b) < b+c›
        ),
        calc
            sub_of_natural (a-b) c = -(from_natural (natural.sub c (a-b)))        : by rw sub_of_natural_sub_ne_zero (natural.lt_sub_nz ‹a-b < c›)
            ...                    = -(from_natural (c - (a-b)))                  : by refl
            ...                    = -(from_natural ((b+c) - a))                  : by rw [←natural.sub_cancel_right, natural.sub_cancel_same ‹b ≤ a›, natural.add_com]
            ...                    = -(from_natural (natural.sub (b+c) a))        : by refl
            ...                    = sub_of_natural a (b+c)                       : by rw sub_of_natural_sub_ne_zero (natural.lt_sub_nz ‹a < b+c›)

lemma sub_of_natural_self (a : 𝐍): sub_of_natural a a = from_natural 0 :=
    have h: natural.sub a a = 0, from natural.sub_self_zero a,
    show sub_of_natural a a = from_natural 0, by rw [sub_of_natural_sub_eq_zero h, h]

lemma inv_sub_of_natural (a b: 𝐍): -(sub_of_natural a b) = sub_of_natural b a :=
if heq: b = a then
    calc
        -(sub_of_natural a b) = -(from_natural 0)     : by rw [heq, sub_of_natural_self]
        ...                   = from_natural 0        : by refl
        ...                   = sub_of_natural b a    : by rw [←sub_of_natural_self, heq]
else
    if hba: natural.sub b a = 0 then
        show -(sub_of_natural a b) = sub_of_natural b a,
        by rw [sub_of_natural_sub_eq_zero hba, sub_of_natural_sub_ne_zero (natural.lt_sub_nz ⟨(natural.diff_zero hba), heq⟩)]
    else
        show -(sub_of_natural a b) = sub_of_natural b a,
        by rw [sub_of_natural_sub_ne_zero hba, ←neg_neg (from_natural (natural.sub b a)), sub_of_natural_sub_eq_zero (natural.le_sub_zero (natural.diff_nz hba).left)]

lemma neg_add (x y: 𝐙): -(x + y) = -x + -y :=
match x, y with
| x,                0                := show -(x + from_natural 0) = -x + from_natural 0, by rw [←add_zero_ x, ←add_zero_ (-x)]
| 0,                y                := show -(from_natural 0 + y) = from_natural 0 + -y, by rw [←zero_add_ y, ←zero_add_ (-y)]
| from_natural a+1, from_natural b+1 := show -(from_natural ((a+1)+(b+1))) = -(from_natural (a+b+1+1)), by rw [←natural.add_asoc (a+1), natural.add_asoc a 1, natural.add_com 1 b, natural.add_asoc a b 1]
| from_natural a+1, -[b+1]           := show -(sub_of_natural (a+1) (b+1)) = sub_of_natural (b+1) (a+1), by rw inv_sub_of_natural
| -[a+1],           from_natural b+1 := show -(sub_of_natural (b+1) (a+1)) = sub_of_natural (a+1) (b+1), by rw inv_sub_of_natural
| -[a+1],           -[b+1]           :=
calc
    from_natural (a+b+1+1) = from_natural (a+(b+1)+1)                 : by rw natural.add_asoc a b 1
    ...                    = from_natural (a+(1+b)+1)                 : by rw natural.add_com b 1
    ...                    = from_natural ((a+1)+(b+1))               : by rw [←natural.add_asoc a 1 b, natural.add_asoc (a+1) b 1]
end

lemma neg_neg_add (x y: 𝐙): (x + y) = -(-x + -y) := by rw [neg_neg (x + y), ←neg_add x y]

lemma add_nn_nn_nn_asoc (a b c: 𝐍):
(from_natural a + from_natural b) + from_natural c = from_natural a + (from_natural b + from_natural c) :=
    show from_natural ((a + b) + c) = from_natural (a + (b + c)), by rw natural.add_asoc

lemma add_nn_nn_ng_asoc (a b c: 𝐍):
(from_natural a + from_natural b) + -[c+1] = from_natural a + (from_natural b + -[c+1]) :=
    show sub_of_natural (a+b) (c+1) = from_natural a + (sub_of_natural b (c+1)),
    by rw sub_of_natural_of_add_asoc

lemma add_nn_ng_nn_asoc (a b c: 𝐍):
(from_natural a + -[b+1]) + from_natural c = from_natural a + (-[b+1] + from_natural c) :=
    show (sub_of_natural a (b+1)) + from_natural c = from_natural a + sub_of_natural c (b+1),
    by rw [←sub_of_natural_of_add_right_asoc, sub_of_natural_of_add_asoc]

lemma add_nn_ng_ng_asoc (a b c: 𝐍):
(from_natural a + -[b+1]) + -[c+1] = from_natural a + (-[b+1] + -[c+1]) :=
    if hbaz: natural.sub (b+1) a = 0 then
        calc
            (sub_of_natural a (b+1)) + -[c+1]  = (from_natural (natural.sub a (b+1))) + -[c+1]    : by rw sub_of_natural_sub_eq_zero hbaz
            ...                                = sub_of_natural (a - (b+1)) (c+1)                 : by refl
            ...                                = sub_of_natural a ((b+1)+(c+1))                   : by rw subnat_of_sub hbaz
            ...                                = sub_of_natural a ((b+c+1)+1)                     : by rw [←natural.add_asoc (b+1), natural.add_asoc b 1 c, natural.add_com 1 c, natural.add_asoc b c]
    else
        calc
            (sub_of_natural a (b+1)) + -[c+1]  = -(from_natural (natural.sub (b+1) a)) + -[c+1]                : by rw sub_of_natural_sub_ne_zero hbaz
            ...                                = -(from_natural (natural.sub (b+1) a)) + -(from_natural (c+1)) : by refl
            ...                                = -((from_natural (natural.sub (b+1) a)) + from_natural (c+1))  : by rw neg_add
            ...                                = -((sub_of_natural (b+1) a) + from_natural (c+1))              : by rw sub_of_natural_sub_eq_zero (natural.sub_nz_implies_anti_sum_zero hbaz)
            ...                                = -(sub_of_natural ((b+1)+(c+1))) a                             : by rw ←sub_of_natural_of_add_right_asoc
            ...                                = sub_of_natural a ((b+1)+(c+1))                                : by rw inv_sub_of_natural
            ...                                = sub_of_natural a ((b+c+1)+1)                                  : by rw [←natural.add_asoc (b+1), natural.add_asoc b 1 c, natural.add_com 1 c, natural.add_asoc b c]

lemma neg_add_add_left (x y z: 𝐙): (-x + y) + z = -((x + -y) + -z) :=
    calc
        (-x + y) + z = -(-(-x + y) + -z)    : by rw neg_neg_add
        ...          = -((-(-x) + -y) + -z) : by rw neg_add (-x) y
        ...          = -((x + -y) + -z)     : by rw ←neg_neg x

lemma neg_add_add_right (x y z: 𝐙): -(x + (-y + -z)) = -x + (y + z) :=
    calc
        -(x + (-y + -z)) = -x + -(-y + -z)   : by rw neg_add
        ...              = -x + -(-(y + z))  : by rw neg_add y z
        ...              = -x + (y + z)      : by rw ←neg_neg (y + z)

lemma neg_assoc {x y z: 𝐙}: (x + (-y)) + (-z) = x + ((-y) + (-z)) → (-x + y) + z = -x + (y + z) :=
    assume h: (x + -y) + -z = x + (-y + -z),
    calc
        ((-x + y) + z) = -((x + -y) + -z)  : by rw neg_add_add_left
        ...            = -(x + (-y + -z))  : by rw h
        ...            = -x + (y + z)      : by rw neg_add_add_right

lemma add_ab0_asoc (a b : 𝐙): (a + b) + 0 = a + (b + 0) :=
    show (a + b) + from_natural 0 = a + (b + from_natural 0),
    by rw [←add_zero_ (a+b), ←add_zero_ b]

lemma add_a0b_asoc (a b : 𝐙): (a + 0) + b = a + (0 + b) :=
    show (a + from_natural 0) + b = a + (from_natural 0 + b),
    by rw [←add_zero_ a, ←zero_add_ b]

lemma add_asoc_nn (a : 𝐍) (y z : 𝐙): (from_natural a + y) + z = from_natural a + (y + z) :=
match y, z with
| from_natural b,     from_natural c     := add_nn_nn_nn_asoc a b c
| from_natural b,     -[c+1]             := add_nn_nn_ng_asoc a b c
| -[b+1],             from_natural c     := add_nn_ng_nn_asoc a b c
| -[b+1],             -[c+1]             := add_nn_ng_ng_asoc a b c
end

lemma add_asoc (x y z : 𝐙): (x + y) + z = x + (y + z) :=
match x with
| from_natural a := add_asoc_nn a y z
| -[a+1]         := neg_assoc (add_asoc_nn (a+1) (-y) (-z))
end

-- Finally! Addition is associative and commutative!

@[reducible]
instance integer_decidable_eq: decidable_eq integer
| (from_natural a) (from_natural b) := if h: a = b then is_true (by rw h) else is_false (assume heq, absurd (by injection heq) h)
| (from_natural a) -[b+1]           := is_false (assume h, integer.no_confusion h)
| -[a+1]           (from_natural b) := is_false (assume h, integer.no_confusion h)
| -[a+1]           -[b+1]           := if h: a = b then is_true (by rw h) else is_false (assume heq, absurd (by injection heq) h)

def le (x y : 𝐙): Prop := ∃ c : 𝐍, (from_natural c) + x = y
instance integer_has_le: has_le integer := ⟨le⟩

def lt (x y : 𝐙): Prop := (x ≤ y) ∧ (x ≠ y)
instance integer_has_lt: has_lt integer := ⟨lt⟩

lemma coe_ge_zero {x :𝐙}: 0 ≤ x ↔ ∃ a: 𝐍, x = from_natural a :=
    iff.intro (
        assume ⟨(a: 𝐍), (h:(from_natural a) + 0 = x)⟩,
        suffices x = from_natural a, from ⟨a, this⟩,
        show x = (from_natural a) + 0, by rw h
    ) (
        assume ⟨a, (h: x = from_natural a)⟩,
        suffices x = from_natural a + 0, from ⟨a, eq.symm this⟩,
        show x = from_natural a + 0, from h
    )

lemma coe_not_lt_zero (a: 𝐍): ¬(from_natural a < 0) :=
    assume ⟨⟨b, (h: from_natural (b + a) = 0)⟩, (heq: from_natural a ≠ 0)⟩,
    have h: b + a = 0, by injection h,
    have heq: a ≠ 0, from assume :a=0, absurd (congr_arg from_natural ‹a=0›) heq,
    suffices a = 0, from absurd this heq,
    natural.zero_sum (by rw [natural.add_com a b, h])

lemma add_neg (x: 𝐙): x + (-x) = 0 :=
match x with
| (from_natural 0)   := by refl
| (from_natural a+1) :=
have hz: natural.sub (a+1) (a+1) = 0, from natural.sub_self_zero (a+1),
calc
    (from_natural (a+1)) + -(from_natural (a+1)) = from_natural (a+1) + -[a+1]             : by refl
    ...                                          = sub_of_natural (a+1) (a+1)              : by refl
    ...                                          = from_natural (natural.sub (a+1) (a+1))  : by rw sub_of_natural_sub_eq_zero hz
    ...                                          = from_natural 0                          : by rw hz
    ...                                          = 0                                       : by refl
| (-[a+1])           :=
have hz: natural.sub (a+1) (a+1) = 0, from natural.sub_self_zero (a+1),
calc
    -[a+1] + -(-[a+1]) = -[a+1] + from_natural (a+1)             : by refl
    ...                = sub_of_natural (a+1) (a+1)              : by refl
    ...                = from_natural (natural.sub (a+1) (a+1))  : by rw sub_of_natural_sub_eq_zero hz
    ...                = from_natural 0                          : by rw hz
    ...                = 0                                       : by refl

end

lemma neg_lt_zero {x :𝐙}: x < 0 ↔ ∃ a: 𝐍, x = -[a+1] :=
    iff.intro (
        match x with
        | from_natural a := assume h, absurd h (coe_not_lt_zero a)
        | -[a+1]         := assume h: -[a+1] < 0, ⟨a, by refl⟩
        end
    ) (
        assume ⟨a, (h: x = -[a+1])⟩,
        have x ≠ 0, from assume :x=0, suffices -[a+1]=0, from integer.no_confusion ‹-[a+1]=0›, by rw [←h, ‹x=0›],
        suffices ↑(a+1) + -[a+1] = 0, from ⟨⟨(a+1), (eq.symm h) ▸ this⟩, ‹x≠0›⟩,
        add_neg (a+1)
    )

lemma pos_gt_zero {x : 𝐙}: x > 0 ↔ ∃ a: 𝐍, x = from_natural a ∧ a ≠ 0 :=
    iff.intro (
        match x with
        | from_natural 0     := assume ⟨(hle: 0 ≤ 0), (lne: 0 ≠ 0)⟩, absurd (eq.refl 0) lne
        | from_natural (a+1) := assume ⟨(hle: 0 ≤ ↑(a+1)), (lne: 0 ≠ ↑(a+1))⟩, ⟨a+1, ⟨by refl, natural.succ_ne_zero a⟩⟩
        | -[a+1]             := assume ⟨⟨c, (hle: from_natural (c + 0) = -[a+1])⟩, (lne: 0 ≠ -[a+1])⟩, integer.no_confusion hle
        end
    ) (
        assume ⟨a, ⟨(hx: x = from_natural a), (hnz: a ≠ 0)⟩⟩,
        have hnz: from_natural a ≠ 0, from assume hc, absurd (by injection hc) hnz,
        have hnz: x ≠ 0, from (eq.symm hx) ▸ hnz,
        ⟨⟨a, eq.symm hx⟩, ne.symm hnz⟩
    )

lemma coe_le {a b: 𝐍}: a ≤ b ↔ from_natural a ≤ from_natural b :=
    iff.intro (
        assume ⟨c, (h: c+a=b)⟩,
        suffices from_natural (c + a) = from_natural b, from ⟨c, this⟩,
        by rw h
    ) (
        assume ⟨c, (h: from_natural (c + a) = from_natural b)⟩,
        ⟨c, by injection h⟩
    )

lemma sub_of_sub (x y z: 𝐙): (x - y) - z = (x - (y+z)) :=
    calc
        (x - y) - z = (x + -y) + -z   : by refl
        ...         = x + (-y + -z)   : by rw add_asoc
        ...         = x + -(y + z)    : by rw neg_add
        ...         = x - (y + z)     : by refl

lemma sub_self (x: 𝐙): x - x = 0 :=
match x with
| from_natural 0     := by refl
| from_natural (a+1) := sub_of_natural_self (a+1)
| -[a+1]             := sub_of_natural_self (a+1)
end

lemma neg_le {a b: 𝐍}: a ≤ b ↔ -[b+1] ≤ -[a+1] :=
    iff.intro (
        assume ⟨c, (h: c+a=b)⟩,
        suffices from_natural c + -[b+1] = -[a+1], from ⟨c, this⟩,
        calc
            from_natural c + -[b+1] = (from_natural c) - (from_natural (b+1))               : by refl
            ...                     = (from_natural c) - (from_natural b + from_natural 1)  : by refl
            ...                     = (from_natural c - from_natural b) - from_natural 1    : by rw sub_of_sub
            ...                     = (↑c - ↑b) - 1                                         : by refl
            ...                     = (↑c - ↑(c+a)) - 1                                     : by rw h
            ...                     = (↑c - (↑c + ↑a)) - 1                                  : by refl
            ...                     = ((↑c - ↑c) - ↑a) - 1                                  : by rw ←sub_of_sub
            ...                     = (0 - ↑a) - 1                                          : by rw sub_self
            ...                     = (0 - (↑a + 1))                                        : by rw sub_of_sub
            ...                     = (0 - ↑(a+1))                                          : by refl
            ...                     = -[a+1]                                                : by refl
    ) (
        assume ⟨c, (h: ↑c  - (↑b+1) = -(↑a+1))⟩,
        suffices c+a=b, from ⟨c, this⟩,
        suffices from_natural (c+a) = (from_natural b), by injection this,
        calc
            from_natural (c+a) = ↑c + ↑a                          : by refl
            ...                = (↑c - 0) + ↑a                    : by refl
            ...                = (↑c - ((↑b+1) - (↑b+1))) + ↑a    : by rw sub_self
            ...                = (↑c - ((↑b+1) + -(↑b+1))) + ↑a   : by refl
            ...                = ((↑c - (↑b+1)) - -(↑b+1)) + ↑a   : by rw sub_of_sub
            ...                = ((↑c - (↑b+1)) + (↑b+1)) + ↑a    : by refl
            ...                = (↑a + -↑a + -1) + (↑b+1)         : by rw [h, neg_add, add_com, add_asoc ↑a, ←add_asoc ↑a]
            ...                = ((↑a - ↑a) + -1) + (↑b+1)        : by refl
            ...                = (0 + -1) + (↑b+1)                : by rw sub_self
            ...                = -1 + (↑b+1)                      : by refl
            ...                = ↑b + (1 + -1)                    : by rw [add_com, add_asoc]
            ...                = ↑b + 0                           : by refl
            ...                = ↑b                               : by refl
    )

lemma coe_lt {a b: 𝐍}: a < b ↔ from_natural a < from_natural b :=
    iff.intro (
        assume ⟨hle, hne⟩,
        have hne: from_natural a ≠ from_natural b, from (
            assume hc: from_natural a = from_natural b,
            absurd (by injection hc) hne
        ),
        ⟨iff.elim_left coe_le hle, hne⟩
    ) (
        assume ⟨hle, hne⟩,
        have hne: a ≠ b, from (
            assume hc: a = b,
            absurd (congr_arg from_natural hc) hne
        ),
        ⟨iff.elim_right coe_le hle, hne⟩
    )

lemma neg_lt {a b: 𝐍}: a < b ↔ -[b+1] < -[a+1] :=
    iff.intro (
        assume ⟨hle, hne⟩,
        have hne: -[b+1] ≠ -[a+1], from (
            assume hc: -[b+1] = -[a+1],
            absurd (by injection hc) (ne.symm hne)
        ),
        ⟨iff.elim_left neg_le hle, hne⟩
    ) (
        assume ⟨hle, hne⟩,
        have hne: a ≠ b, from (
            assume hc: a = b,
            absurd (congr_arg neg_succ_to_natural hc) (ne.symm hne)
        ),
        ⟨iff.elim_right neg_le hle, hne⟩
    )

lemma neg_lt_coe (a b: 𝐍): -[a+1] < from_natural b :=
    have hne: -[a+1] ≠ ↑b, from assume hc, integer.no_confusion hc,
    suffices -[a+1] ≤ ↑b, from ⟨this, hne⟩,
    suffices ↑(b+(a+1)) - ↑(a+1) = ↑b, from ⟨b+(a+1), this⟩,
    calc
        from_natural (b+(a+1)) - ↑(a+1) = from_natural (b+(a+1)) - ↑(a+1)  : by refl
        ...                             = (↑b + ↑(a+1)) + -↑(a+1)          : by refl
        ...                             = (↑b) + (↑(a+1) + -(↑(a+1)))      : by rw add_asoc
        ...                             = ↑b + (↑(a+1) - ↑(a+1))           : by refl
        ...                             = ↑b + 0                           : by rw sub_self
        ...                             = ↑b                               : by refl

lemma coe_not_le_neg (a b: 𝐍): ¬(from_natural a ≤ -[b+1]) :=
    assume ⟨c, (hc: from_natural (c+a) = -[b+1])⟩,
    integer.no_confusion hc

@[reducible]
instance integer_decidable_le: ∀ x y: 𝐙, decidable (x ≤ y)
| (from_natural a) (from_natural b)  := if h: a ≤ b then is_true (iff.elim_left coe_le h) else is_false (mt (iff.elim_right coe_le) h)
| (from_natural a) -[b+1]            := is_false (coe_not_le_neg a b)
| -[a+1]           (from_natural b)  := is_true (neg_lt_coe a b).left
| -[a+1]           -[b+1]            := if h: b ≤ a then is_true (iff.elim_left neg_le h) else is_false (mt (iff.elim_right neg_le) h)

@[reducible]
instance integer_decidable_lt: ∀ x y: 𝐙, decidable (x < y) :=
assume x y: 𝐙,
match (integer.integer_decidable_le x y), (integer.integer_decidable_eq x y) with
| (is_true hle), (is_false hne) := is_true ⟨hle, hne⟩
| (is_true hle), (is_true heq)  := is_false (assume hlt, absurd heq hlt.right)
| (is_false hgt), _             := is_false (assume hlt, absurd hlt.left hgt)
end


-- And multiplication

lemma mul_com (x y: 𝐙): x * y = y * x :=
match x, y with
| (from_natural a), (from_natural b) := show from_natural (a*b) = from_natural (b*a), by rw natural.mult_com
| (-[a+1]),         (from_natural b) := show -from_natural((a+1)*b) = -from_natural(b*(a+1)), by rw natural.mult_com
| (from_natural a), (-[b+1])         := show -from_natural(a*(b+1)) = -from_natural((b+1)*a), by rw natural.mult_com
| (-[a+1]),         (-[b+1])         := show from_natural((a+1)*(b+1)) = from_natural((b+1)*(a+1)), by rw natural.mult_com
end

lemma mult_int_neg (x y: 𝐙): x * (-y) = -(x*y) :=
match x, y with
| (from_natural a), 0                    := by refl
| (from_natural a), (from_natural (b+1)) := by refl
| -[a+1],           0                    := by refl
| (-[a+1]),         (from_natural (b+1)) := show from_natural ((a+1)*(b+1)) = -(-(from_natural ((a+1)*(b+1)))), by rw ←neg_neg (from_natural ((a+1)*(b+1)))
| (from_natural a), (-[b+1])             := show from_natural (a * (b+1)) = -(-(from_natural (a * (b+1)))), by rw ←neg_neg (from_natural (a * (b+1)))
| (-[a+1]),         (-[b+1])             := by refl
end

lemma mult_neg_int (x y: 𝐙): (-x) * y = -(x*y) := by rw [mul_com, mult_int_neg, mul_com]

lemma mult_neg_neg (x y: 𝐙): x * y = (-x) * (-y) :=
calc
    x * y = (- -x) * y    : by rw ←neg_neg x
    ...   = -(-x * y)     : by rw mult_neg_int (-x) y
    ...   = -(-x * -(-y)) : by rw ←neg_neg y
    ...   = -x * -y       : by rw [mult_int_neg, ←neg_neg (-x * -y)]


lemma mul_asoc_nat (a: 𝐍) (y z: 𝐙): (from_natural a) * (y*z) = ((from_natural a)*y)*z :=
match y, z with
| (from_natural b), (from_natural c) := show from_natural (a*(b*c)) = from_natural ((a*b)*c), by rw natural.mult_asoc
| (-[b+1]),         (from_natural c) := suffices -((from_natural a) * from_natural ((b+1)*c)) = -(from_natural (a*(b+1)) * from_natural c), from show from_natural a * -from_natural((b+1)*c) = -from_natural (a*(b+1)) * from_natural c, by rw [mult_int_neg, this, mult_neg_int], show -(from_natural (a*((b+1)*c))) = -(from_natural ((a*(b+1))*c)), by rw natural.mult_asoc
| (from_natural b), (-[c+1])         :=
calc
    from_natural a * (-(from_natural (b*(c+1)))) = -(from_natural a * from_natural (b*(c+1)))   : by rw mult_int_neg
    ...                                          = -(from_natural (a * (b*(c+1))))              : by refl
    ...                                          = -(from_natural ((a*b)*(c+1)))                : by rw natural.mult_asoc
| (-[b+1]),         (-[c+1])         :=
calc
    from_natural (a* ((b+1)*(c+1)))      = from_natural ((a*(b+1))*(c+1))                    : by rw natural.mult_asoc
    ...                                  = from_natural (a*(b+1)) * from_natural (c+1)       : by refl
    ...                                  = (-from_natural (a*(b+1))) * (-from_natural (c+1)) : by rw mult_neg_neg
end

@[simp]
lemma mul_asoc (x y z: 𝐙): x * (y * z) = (x * y) * z :=
match x with
| (from_natural a) := mul_asoc_nat a y z
| -[a+1]           :=
calc
    -[a+1] * (y*z) = (-from_natural (a+1)) * (y*z)   : by refl
    ...            = -(from_natural (a+1) * (y*z))   : by rw mult_neg_int
    ...            = -((from_natural (a+1) * y) * z) : by rw mul_asoc_nat
    ...            = (-(from_natural (a+1) * y)) * z : by rw mult_neg_int
    ...            = ((-from_natural (a+1)) * y) * z : by rw ←mult_neg_int
    ...            = (-[a+1] * y) * z                : by refl
end

@[simp]
lemma mul_reorder_four (w x y z: 𝐙): w*x*y*z = w*y*x*z :=
    calc
        w*x*y*z = (w*(x*y))*z  : by rw mul_asoc
        ...     = (w*(y*x))*z  : by rw ←mul_com x
        ...     = w*y*x*z      : by rw mul_asoc

lemma mult_zero (x:𝐙): x*0 = 0 :=
match x with
| from_natural a := by refl
| -[a+1]         := by refl
end

lemma zero_mult (x:𝐙): 0*x = 0 := by rw [mul_com, mult_zero]

lemma one_mult (x:𝐙): 1*x = x :=
match x with
| from_natural a := show from_natural (1*a) = from_natural a, by rw natural.one_mult
| -[a+1]         := show -from_natural (1*(a+1)) = -from_natural(a+1), by rw natural.one_mult
end

lemma mult_one (x:𝐙): x*1 = x :=
match x with
| from_natural a := show from_natural (a*1) = from_natural a, by rw natural.mult_one
| -[a+1]         := show -from_natural ((a+1)*1) = -from_natural(a+1), by rw natural.mult_one
end

lemma ne_implies_lt_or_gt {x y: 𝐙}: x ≠ y → x < y ∨ y < x :=
match x, y with
| from_natural a, from_natural b :=
    assume h: from_natural a ≠ from_natural b,
    have h: a ≠ b, from (
        assume hc, absurd (congr_arg from_natural hc) h
    ),
    or.elim (natural.ne_implies_lt_or_gt h) (
        assume h: a < b,
        or.intro_left _ (iff.elim_left coe_lt h)
    ) (
        assume h: b < a,
        or.intro_right _ (iff.elim_left coe_lt h)
    )
| from_natural a, -[b+1]         := assume _, or.intro_right _ (neg_lt_coe b a)
| -[a+1],         from_natural b := assume _, or.intro_left _ (neg_lt_coe a b)
| -[a+1],         -[b+1]         :=
    assume h: -[a+1] ≠ -[b+1],
    have h: a ≠ b, from (
        assume hc,
        have hc: -[a+1] = -[b+1], from congr_arg integer.neg_succ_to_natural hc,
        absurd hc h
    ),
    or.elim (natural.ne_implies_lt_or_gt h) (
        assume h: a < b,
        or.intro_right _ (iff.elim_left neg_lt h)
    ) (
        assume h: b < a,
        or.intro_left _ (iff.elim_left neg_lt h)
    )
end

lemma neg_equal {x y: 𝐙}: x = y ↔ -x = -y :=
iff.intro (
    assume h: x = y,
    by rw h
) (
    assume h: -x = -y,
    calc
        x   = - -x  : by rw ←neg_neg x
        ... = - -y  : by rw h
        ... = y     : by rw ←neg_neg y
)

lemma mult_nz_eq_z_imp_z {x y : 𝐙}: x*y = 0 → y ≠ 0 → x = 0 :=
    assume h: x * y = 0,
    assume hy:y ≠ 0,
    if hx: x = 0 then
        hx
    else
        or.elim (ne_implies_lt_or_gt hx) (
            assume hx: x < 0,
            let ⟨a, hx⟩ := (iff.elim_left neg_lt_zero hx) in (
                suffices a+1 = 0, from absurd this (natural.succ_ne_zero a),
                or.elim (ne_implies_lt_or_gt hy) (
                    assume hy: y < 0,
                    let ⟨b, hy⟩ := (iff.elim_left neg_lt_zero hy) in (
                        have h: (-[a+1])*(-[b+1]) = 0, from hx ▸ hy ▸ h,
                        have h: from_natural ((a+1)*(b+1)) = 0, from h,
                        have h: (a+1)*(b+1) = 0, by injection h,
                        show a+1 = 0, from natural.mult_nz_eq_z_imp_z h (natural.succ_ne_zero b)
                    )
                ) (
                    assume ⟨hy, hnz⟩,
                    let ⟨b, hy⟩ := (iff.elim_left coe_ge_zero hy) in (
                        have b ≠ 0, from (
                            assume hc: b=0,
                            suffices y=0, from absurd this (ne.symm hnz),
                            show y = from_natural 0, by rw [hy, hc]
                        ),
                        have h: (-[a+1])*(from_natural b) = 0, from hx ▸ hy ▸ h,
                        have h: -(from_natural ((a+1)*b)) = 0, from h,
                        have h: from_natural ((a+1)*b) = 0, from iff.elim_right neg_equal h,
                        have h: (a+1)*b = 0, by injection h,
                        show a+1 = 0, from natural.mult_nz_eq_z_imp_z h ‹b≠0›
                    )
                )
            )
        ) (
            assume ⟨hx, hnz⟩,
            let ⟨a, hx⟩ := (iff.elim_left coe_ge_zero hx) in (
                have hnz: a ≠ 0, from (
                    assume hc: a=0,
                    suffices x=0, from absurd this (ne.symm hnz),
                    show x = from_natural 0, by rw [hx, hc]
                ),
                suffices a = 0, from absurd this hnz,
                or.elim (ne_implies_lt_or_gt hy) (
                    assume hy: y < 0,
                    let ⟨b, hy⟩ := (iff.elim_left neg_lt_zero hy) in (
                        have h: (from_natural a)*(-[b+1]) = 0, from hx ▸ hy ▸ h,
                        have h: -(from_natural (a*(b+1))) = 0, from h,
                        have h: from_natural (a*(b+1)) = 0, from iff.elim_right neg_equal h,
                        have h: a*(b+1) = 0, by injection h,
                        show a = 0, from natural.mult_nz_eq_z_imp_z h (natural.succ_ne_zero b)
                    )
                ) (
                    assume ⟨hy, hnz⟩,
                    let ⟨b, hy⟩ := (iff.elim_left coe_ge_zero hy) in (
                        have hnz: b ≠ 0, from (
                            assume hc: b = 0,
                            suffices y=0, from absurd this (ne.symm hnz),
                            show y = from_natural 0, by rw [hy, hc]
                        ),
                        have h: (from_natural a)*(from_natural b) = 0, from hx ▸ hy ▸ h,
                        have h: (from_natural (a*b)) = 0, from h,
                        have h: a*b = 0, by injection h,
                        show a = 0, from natural.mult_nz_eq_z_imp_z h hnz
                    )
                )
            )
        )

lemma mult_minusone (x: 𝐙): x*(-1) = -x := by rw [mult_int_neg, mult_one]

lemma minusone_mult (x: 𝐙): -1 * x = -x := by rw [mul_com, mult_minusone]

lemma coe_ne_neg_coe {a b : 𝐍}: a ≠ 0 → from_natural a ≠ - from_natural b :=
    assume h: a ≠ 0,
    assume hc: from_natural a = - from_natural b,
    if hb: b = 0 then
        have hc: from_natural a = -from_natural 0, by rw [hc, hb],
        have hc: from_natural a = from_natural 0, from hc,
        have hc: a = 0, by injection hc,
        absurd hc h
    else
        let ⟨c, hb⟩ := natural.nz_implies_succ hb in (
            have hc: from_natural a = -from_natural (c+1), by rw [hc, hb],
            have hc: from_natural a = -[c+1], from hc,
            integer.no_confusion hc
        )

lemma neg_mult_neg_is_pos {x y: 𝐙}: y < 0 → (x < 0 ↔ x*y > 0) :=
    assume hy: y < 0,
    let ⟨b, hy⟩ := iff.elim_left neg_lt_zero hy in (
        iff.intro (
            assume hx: x < 0,
            let ⟨a, hx⟩ := iff.elim_left neg_lt_zero hx in (
                have h: x * y = from_natural ((a+1)*(b+1)), from (show x * y = -[a+1] * -[b+1], by rw [hx, hy]),
                have 0 ≤ x*y, from iff.elim_right coe_ge_zero ⟨(a+1)*(b+1), h⟩,
                have 0 ≠ x*y, from (
                    assume hc: 0 = x*y,
                    have h: from_natural ((a+1)*(b+1)) = 0, from (
                        calc
                            from_natural ((a+1)*(b+1)) = -[a+1] * -[b+1]  : by refl
                            ...                        = x * y            : by rw [hx, hy]
                            ...                        = 0                : by rw hc
                    ),
                    have h: (a+1)*(b+1) = 0, by injection h,
                    have h: (((a+1)*b) + a) + 1 = 0, from (calc
                        (((a+1)*b) + a) + 1 = ((a+1)*b) + (a + 1)  : by rw natural.add_asoc
                        ...                 = (a+1) + ((a+1)*b)    : by rw natural.add_com
                        ...                 = ((a+1)*(b+1))        : by refl
                        ...                 = 0                    : by rw h
                    ),
                    natural.no_confusion h
                ),
                ⟨‹0 ≤ x*y›, ‹0 ≠ x*y›⟩
            )
        ) (
            assume ⟨hle, hne⟩,
            let ⟨c, h⟩ := iff.elim_left coe_ge_zero hle in (
                have hne: from_natural c ≠ 0, from h ▸ (ne.symm hne),
                have hne: c ≠ 0, from (
                    assume hc: c = 0,
                    suffices from_natural c = 0, from absurd this hne,
                    show from_natural c = from_natural 0, by rw hc
                ),
                suffices x*(-[b+1])=from_natural c → x < 0, from this (hy ▸ h),
                match x with
                | from_natural a := assume hc: -(from_natural (a*(b+1))) = from_natural c, absurd hc (ne.symm (coe_ne_neg_coe ‹c ≠ 0›))
                | -[a+1]         := assume _, iff.elim_right neg_lt_zero ⟨a, eq.refl (-[a+1])⟩
                end
            )
        )
    )

lemma nz_impl_coe_nz {a: 𝐍}: a ≠ 0 → from_natural a ≠ 0 :=
    assume h: a ≠ 0,
    assume hc: from_natural a = from_natural 0,
    absurd (by injection hc) h
lemma coe_nz_impl_nz {a: 𝐍}: from_natural a ≠ 0 → a ≠ 0 := mt (congr_arg from_natural)


lemma neg_lt_gt {x: 𝐙}: x > 0 ↔ -x < 0 :=
    iff.intro (
        assume ⟨hge, hne⟩,
        let ⟨a, hx⟩ := iff.elim_left coe_ge_zero hge in (
            have hne: a ≠ 0, from coe_nz_impl_nz (hx ▸ (ne.symm hne)),
            let ⟨b, ha⟩ := natural.nz_implies_succ hne in (
                have hx: -x = -[b+1], from show -x = -(from_natural (b+1)), by rw [hx, ha],
                iff.elim_right neg_lt_zero ⟨b, hx⟩
            )
        )
    ) (
        assume ⟨hle, hne⟩,
        have x ≠ 0, from assume hc: x = 0, have hc:-x = -0, by rw hc, absurd hc hne,
        let ⟨a, hx⟩ := iff.elim_left neg_lt_zero ⟨hle, hne⟩ in (
            suffices x ≥ 0, from ⟨this, (ne.symm ‹x ≠ 0›)⟩,
            suffices x = from_natural (a+1), from iff.elim_right coe_ge_zero ⟨a+1, this⟩,
            calc
                x    =  - -x               : by rw ←neg_neg x
                ...  =  - (-[a+1])         : by rw hx
                ...  =  from_natural (a+1) : by refl
        )
    )

lemma neg_gt_lt {x: 𝐙}: x < 0 ↔ -x > 0 :=
iff.intro (
    match x with
    | from_natural a := assume h: from_natural (a) < 0, let ⟨b, h⟩ := iff.elim_left neg_lt_zero h in (integer.no_confusion h)
    | -[a+1]         := assume _, show from_natural (a+1) > 0, from ⟨iff.elim_right coe_ge_zero ⟨a+1,rfl⟩, ne.symm (nz_impl_coe_nz (natural.succ_ne_zero a))⟩
    end
) (
    match x with
    | from_natural (a+1) := assume h: -[a+1] > 0, let ⟨b, h⟩ := iff.elim_left coe_ge_zero h.left in (integer.no_confusion h)
    | from_natural 0     := assume h:0 > 0, absurd rfl h.right
    | -[a+1]             := assume _, iff.elim_right neg_lt_zero ⟨a, rfl⟩
    end
)

lemma neg_mult (x y : 𝐙): (-x) * y = - (x * y) :=
match x, y with
| from_natural 0,     y              :=
calc
    -(from_natural 0) * y = 0 * y     : by refl
    ...                   = 0         : by rw zero_mult
    ...                   = -0        : by refl
    ...                   = -(0 * y)  : by rw zero_mult
| from_natural (a+1), from_natural b := by refl
| from_natural (a+1), -[b+1]         := calc
    (-from_natural (a+1))*(-[b+1]) = (-[a+1])*(-[b+1])                 : by refl
    ...                            = from_natural ((a+1) * (b+1))      : by refl
    ...                            = - -from_natural ((a+1) * (b+1))   : by rw ←neg_neg (from_natural ((a+1) * (b+1)))
    ...                            = -((from_natural (a+1))*(-[b+1]))  : by refl
| -[a+1],             from_natural b := calc
    (- -[a+1])*(from_natural b) = (from_natural (a+1)) * (from_natural b)   : by refl
    ...                         = from_natural ((a+1)*b)                    : by refl
    ...                         = - (-from_natural ((a+1)*b))               : by rw ←neg_neg (from_natural ((a+1)*b))
    ...                         = -(-[a+1] * (from_natural b))              : by refl
| -[a+1],             -[b+1]         := by refl
end

lemma mult_neg (x y : 𝐙): x * -y = - (x * y) := by rw [mul_com, neg_mult, mul_com]

lemma neg_mult_neg (x y : 𝐙): -x * -y = x * y := by rw [neg_mult, mult_neg, ←neg_neg (x*y)]

lemma pos_mult_pos_is_pos {x y: 𝐙}: y > 0 → (x > 0 ↔ x*y > 0) :=
assume hy: y > 0,
have hy: -y < 0, from iff.elim_left neg_lt_gt hy,
iff.intro (
    assume hx: x > 0,
    have hx: -x < 0, from iff.elim_left neg_lt_gt hx,
    suffices (-x) * (-y) > 0, from neg_mult_neg x y ▸ this,
    iff.elim_left (neg_mult_neg_is_pos hy) hx
) (
    assume h: x*y > 0,
    suffices -x < 0, from iff.elim_right neg_lt_gt this,
    suffices (-x)*(-y) > 0, from iff.elim_right (neg_mult_neg_is_pos hy) this,
    (eq.symm (neg_mult_neg x y)) ▸ h
)


lemma mult_elim_right_neg_neg {x y z: 𝐙}: y < 0 → x < 0 → x*y = z*y → x = z :=
    assume hy: y < 0,
    assume hx: x < 0,
    assume hxyzy: x*y = z*y,
    have x*y > 0, from iff.elim_left (neg_mult_neg_is_pos hy) hx,
    have z*y > 0, from hxyzy ▸ ‹x*y > 0›,
    have hz: z < 0, from iff.elim_right (neg_mult_neg_is_pos hy) ‹z*y > 0›,
    let ⟨a, ha⟩ := (iff.elim_left neg_lt_zero hx) in (
        let ⟨b, hb⟩ := (iff.elim_left neg_lt_zero hy) in (
            let ⟨c, hc⟩ := (iff.elim_left neg_lt_zero hz) in (
                have hxyzy: (-[a+1])*(-[b+1]) = (-[c+1])*(-[b+1]), from (ha ▸ hb ▸ hc ▸ hxyzy),
                have hxyzy: (from_natural ((a+1)*(b+1))) = (from_natural ((c+1)*(b+1))), from hxyzy,
                have hxyzy: (a+1)*(b+1) = (c+1)*(b+1), by injection hxyzy,
                have hac: a+1 = c+1, from natural.mult_elim_right (natural.succ_ne_zero b) hxyzy,
                have hac: a = c, from natural.add_cancel_right hac,
                have hac: -[a+1] = -[c+1], from hac ▸ (eq.refl (-[a+1])),
                show x=z, from (eq.symm ha) ▸ (eq.symm hc) ▸ hac
            )
        )
    )

lemma neg_mult_pos_is_neg {x y: 𝐙}: y > 0 → (x < 0 ↔ x*y < 0) :=
assume hy: y > 0,
iff.intro (
    assume hx: x < 0,
    have hx: -x > 0, from iff.elim_left neg_gt_lt hx,
    suffices -(x*y) > 0, from iff.elim_right neg_gt_lt this,
    suffices (-x)*y > 0, from neg_mult x y ▸ this,
    iff.elim_left (pos_mult_pos_is_pos hy) hx
) (
    assume h: x*y < 0,
    have h: -(x*y) > 0, from iff.elim_left neg_gt_lt h,
    have h: (-x)*y > 0, from (eq.symm (neg_mult x y)) ▸ h,
    suffices -x > 0, from iff.elim_right neg_gt_lt this,
    iff.elim_right (pos_mult_pos_is_pos hy) h
)

lemma pos_mult_neg_is_neg {x y: 𝐙}: y < 0 → (x > 0 ↔ x*y < 0) :=
assume hy: y < 0,
have hy: -y > 0, from iff.elim_left neg_gt_lt hy,
iff.intro (
    assume hx: x > 0,
    have hx: -x < 0, from iff.elim_left neg_lt_gt hx,
    suffices (-x)*(-y) < 0, from neg_mult_neg x y ▸ this,
    iff.elim_left (neg_mult_pos_is_neg hy) hx
) (
    assume h: x*y < 0,
    have h: (-x)*(-y) < 0, from (eq.symm (neg_mult_neg x y)) ▸ h,
    suffices -x < 0, from iff.elim_right neg_lt_gt this,
    iff.elim_right (neg_mult_pos_is_neg hy) h
)

lemma mult_elim_right {x y z: 𝐙}: y ≠ 0 → x*y = z*y → x=z :=
    assume hy: y ≠ 0,
    if hx: x = 0 then
        assume hxyzy: x*y = z*y,
        suffices z = 0, from ((eq.symm hx) ▸ (eq.symm this)),
        suffices z*y = 0, from mult_nz_eq_z_imp_z this hy,
        ((zero_mult y) ▸ (eq.symm (hx ▸ hxyzy)))
    else
        assume hxyzy: x*y = z*y,
        or.elim (ne_implies_lt_or_gt hy) (
            assume hy: y < 0,
            or.elim (ne_implies_lt_or_gt hx) (
                assume hx: x < 0,
                mult_elim_right_neg_neg ‹y < 0› ‹x < 0› hxyzy
            ) (
                assume hx: x > 0,
                have hxyzy: (-x)*y = (-z)*y, from show -x * y = (-z)*y, by rw [neg_mult, hxyzy, neg_mult],
                suffices -x = -z, from iff.elim_right neg_equal this,
                mult_elim_right_neg_neg ‹y < 0› (iff.elim_left neg_lt_gt ‹x > 0›) hxyzy
            )
        ) (
            assume hy: y > 0,
            or.elim (ne_implies_lt_or_gt hx) (
                assume hx: x < 0,
                have hxyzy: x*-y = z*-y, from show x * -y = z*-y, by rw [mult_neg, hxyzy, mult_neg],
                mult_elim_right_neg_neg (iff.elim_left neg_lt_gt ‹y > 0›) ‹x < 0› hxyzy
            ) (
                assume hx: x > 0,
                have hxyzy: -x*-y = -z*-y, from show -x * -y = -z*-y, by rw [neg_mult_neg, hxyzy, neg_mult_neg],
                suffices -x = -z, from iff.elim_right neg_equal this,
                mult_elim_right_neg_neg (iff.elim_left neg_lt_gt ‹y > 0›) (iff.elim_left neg_lt_gt ‹x > 0›) hxyzy
            )
        )

lemma add_mult_coe_coe_coe (a b c: 𝐍): (from_natural a + from_natural b)*from_natural c = from_natural a*from_natural c + from_natural b*from_natural c :=
show from_natural ((a+b)*c) = from_natural (a*c + b*c), by rw natural.add_dist_mult

lemma add_mult_coe_coe_neg (a b c: 𝐍): (from_natural a + from_natural b)*(-[c+1]) = from_natural a*(-[c+1]) + from_natural b*(-[c+1]) :=
calc
    (from_natural a + from_natural b)*(-[c+1]) = (from_natural (a+b))*(-[c+1])                          : by refl
    ...                                        = -from_natural ((a+b)*(c+1))                            : by refl
    ...                                        = -from_natural (a*(c+1) + b*(c+1))                      : by rw natural.add_dist_mult
    ...                                        = -(from_natural (a*(c+1)) + from_natural (b*(c+1)))     : by refl
    ...                                        = -from_natural (a*(c+1)) + -from_natural (b*(c+1))      : by rw neg_add
    ...                                        = (from_natural a)*(-[c+1]) + (from_natural b)*(-[c+1])  : by refl

lemma add_mult_coe_neg_coe (a b c: 𝐍): (from_natural a + -[b+1])*from_natural c = from_natural a*from_natural c + -[b+1]*from_natural c :=
if hc: c = 0 then
    calc
        (from_natural a + -[b+1]) * from_natural (c) = (from_natural a + -[b+1]) * from_natural 0                   : by rw hc
        ...                                          = (from_natural a + -[b+1]) * 0                                : by refl
        ...                                          = 0                                                            : by rw mult_zero
        ...                                          = 0 + from_natural 0                                           : by rw ←add_zero_ 0
        ...                                          = 0 + 0                                                        : by refl
        ...                                          = (from_natural a)*0 + 0                                       : by rw mult_zero
        ...                                          = (from_natural a)*0 + -[b+1]*0                                : by rw mult_zero (-[b+1])
        ...                                          = (from_natural a)*(from_natural 0) + -[b+1]*(from_natural 0)  : by refl
        ...                                          = (from_natural a)*(from_natural c) + -[b+1]*(from_natural c)  : by rw hc
else
    let ⟨d, hc⟩ := natural.nz_implies_succ hc in (
        if hz: (b+1) ≤ a then
            have (b+1)*(d+1) ≤ a*(d+1), from iff.elim_left natural.le_mult_cancel_right (or.intro_left _ hz),
            have natural.sub (b+1) a = 0, from natural.le_sub_zero hz,
            have natural.sub ((b+1)*(d+1)) (a*(d+1)) = 0, from natural.le_sub_zero ‹(b+1)*(d+1) ≤ a*(d+1)›,
            calc
                (from_natural a + -[b+1]) * from_natural (c) = (from_natural a + -[b+1]) * from_natural (d+1)                             : by rw hc
                ...                                          = (sub_of_natural a (b+1)) * from_natural (d+1)                              : by refl
                ...                                          = (from_natural (natural.sub a (b+1)))* from_natural (d+1)                   : by rw sub_of_natural_sub_eq_zero ‹natural.sub (b+1) a = 0›
                ...                                          = from_natural ((a - (b+1))*(d+1))                                           : by refl
                ...                                          = from_natural (a*(d+1) - (b+1)*(d+1))                                       : by rw natural.sub_dist_mult ‹b+1 ≤ a›
                ...                                          = from_natural (natural.sub (a*(d+1)) ((b+1)*(d+1)))                         : by refl
                ...                                          = sub_of_natural (a*(d+1)) ((b+1)*(d+1))                                     : by rw sub_of_natural_sub_eq_zero ‹natural.sub ((b+1)*(d+1)) (a*(d+1)) = 0›
                ...                                          = sub_of_natural (a*(d+1)) ((d+1)*(b+1))                                     : by rw natural.mult_com (b+1)
                ...                                          = sub_of_natural (a*(d+1)) ((d+1) + (d+1)*b)                                 : by refl
                ...                                          = sub_of_natural (a*(d+1)) ((d+1)*b + d + 1)                                 : by rw [natural.add_com (d+1), natural.add_asoc]
                ...                                          = from_natural (a*(d+1)) + -[((d+1)*b + d)+1]                                : by refl
                ...                                          = from_natural a * (from_natural (d+1)) + -(from_natural ((d+1)*b + d + 1))  : by refl
                ...                                          = from_natural a * (from_natural (d+1)) + -(from_natural ((d+1) + (d+1)*b))  : by rw [natural.add_asoc ((d+1)*b), natural.add_com (d+1)]
                ...                                          = from_natural a * (from_natural (d+1)) + -(from_natural ((d+1)*(b+1)))      : by refl
                ...                                          = from_natural a * (from_natural (d+1)) + from_natural (d+1) * (-[b+1])      : by refl
                ...                                          = from_natural a * (from_natural (d+1)) + (-[b+1]) * (from_natural (d+1))    : by rw mul_com (from_natural (d+1))
                ...                                          = from_natural a * (from_natural c) + (-[b+1]) * (from_natural c)            : by rw hc
        else
            have hz: a < b+1, from iff.elim_left natural.not_le hz,
            have a*c < (b+1)*c, from iff.elim_left natural.lt_mult_cancel_right ⟨hz, ‹c≠0›⟩,
            have natural.sub (b+1) a ≠ 0, from natural.lt_sub_nz hz,
            have natural.sub ((b+1)*c) (a*c) ≠ 0, from natural.lt_sub_nz ‹a*c < (b+1)*c›,
            calc
                (from_natural a + -[b+1]) * from_natural (c) = (sub_of_natural a (b+1)) * from_natural (c)                : by refl
                ...                                          = (-from_natural (natural.sub (b+1) a))*(from_natural c)     : by rw sub_of_natural_sub_ne_zero ‹natural.sub (b+1) a ≠ 0›
                ...                                          = -((from_natural (natural.sub (b+1) a))*(from_natural c))   : by rw neg_mult
                ...                                          = -from_natural (((b+1) - a)*c)                              : by refl
                ...                                          = -from_natural ((b+1)*c - a*c)                              : by rw natural.sub_dist_mult ‹a < b+1›.left
                ...                                          = -from_natural (natural.sub ((b+1)*c) (a*c))                : by refl
                ...                                          = sub_of_natural (a*c) ((b+1)*c)                             : by rw sub_of_natural_sub_ne_zero ‹natural.sub ((b+1)*c) (a*c) ≠ 0›
                ...                                          = sub_of_natural (a*c) ((b+1)*(d+1))                         : by rw hc
                ...                                          = sub_of_natural (a*c) ((b+1) + (b+1)*d)                     : by refl
                ...                                          = sub_of_natural (a*c) ((b+1)*d + b + 1)                     : by rw [natural.add_com, natural.add_asoc]
                ...                                          = from_natural (a*c) + -[((b+1)*d + b)+1]                    : by refl
                ...                                          = from_natural (a*c) + -from_natural ((b+1)*d + b + 1)       : by refl
                ...                                          = from_natural (a*c) + -from_natural ((b+1) + (b+1)*d)       : by rw [natural.add_asoc, natural.add_com]
                ...                                          = from_natural (a*c) + -from_natural ((b+1)*(d+1))           : by refl
                ...                                          = from_natural (a*c) + -from_natural ((b+1)*c)               : by rw hc
                ...                                          = from_natural (a*c) + -from_natural ((b+1)*c)               : by rw hc
                ...                                          = from_natural a * from_natural c + (-[b+1])*from_natural c  : by refl
    )


lemma add_com_mult {x y z: 𝐙}: ((x + y)*z = x*z + y*z) → (y + x)*z = y*z + x*z :=
    assume h: (x + y)*z = x*z + y*z,
    calc
        (y + x) * z = (x + y)*z  : by rw add_com
        ...         = x*z + y*z  : by rw h
        ...         = y*z + x*z  : by rw add_com

lemma add_neg_mult {x y z: 𝐙}: ((x + y)*z = x*z + y*z) → (-x + -y)*z = -x*z + -y*z :=
    assume h: (x + y)*z = x*z + y*z,
    calc
        (-x + -y) * z = (-(x + y))*z     : by rw neg_add
        ...           = -((x+y)*z)       : by rw neg_mult
        ...           = -(x*z + y*z)     : by rw h
        ...           = -(x*z) + -(y*z)  : by rw neg_add
        ...           = -x*z + -y*z      : by rw [neg_mult, neg_mult]

lemma add_mult_neg {x y z: 𝐙}: ((x + y)*z = x*z + y*z) → (x + y)*-z = x*-z + y*-z :=
    assume h: (x + y)*z = x*z + y*z,
    calc
        (x + y)*(-z) = -((x+y)*z)       : by rw mult_neg
        ...          = -(x*z + y*z)     : by rw h
        ...          = -(x*z) + -(y*z)  : by rw neg_add
        ...          = x*(-z) + y*(-z)  : by rw [mult_neg, mult_neg]


lemma add_mult__coe (x y: 𝐙) (c: 𝐍): (x + y) * from_natural c = x*from_natural c + y*from_natural c :=
match x, y with
| from_natural a, from_natural b := add_mult_coe_coe_coe a b c
| from_natural a, -[b+1]         := add_mult_coe_neg_coe a b c
| -[a+1],         from_natural b := add_com_mult (add_mult_coe_neg_coe b a c)
| -[a+1],         -[b+1]         := add_neg_mult (add_mult_coe_coe_coe (a+1) (b+1) c)
end

@[simp]
lemma add_mult (x y z : 𝐙): (x + y)*z = x*z + y*z :=
match z with
| from_natural c := add_mult__coe x y c
| -[c+1]         := add_mult_neg (add_mult__coe x y (c+1))
end

lemma nz_mult_nz_nz {x y: 𝐙}: x ≠ 0 → y ≠ 0 → x*y ≠ 0 := assume hx: x ≠ 0, assume hy: y ≠ 0, assume hc: x*y = 0, absurd (mult_nz_eq_z_imp_z hc hy) hx


-- All of this induces a Ring structure on 𝐙, and furthermore 𝐙 is an Integral Domain

def to_IntegralDomain: IntegralDomain 𝐙 :=
{
    is_set := assume a b, if h: a = b then or.intro_left _ h else or.intro_right _ h,
    add_assoc := add_asoc,
    add_comm := add_com,
    left_zero := assume x:𝐙, eq.symm (zero_add_ x),
    left_neg := assume x:𝐙, by rw [add_com, add_neg],
    mul_assoc := assume x y z, eq.symm (mul_asoc x y z),
    mul_comm := mul_com,
    left_distrib := assume x y z, by rw [mul_com, add_mult, mul_com x, mul_com y],
    left_one := one_mult,
    nzd := assume a b, assume h : a * b = 0, assume ha: a ≠ 0, if hb: b = 0 then hb else absurd h (nz_mult_nz_nz ha hb)
}
instance: IntegralDomain 𝐙 := to_IntegralDomain
def to_CommNZDRing: CommNZDRing 𝐙 := integer.to_IntegralDomain.to_CommNZDRing
instance: CommNZDRing 𝐙 := to_CommNZDRing
def to_UnitRing: UnitRing 𝐙 := integer.to_IntegralDomain.to_UnitRing
instance: UnitRing 𝐙 := to_UnitRing
def to_NZDRing: NZDRing 𝐙 := integer.to_IntegralDomain.to_NZDRing
instance: NZDRing 𝐙 := to_NZDRing
def to_Ring: Ring 𝐙 := integer.to_IntegralDomain.to_Ring
instance: Ring 𝐙 := to_Ring

-- divisibility

def dvd (x y: 𝐙):= ∃ z: 𝐙, x*z = y
instance integer_has_dvd: has_dvd integer := ⟨dvd⟩

lemma dvd_zero (x: 𝐙): x∣0 := ⟨0, by rw mult_zero⟩

lemma one_dvd (x: 𝐙): 1∣x := ⟨x, by rw one_mult⟩

lemma dvd_refl (x: 𝐙): x∣x := ⟨1, by rw mult_one⟩
lemma dvd_antirefl (x: 𝐙): x∣-x := ⟨-1, by rw mult_minusone⟩

lemma dvd_neg (x y: 𝐙): x∣y ↔ -x∣y :=
    iff.intro (
        assume ⟨z, (h: x*z=y)⟩,
        ⟨-z, (eq.symm (h ▸ (mult_neg_neg x z)))⟩
    ) (
        assume ⟨z, (h: -x*z=y)⟩,
        ⟨-z, show x * -z = y, by rw [mult_int_neg, ←mult_neg_int, h]⟩
    )

-- A couple of useful functions

def abs: 𝐙 → 𝐍
| (from_natural a) := a
| -[a+1]           := a+1

def sgn: 𝐙 → 𝐙
| (from_natural a+1) := 1
| (from_natural 0)   := 0
| -[a+1]             := -1

lemma abs_zero {x: 𝐙}: x = 0 ↔ abs x = 0 :=
iff.intro (
    assume hx: x = from_natural 0,
    show abs x = abs (from_natural 0), by rw hx
) (
    match x with
    | from_natural (a+1) := assume :a+1 = 0, absurd this (natural.succ_ne_zero a)
    | from_natural 0     := assume _, by refl
    | -[a+1]             := assume :a+1 = 0, absurd this (natural.succ_ne_zero a)
    end
)

lemma sgn_zero {x : 𝐙}: x = 0 ↔ sgn x = 0 :=
iff.intro (
    assume h: x= from_natural 0,
    show sgn x = sgn (from_natural 0), by rw h
) (
    match x with
    | from_natural (a+1) := assume h: from_natural 1 = from_natural 0, have h: (1: 𝐍) = 0, by injection h, natural.no_confusion h
    | from_natural 0     := assume _, by refl
    | -[a+1]             := assume h: -[0+1] = from_natural 0, integer.no_confusion h
    end
)

lemma sgn_neg {x: 𝐙}: x < 0 ↔ sgn x = -1 :=
iff.intro (
    assume h: x < 0,
    let ⟨a, h⟩ := iff.elim_left neg_lt_zero h in (
        calc
            sgn x = sgn (-[a+1])  : by rw h
            ...   = -1            : by refl
    )
) (
    match x with
    | from_natural (a+1) := assume h, suffices 1 = (-1 : 𝐙), from integer.no_confusion this, show sgn (from_natural (a+1)) = (-1: 𝐙), by rw h
    | from_natural 0     := assume h, suffices 0 = (-1 : 𝐙), from integer.no_confusion this, show sgn (from_natural 0) = (-1: 𝐙), by rw h
    | -[a+1]             := assume h, iff.elim_right neg_lt_zero ⟨a, rfl⟩
    end
)

lemma sgn_pos {x: 𝐙}: x > 0 ↔ sgn x = 1 :=
iff.intro (
    assume h: x > 0,
    let ⟨a, hle⟩ := iff.elim_left coe_ge_zero h.left in (
        have h: from_natural a ≠ 0, from assume hc, have x = 0, from (eq.symm hle) ▸ hc, absurd this (ne.symm h.right),
        have a ≠ 0, from coe_nz_impl_nz h,
        let ⟨b, h⟩ := natural.nz_implies_succ ‹a ≠ 0› in (
            calc
                sgn x = sgn (from_natural a)      : by rw hle
                ...   = sgn (from_natural (b+1))  : by rw h
                ...   = 1                         : by refl
        )
    )
) (
    match x with
    | from_natural (a+1) := assume h, suffices from_natural (a+1) ≠ 0, from ⟨iff.elim_right coe_ge_zero ⟨a+1, rfl⟩, (ne.symm this)⟩, assume hc, have hc: a+1 = 0, by injection hc, natural.no_confusion hc
    | from_natural 0     := assume h, have 0 = (1: 𝐙), from h, have h: 0 = (1: 𝐍), by injection h, natural.no_confusion h
    | -[a+1]             := assume h, suffices -1 = (1 : 𝐙), from integer.no_confusion this, show sgn (-[a+1]) = (1: 𝐙), by rw h
    end
)

lemma sgn_mult_abs (x: 𝐙): sgn x * abs x = x :=
match x with
| from_natural (a+1) := show 1 * from_natural (a+1) = from_natural (a+1), by rw one_mult
| from_natural 0     := by refl
| -[a+1]             := show -1 * from_natural (a+1) = -from_natural (a+1), by rw minusone_mult
end

lemma sgn_mult_nat {y: 𝐍}: y ≠ 0 → ∀ x: 𝐙, sgn x = sgn (x*↑y) :=
assume hy: y ≠ 0,
assume x: 𝐙,
have hy: from_natural y > 0, from ⟨iff.elim_right coe_ge_zero ⟨y, rfl⟩, ne.symm (nz_impl_coe_nz hy)⟩,
suffices sgn (x*from_natural y) = sgn x, from eq.symm this,
if hx: x = 0 then
    calc
        sgn (x*from_natural y) = sgn (0*from_natural y)  : by rw hx
        ...                    = sgn 0                   : by rw zero_mult
        ...                    = sgn x                   : by rw hx
else
    or.elim (ne_implies_lt_or_gt hx) (
        assume hx: x < 0,
        have h: x*from_natural y < 0, from iff.elim_left (neg_mult_pos_is_neg hy) hx,
        calc
            sgn (x*from_natural y) = -1    : by rw iff.elim_left sgn_neg h
            ...                    = sgn x : by rw iff.elim_left sgn_neg hx
    ) (
        assume hx: x > 0,
        have h: x*from_natural y > 0, from iff.elim_left (pos_mult_pos_is_pos hy) hx,
        calc
            sgn (x*from_natural y) = 1     : by rw iff.elim_left sgn_pos h
            ...                    = sgn x : by rw iff.elim_left sgn_pos hx
    )

lemma sgn_mult_sgn {x : 𝐙}: x ≠ 0 → sgn x * sgn x = 1 :=
match x with
| from_natural (a+1) := assume _, show (1:𝐙) * (1:𝐙) = (1:𝐙), from mult_one 1
| from_natural 0     := assume h, absurd (rfl) h
| -[a+1]             := assume _, show (-1 * -1 : 𝐙) = 1, by rw [neg_mult_neg, mult_one]
end

end integer
