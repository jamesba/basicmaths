import .natural

-- So having constructed the natural numbers I'm now going to construct the integers
inductive integer: Type
| from_natural (n : natural)
| neg_succ_to_natural (n : natural)

-- Coercion from naturals

instance has_coe_natural_integer: has_coe natural integer := ⟨integer.from_natural⟩

namespace integer

open integer

-- Add some notation for them
notation `-[` n `+1]` := neg_succ_to_natural n
def zero: integer := from_natural 0
def one: integer := from_natural 1

instance integer_has_zero: has_zero integer := ⟨zero⟩
instance integer_has_one: has_one integer := ⟨one⟩

-- Add a representation

def repr: integer → string
| (from_natural n) := (natural.repr n)
| -[n+1] := "-" ++ (natural.repr (natural.succ n))

instance integer_has_repr: has_repr integer := ⟨repr⟩


-- negation
def sub_of_natural (x y : natural): integer :=
match (natural.sub y x) with
| 0     := from_natural (natural.sub x y)
| (n+1) := -[n+1]
end

def neg: integer → integer
| (from_natural 0)     := 0
| (from_natural (n+1)) := -[n+1]
| -[n+1]               := from_natural (n+1)

instance integer_has_neg: has_neg integer := ⟨neg⟩

-- addition
def add: integer → integer → integer
| (from_natural n) (from_natural m) := from_natural (n + m)
| (from_natural n) -[m+1]           := sub_of_natural n (m+1)
| -[n+1]           (from_natural m) := sub_of_natural m (n+1)
| -[n+1]           -[m+1]           := -[(n+m+1)+1]

instance integer_has_add: has_add integer := ⟨add⟩
instance integer_has_sub: has_sub integer := ⟨λ x y, x + (-y)⟩

def succ: integer → integer
| (from_natural a) := from_natural (a+1)
| -[0+1]           := from_natural 0
| -[(n+1)+1]       := -[n+1]

def pred: integer → integer
| (from_natural (n+1)) := from_natural n
| (from_natural 0)     := -[0+1]
| -[n+1]               := -[(n+1)+1]

-- multiplication
def mult: integer → integer → integer
| (from_natural n) (from_natural m) := from_natural (n*m)
| (from_natural n) -[m+1]           := -(from_natural (n*(m+1)))
| -[n+1]           (from_natural m) := -(from_natural ((n+1)*m))
| -[n+1]           -[m+1]           := from_natural ((n+1)*(m+1))

instance integer_has_mult : has_mul integer := ⟨mult⟩


-- properties
lemma neg_neg (x : integer): x = -(-x) :=
match x with
| (from_natural 0)     := by refl
| (from_natural (n+1)) := by refl
| -[n+1]               := by refl
end

lemma sub_of_natural_sub_eq_zero {x y: natural} (h: natural.sub y x = 0): sub_of_natural x y = from_natural (natural.sub x y) :=
begin
    unfold sub_of_natural,
    rw h,
    unfold sub_of_natural._match_1
end

lemma sub_of_natural_sub_ne_zero {x y: natural} (h: natural.sub y x ≠ 0): sub_of_natural x y = -from_natural (natural.sub y x) :=
let ⟨z, (h: natural.sub y x = z+1)⟩ := natural.nz_implies_succ h in
begin
    unfold sub_of_natural,
    rw h,
    unfold sub_of_natural._match_1,
    refl
end

@[simp]
lemma succ_of_neg_succ_is_plus_one (n: natural): succ (-[(n+1)+1]) = (-[(n+1)+1]) + 1 :=
have h: natural.sub ((n+1) + 1) 1 = n+1, from natural.succ_sub_one (n+1),
have nz: natural.sub ((n+1) + 1) 1 ≠ 0, from h ▸ (natural.succ_ne_zero n),
show -(from_natural (n+1)) = sub_of_natural 1 ((n+1) + 1), from  h ▸ (sub_of_natural_sub_ne_zero nz)

@[reducible, simp]
lemma succ_is_add_one (x: integer): succ x = x + 1 :=
    match x with
    | (from_natural a) := by refl
    | -[0+1]           := by refl
    | -[(n+1)+1]       := succ_of_neg_succ_is_plus_one n
    end

@[simp]
lemma pred_succ_is_succ_sub_one (n: natural): pred (from_natural (n+1)) = (from_natural (n+1)) - 1 :=
    have 1 ≤ (n+1), from ⟨n, by refl⟩,
    have natural.sub 1 (n+1) = 0, from natural.le_sub_zero ‹1 ≤ (n+1)›,
    suffices (from_natural (n+1)) - 1 = pred (from_natural (n+1)), from eq.symm this,
    show sub_of_natural (n+1) (0+1) = from_natural (natural.sub (n+1) 1), by rw [natural.zero_add_ 1, sub_of_natural_sub_eq_zero ‹natural.sub 1 (n+1) = 0›]

@[reducible, simp]
lemma pred_is_sub_one (x: integer): pred x = x - 1 :=
    match x with
    | (from_natural (n+1)) := pred_succ_is_succ_sub_one n
    | (from_natural 0)     := by refl
    | -[n+1]               := by refl
    end

@[simp]
lemma sub_of_natural_zero (a: natural): sub_of_natural a 0 = from_natural a := sub_of_natural_sub_eq_zero (natural.zero_sub a)

lemma coe_of_pred_is_pred {x: natural}: x≠0 → from_natural (natural.pred x) = pred (from_natural x) :=
    assume h,
    let ⟨y, (h: x = y + 1)⟩ := natural.nz_implies_succ ‹x≠0› in (
        calc
            from_natural (natural.pred x) = from_natural (natural.pred (y+1))  : by rw h
            ...                           = pred (from_natural (y+1))          : by refl
            ...                           = pred (from_natural x)              : by rw h
    )

lemma coe_of_succ_is_succ (x: natural):  from_natural (x+1) = from_natural x + 1 :=
    natural.rec_on x (by refl) (assume n: natural, assume hr: from_natural (n + 1) = ↑n + 1, by refl)

@[simp]
lemma succ_of_neg_succ (x: natural): -[x+1] + 1 = -(from_natural x) :=
    natural.rec_on x (
        by refl
    ) (
        assume n: natural,
        assume hr: -[n+1] + 1 = -from_natural n,
        show -[(n+1)+1] + 1 = succ (-[(n+1)+1]), by rw succ_is_add_one
    )

lemma inv_succ_of_nat_is_pred (n: natural): -(from_natural n + 1) = pred (-from_natural n) :=
    if h: n = 0 then
        suffices -(from_natural n + 1) = pred (-from_natural 0), by rw [this, h],
        show -(from_natural n + 1) = -(from_natural 0 + 1), by rw h
    else
        let ⟨m, (_: n = m+1)⟩ := natural.nz_implies_succ h in
            calc
                -(from_natural n + 1) = -(from_natural (m+1) + 1)  : by rw ‹n=m+1›
                ...                   = pred (-from_natural (m+1)) : by refl
                ...                   = pred (-from_natural n)     : by rw ‹n=m+1›

lemma inv_succ_of_neg_is_pred (n: natural): -(-[n+1] + 1) = pred (-(-[n+1])) :=
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

@[simp]
lemma inv_succ_is_pred (x: integer): -(x + 1) = pred (-x) :=
match x with
| from_natural n := inv_succ_of_nat_is_pred n
| -[n+1]         := inv_succ_of_neg_is_pred n
end

@[simp]
lemma inv_pred_is_succ (x: integer): -(pred x) = -x + 1 :=
    calc
        -(pred x) = -(pred (-(-x)))  : by rw ←neg_neg x
        ...       = -(-(-x + 1))     : by rw inv_succ_is_pred
        ...       = -x + 1           : by rw ←neg_neg (-x + 1)

lemma zero_add_ (x: integer): x = (from_natural 0) + x :=
match x with
| (from_natural n) := show from_natural n = from_natural (0+n), by rw natural.zero_add_
| -[n+1]           := by refl
end

lemma add_zero_ (x: integer): x = x + (from_natural 0) :=
match x with
| (from_natural n) := by refl
| -[n+1]           := by refl
end

@[simp]
lemma pred_succ (x: integer): pred (x+1) = x :=
match x with
| (from_natural n) := by refl
| -[0+1]           := by refl
| -[(n+1)+1]       := by refl
end

@[simp]
lemma succ_pred (x: integer): (pred x) + 1 = x :=
match x with
| (from_natural (n+1)) := by refl
| (from_natural 0)     := by refl
| -[n+1]               := by refl
end

@[simp]
lemma pred_of_sum_is_sum_with_pred_nat_nat (a b : natural): pred (from_natural a + from_natural b) = from_natural a + (pred (from_natural b)) :=
match b with
| 0    := show pred (a + from_natural 0) = a - 1, by rw [pred_is_sub_one, ←add_zero_ a]
| b+1  :=
calc
    pred (from_natural (a+(b+1))) = from_natural (natural.pred ((a+b)+1))                : by rw [←natural.add_asoc, coe_of_pred_is_pred (natural.succ_ne_zero (a+b))]
    ...                           = from_natural a + from_natural (natural.pred (b+1))   : by refl
    ...                           = from_natural a + pred (from_natural (b+1))           : by rw coe_of_pred_is_pred (natural.succ_ne_zero b)
end

@[simp]
lemma sub_of_natural_succ (a b : natural): sub_of_natural (a+1) b = (sub_of_natural a b) + 1 :=
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

@[simp]
lemma sub_of_natural_pred (a b : natural): sub_of_natural a (b+1) = pred (sub_of_natural a b) :=
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

@[simp]
lemma pred_of_sum_is_sum_with_pred_neg_nat (a b : natural): pred (-[a+1] + from_natural b) = -[a+1] + pred (from_natural b) :=
match b with
| 0   := show pred (-[a+1] + from_natural 0) = pred (-[a+1]), by rw ←add_zero_ (-[a+1])
| b+1 :=
calc
    pred (sub_of_natural (b+1) (a+1))  = sub_of_natural b (a+1)                 : by rw [sub_of_natural_succ, pred_succ]
    ...                                = -[a+1] + from_natural b                : by refl
    ...                                = -[a+1] + (pred (from_natural (b+1)))   : by rw [←pred_succ (from_natural b), coe_of_succ_is_succ b]
end

@[simp]
lemma pred_of_sum_is_sum_with_pred_nat_neg (a b : natural): pred (from_natural a + -[b+1]) = from_natural a + pred(-[b+1]) :=
show pred (sub_of_natural a (b+1)) = sub_of_natural a ((b+1)+1), by rw ←sub_of_natural_pred


@[simp]
lemma pred_of_sum_is_sum_with_pred_neg_neg (a b : natural): pred (-[a+1] + -[b+1]) = -[a+1] + pred(-[b+1]) :=
show -[((a+b+1)+1)+1] = -[(a+(b+1)+1)+1], by rw natural.add_asoc a


@[simp]
lemma pred_of_sum_is_sum_with_pred (x y : integer): pred (x + y) = x + (pred y) :=
match x, y with
| from_natural a, from_natural b := pred_of_sum_is_sum_with_pred_nat_nat a b
| -[a+1],         from_natural b := pred_of_sum_is_sum_with_pred_neg_nat a b
| from_natural a, -[b+1]         := pred_of_sum_is_sum_with_pred_nat_neg a b
| -[a+1],         -[b+1]         := pred_of_sum_is_sum_with_pred_neg_neg a b
end

@[simp]
lemma sub_of_natural_of_add_asoc (a b c: natural): sub_of_natural (a + b) c = from_natural a + sub_of_natural b c :=
    natural.rec_on c (
        calc
            sub_of_natural (a + b) 0 = from_natural (a + b)                   : by rw sub_of_natural_zero
            ...                      = from_natural a + from_natural b        : by refl
            ...                      = from_natural a + (sub_of_natural b 0)  : by rw sub_of_natural_zero
    ) (
        assume n: natural,
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

@[simp]
lemma add_com (x y : integer): x + y = y + x :=
match x, y with
| from_natural a, from_natural b := show from_natural (a+b) = from_natural (b+a), by rw natural.add_com
| from_natural a, -[b+1]         := by refl
| -[a+1],         from_natural b := by refl
| -[a+1],         -[b+1]         := show -[(a+b+1)+1] = -[(b+a+1)+1], by rw natural.add_com a b
end

@[simp]
lemma sub_of_natural_of_add_right_asoc (a b c: natural): sub_of_natural (a + b) c = sub_of_natural a c + from_natural b:=
calc
    sub_of_natural (a+b) c = sub_of_natural (b+a) c                 : by rw natural.add_com
    ...                    = from_natural b + sub_of_natural a c    : by rw sub_of_natural_of_add_asoc
    ...                    = (sub_of_natural a c) + from_natural b  : by rw add_com

lemma sub_of_sub {a b : natural}: natural.sub b a = 0 → (∀ c: natural, sub_of_natural (a - b) c = sub_of_natural a (b+c)) :=
    assume h: natural.sub b a = 0,
    assume c: natural,
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

lemma sub_of_natural_self (a : natural): sub_of_natural a a = from_natural 0 :=
    have h: natural.sub a a = 0, from natural.sub_self_zero a,
    show sub_of_natural a a = from_natural 0, by rw [sub_of_natural_sub_eq_zero h, h]

@[simp]
lemma inv_sub_of_natural (a b: natural): -(sub_of_natural a b) = sub_of_natural b a :=
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

@[simp]
lemma neg_add (x y: integer): -(x + y) = -x + -y :=
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

@[simp]
lemma neg_neg_add (x y: integer): (x + y) = -(-x + -y) := by rw [neg_neg (x + y), ←neg_add x y]

lemma add_nn_nn_nn_asoc (a b c: natural):
(from_natural a + from_natural b) + from_natural c = from_natural a + (from_natural b + from_natural c) :=
    show from_natural ((a + b) + c) = from_natural (a + (b + c)), by rw natural.add_asoc

lemma add_nn_nn_ng_asoc (a b c: natural):
(from_natural a + from_natural b) + -[c+1] = from_natural a + (from_natural b + -[c+1]) :=
    show sub_of_natural (a+b) (c+1) = from_natural a + (sub_of_natural b (c+1)),
    by rw sub_of_natural_of_add_asoc

lemma add_nn_ng_nn_asoc (a b c: natural):
(from_natural a + -[b+1]) + from_natural c = from_natural a + (-[b+1] + from_natural c) :=
    show (sub_of_natural a (b+1)) + from_natural c = from_natural a + sub_of_natural c (b+1),
    by rw [←sub_of_natural_of_add_right_asoc, sub_of_natural_of_add_asoc]

lemma add_nn_ng_ng_asoc (a b c: natural):
(from_natural a + -[b+1]) + -[c+1] = from_natural a + (-[b+1] + -[c+1]) :=
    if hbaz: natural.sub (b+1) a = 0 then
        calc
            (sub_of_natural a (b+1)) + -[c+1]  = (from_natural (natural.sub a (b+1))) + -[c+1]    : by rw sub_of_natural_sub_eq_zero hbaz
            ...                                = sub_of_natural (a - (b+1)) (c+1)                 : by refl
            ...                                = sub_of_natural a ((b+1)+(c+1))                   : by rw sub_of_sub hbaz
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

@[simp]
lemma neg_add_add_left (x y z: integer): (-x + y) + z = -((x + -y) + -z) :=
    calc
        (-x + y) + z = -(-(-x + y) + -z)    : by rw neg_neg_add
        ...          = -((-(-x) + -y) + -z) : by rw neg_add (-x) y
        ...          = -((x + -y) + -z)     : by rw ←neg_neg x

@[simp]
lemma neg_add_add_right (x y z: integer): -(x + (-y + -z)) = -x + (y + z) :=
    calc
        -(x + (-y + -z)) = -x + -(-y + -z)   : by rw neg_add
        ...              = -x + -(-(y + z))  : by rw neg_add y z
        ...              = -x + (y + z)      : by rw ←neg_neg (y + z)

lemma neg_assoc {x y z: integer}: (x + (-y)) + (-z) = x + ((-y) + (-z)) → (-x + y) + z = -x + (y + z) :=
    assume h: (x + -y) + -z = x + (-y + -z),
    calc
        ((-x + y) + z) = -((x + -y) + -z)  : by rw neg_add_add_left
        ...            = -(x + (-y + -z))  : by rw h
        ...            = -x + (y + z)      : by rw neg_add_add_right

lemma add_ab0_asoc (a b : integer): (a + b) + 0 = a + (b + 0) :=
    show (a + b) + from_natural 0 = a + (b + from_natural 0),
    by rw [←add_zero_ (a+b), ←add_zero_ b]

lemma add_a0b_asoc (a b : integer): (a + 0) + b = a + (0 + b) :=
    show (a + from_natural 0) + b = a + (from_natural 0 + b),
    by rw [←add_zero_ a, ←zero_add_ b]

lemma add_asoc_nn (a : natural) (y z : integer): (from_natural a + y) + z = from_natural a + (y + z) :=
match y, z with
| from_natural b,     from_natural c     := add_nn_nn_nn_asoc a b c
| from_natural b,     -[c+1]             := add_nn_nn_ng_asoc a b c
| -[b+1],             from_natural c     := add_nn_ng_nn_asoc a b c
| -[b+1],             -[c+1]             := add_nn_ng_ng_asoc a b c
end

@[simp]
lemma add_asoc (x y z : integer): (x + y) + z = x + (y + z) :=
match x with
| from_natural a := add_asoc_nn a y z
| -[a+1]         := neg_assoc (add_asoc_nn (a+1) (-y) (-z))
end

end integer