/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import algebra.associated
import tactic.ring

/-! # ℤ[√d]

The ring of integers adjoined with a square root of `d : ℤ`.

After defining the norm, we show that it is a linearly ordered commutative ring,
as well as an integral domain.

We provide the universal property, that ring homomorphisms `ℤ√d →+* R` correspond
to choices of square roots of `d` in `R`.

-/

/-- The ring of integers adjoined with a square root of `d`.
  These have the form `a + b √d` where `a b : ℤ`. The components
  are called `re` and `im` by analogy to the negative `d` case. -/
structure zsqrtd (d : ℤ) :=
(re : ℤ)
(im : ℤ)

prefix `ℤ√`:100 := zsqrtd

namespace zsqrtd
section
parameters {d : ℤ}

instance : decidable_eq ℤ√d :=
by tactic.mk_dec_eq_instance

theorem ext : ∀ {z w : ℤ√d}, z = w ↔ z.re = w.re ∧ z.im = w.im
| ⟨x, y⟩ ⟨x', y'⟩ := ⟨λ h, by injection h; split; assumption,
                      λ ⟨h₁, h₂⟩, by congr; assumption⟩

/-- Convert an integer to a `ℤ√d` -/
def of_int (n : ℤ) : ℤ√d := ⟨n, 0⟩
theorem of_int_re (n : ℤ) : (of_int n).re = n := rfl
theorem of_int_im (n : ℤ) : (of_int n).im = 0 := rfl

/-- The zero of the ring -/
def zero : ℤ√d := of_int 0
instance : has_zero ℤ√d := ⟨zsqrtd.zero⟩
@[simp] theorem zero_re : (0 : ℤ√d).re = 0 := rfl
@[simp] theorem zero_im : (0 : ℤ√d).im = 0 := rfl

instance : inhabited ℤ√d := ⟨0⟩

/-- The one of the ring -/
def one : ℤ√d := of_int 1
instance : has_one ℤ√d := ⟨zsqrtd.one⟩
@[simp] theorem one_re : (1 : ℤ√d).re = 1 := rfl
@[simp] theorem one_im : (1 : ℤ√d).im = 0 := rfl

/-- The representative of `√d` in the ring -/
def sqrtd : ℤ√d := ⟨0, 1⟩
@[simp] theorem sqrtd_re : (sqrtd : ℤ√d).re = 0 := rfl
@[simp] theorem sqrtd_im : (sqrtd : ℤ√d).im = 1 := rfl

/-- Addition of elements of `ℤ√d` -/
def add : ℤ√d → ℤ√d → ℤ√d
| ⟨x, y⟩ ⟨x', y'⟩ := ⟨x + x', y + y'⟩
instance : has_add ℤ√d := ⟨zsqrtd.add⟩
@[simp] theorem add_def (x y x' y' : ℤ) :
  (⟨x, y⟩ + ⟨x', y'⟩ : ℤ√d) = ⟨x + x', y + y'⟩ := rfl
@[simp] theorem add_re : ∀ z w : ℤ√d, (z + w).re = z.re + w.re
| ⟨x, y⟩ ⟨x', y'⟩ := rfl
@[simp] theorem add_im : ∀ z w : ℤ√d, (z + w).im = z.im + w.im
| ⟨x, y⟩ ⟨x', y'⟩ := rfl

@[simp] theorem bit0_re (z) : (bit0 z : ℤ√d).re = bit0 z.re := add_re _ _
@[simp] theorem bit0_im (z) : (bit0 z : ℤ√d).im = bit0 z.im := add_im _ _

@[simp] theorem bit1_re (z) : (bit1 z : ℤ√d).re = bit1 z.re := by simp [bit1]
@[simp] theorem bit1_im (z) : (bit1 z : ℤ√d).im = bit0 z.im := by simp [bit1]

/-- Negation in `ℤ√d` -/
def neg : ℤ√d → ℤ√d
| ⟨x, y⟩ := ⟨-x, -y⟩
instance : has_neg ℤ√d := ⟨zsqrtd.neg⟩
@[simp] theorem neg_re : ∀ z : ℤ√d, (-z).re = -z.re
| ⟨x, y⟩ := rfl
@[simp] theorem neg_im : ∀ z : ℤ√d, (-z).im = -z.im
| ⟨x, y⟩ := rfl

/-- Multiplication in `ℤ√d` -/
def mul : ℤ√d → ℤ√d → ℤ√d
| ⟨x, y⟩ ⟨x', y'⟩ := ⟨x * x' + d * y * y', x * y' + y * x'⟩
instance : has_mul ℤ√d := ⟨zsqrtd.mul⟩
@[simp] theorem mul_re : ∀ z w : ℤ√d, (z * w).re = z.re * w.re + d * z.im * w.im
| ⟨x, y⟩ ⟨x', y'⟩ := rfl
@[simp] theorem mul_im : ∀ z w : ℤ√d, (z * w).im = z.re * w.im + z.im * w.re
| ⟨x, y⟩ ⟨x', y'⟩ := rfl

instance : comm_ring ℤ√d :=
by refine_struct
{ add            := (+),
  zero           := (0 : ℤ√d),
  neg            := has_neg.neg,
  mul            := (*),
  sub            := λ a b, a + -b,
  one            := 1,
  npow           := @npow_rec _ ⟨1⟩ ⟨(*)⟩,
  nsmul          := @nsmul_rec _ ⟨0⟩ ⟨(+)⟩,
  gsmul          := @gsmul_rec _ ⟨0⟩ ⟨(+)⟩ ⟨zsqrtd.neg⟩ };
intros; try { refl }; simp [ext, add_mul, mul_add, add_comm, add_left_comm, mul_comm, mul_left_comm]

instance : add_comm_monoid ℤ√d    := by apply_instance
instance : add_monoid ℤ√d         := by apply_instance
instance : monoid ℤ√d             := by apply_instance
instance : comm_monoid ℤ√d        := by apply_instance
instance : comm_semigroup ℤ√d     := by apply_instance
instance : semigroup ℤ√d          := by apply_instance
instance : add_comm_semigroup ℤ√d := by apply_instance
instance : add_semigroup ℤ√d      := by apply_instance
instance : comm_semiring ℤ√d      := by apply_instance
instance : semiring ℤ√d           := by apply_instance
instance : ring ℤ√d               := by apply_instance
instance : distrib ℤ√d            := by apply_instance

/-- Conjugation in `ℤ√d`. The conjugate of `a + b √d` is `a - b √d`. -/
def conj : ℤ√d → ℤ√d
| ⟨x, y⟩ := ⟨x, -y⟩
@[simp] theorem conj_re : ∀ z : ℤ√d, (conj z).re = z.re
| ⟨x, y⟩ := rfl
@[simp] theorem conj_im : ∀ z : ℤ√d, (conj z).im = -z.im
| ⟨x, y⟩ := rfl

/-- `conj` as an `add_monoid_hom`. -/
def conj_hom : ℤ√d →+ ℤ√d :=
{ to_fun := conj,
  map_add' := λ ⟨a, ai⟩ ⟨b, bi⟩, ext.mpr ⟨rfl, neg_add _ _⟩,
  map_zero' := ext.mpr ⟨rfl, neg_zero⟩ }

@[simp] lemma conj_zero : conj (0 : ℤ√d) = 0 :=
conj_hom.map_zero

@[simp] lemma conj_one : conj (1 : ℤ√d) = 1 :=
by simp only [zsqrtd.ext, zsqrtd.conj_re, zsqrtd.conj_im, zsqrtd.one_im, neg_zero, eq_self_iff_true,
  and_self]

@[simp] lemma conj_neg (x : ℤ√d) : (-x).conj = -x.conj :=
conj_hom.map_neg x

@[simp] lemma conj_add (x y : ℤ√d) : (x + y).conj = x.conj + y.conj :=
conj_hom.map_add x y

@[simp] lemma conj_sub (x y : ℤ√d) : (x - y).conj = x.conj - y.conj :=
conj_hom.map_sub x y

@[simp] lemma conj_conj {d : ℤ} (x : ℤ√d) : x.conj.conj = x :=
by simp only [ext, true_and, conj_re, eq_self_iff_true, neg_neg, conj_im]

instance : nontrivial ℤ√d :=
⟨⟨0, 1, dec_trivial⟩⟩

@[simp] theorem coe_nat_re (n : ℕ) : (n : ℤ√d).re = n :=
by induction n; simp *
@[simp] theorem coe_nat_im (n : ℕ) : (n : ℤ√d).im = 0 :=
by induction n; simp *
theorem coe_nat_val (n : ℕ) : (n : ℤ√d) = ⟨n, 0⟩ :=
by simp [ext]

@[simp] theorem coe_int_re (n : ℤ) : (n : ℤ√d).re = n :=
by cases n; simp [*, int.of_nat_eq_coe, int.neg_succ_of_nat_eq]
@[simp] theorem coe_int_im (n : ℤ) : (n : ℤ√d).im = 0 :=
by cases n; simp *
theorem coe_int_val (n : ℤ) : (n : ℤ√d) = ⟨n, 0⟩ :=
by simp [ext]

instance : char_zero ℤ√d :=
{ cast_injective := λ m n, by simp [ext] }

@[simp] theorem of_int_eq_coe (n : ℤ) : (of_int n : ℤ√d) = n :=
by simp [ext, of_int_re, of_int_im]

@[simp] theorem smul_val (n x y : ℤ) : (n : ℤ√d) * ⟨x, y⟩ = ⟨n * x, n * y⟩ :=
by simp [ext]

@[simp] theorem muld_val (x y : ℤ) : sqrtd * ⟨x, y⟩ = ⟨d * y, x⟩ :=
by simp [ext]

@[simp] theorem dmuld : sqrtd * sqrtd = d :=
by simp [ext]

@[simp] theorem smuld_val (n x y : ℤ) : sqrtd * (n : ℤ√d) * ⟨x, y⟩ = ⟨d * n * y, n * x⟩ :=
by simp [ext]

theorem decompose {x y : ℤ} : (⟨x, y⟩ : ℤ√d) = x + sqrtd * y :=
by simp [ext]

theorem mul_conj {x y : ℤ} : (⟨x, y⟩ * conj ⟨x, y⟩ : ℤ√d) = x * x - d * y * y :=
by simp [ext, sub_eq_add_neg, mul_comm]

theorem conj_mul {a b : ℤ√d} : conj (a * b) = conj a * conj b :=
by { simp [ext], ring }

protected lemma coe_int_add (m n : ℤ) : (↑(m + n) : ℤ√d) = ↑m + ↑n :=
(int.cast_ring_hom _).map_add _ _
protected lemma coe_int_sub (m n : ℤ) : (↑(m - n) : ℤ√d) = ↑m - ↑n :=
(int.cast_ring_hom _).map_sub _ _
protected lemma coe_int_mul (m n : ℤ) : (↑(m * n) : ℤ√d) = ↑m * ↑n :=
(int.cast_ring_hom _).map_mul _ _
protected lemma coe_int_inj {m n : ℤ} (h : (↑m : ℤ√d) = ↑n) : m = n :=
by simpa using congr_arg re h

lemma coe_int_dvd_iff {d : ℤ} (z : ℤ) (a : ℤ√d) : ↑z ∣ a ↔ z ∣ a.re ∧ z ∣ a.im :=
begin
  split,
  { rintro ⟨x, rfl⟩,
    simp only [add_zero, coe_int_re, zero_mul, mul_im, dvd_mul_right, and_self, mul_re, mul_zero,
      coe_int_im] },
  { rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩,
    use ⟨r, i⟩,
    rw [smul_val, ext],
    exact ⟨hr, hi⟩ },
end

/-- Read `sq_le a c b d` as `a √c ≤ b √d` -/
def sq_le (a c b d : ℕ) : Prop := c*a*a ≤ d*b*b

theorem sq_le_of_le {c d x y z w : ℕ} (xz : z ≤ x) (yw : y ≤ w) (xy : sq_le x c y d) :
  sq_le z c w d :=
le_trans (mul_le_mul (nat.mul_le_mul_left _ xz) xz (nat.zero_le _) (nat.zero_le _)) $
  le_trans xy (mul_le_mul (nat.mul_le_mul_left _ yw) yw (nat.zero_le _) (nat.zero_le _))

theorem sq_le_add_mixed {c d x y z w : ℕ} (xy : sq_le x c y d) (zw : sq_le z c w d) :
  c * (x * z) ≤ d * (y * w) :=
nat.mul_self_le_mul_self_iff.2 $
by simpa [mul_comm, mul_left_comm] using
   mul_le_mul xy zw (nat.zero_le _) (nat.zero_le _)

theorem sq_le_add {c d x y z w : ℕ} (xy : sq_le x c y d) (zw : sq_le z c w d) :
  sq_le (x + z) c (y + w) d :=
begin
  have xz := sq_le_add_mixed xy zw,
  simp [sq_le, mul_assoc] at xy zw,
  simp [sq_le, mul_add, mul_comm, mul_left_comm, add_le_add, *]
end

theorem sq_le_cancel {c d x y z w : ℕ} (zw : sq_le y d x c) (h : sq_le (x + z) c (y + w) d) :
  sq_le z c w d :=
begin
  apply le_of_not_gt,
  intro l,
  refine not_le_of_gt _ h,
  simp [sq_le, mul_add, mul_comm, mul_left_comm, add_assoc],
  have hm := sq_le_add_mixed zw (le_of_lt l),
  simp [sq_le, mul_assoc] at l zw,
  exact lt_of_le_of_lt (add_le_add_right zw _)
    (add_lt_add_left (add_lt_add_of_le_of_lt hm (add_lt_add_of_le_of_lt hm l)) _)
end

theorem sq_le_smul {c d x y : ℕ} (n : ℕ) (xy : sq_le x c y d) : sq_le (n * x) c (n * y) d :=
by simpa [sq_le, mul_left_comm, mul_assoc] using
   nat.mul_le_mul_left (n * n) xy

theorem sq_le_mul {d x y z w : ℕ} :
  (sq_le x 1 y d → sq_le z 1 w d → sq_le (x * w + y * z) d (x * z + d * y * w) 1) ∧
  (sq_le x 1 y d → sq_le w d z 1 → sq_le (x * z + d * y * w) 1 (x * w + y * z) d) ∧
  (sq_le y d x 1 → sq_le z 1 w d → sq_le (x * z + d * y * w) 1 (x * w + y * z) d) ∧
  (sq_le y d x 1 → sq_le w d z 1 → sq_le (x * w + y * z) d (x * z + d * y * w) 1) :=
by refine ⟨_, _, _, _⟩; {
  intros xy zw,
  have := int.mul_nonneg (sub_nonneg_of_le (int.coe_nat_le_coe_nat_of_le xy))
                         (sub_nonneg_of_le (int.coe_nat_le_coe_nat_of_le zw)),
  refine int.le_of_coe_nat_le_coe_nat (le_of_sub_nonneg _),
  convert this,
  simp only [one_mul, int.coe_nat_add, int.coe_nat_mul],
  ring }

/-- "Generalized" `nonneg`. `nonnegg c d x y` means `a √c + b √d ≥ 0`;
  we are interested in the case `c = 1` but this is more symmetric -/
def nonnegg (c d : ℕ) : ℤ → ℤ → Prop
| (a : ℕ) (b : ℕ) := true
| (a : ℕ) -[1+ b] := sq_le (b+1) c a d
| -[1+ a] (b : ℕ) := sq_le (a+1) d b c
| -[1+ a] -[1+ b] := false

theorem nonnegg_comm {c d : ℕ} {x y : ℤ} : nonnegg c d x y = nonnegg d c y x :=
by induction x; induction y; refl

theorem nonnegg_neg_pos {c d} : Π {a b : ℕ}, nonnegg c d (-a) b ↔ sq_le a d b c
| 0     b := ⟨by simp [sq_le, nat.zero_le], λa, trivial⟩
| (a+1) b := by rw ← int.neg_succ_of_nat_coe; refl

theorem nonnegg_pos_neg {c d} {a b : ℕ} : nonnegg c d a (-b) ↔ sq_le b c a d :=
by rw nonnegg_comm; exact nonnegg_neg_pos

theorem nonnegg_cases_right {c d} {a : ℕ} :
  Π {b : ℤ}, (Π x : ℕ, b = -x → sq_le x c a d) → nonnegg c d a b
| (b:nat) h := trivial
| -[1+ b] h := h (b+1) rfl

theorem nonnegg_cases_left {c d} {b : ℕ} {a : ℤ} (h : Π x : ℕ, a = -x → sq_le x d b c) :
  nonnegg c d a b :=
cast nonnegg_comm (nonnegg_cases_right h)

section norm

def norm (n : ℤ√d) : ℤ := n.re * n.re - d * n.im * n.im
lemma norm_def (n : ℤ√d) : n.norm = n.re * n.re - d * n.im * n.im := rfl

@[simp] lemma norm_zero : norm 0 = 0 := by simp [norm]

@[simp] lemma norm_one : norm 1 = 1 := by simp [norm]

@[simp] lemma norm_int_cast (n : ℤ) : norm n = n * n := by simp [norm]

@[simp] lemma norm_nat_cast (n : ℕ) : norm n = n * n := norm_int_cast n

@[simp] lemma norm_mul (n m : ℤ√d) : norm (n * m) = norm n * norm m :=
by { simp only [norm, mul_im, mul_re], ring }

/-- `norm` as a `monoid_hom`. -/
def norm_monoid_hom : ℤ√d →* ℤ :=
{ to_fun := norm,
  map_mul' := norm_mul,
  map_one' := norm_one }

lemma norm_eq_mul_conj (n : ℤ√d) : (norm n : ℤ√d) = n * n.conj :=
by cases n; simp [norm, conj, zsqrtd.ext, mul_comm, sub_eq_add_neg]

@[simp] lemma norm_neg (x : ℤ√d) : (-x).norm = x.norm :=
coe_int_inj $ by simp only [norm_eq_mul_conj, conj_neg, neg_mul_eq_neg_mul_symm,
  mul_neg_eq_neg_mul_symm, neg_neg]

@[simp] lemma norm_conj (x : ℤ√d) : x.conj.norm = x.norm :=
coe_int_inj $ by simp only [norm_eq_mul_conj, conj_conj, mul_comm]

instance : is_monoid_hom norm :=
{ map_one := norm_one, map_mul := norm_mul }

lemma norm_nonneg (hd : d ≤ 0) (n : ℤ√d) : 0 ≤ n.norm :=
add_nonneg (mul_self_nonneg _)
  (by rw [mul_assoc, neg_mul_eq_neg_mul];
    exact (mul_nonneg (neg_nonneg.2 hd) (mul_self_nonneg _)))

lemma norm_eq_one_iff {x : ℤ√d} : x.norm.nat_abs = 1 ↔ is_unit x :=
⟨λ h, is_unit_iff_dvd_one.2 $
  (le_total 0 (norm x)).cases_on
    (λ hx, show x ∣ 1, from ⟨x.conj,
      by rwa [← int.coe_nat_inj', int.nat_abs_of_nonneg hx,
        ← @int.cast_inj (ℤ√d) _ _, norm_eq_mul_conj, eq_comm] at h⟩)
    (λ hx, show x ∣ 1, from ⟨- x.conj,
      by rwa [← int.coe_nat_inj', int.of_nat_nat_abs_of_nonpos hx,
        ← @int.cast_inj (ℤ√d) _ _, int.cast_neg, norm_eq_mul_conj, neg_mul_eq_mul_neg,
        eq_comm] at h⟩),
λ h, let ⟨y, hy⟩ := is_unit_iff_dvd_one.1 h in begin
  have := congr_arg (int.nat_abs ∘ norm) hy,
  rw [function.comp_app, function.comp_app, norm_mul, int.nat_abs_mul,
    norm_one, int.nat_abs_one, eq_comm, nat.mul_eq_one_iff] at this,
  exact this.1
end⟩

lemma is_unit_iff_norm_is_unit {d : ℤ} (z : ℤ√d) : is_unit z ↔ is_unit z.norm :=
by rw [int.is_unit_iff_nat_abs_eq, norm_eq_one_iff]

lemma norm_eq_one_iff' {d : ℤ} (hd : d ≤ 0) (z : ℤ√d) : z.norm = 1 ↔ is_unit z :=
by rw [←norm_eq_one_iff, ←int.coe_nat_inj', int.nat_abs_of_nonneg (norm_nonneg hd z),
  int.coe_nat_one]

lemma norm_eq_zero_iff {d : ℤ} (hd : d < 0) (z : ℤ√d) : z.norm = 0 ↔ z = 0 :=
begin
  split,
  { intro h,
    rw [ext, zero_re, zero_im],
    rw [norm_def, sub_eq_add_neg, mul_assoc] at h,
    have left := mul_self_nonneg z.re,
    have right := neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg hd.le (mul_self_nonneg z.im)),
    obtain ⟨ha, hb⟩ := (add_eq_zero_iff' left right).mp h,
    split; apply eq_zero_of_mul_self_eq_zero,
    { exact ha },
    { rw [neg_eq_zero, mul_eq_zero] at hb,
      exact hb.resolve_left hd.ne } },
  { rintro rfl, exact norm_zero }
end

lemma norm_eq_of_associated {d : ℤ} (hd : d ≤ 0) {x y : ℤ√d} (h : associated x y) :
  x.norm = y.norm :=
begin
  obtain ⟨u, rfl⟩ := h,
  rw [norm_mul, (norm_eq_one_iff' hd _).mpr u.is_unit, mul_one],
end

end norm

end

section
parameter {d : ℕ}

/-- Nonnegativity of an element of `ℤ√d`. -/
def nonneg : ℤ√d → Prop | ⟨a, b⟩ := nonnegg d 1 a b

protected def le (a b : ℤ√d) : Prop := nonneg (b - a)

instance : has_le ℤ√d := ⟨zsqrtd.le⟩

protected def lt (a b : ℤ√d) : Prop := ¬(b ≤ a)

instance : has_lt ℤ√d := ⟨zsqrtd.lt⟩

instance decidable_nonnegg (c d a b) : decidable (nonnegg c d a b) :=
by cases a; cases b; repeat {rw int.of_nat_eq_coe}; unfold nonnegg sq_le; apply_instance

instance decidable_nonneg : Π (a : ℤ√d), decidable (nonneg a)
| ⟨a, b⟩ := zsqrtd.decidable_nonnegg _ _ _ _

instance decidable_le (a b : ℤ√d) : decidable (a ≤ b) := decidable_nonneg _

theorem nonneg_cases : Π {a : ℤ√d}, nonneg a → ∃ x y : ℕ, a = ⟨x, y⟩ ∨ a = ⟨x, -y⟩ ∨ a = ⟨-x, y⟩
| ⟨(x : ℕ), (y : ℕ)⟩ h := ⟨x, y, or.inl rfl⟩
| ⟨(x : ℕ), -[1+ y]⟩ h := ⟨x, y+1, or.inr $ or.inl rfl⟩
| ⟨-[1+ x], (y : ℕ)⟩ h := ⟨x+1, y, or.inr $ or.inr rfl⟩
| ⟨-[1+ x], -[1+ y]⟩ h := false.elim h

lemma nonneg_add_lem {x y z w : ℕ} (xy : nonneg ⟨x, -y⟩) (zw : nonneg ⟨-z, w⟩) :
  nonneg (⟨x, -y⟩ + ⟨-z, w⟩) :=
have nonneg ⟨int.sub_nat_nat x z, int.sub_nat_nat w y⟩, from int.sub_nat_nat_elim x z
  (λm n i, sq_le y d m 1 → sq_le n 1 w d → nonneg ⟨i, int.sub_nat_nat w y⟩)
  (λj k, int.sub_nat_nat_elim w y
    (λm n i, sq_le n d (k + j) 1 → sq_le k 1 m d → nonneg ⟨int.of_nat j, i⟩)
    (λm n xy zw, trivial)
    (λm n xy zw, sq_le_cancel zw xy))
  (λj k, int.sub_nat_nat_elim w y
    (λm n i, sq_le n d k 1 → sq_le (k + j + 1) 1 m d → nonneg ⟨-[1+ j], i⟩)
    (λm n xy zw, sq_le_cancel xy zw)
    (λm n xy zw, let t := nat.le_trans zw (sq_le_of_le (nat.le_add_right n (m+1)) (le_refl _) xy) in
      have k + j + 1 ≤ k, from nat.mul_self_le_mul_self_iff.2 (by repeat{rw one_mul at t}; exact t),
      absurd this (not_le_of_gt $ nat.succ_le_succ $ nat.le_add_right _ _))) (nonnegg_pos_neg.1 xy)
        (nonnegg_neg_pos.1 zw),
show nonneg ⟨_, _⟩, by rw [neg_add_eq_sub];
  rwa [int.sub_nat_nat_eq_coe,int.sub_nat_nat_eq_coe] at this

theorem nonneg_add {a b : ℤ√d} (ha : nonneg a) (hb : nonneg b) : nonneg (a + b) :=
begin
  rcases nonneg_cases ha with ⟨x, y, rfl|rfl|rfl⟩;
  rcases nonneg_cases hb with ⟨z, w, rfl|rfl|rfl⟩; dsimp [add, nonneg] at ha hb ⊢,
  { trivial },
  { refine nonnegg_cases_right (λi h, sq_le_of_le _ _ (nonnegg_pos_neg.1 hb)),
    { exact int.coe_nat_le.1 (le_of_neg_le_neg (@int.le.intro _ _ y (by simp [add_comm, *]))) },
    { apply nat.le_add_left } },
  { refine nonnegg_cases_left (λi h, sq_le_of_le _ _ (nonnegg_neg_pos.1 hb)),
    { exact int.coe_nat_le.1 (le_of_neg_le_neg (@int.le.intro _ _ x (by simp [add_comm, *]))) },
    { apply nat.le_add_left } },
  { refine nonnegg_cases_right (λi h, sq_le_of_le _ _ (nonnegg_pos_neg.1 ha)),
    { exact int.coe_nat_le.1 (le_of_neg_le_neg (@int.le.intro _ _ w (by simp *))) },
    { apply nat.le_add_right } },
  { simpa [add_comm] using
      nonnegg_pos_neg.2 (sq_le_add (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb)) },
  { exact nonneg_add_lem ha hb },
  { refine nonnegg_cases_left (λi h, sq_le_of_le _ _ (nonnegg_neg_pos.1 ha)),
    { exact int.coe_nat_le.1 (le_of_neg_le_neg (int.le.intro h)) },
    { apply nat.le_add_right } },
  { rw [add_comm, add_comm ↑y], exact nonneg_add_lem hb ha },
  { simpa [add_comm] using
      nonnegg_neg_pos.2 (sq_le_add (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb)) },
end

theorem le_refl (a : ℤ√d) : a ≤ a := show nonneg (a - a), by simp

protected theorem le_trans {a b c : ℤ√d} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c :=
have nonneg (b - a + (c - b)), from nonneg_add ab bc,
by simpa [sub_add_sub_cancel']

theorem nonneg_iff_zero_le {a : ℤ√d} : nonneg a ↔ 0 ≤ a := show _ ↔ nonneg _, by simp

theorem le_of_le_le {x y z w : ℤ} (xz : x ≤ z) (yw : y ≤ w) : (⟨x, y⟩ : ℤ√d) ≤ ⟨z, w⟩ :=
show nonneg ⟨z - x, w - y⟩, from
match z - x, w - y, int.le.dest_sub xz, int.le.dest_sub yw with ._, ._, ⟨a, rfl⟩, ⟨b, rfl⟩ :=
  trivial end

theorem le_arch (a : ℤ√d) : ∃n : ℕ, a ≤ n :=
let ⟨x, y, (h : a ≤ ⟨x, y⟩)⟩ := show ∃x y : ℕ, nonneg (⟨x, y⟩ + -a), from match -a with
| ⟨int.of_nat x, int.of_nat y⟩ := ⟨0, 0, trivial⟩
| ⟨int.of_nat x, -[1+ y]⟩      := ⟨0, y+1, by simp [int.neg_succ_of_nat_coe, add_assoc]⟩
| ⟨-[1+ x],      int.of_nat y⟩ := ⟨x+1, 0, by simp [int.neg_succ_of_nat_coe, add_assoc]⟩
| ⟨-[1+ x],      -[1+ y]⟩      := ⟨x+1, y+1, by simp [int.neg_succ_of_nat_coe, add_assoc]⟩
end in begin
  refine ⟨x + d*y, zsqrtd.le_trans h _⟩,
  rw [← int.cast_coe_nat, ← of_int_eq_coe],
  change nonneg ⟨(↑x + d*y) - ↑x, 0-↑y⟩,
  cases y with y,
  { simp },
  have h : ∀y, sq_le y d (d * y) 1 := λ y,
    by simpa [sq_le, mul_comm, mul_left_comm] using
       nat.mul_le_mul_right (y * y) (nat.le_mul_self d),
  rw [show (x:ℤ) + d * nat.succ y - x = d * nat.succ y, by simp],
  exact h (y+1)
end

protected theorem nonneg_total : Π (a : ℤ√d), nonneg a ∨ nonneg (-a)
| ⟨(x : ℕ), (y : ℕ)⟩ := or.inl trivial
| ⟨-[1+ x], -[1+ y]⟩ := or.inr trivial
| ⟨0,       -[1+ y]⟩ := or.inr trivial
| ⟨-[1+ x], 0⟩       := or.inr trivial
| ⟨(x+1:ℕ), -[1+ y]⟩ := nat.le_total
| ⟨-[1+ x], (y+1:ℕ)⟩ := nat.le_total

protected theorem le_total (a b : ℤ√d) : a ≤ b ∨ b ≤ a :=
let t := nonneg_total (b - a) in by rw [show -(b-a) = a-b, from neg_sub b a] at t; exact t

instance : preorder ℤ√d :=
{ le               := zsqrtd.le,
  le_refl          := zsqrtd.le_refl,
  le_trans         := @zsqrtd.le_trans,
  lt               := zsqrtd.lt,
  lt_iff_le_not_le := λ a b,
    (and_iff_right_of_imp (zsqrtd.le_total _ _).resolve_left).symm }

protected theorem add_le_add_left (a b : ℤ√d) (ab : a ≤ b) (c : ℤ√d) : c + a ≤ c + b :=
show nonneg _, by rw add_sub_add_left_eq_sub; exact ab

protected theorem le_of_add_le_add_left (a b c : ℤ√d) (h : c + a ≤ c + b) : a ≤ b :=
by simpa using zsqrtd.add_le_add_left _ _ h (-c)

protected theorem add_lt_add_left (a b : ℤ√d) (h : a < b) (c) : c + a < c + b :=
λ h', h (zsqrtd.le_of_add_le_add_left _ _ _ h')

theorem nonneg_smul {a : ℤ√d} {n : ℕ} (ha : nonneg a) : nonneg (n * a) :=
by rw ← int.cast_coe_nat; exact match a, nonneg_cases ha, ha with
| ._, ⟨x, y, or.inl rfl⟩,          ha := by rw smul_val; trivial
| ._, ⟨x, y, or.inr $ or.inl rfl⟩, ha := by rw smul_val; simpa using
  nonnegg_pos_neg.2 (sq_le_smul n $ nonnegg_pos_neg.1 ha)
| ._, ⟨x, y, or.inr $ or.inr rfl⟩, ha := by rw smul_val; simpa using
  nonnegg_neg_pos.2 (sq_le_smul n $ nonnegg_neg_pos.1 ha)
end

theorem nonneg_muld {a : ℤ√d} (ha : nonneg a) : nonneg (sqrtd * a) :=
by refine match a, nonneg_cases ha, ha with
| ._, ⟨x, y, or.inl rfl⟩,          ha := trivial
| ._, ⟨x, y, or.inr $ or.inl rfl⟩, ha := by simp; apply nonnegg_neg_pos.2;
  simpa [sq_le, mul_comm, mul_left_comm] using
    nat.mul_le_mul_left d (nonnegg_pos_neg.1 ha)
| ._, ⟨x, y, or.inr $ or.inr rfl⟩, ha := by simp; apply nonnegg_pos_neg.2;
  simpa [sq_le, mul_comm, mul_left_comm] using
    nat.mul_le_mul_left d (nonnegg_neg_pos.1 ha)
end

theorem nonneg_mul_lem {x y : ℕ} {a : ℤ√d} (ha : nonneg a) : nonneg (⟨x, y⟩ * a) :=
have (⟨x, y⟩ * a : ℤ√d) = x * a + sqrtd * (y * a), by rw [decompose, right_distrib, mul_assoc];
  refl,
by rw this; exact nonneg_add (nonneg_smul ha) (nonneg_muld $ nonneg_smul ha)

theorem nonneg_mul {a b : ℤ√d} (ha : nonneg a) (hb : nonneg b) : nonneg (a * b) :=
match a, b, nonneg_cases ha, nonneg_cases hb, ha, hb with
| ._, ._, ⟨x, y, or.inl rfl⟩,          ⟨z, w, or.inl rfl⟩,          ha, hb := trivial
| ._, ._, ⟨x, y, or.inl rfl⟩,          ⟨z, w, or.inr $ or.inr rfl⟩, ha, hb := nonneg_mul_lem hb
| ._, ._, ⟨x, y, or.inl rfl⟩,          ⟨z, w, or.inr $ or.inl rfl⟩, ha, hb := nonneg_mul_lem hb
| ._, ._, ⟨x, y, or.inr $ or.inr rfl⟩, ⟨z, w, or.inl rfl⟩,          ha, hb :=
  by rw mul_comm; exact nonneg_mul_lem ha
| ._, ._, ⟨x, y, or.inr $ or.inl rfl⟩, ⟨z, w, or.inl rfl⟩,          ha, hb :=
  by rw mul_comm; exact nonneg_mul_lem ha
| ._, ._, ⟨x, y, or.inr $ or.inr rfl⟩, ⟨z, w, or.inr $ or.inr rfl⟩, ha, hb :=
  by rw [calc (⟨-x, y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ : rfl
      ... = ⟨x * z + d * y * w, -(x * w + y * z)⟩ : by simp [add_comm]]; exact
  nonnegg_pos_neg.2 (sq_le_mul.left (nonnegg_neg_pos.1 ha) (nonnegg_neg_pos.1 hb))
| ._, ._, ⟨x, y, or.inr $ or.inr rfl⟩, ⟨z, w, or.inr $ or.inl rfl⟩, ha, hb :=
  by rw [calc (⟨-x, y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ : rfl
      ... = ⟨-(x * z + d * y * w), x * w + y * z⟩ : by simp [add_comm]]; exact
  nonnegg_neg_pos.2 (sq_le_mul.right.left (nonnegg_neg_pos.1 ha) (nonnegg_pos_neg.1 hb))
| ._, ._, ⟨x, y, or.inr $ or.inl rfl⟩, ⟨z, w, or.inr $ or.inr rfl⟩, ha, hb :=
  by rw [calc (⟨x, -y⟩ * ⟨-z, w⟩ : ℤ√d) = ⟨_, _⟩ : rfl
      ... = ⟨-(x * z + d * y * w), x * w + y * z⟩ : by simp [add_comm]]; exact
  nonnegg_neg_pos.2 (sq_le_mul.right.right.left (nonnegg_pos_neg.1 ha) (nonnegg_neg_pos.1 hb))
| ._, ._, ⟨x, y, or.inr $ or.inl rfl⟩, ⟨z, w, or.inr $ or.inl rfl⟩, ha, hb :=
  by rw [calc (⟨x, -y⟩ * ⟨z, -w⟩ : ℤ√d) = ⟨_, _⟩ : rfl
      ... = ⟨x * z + d * y * w, -(x * w + y * z)⟩ : by simp [add_comm]]; exact
  nonnegg_pos_neg.2 (sq_le_mul.right.right.right (nonnegg_pos_neg.1 ha) (nonnegg_pos_neg.1 hb))
end

protected theorem mul_nonneg (a b : ℤ√d) : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
by repeat {rw ← nonneg_iff_zero_le}; exact nonneg_mul

theorem not_sq_le_succ (c d y) (h : 0 < c) : ¬sq_le (y + 1) c 0 d :=
not_le_of_gt $ mul_pos (mul_pos h $ nat.succ_pos _) $ nat.succ_pos _

/-- A nonsquare is a natural number that is not equal to the square of an
  integer. This is implemented as a typeclass because it's a necessary condition
  for much of the Pell equation theory. -/
class nonsquare (x : ℕ) : Prop := (ns [] : ∀n : ℕ, x ≠ n*n)

parameter [dnsq : nonsquare d]
include dnsq

theorem d_pos : 0 < d := lt_of_le_of_ne (nat.zero_le _) $ ne.symm $ (nonsquare.ns d 0)

theorem divides_sq_eq_zero {x y} (h : x * x = d * y * y) : x = 0 ∧ y = 0 :=
let g := x.gcd y in or.elim g.eq_zero_or_pos
  (λH, ⟨nat.eq_zero_of_gcd_eq_zero_left H, nat.eq_zero_of_gcd_eq_zero_right H⟩)
  (λgpos, false.elim $
    let ⟨m, n, co, (hx : x = m * g), (hy : y = n * g)⟩ := nat.exists_coprime gpos in
    begin
      rw [hx, hy] at h,
      have : m * m = d * (n * n) := nat.eq_of_mul_eq_mul_left (mul_pos gpos gpos)
        (by simpa [mul_comm, mul_left_comm] using h),
      have co2 := let co1 := co.mul_right co in co1.mul co1,
      exact nonsquare.ns d m (nat.dvd_antisymm (by rw this; apply dvd_mul_right) $
        co2.dvd_of_dvd_mul_right $ by simp [this])
    end)

theorem divides_sq_eq_zero_z {x y : ℤ} (h : x * x = d * y * y) : x = 0 ∧ y = 0 :=
by rw [mul_assoc, ← int.nat_abs_mul_self, ← int.nat_abs_mul_self, ← int.coe_nat_mul, ← mul_assoc]
  at h;
exact let ⟨h1, h2⟩ := divides_sq_eq_zero (int.coe_nat_inj h) in
⟨int.eq_zero_of_nat_abs_eq_zero h1, int.eq_zero_of_nat_abs_eq_zero h2⟩

theorem not_divides_sq (x y) : (x + 1) * (x + 1) ≠ d * (y + 1) * (y + 1) :=
λe, by have t := (divides_sq_eq_zero e).left; contradiction

theorem nonneg_antisymm : Π {a : ℤ√d}, nonneg a → nonneg (-a) → a = 0
| ⟨0,         0⟩         xy yx := rfl
| ⟨-[1+ x],   -[1+ y]⟩   xy yx := false.elim xy
| ⟨(x+1:nat), (y+1:nat)⟩ xy yx := false.elim yx
| ⟨-[1+ x],   0⟩         xy yx := absurd xy (not_sq_le_succ _ _ _ dec_trivial)
| ⟨(x+1:nat), 0⟩         xy yx := absurd yx (not_sq_le_succ _ _ _ dec_trivial)
| ⟨0,         -[1+ y]⟩   xy yx := absurd xy (not_sq_le_succ _ _ _ d_pos)
| ⟨0,         (y+1:nat)⟩ _  yx := absurd yx (not_sq_le_succ _ _ _ d_pos)
| ⟨(x+1:nat), -[1+ y]⟩   (xy : sq_le _ _ _ _) (yx : sq_le _ _ _ _) :=
  let t := le_antisymm yx xy in by rw[one_mul] at t; exact absurd t (not_divides_sq _ _)
| ⟨-[1+ x],   (y+1:nat)⟩ (xy : sq_le _ _ _ _) (yx : sq_le _ _ _ _) :=
  let t := le_antisymm xy yx in by rw[one_mul] at t; exact absurd t (not_divides_sq _ _)

theorem le_antisymm {a b : ℤ√d} (ab : a ≤ b) (ba : b ≤ a) : a = b :=
eq_of_sub_eq_zero $ nonneg_antisymm ba (by rw neg_sub; exact ab)

instance : linear_order ℤ√d :=
{ le_antisymm     := @zsqrtd.le_antisymm,
  le_total        := zsqrtd.le_total,
  decidable_le    := zsqrtd.decidable_le,
  ..zsqrtd.preorder }

protected theorem eq_zero_or_eq_zero_of_mul_eq_zero : Π {a b : ℤ√d}, a * b = 0 → a = 0 ∨ b = 0
| ⟨x, y⟩ ⟨z, w⟩ h := by injection h with h1 h2; exact
  have h1 : x*z = -(d*y*w), from eq_neg_of_add_eq_zero h1,
  have h2 : x*w = -(y*z), from eq_neg_of_add_eq_zero h2,
  have fin : x*x = d*y*y → (⟨x, y⟩:ℤ√d) = 0, from
  λe, match x, y, divides_sq_eq_zero_z e with ._, ._, ⟨rfl, rfl⟩ := rfl end,
  if z0 : z = 0 then if w0 : w = 0 then
    or.inr (match z, w, z0, w0 with ._, ._, rfl, rfl := rfl end)
  else
     or.inl $ fin $ mul_right_cancel' w0 $ calc
       x * x * w = -y * (x * z) : by simp [h2, mul_assoc, mul_left_comm]
             ... = d * y * y * w : by simp [h1, mul_assoc, mul_left_comm]
  else
     or.inl $ fin $ mul_right_cancel' z0 $ calc
       x * x * z = d * -y * (x * w) : by simp [h1, mul_assoc, mul_left_comm]
             ... = d * y * y * z : by simp [h2, mul_assoc, mul_left_comm]

instance : integral_domain ℤ√d :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := @zsqrtd.eq_zero_or_eq_zero_of_mul_eq_zero,
  .. zsqrtd.comm_ring, .. zsqrtd.nontrivial }

protected theorem mul_pos (a b : ℤ√d) (a0 : 0 < a) (b0 : 0 < b) : 0 < a * b := λab,
or.elim (eq_zero_or_eq_zero_of_mul_eq_zero
         (le_antisymm ab (mul_nonneg _ _ (le_of_lt a0) (le_of_lt b0))))
  (λe, ne_of_gt a0 e)
  (λe, ne_of_gt b0 e)

instance : linear_ordered_comm_ring ℤ√d :=
{ add_le_add_left := @zsqrtd.add_le_add_left,
  mul_pos         := @zsqrtd.mul_pos,
  zero_le_one     := dec_trivial,
  .. zsqrtd.comm_ring, .. zsqrtd.linear_order, .. zsqrtd.nontrivial }

instance : linear_ordered_ring ℤ√d := by apply_instance
instance : ordered_ring ℤ√d        := by apply_instance

end

lemma norm_eq_zero {d : ℤ} (h_nonsquare : ∀ n : ℤ, d ≠ n*n) (a : ℤ√d) :
  norm a = 0 ↔ a = 0 :=
begin
  refine ⟨λ ha, ext.mpr _, λ h, by rw [h, norm_zero]⟩,
  delta norm at ha,
  rw sub_eq_zero at ha,
  by_cases h : 0 ≤ d,
  { obtain ⟨d', rfl⟩ := int.eq_coe_of_zero_le h,
    haveI : nonsquare d' := ⟨λ n h, h_nonsquare n $ by exact_mod_cast h⟩,
    exact divides_sq_eq_zero_z ha, },
  { push_neg at h,
    suffices : a.re * a.re = 0,
    { rw eq_zero_of_mul_self_eq_zero this at ha ⊢,
      simpa only [true_and, or_self_right, zero_re, zero_im, eq_self_iff_true,
        zero_eq_mul, mul_zero, mul_eq_zero, h.ne, false_or, or_self] using ha },
    apply _root_.le_antisymm _ (mul_self_nonneg _),
    rw [ha, mul_assoc],
    exact mul_nonpos_of_nonpos_of_nonneg h.le (mul_self_nonneg _) }
end

variables {R : Type} [comm_ring R]

@[ext] lemma hom_ext {d : ℤ} (f g : ℤ√d →+* R) (h : f sqrtd = g sqrtd) : f = g :=
begin
  ext ⟨x_re, x_im⟩,
  simp [decompose, h],
end

/-- The unique `ring_hom` from `ℤ√d` to a ring `R`, constructed by replacing `√d` with the provided
root. Conversely, this associates to every mapping `ℤ√d →+* R` a value of `√d` in `R`. -/
@[simps]
def lift {d : ℤ} : {r : R // r * r = ↑d} ≃ (ℤ√d →+* R) :=
{ to_fun := λ r,
  { to_fun := λ a, a.1 + a.2*(r : R),
    map_zero' := by simp,
    map_add' := λ a b, by { simp, ring, },
    map_one' := by simp,
    map_mul' := λ a b, by {
      have : (a.re + a.im * r : R) * (b.re + b.im * r) =
              a.re * b.re + (a.re * b.im + a.im * b.re) * r + a.im * b.im * (r * r) := by ring,
      simp [this, r.prop],
      ring, } },
  inv_fun := λ f, ⟨f sqrtd, by rw [←f.map_mul, dmuld, ring_hom.map_int_cast]⟩,
  left_inv := λ r, by { ext, simp },
  right_inv := λ f, by { ext, simp } }

/-- `lift r` is injective if `d` is non-square, and R has characteristic zero (that is, the map from
`ℤ` into `R` is injective). -/
lemma lift_injective [char_zero R] {d : ℤ} (r : {r : R // r * r = ↑d}) (hd : ∀ n : ℤ, d ≠ n*n) :
  function.injective (lift r) :=
(lift r).injective_iff.mpr $ λ a ha,
begin
  have h_inj : function.injective (coe : ℤ → R) := int.cast_injective,
  suffices : lift r a.norm = 0,
  { simp only [coe_int_re, add_zero, lift_apply_apply, coe_int_im, int.cast_zero, zero_mul] at this,
    rwa [← int.cast_zero, h_inj.eq_iff, norm_eq_zero hd] at this },
  rw [norm_eq_mul_conj, ring_hom.map_mul, ha, zero_mul]
end

end zsqrtd
