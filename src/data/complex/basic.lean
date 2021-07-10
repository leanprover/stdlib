/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import data.real.sqrt

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. The result that the complex numbers are algebraically closed, see
`field_theory.algebraic_closure`.
-/

open_locale big_operators

/-! ### Definition and basic arithmmetic -/

/-- Complex numbers consist of two `real`s: a real part `re` and an imaginary part `im`. -/
structure complex : Type :=
(re : ℝ) (im : ℝ)

notation `ℂ` := complex

namespace complex

noncomputable instance : decidable_eq ℂ := classical.dec_eq _

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
def equiv_real_prod : ℂ ≃ (ℝ × ℝ) :=
{ to_fun := λ z, ⟨z.re, z.im⟩,
  inv_fun := λ p, ⟨p.1, p.2⟩,
  left_inv := λ ⟨x, y⟩, rfl,
  right_inv := λ ⟨x, y⟩, rfl }

@[simp] theorem equiv_real_prod_apply (z : ℂ) : equiv_real_prod z = (z.re, z.im) := rfl
theorem equiv_real_prod_symm_re (x y : ℝ) : (equiv_real_prod.symm (x, y)).re = x := rfl
theorem equiv_real_prod_symm_im (x y : ℝ) : (equiv_real_prod.symm (x, y)).im = y := rfl

@[simp] theorem eta : ∀ z : ℂ, complex.mk z.re z.im = z
| ⟨a, b⟩ := rfl

@[ext]
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
| ⟨zr, zi⟩ ⟨_, _⟩ rfl rfl := rfl

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
⟨λ H, by simp [H], and.rec ext⟩

instance : has_coe ℝ ℂ := ⟨λ r, ⟨r, 0⟩⟩

@[simp, norm_cast] lemma of_real_re (r : ℝ) : (r : ℂ).re = r := rfl
@[simp, norm_cast] lemma of_real_im (r : ℝ) : (r : ℂ).im = 0 := rfl
lemma of_real_def (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ := rfl

@[simp, norm_cast] theorem of_real_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
⟨congr_arg re, congr_arg _⟩

instance : has_zero ℂ := ⟨(0 : ℝ)⟩
instance : inhabited ℂ := ⟨0⟩

@[simp] lemma zero_re : (0 : ℂ).re = 0 := rfl
@[simp] lemma zero_im : (0 : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma of_real_zero : ((0 : ℝ) : ℂ) = 0 := rfl

@[simp] theorem of_real_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 := of_real_inj
theorem of_real_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 := not_congr of_real_eq_zero

instance : has_one ℂ := ⟨(1 : ℝ)⟩

@[simp] lemma one_re : (1 : ℂ).re = 1 := rfl
@[simp] lemma one_im : (1 : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma of_real_one : ((1 : ℝ) : ℂ) = 1 := rfl

instance : has_add ℂ := ⟨λ z w, ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp] lemma add_re (z w : ℂ) : (z + w).re = z.re + w.re := rfl
@[simp] lemma add_im (z w : ℂ) : (z + w).im = z.im + w.im := rfl

@[simp] lemma bit0_re (z : ℂ) : (bit0 z).re = bit0 z.re := rfl
@[simp] lemma bit1_re (z : ℂ) : (bit1 z).re = bit1 z.re := rfl
@[simp] lemma bit0_im (z : ℂ) : (bit0 z).im = bit0 z.im := eq.refl _
@[simp] lemma bit1_im (z : ℂ) : (bit1 z).im = bit0 z.im := add_zero _

@[simp, norm_cast] lemma of_real_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
ext_iff.2 $ by simp

@[simp, norm_cast] lemma of_real_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 r :=
ext_iff.2 $ by simp [bit0]

@[simp, norm_cast] lemma of_real_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 r :=
ext_iff.2 $ by simp [bit1]

instance : has_neg ℂ := ⟨λ z, ⟨-z.re, -z.im⟩⟩

@[simp] lemma neg_re (z : ℂ) : (-z).re = -z.re := rfl
@[simp] lemma neg_im (z : ℂ) : (-z).im = -z.im := rfl
@[simp, norm_cast] lemma of_real_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r := ext_iff.2 $ by simp

instance : has_sub ℂ := ⟨λ z w, ⟨z.re - w.re, z.im - w.im⟩⟩

instance : has_mul ℂ := ⟨λ z w, ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp] lemma mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl
@[simp] lemma mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re := rfl
@[simp, norm_cast] lemma of_real_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s := ext_iff.2 $ by simp

lemma of_real_mul_re (r : ℝ) (z : ℂ) : (↑r * z).re = r * z.re := by simp
lemma of_real_mul_im (r : ℝ) (z : ℂ) : (↑r * z).im = r * z.im := by simp
lemma of_real_mul' (r : ℝ) (z : ℂ) : (↑r * z) = ⟨r * z.re, r * z.im⟩ :=
ext (of_real_mul_re _ _) (of_real_mul_im _ _)

/-! ### The imaginary unit, `I` -/

/-- The imaginary unit. -/
def I : ℂ := ⟨0, 1⟩

@[simp] lemma I_re : I.re = 0 := rfl
@[simp] lemma I_im : I.im = 1 := rfl

@[simp] lemma I_mul_I : I * I = -1 := ext_iff.2 $ by simp
lemma I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
ext_iff.2 $ by simp

lemma I_ne_zero : (I : ℂ) ≠ 0 := mt (congr_arg im) zero_ne_one.symm

lemma mk_eq_add_mul_I (a b : ℝ) : complex.mk a b = a + b * I :=
ext_iff.2 $ by simp

@[simp] lemma re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
ext_iff.2 $ by simp

/-! ### Commutative ring instance and lemmas -/

instance : comm_ring ℂ :=
by refine_struct { zero := (0 : ℂ), add := (+), neg := has_neg.neg, sub := has_sub.sub, one := 1,
  mul := (*), nsmul := @nsmul_rec _ ⟨(0)⟩ ⟨(+)⟩, npow := @npow_rec _ ⟨(1)⟩ ⟨(*)⟩,
  gsmul := @gsmul_rec _ ⟨(0)⟩ ⟨(+)⟩ ⟨has_neg.neg⟩ };
intros; try { refl }; apply ext_iff.2; split; simp; {ring1 <|> ring_nf}

/-- This shortcut instance ensures we do not find `ring` via the noncomputable `complex.field`
instance. -/
instance : ring ℂ := by apply_instance

instance re.is_add_group_hom : is_add_group_hom complex.re :=
{ map_add := complex.add_re }

instance im.is_add_group_hom : is_add_group_hom complex.im :=
{ map_add := complex.add_im }

@[simp] lemma I_pow_bit0 (n : ℕ) : I ^ (bit0 n) = (-1) ^ n :=
by rw [pow_bit0', I_mul_I]

@[simp] lemma I_pow_bit1 (n : ℕ) : I ^ (bit1 n) = (-1) ^ n * I :=
by rw [pow_bit1', I_mul_I]

/-! ### Complex conjugation -/

/-- The complex conjugate. -/
def conj : ℂ →+* ℂ :=
begin
  refine_struct { to_fun := λ z : ℂ, (⟨z.re, -z.im⟩ : ℂ), .. };
  { intros, ext; simp [add_comm], },
end

@[simp] lemma conj_re (z : ℂ) : (conj z).re = z.re := rfl
@[simp] lemma conj_im (z : ℂ) : (conj z).im = -z.im := rfl

@[simp] lemma conj_of_real (r : ℝ) : conj r = r := ext_iff.2 $ by simp [conj]

@[simp] lemma conj_I : conj I = -I := ext_iff.2 $ by simp

@[simp] lemma conj_bit0 (z : ℂ) : conj (bit0 z) = bit0 (conj z) := ext_iff.2 $ by simp [bit0]
@[simp] lemma conj_bit1 (z : ℂ) : conj (bit1 z) = bit1 (conj z) := ext_iff.2 $ by simp [bit0]

@[simp] lemma conj_neg_I : conj (-I) = I := ext_iff.2 $ by simp

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
ext_iff.2 $ by simp

lemma conj_involutive : function.involutive conj := conj_conj

lemma conj_bijective : function.bijective conj := conj_involutive.bijective

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
conj_bijective.1.eq_iff

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
by simpa using @conj_inj z 0

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
⟨λ h, ⟨z.re, ext rfl $ eq_zero_of_neg_eq (congr_arg im h)⟩,
 λ ⟨h, e⟩, by rw [e, conj_of_real]⟩

lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
eq_conj_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp, λ h, ⟨_, h.symm⟩⟩


lemma conj_sub (z z': ℂ) : conj (z - z') = conj z - conj z' := conj.map_sub z z'

lemma conj_one : conj 1 = 1 := by rw conj.map_one

lemma eq_conj_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
⟨λ h, add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)),
  λ h, ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

instance : star_ring ℂ :=
{ star := λ z, conj z,
  star_involutive := λ z, by simp,
  star_mul := λ r s, by { ext; simp [mul_comm], },
  star_add := by simp, }

/-! ### Norm squared -/

/-- The norm squared function. -/
@[pp_nodot] def norm_sq : monoid_with_zero_hom ℂ ℝ :=
{ to_fun := λ z, z.re * z.re + z.im * z.im,
  map_zero' := by simp,
  map_one' := by simp,
  map_mul' := λ z w, by { dsimp, ring } }

lemma norm_sq_apply (z : ℂ) : norm_sq z = z.re * z.re + z.im * z.im := rfl

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
by simp [norm_sq]

lemma norm_sq_eq_conj_mul_self {z : ℂ} : (norm_sq z : ℂ) = conj z * z :=
by { ext; simp [norm_sq, mul_comm], }

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := norm_sq.map_zero
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := norm_sq.map_one
@[simp] lemma norm_sq_I : norm_sq I = 1 := by simp [norm_sq]

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z :=
add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
⟨λ h, ext
  (eq_zero_of_mul_self_add_mul_self_eq_zero h)
  (eq_zero_of_mul_self_add_mul_self_eq_zero $ (add_comm _ _).trans h),
 λ h, h.symm ▸ norm_sq_zero⟩

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
(norm_sq_nonneg z).lt_iff_ne.trans $ not_congr (eq_comm.trans norm_sq_eq_zero)

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
by simp [norm_sq]

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
by simp [norm_sq]

lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
norm_sq.map_mul z w

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
by dsimp [norm_sq]; ring

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
le_add_of_nonneg_right (mul_self_nonneg _)

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
ext_iff.2 $ by simp [norm_sq, mul_comm, sub_eq_neg_add, add_comm]

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
ext_iff.2 $ by simp [two_mul]

/-- The coercion `ℝ → ℂ` as a `ring_hom`. -/
def of_real : ℝ →+* ℂ := ⟨coe, of_real_one, of_real_mul, of_real_zero, of_real_add⟩

@[simp] lemma of_real_eq_coe (r : ℝ) : of_real r = r := rfl

@[simp] lemma I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]

@[simp] lemma sub_re (z w : ℂ) : (z - w).re = z.re - w.re := rfl
@[simp] lemma sub_im (z w : ℂ) : (z - w).im = z.im - w.im := rfl
@[simp, norm_cast] lemma of_real_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s := ext_iff.2 $ by simp
@[simp, norm_cast] lemma of_real_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = r ^ n :=
by induction n; simp [*, of_real_mul, pow_succ]

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
ext_iff.2 $ by simp [two_mul, sub_eq_add_neg]

lemma norm_sq_sub (z w : ℂ) : norm_sq (z - w) =
  norm_sq z + norm_sq w - 2 * (z * conj w).re :=
by rw [sub_eq_add_neg, norm_sq_add]; simp [-mul_re, add_comm, add_left_comm, sub_eq_add_neg]

/-! ### Inversion -/

noncomputable instance : has_inv ℂ := ⟨λ z, conj z * ((norm_sq z)⁻¹:ℝ)⟩

theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((norm_sq z)⁻¹:ℝ) := rfl
@[simp] lemma inv_re (z : ℂ) : (z⁻¹).re = z.re / norm_sq z := by simp [inv_def, division_def]
@[simp] lemma inv_im (z : ℂ) : (z⁻¹).im = -z.im / norm_sq z := by simp [inv_def, division_def]

@[simp, norm_cast] lemma of_real_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = r⁻¹ :=
ext_iff.2 $ by simp

protected lemma inv_zero : (0⁻¹ : ℂ) = 0 :=
by rw [← of_real_zero, ← of_real_inv, inv_zero]

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 :=
by rw [inv_def, ← mul_assoc, mul_conj, ← of_real_mul,
  mul_inv_cancel (mt norm_sq_eq_zero.1 h), of_real_one]

/-! ### Field instance and lemmas -/

noncomputable instance : field ℂ :=
{ inv := has_inv.inv,
  exists_pair_ne := ⟨0, 1, mt (congr_arg re) zero_ne_one⟩,
  mul_inv_cancel := @complex.mul_inv_cancel,
  inv_zero := complex.inv_zero,
  ..complex.comm_ring }

@[simp] lemma I_fpow_bit0 (n : ℤ) : I ^ (bit0 n) = (-1) ^ n :=
by rw [fpow_bit0', I_mul_I]

@[simp] lemma I_fpow_bit1 (n : ℤ) : I ^ (bit1 n) = (-1) ^ n * I :=
by rw [fpow_bit1', I_mul_I]

lemma div_re (z w : ℂ) : (z / w).re = z.re * w.re / norm_sq w + z.im * w.im / norm_sq w :=
by simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]
lemma div_im (z w : ℂ) : (z / w).im = z.im * w.re / norm_sq w - z.re * w.im / norm_sq w :=
by simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

@[simp, norm_cast] lemma of_real_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s :=
of_real.map_div r s

@[simp, norm_cast] lemma of_real_fpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n :=
of_real.map_fpow r n

@[simp] lemma div_I (z : ℂ) : z / I = -(z * I) :=
(div_eq_iff_mul_eq I_ne_zero).2 $ by simp [mul_assoc]

@[simp] lemma inv_I : I⁻¹ = -I :=
by simp [inv_eq_one_div]

@[simp] lemma norm_sq_inv (z : ℂ) : norm_sq z⁻¹ = (norm_sq z)⁻¹ :=
norm_sq.map_inv' z

@[simp] lemma norm_sq_div (z w : ℂ) : norm_sq (z / w) = norm_sq z / norm_sq w :=
norm_sq.map_div z w

/-! ### Cast lemmas -/

@[simp, norm_cast] theorem of_real_nat_cast (n : ℕ) : ((n : ℝ) : ℂ) = n :=
of_real.map_nat_cast n

@[simp, norm_cast] lemma nat_cast_re (n : ℕ) : (n : ℂ).re = n :=
by rw [← of_real_nat_cast, of_real_re]

@[simp, norm_cast] lemma nat_cast_im (n : ℕ) : (n : ℂ).im = 0 :=
by rw [← of_real_nat_cast, of_real_im]

@[simp, norm_cast] theorem of_real_int_cast (n : ℤ) : ((n : ℝ) : ℂ) = n :=
of_real.map_int_cast n

@[simp, norm_cast] lemma int_cast_re (n : ℤ) : (n : ℂ).re = n :=
by rw [← of_real_int_cast, of_real_re]

@[simp, norm_cast] lemma int_cast_im (n : ℤ) : (n : ℂ).im = 0 :=
by rw [← of_real_int_cast, of_real_im]

@[simp, norm_cast] theorem of_real_rat_cast (n : ℚ) : ((n : ℝ) : ℂ) = n :=
of_real.map_rat_cast n

@[simp, norm_cast] lemma rat_cast_re (q : ℚ) : (q : ℂ).re = q :=
by rw [← of_real_rat_cast, of_real_re]

@[simp, norm_cast] lemma rat_cast_im (q : ℚ) : (q : ℂ).im = 0 :=
by rw [← of_real_rat_cast, of_real_im]

/-! ### Characteristic zero -/

instance char_zero_complex : char_zero ℂ :=
char_zero_of_inj_zero $ λ n h,
by rwa [← of_real_nat_cast, of_real_eq_zero, nat.cast_eq_zero] at h

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 :=
by simp only [add_conj, of_real_mul, of_real_one, of_real_bit0,
     mul_div_cancel_left (z.re:ℂ) two_ne_zero']

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj(z))/(2 * I) :=
by simp only [sub_conj, of_real_mul, of_real_one, of_real_bit0, mul_right_comm,
     mul_div_cancel_left _ (mul_ne_zero two_ne_zero' I_ne_zero : 2 * I ≠ 0)]

/-! ### Absolute value -/

/-- The complex absolute value function, defined as the square root of the norm squared. -/
@[pp_nodot] noncomputable def abs (z : ℂ) : ℝ := (norm_sq z).sqrt

local notation `abs'` := _root_.abs

@[simp, norm_cast] lemma abs_of_real (r : ℝ) : abs r = abs' r :=
by simp [abs, norm_sq_of_real, real.sqrt_mul_self_eq_abs]

lemma abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : abs r = r :=
(abs_of_real _).trans (abs_of_nonneg h)

lemma abs_of_nat (n : ℕ) : complex.abs n = n :=
calc complex.abs n = complex.abs (n:ℝ) : by rw [of_real_nat_cast]
  ... = _ : abs_of_nonneg (nat.cast_nonneg n)

lemma mul_self_abs (z : ℂ) : abs z * abs z = norm_sq z :=
real.mul_self_sqrt (norm_sq_nonneg _)

@[simp] lemma abs_zero : abs 0 = 0 := by simp [abs]
@[simp] lemma abs_one : abs 1 = 1 := by simp [abs]
@[simp] lemma abs_I : abs I = 1 := by simp [abs]

@[simp] lemma abs_two : abs 2 = 2 :=
calc abs 2 = abs (2 : ℝ) : by rw [of_real_bit0, of_real_one]
... = (2 : ℝ) : abs_of_nonneg (by norm_num)

lemma abs_nonneg (z : ℂ) : 0 ≤ abs z :=
real.sqrt_nonneg _

@[simp] lemma abs_eq_zero {z : ℂ} : abs z = 0 ↔ z = 0 :=
(real.sqrt_eq_zero $ norm_sq_nonneg _).trans norm_sq_eq_zero

lemma abs_ne_zero {z : ℂ} : abs z ≠ 0 ↔ z ≠ 0 :=
not_congr abs_eq_zero

@[simp] lemma abs_conj (z : ℂ) : abs (conj z) = abs z :=
by simp [abs]

@[simp] lemma abs_mul (z w : ℂ) : abs (z * w) = abs z * abs w :=
by rw [abs, norm_sq_mul, real.sqrt_mul (norm_sq_nonneg _)]; refl

lemma abs_re_le_abs (z : ℂ) : abs' z.re ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg z.re) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply re_sq_le_norm_sq

lemma abs_im_le_abs (z : ℂ) : abs' z.im ≤ abs z :=
by rw [mul_self_le_mul_self_iff (_root_.abs_nonneg z.im) (abs_nonneg _),
       abs_mul_abs_self, mul_self_abs];
   apply im_sq_le_norm_sq

lemma re_le_abs (z : ℂ) : z.re ≤ abs z :=
(abs_le.1 (abs_re_le_abs _)).2

lemma im_le_abs (z : ℂ) : z.im ≤ abs z :=
(abs_le.1 (abs_im_le_abs _)).2

/--
The **triangle inequality** for complex numbers.
-/
lemma abs_add (z w : ℂ) : abs (z + w) ≤ abs z + abs w :=
(mul_self_le_mul_self_iff (abs_nonneg _)
  (add_nonneg (abs_nonneg _) (abs_nonneg _))).2 $
begin
  rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs,
      add_right_comm, norm_sq_add, add_le_add_iff_left,
      mul_assoc, mul_le_mul_left (@zero_lt_two ℝ _ _)],
  simpa [-mul_re] using re_le_abs (z * conj w)
end

instance : is_absolute_value abs :=
{ abv_nonneg  := abs_nonneg,
  abv_eq_zero := λ _, abs_eq_zero,
  abv_add     := abs_add,
  abv_mul     := abs_mul }
open is_absolute_value

@[simp] lemma abs_abs (z : ℂ) : abs' (abs z) = abs z :=
_root_.abs_of_nonneg (abs_nonneg _)

@[simp] lemma abs_pos {z : ℂ} : 0 < abs z ↔ z ≠ 0 := abv_pos abs
@[simp] lemma abs_neg : ∀ z, abs (-z) = abs z := abv_neg abs
lemma abs_sub_comm : ∀ z w, abs (z - w) = abs (w - z) := abv_sub abs
lemma abs_sub_le : ∀ a b c, abs (a - c) ≤ abs (a - b) + abs (b - c) := abv_sub_le abs
@[simp] theorem abs_inv : ∀ z, abs z⁻¹ = (abs z)⁻¹ := abv_inv abs
@[simp] theorem abs_div : ∀ z w, abs (z / w) = abs z / abs w := abv_div abs

lemma abs_abs_sub_le_abs_sub : ∀ z w, abs' (abs z - abs w) ≤ abs (z - w) :=
abs_abv_sub_le_abv_sub abs

lemma abs_le_abs_re_add_abs_im (z : ℂ) : abs z ≤ abs' z.re + abs' z.im :=
by simpa [re_add_im] using abs_add z.re (z.im * I)

lemma abs_re_div_abs_le_one (z : ℂ) : abs' (z.re / z.abs) ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one]
else by { simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mul, abs_re_le_abs] }

lemma abs_im_div_abs_le_one (z : ℂ) : abs' (z.im / z.abs) ≤ 1 :=
if hz : z = 0 then by simp [hz, zero_le_one]
else by { simp_rw [_root_.abs_div, abs_abs, div_le_iff (abs_pos.2 hz), one_mul, abs_im_le_abs] }

@[simp, norm_cast] lemma abs_cast_nat (n : ℕ) : abs (n : ℂ) = n :=
by rw [← of_real_nat_cast, abs_of_nonneg (nat.cast_nonneg n)]

@[simp, norm_cast] lemma int_cast_abs (n : ℤ) : ↑(abs' n) = abs n :=
by rw [← of_real_int_cast, abs_of_real, int.cast_abs]

lemma norm_sq_eq_abs (x : ℂ) : norm_sq x = abs x ^ 2 :=
by rw [abs, sq, real.mul_self_sqrt (norm_sq_nonneg _)]

/--
We put a partial order on ℂ so that `z ≤ w` exactly if `w - z` is real and nonnegative.
Complex numbers with different imaginary parts are incomparable.
-/
def complex_order : partial_order ℂ :=
{ le := λ z w, ∃ x : ℝ, 0 ≤ x ∧ w = z + x,
  le_refl := λ x, ⟨0, by simp⟩,
  le_trans := λ x y z h₁ h₂,
  begin
    obtain ⟨w₁, l₁, rfl⟩ := h₁,
    obtain ⟨w₂, l₂, rfl⟩ := h₂,
    refine ⟨w₁ + w₂, _, _⟩,
    { linarith, },
    { simp [add_assoc], },
  end,
  le_antisymm := λ z w h₁ h₂,
  begin
    obtain ⟨w₁, l₁, rfl⟩ := h₁,
    obtain ⟨w₂, l₂, e⟩ := h₂,
    have h₃ : w₁ + w₂ = 0,
    { symmetry,
      rw add_assoc at e,
      apply of_real_inj.mp,
      apply add_left_cancel,
      convert e; simp, },
    have h₄ : w₁ = 0, linarith,
    simp [h₄],
  end, }

localized "attribute [instance] complex_order" in complex_order

section complex_order
open_locale complex_order

lemma le_def {z w : ℂ} : z ≤ w ↔ ∃ x : ℝ, 0 ≤ x ∧ w = z + x := iff.refl _
lemma lt_def {z w : ℂ} : z < w ↔ ∃ x : ℝ, 0 < x ∧ w = z + x :=
begin
  rw [lt_iff_le_not_le],
  fsplit,
  { rintro ⟨⟨x, l, rfl⟩, h⟩,
    by_cases hx : x = 0,
    { simpa [hx] using h },
    { replace l : 0 < x := l.lt_of_ne (ne.symm hx),
      exact ⟨x, l, rfl⟩, } },
  { rintro ⟨x, l, rfl⟩,
    fsplit,
    { exact ⟨x, l.le, rfl⟩, },
    { rintro ⟨x', l', e⟩,
      rw [add_assoc] at e,
      replace e := add_left_cancel (by { convert e, simp }),
      norm_cast at e,
      linarith, } }
end

@[simp, norm_cast] lemma real_le_real {x y : ℝ} : (x : ℂ) ≤ (y : ℂ) ↔ x ≤ y :=
begin
  rw [le_def],
  fsplit,
  { rintro ⟨r, l, e⟩,
    norm_cast at e,
    subst e,
    exact le_add_of_nonneg_right l, },
  { intro h,
    exact ⟨y - x, sub_nonneg.mpr h, (by simp)⟩, },
end
@[simp, norm_cast] lemma real_lt_real {x y : ℝ} : (x : ℂ) < (y : ℂ) ↔ x < y :=
begin
  rw [lt_def],
  fsplit,
  { rintro ⟨r, l, e⟩,
    norm_cast at e,
    subst e,
    exact lt_add_of_pos_right x l, },
  { intro h,
    exact ⟨y - x, sub_pos.mpr h, (by simp)⟩, },
end
@[simp, norm_cast] lemma zero_le_real {x : ℝ} : (0 : ℂ) ≤ (x : ℂ) ↔ 0 ≤ x := real_le_real
@[simp, norm_cast] lemma zero_lt_real {x : ℝ} : (0 : ℂ) < (x : ℂ) ↔ 0 < x := real_lt_real

/--
With `z ≤ w` iff `w - z` is real and nonnegative, `ℂ` is an ordered ring.
-/
def complex_ordered_comm_ring : ordered_comm_ring ℂ :=
{ zero_le_one := ⟨1, zero_le_one, by simp⟩,
  add_le_add_left := λ w z h y,
  begin
    obtain ⟨x, l, rfl⟩ := h,
    exact ⟨x, l, by simp [add_assoc]⟩,
  end,
  mul_pos := λ z w hz hw,
  begin
    obtain ⟨zx, lz, rfl⟩ := lt_def.mp hz,
    obtain ⟨wx, lw, rfl⟩ := lt_def.mp hw,
    norm_cast,
    simp only [mul_pos, lz, lw, zero_add],
  end,
  le_of_add_le_add_left := λ u v z h,
  begin
    obtain ⟨x, l, e⟩ := h,
    rw add_assoc at e,
    exact ⟨x, l, add_left_cancel e⟩,
  end,
  mul_lt_mul_of_pos_left := λ u v z h₁ h₂,
  begin
    obtain ⟨x₁, l₁, rfl⟩ := lt_def.mp h₁,
    obtain ⟨x₂, l₂, rfl⟩ := lt_def.mp h₂,
    simp only [mul_add, zero_add],
    exact lt_def.mpr ⟨x₂ * x₁, mul_pos l₂ l₁, (by norm_cast)⟩,
  end,
  mul_lt_mul_of_pos_right := λ u v z h₁ h₂,
  begin
    obtain ⟨x₁, l₁, rfl⟩ := lt_def.mp h₁,
    obtain ⟨x₂, l₂, rfl⟩ := lt_def.mp h₂,
    simp only [add_mul, zero_add],
    exact lt_def.mpr ⟨x₁ * x₂, mul_pos l₁ l₂, (by norm_cast)⟩,
  end,
-- we need more instances here because comm_ring doesn't have zero_add et al as fields,
-- they are derived as lemmas
  ..(by apply_instance : partial_order ℂ),
  ..(by apply_instance : comm_ring ℂ),
  ..(by apply_instance : comm_semiring ℂ),
  ..(by apply_instance : add_cancel_monoid ℂ) }

localized "attribute [instance] complex_ordered_comm_ring" in complex_order

/--
With `z ≤ w` iff `w - z` is real and nonnegative, `ℂ` is a star ordered ring.
(That is, an ordered ring in which every element of the form `star z * z` is nonnegative.)

In fact, the nonnegative elements are precisely those of this form.
This hold in any `C^*`-algebra, e.g. `ℂ`,
but we don't yet have `C^*`-algebras in mathlib.
-/
def complex_star_ordered_ring : star_ordered_ring ℂ :=
{ star_mul_self_nonneg := λ z,
  begin
    refine ⟨z.abs^2, pow_nonneg (abs_nonneg z) 2, _⟩,
    simp only [has_star.star, of_real_pow, zero_add],
    norm_cast,
    rw [←norm_sq_eq_abs, norm_sq_eq_conj_mul_self],
  end, }

localized "attribute [instance] complex_star_ordered_ring" in complex_order

end complex_order

/-! ### Cauchy sequences -/

theorem is_cau_seq_re (f : cau_seq ℂ abs) : is_cau_seq abs' (λ n, (f n).re) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa using abs_re_le_abs (f j - f i)) (H _ ij)

theorem is_cau_seq_im (f : cau_seq ℂ abs) : is_cau_seq abs' (λ n, (f n).im) :=
λ ε ε0, (f.cauchy ε0).imp $ λ i H j ij,
lt_of_le_of_lt (by simpa using abs_im_le_abs (f j - f i)) (H _ ij)

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_re (f : cau_seq ℂ abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_re f⟩

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_im (f : cau_seq ℂ abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_im f⟩

lemma is_cau_seq_abs {f : ℕ → ℂ} (hf : is_cau_seq abs f) :
  is_cau_seq abs' (abs ∘ f) :=
λ ε ε0, let ⟨i, hi⟩ := hf ε ε0 in
⟨i, λ j hj, lt_of_le_of_lt (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩

/-- The limit of a Cauchy sequence of complex numbers. -/
noncomputable def lim_aux (f : cau_seq ℂ abs) : ℂ :=
⟨cau_seq.lim (cau_seq_re f), cau_seq.lim (cau_seq_im f)⟩

theorem equiv_lim_aux (f : cau_seq ℂ abs) : f ≈ cau_seq.const abs (lim_aux f) :=
λ ε ε0, (exists_forall_ge_and
  (cau_seq.equiv_lim ⟨_, is_cau_seq_re f⟩ _ (half_pos ε0))
  (cau_seq.equiv_lim ⟨_, is_cau_seq_im f⟩ _ (half_pos ε0))).imp $
λ i H j ij, begin
  cases H _ ij with H₁ H₂,
  apply lt_of_le_of_lt (abs_le_abs_re_add_abs_im _),
  dsimp [lim_aux] at *,
  have := add_lt_add H₁ H₂,
  rwa add_halves at this,
end

noncomputable instance : cau_seq.is_complete ℂ abs :=
⟨λ f, ⟨lim_aux f, equiv_lim_aux f⟩⟩

open cau_seq

lemma lim_eq_lim_im_add_lim_re (f : cau_seq ℂ abs) : lim f =
  ↑(lim (cau_seq_re f)) + ↑(lim (cau_seq_im f)) * I :=
lim_eq_of_equiv_const $
calc f ≈ _ : equiv_lim_aux f
... = cau_seq.const abs (↑(lim (cau_seq_re f)) + ↑(lim (cau_seq_im f)) * I) :
  cau_seq.ext (λ _, complex.ext (by simp [lim_aux, cau_seq_re]) (by simp [lim_aux, cau_seq_im]))

lemma lim_re (f : cau_seq ℂ abs) : lim (cau_seq_re f) = (lim f).re :=
by rw [lim_eq_lim_im_add_lim_re]; simp

lemma lim_im (f : cau_seq ℂ abs) : lim (cau_seq_im f) = (lim f).im :=
by rw [lim_eq_lim_im_add_lim_re]; simp

lemma is_cau_seq_conj (f : cau_seq ℂ abs) : is_cau_seq abs (λ n, conj (f n)) :=
λ ε ε0, let ⟨i, hi⟩ := f.2 ε ε0 in
⟨i, λ j hj, by rw [← conj.map_sub, abs_conj]; exact hi j hj⟩

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
noncomputable def cau_seq_conj (f : cau_seq ℂ abs) : cau_seq ℂ abs :=
⟨_, is_cau_seq_conj f⟩

lemma lim_conj (f : cau_seq ℂ abs) : lim (cau_seq_conj f) = conj (lim f) :=
complex.ext (by simp [cau_seq_conj, (lim_re _).symm, cau_seq_re])
  (by simp [cau_seq_conj, (lim_im _).symm, cau_seq_im, (lim_neg _).symm]; refl)

/-- The absolute value of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cau_seq_abs (f : cau_seq ℂ abs) : cau_seq ℝ abs' :=
⟨_, is_cau_seq_abs f.2⟩

lemma lim_abs (f : cau_seq ℂ abs) : lim (cau_seq_abs f) = abs (lim f) :=
lim_eq_of_equiv_const (λ ε ε0,
let ⟨i, hi⟩ := equiv_lim f ε ε0 in
⟨i, λ j hj, lt_of_le_of_lt (abs_abs_sub_le_abs_sub _ _) (hi j hj)⟩)

@[simp, norm_cast] lemma of_real_prod {α : Type*} (s : finset α) (f : α → ℝ) :
  ((∏ i in s, f i : ℝ) : ℂ) = ∏ i in s, (f i : ℂ) :=
ring_hom.map_prod of_real _ _

@[simp, norm_cast] lemma of_real_sum {α : Type*} (s : finset α) (f : α → ℝ) :
  ((∑ i in s, f i : ℝ) : ℂ) = ∑ i in s, (f i : ℂ) :=
ring_hom.map_sum of_real _ _

end complex
