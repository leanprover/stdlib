/-
Copyright (c) 2019 Tim Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baanen, Lu-Ming Zhang
-/
import algebra.associated
import linear_algebra.matrix.determinant
import tactic.linarith
import tactic.ring_exp

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible
determinant. For matrices that are not square or not of full rank, there is a
more general notion of pseudoinverses which we do not consider here.

The definition of inverse used in this file is the adjugate divided by the determinant.
The adjugate is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.update_column i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the determinants of each minor of `A`.
Instead of defining a minor to be `A` with row `i` and column `j` deleted, we
replace the `i`th row of `A` with the `j`th basis vector; this has the same
determinant as the minor but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`. Finally, we show that dividing
the adjugate by `det A` (if possible), giving a matrix `nonsing_inv A`, will
result in a multiplicative inverse to `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/

namespace matrix
universes u v
variables {n : Type u} [decidable_eq n] [fintype n] {α : Type v} [comm_ring α]
open_locale matrix big_operators
open equiv equiv.perm finset

section cramer
/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramer_map`.
  After defining `cramer_map` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/
variables (A : matrix n n α) (b : n → α)

/--
  `cramer_map A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer_map A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer_map A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer_map` is well-defined but not necessarily useful.
-/
def cramer_map (i : n) : α := (A.update_column i b).det

lemma cramer_map_is_linear (i : n) : is_linear_map α (λ b, cramer_map A b i) :=
{ map_add := det_update_column_add _ _,
  map_smul := det_update_column_smul _ _ }

lemma cramer_is_linear : is_linear_map α (cramer_map A) :=
begin
  split; intros; ext i,
  { apply (cramer_map_is_linear A i).1 },
  { apply (cramer_map_is_linear A i).2 }
end

/--
  `cramer A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer` is well-defined but not necessarily useful.
 -/
def cramer (A : matrix n n α) : (n → α) →ₗ[α] (n → α) :=
is_linear_map.mk' (cramer_map A) (cramer_is_linear A)

lemma cramer_apply (i : n) : cramer A b i = (A.update_column i b).det := rfl

lemma cramer_transpose_row_self (i : n) :
  Aᵀ.cramer (A i) = λ j, ite (i = j) A.det 0 :=
begin
  ext j,
  rw cramer_apply,
  by_cases h : i = j,
  { -- i = j: this entry should be `A.det`
    rw [update_column_transpose, det_transpose], simp [update_row, h], },
  { -- i ≠ j: this entry should be 0
    rw [if_neg h, update_column_transpose, det_transpose],
    apply det_zero_of_row_eq h,
    rw [update_row_self, update_row_ne],
    apply h }
end

/-- Use linearity of `cramer` to take it out of a summation. -/
lemma sum_cramer {β} (s : finset β) (f : β → n → α) :
  ∑ x in s, cramer A (f x) = cramer A (∑ x in s, f x) :=
(linear_map.map_sum (cramer A)).symm

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
lemma sum_cramer_apply {β} (s : finset β) (f : n → β → α) (i : n) :
∑ x in s, cramer A (λ j, f j x) i = cramer A (λ (j : n), ∑ x in s, f j x) i :=
calc ∑ x in s, cramer A (λ j, f j x) i
    = (∑ x in s, cramer A (λ j, f j x)) i : (finset.sum_apply i s _).symm
... = cramer A (λ (j : n), ∑ x in s, f j x) i :
  by { rw [sum_cramer, cramer_apply], congr' with j, apply finset.sum_apply }

end cramer

section adjugate
/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring,
while the `inv` section is specifically for invertible matrices.
-/

/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking the determinant of minors,
  i.e. the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we define the
  minor as replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
def adjugate (A : matrix n n α) : matrix n n α := λ i, cramer Aᵀ (λ j, if i = j then 1 else 0)

lemma adjugate_def (A : matrix n n α) :
  adjugate A = λ i, cramer Aᵀ (λ j, if i = j then 1 else 0) := rfl

lemma adjugate_apply (A : matrix n n α) (i j : n) :
  adjugate A i j = (A.update_row j (λ j, if i = j then 1 else 0)).det :=
by { rw adjugate_def, simp only, rw [cramer_apply, update_column_transpose, det_transpose], }

lemma adjugate_transpose (A : matrix n n α) : (adjugate A)ᵀ = adjugate (Aᵀ) :=
begin
  ext i j,
  rw [transpose_apply, adjugate_apply, adjugate_apply, update_row_transpose, det_transpose],
  rw [det_apply', det_apply'],
  apply finset.sum_congr rfl,
  intros σ _,
  congr' 1,

  by_cases i = σ j,
  { -- Everything except `(i , j)` (= `(σ j , j)`) is given by A, and the rest is a single `1`.
    congr; ext j',
    have := (@equiv.injective _ _ σ j j' : σ j = σ j' → j = j'),
    rw [update_row_apply, update_column_apply],
    finish },
  { -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, update_column A j (λ (i' : n), ite (i = i') 1 0) (σ j') j') = 0,
    { apply prod_eq_zero (mem_univ j),
      rw [update_column_self],
      exact if_neg h },
    rw this,
    apply prod_eq_zero (mem_univ (σ⁻¹ i)),
    erw [apply_symm_apply σ i, update_row_self],
    apply if_neg,
    intro h',
    exact h ((symm_apply_eq σ).mp h'.symm) }
end

/-- Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by some matrix. This
matrix is `A.adjugate`. -/
lemma cramer_eq_adjugate_mul_vec (A : matrix n n α) (b : n → α) :
  cramer A b = A.adjugate.mul_vec b :=
begin
  nth_rewrite 1 ← A.transpose_transpose,
  rw [← adjugate_transpose, adjugate_def],
  have : b = ∑ i, (b i) • (λ j, if i = j then 1 else 0), { ext i, simp, },
  rw this, ext k,
  simp [mul_vec, dot_product, mul_comm],
end

lemma mul_adjugate_apply (A : matrix n n α) (i j k) :
  A i k * adjugate A k j = cramer Aᵀ (λ j, if k = j then A i k else 0) j :=
begin
  erw [←smul_eq_mul, ←pi.smul_apply, ←linear_map.map_smul],
  congr' with l,
  rw [pi.smul_apply, smul_eq_mul, mul_boole],
end

lemma mul_adjugate (A : matrix n n α) : A ⬝ adjugate A = A.det • 1 :=
begin
  ext i j,
  rw [mul_apply, pi.smul_apply, pi.smul_apply, one_apply, smul_eq_mul, mul_boole],
  simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self],
end

lemma adjugate_mul (A : matrix n n α) : adjugate A ⬝ A = A.det • 1 :=
calc adjugate A ⬝ A = (Aᵀ ⬝ (adjugate Aᵀ))ᵀ :
  by rw [←adjugate_transpose, ←transpose_mul, transpose_transpose]
... = A.det • 1 : by rw [mul_adjugate (Aᵀ), det_transpose, transpose_smul, transpose_one]

/-- `det_adjugate_of_cancel` is an auxiliary lemma for computing `(adjugate A).det`,
  used in `det_adjugate_eq_one` and `det_adjugate_of_is_unit`.

  The formula for the determinant of the adjugate of an `n` by `n` matrix `A`
  is in general `(adjugate A).det = A.det ^ (n - 1)`, but the proof differs in several cases.
  This lemma `det_adjugate_of_cancel` covers the case that `det A` cancels
  on the left of the equation `A.det * b = A.det ^ n`.
-/
lemma det_adjugate_of_cancel {A : matrix n n α}
  (h : ∀ b, A.det * b = A.det ^ fintype.card n → b = A.det ^ (fintype.card n - 1)) :
  (adjugate A).det = A.det ^ (fintype.card n - 1) :=
h (adjugate A).det (calc A.det * (adjugate A).det = (A ⬝ adjugate A).det   : (det_mul _ _).symm
                                              ... = A.det ^ fintype.card n : by simp [mul_adjugate])

lemma adjugate_eq_one_of_card_eq_one {A : matrix n n α} (h : fintype.card n = 1) : adjugate A = 1 :=
begin
  haveI : subsingleton n := fintype.card_le_one_iff_subsingleton.mp h.le,
  ext i j,
  simp [subsingleton.elim i j, adjugate_apply, det_eq_elem_of_card_eq_one h j],
end

@[simp] lemma adjugate_zero (h : 1 < fintype.card n) : adjugate (0 : matrix n n α) = 0 :=
begin
  ext i j,
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := fintype.exists_ne_of_one_lt_card h j,
  apply det_eq_zero_of_column_eq_zero j',
  intro j'',
  simp [update_column_ne hj'],
end

lemma det_adjugate_eq_one {A : matrix n n α} (h : A.det = 1) : (adjugate A).det = 1 :=
calc (adjugate A).det
    = A.det ^ (fintype.card n - 1) : det_adjugate_of_cancel (λ b hb, by simpa [h] using hb)
... = 1                            : by rw [h, one_pow]

/-- `det_adjugate_of_is_unit` gives the formula for `(adjugate A).det` if `A.det` has an inverse.

  The formula for the determinant of the adjugate of an `n` by `n` matrix `A`
  is in general `(adjugate A).det = A.det ^ (n - 1)`, but the proof differs in several cases.
  This lemma `det_adjugate_of_is_unit` covers the case that `det A` has an inverse.
-/
lemma det_adjugate_of_is_unit {A : matrix n n α} (h : is_unit A.det) :
  (adjugate A).det = A.det ^ (fintype.card n - 1) :=
begin
  rcases is_unit_iff_exists_inv'.mp h with ⟨a, ha⟩,
  by_cases card_lt_zero : fintype.card n ≤ 0,
  { have h : fintype.card n = 0 := by linarith,
    simp [det_eq_one_of_card_eq_zero h] },
  have zero_lt_card : 0 < fintype.card n := by linarith,
  have n_nonempty : nonempty n := fintype.card_pos_iff.mp zero_lt_card,

  by_cases card_lt_one : fintype.card n ≤ 1,
  { have h : fintype.card n = 1 := by linarith,
    simp [h, adjugate_eq_one_of_card_eq_one h] },
  have one_lt_card : 1 < fintype.card n := by linarith,
  have zero_lt_card_sub_one : 0 < fintype.card n - 1 :=
    (nat.sub_lt_sub_right_iff (refl 1)).mpr one_lt_card,

  apply det_adjugate_of_cancel,
  intros b hb,
  calc b = a * (det A ^ (fintype.card n - 1 + 1)) :
       by rw [←one_mul b, ←ha, mul_assoc, hb, nat.sub_add_cancel zero_lt_card]
     ... = a * det A * det A ^ (fintype.card n - 1) : by ring_exp
     ... = det A ^ (fintype.card n - 1) : by rw [ha, one_mul]
end

end adjugate

section inv
/-!
### `inv` section

Defines the matrix `nonsing_inv A` and proves it is the inverse matrix
of a square matrix `A` as long as `det A` has a multiplicative inverse.
-/

variables (A : matrix n n α) (B : matrix n n α)

open_locale classical

lemma is_unit_det_transpose (h : is_unit A.det) : is_unit Aᵀ.det :=
by { rw det_transpose, exact h, }

/-- The inverse of a square matrix, when it is invertible (and zero otherwise).-/
noncomputable def nonsing_inv : matrix n n α :=
if h : is_unit A.det then h.unit⁻¹ • A.adjugate else 0

noncomputable instance : has_inv (matrix n n α) := ⟨matrix.nonsing_inv⟩

lemma nonsing_inv_apply (h : is_unit A.det) :
  A⁻¹ = h.unit⁻¹ • A.adjugate :=
by { change A.nonsing_inv = _, dunfold nonsing_inv, simp only [dif_pos, h], }

lemma transpose_nonsing_inv (h : is_unit A.det) :
  (A⁻¹)ᵀ = (Aᵀ)⁻¹ :=
begin
  have h' := A.is_unit_det_transpose h,
  have dets_eq : h.unit = h'.unit := units.ext (by rw [h.unit_spec, h'.unit_spec, det_transpose]),
  rw [A.nonsing_inv_apply h, Aᵀ.nonsing_inv_apply h', dets_eq, A.adjugate_transpose.symm],
  refl,
end

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp] lemma mul_nonsing_inv (h : is_unit A.det) : A ⬝ A⁻¹ = 1 :=
by rw [A.nonsing_inv_apply h, units.smul_def, mul_smul, mul_adjugate, smul_smul,
       units.inv_mul_of_eq h.unit_spec, one_smul]

/-- The `nonsing_inv` of `A` is a left inverse. -/
@[simp] lemma nonsing_inv_mul (h : is_unit A.det) : A⁻¹ ⬝ A = 1 :=
calc A⁻¹ ⬝ A = (Aᵀ ⬝ (Aᵀ)⁻¹)ᵀ : by { rw [transpose_mul,
                                    Aᵀ.transpose_nonsing_inv (A.is_unit_det_transpose h),
                                    transpose_transpose], }
         ... = 1ᵀ             : by { rw Aᵀ.mul_nonsing_inv, exact A.is_unit_det_transpose h, }
         ... = 1              : transpose_one

@[simp] lemma nonsing_inv_det (h : is_unit A.det) : A⁻¹.det * A.det = 1 :=
by rw [←det_mul, A.nonsing_inv_mul h, det_one]

lemma is_unit_nonsing_inv_det (h : is_unit A.det) : is_unit A⁻¹.det :=
is_unit_of_mul_eq_one _ _ (A.nonsing_inv_det h)

@[simp] lemma nonsing_inv_nonsing_inv (h : is_unit A.det) : (A⁻¹)⁻¹ = A :=
calc (A⁻¹)⁻¹ = 1 ⬝ (A⁻¹)⁻¹        : by rw matrix.one_mul
         ... = A ⬝ A⁻¹ ⬝ (A⁻¹)⁻¹  : by rw A.mul_nonsing_inv h
         ... = A                  : by { rw [matrix.mul_assoc,
                                         (A⁻¹).mul_nonsing_inv (A.is_unit_nonsing_inv_det h),
                                         matrix.mul_one], }

/-- If `A.det` has a constructive inverse, produce one for `A`. -/
def invertible_of_det_invertible [invertible A.det] : invertible A :=
{ inv_of := ⅟A.det • A.adjugate,
  mul_inv_of_self :=
    by rw [mul_smul_comm, matrix.mul_eq_mul, mul_adjugate, smul_smul, inv_of_mul_self, one_smul],
  inv_of_mul_self :=
    by rw [smul_mul_assoc, matrix.mul_eq_mul, adjugate_mul, smul_smul, inv_of_mul_self, one_smul] }

/-- `A.det` is invertible if `A` has a left inverse. -/
def det_invertible_of_left_inverse (h : B ⬝ A = 1) : invertible A.det :=
{ inv_of := B.det,
  mul_inv_of_self := by rw [mul_comm, ← det_mul, h, det_one],
  inv_of_mul_self := by rw [← det_mul, h, det_one] }

/-- `A.det` is invertible if `A` has a right inverse. -/
def det_invertible_of_right_inverse (h : A ⬝ B = 1) : invertible A.det :=
{ inv_of := B.det,
  mul_inv_of_self := by rw [← det_mul, h, det_one],
  inv_of_mul_self := by rw [mul_comm, ← det_mul, h, det_one] }

/-- If `A` has a constructive inverse, produce one for `A.det`. -/
def det_invertible_of_invertible [invertible A] : invertible A.det :=
det_invertible_of_left_inverse A (⅟A) (inv_of_mul_self _)

/-- Given a proof that `A.det` has a constructive inverse, lift `A` to `units (matrix n n α)`-/
def unit_of_det_invertible [invertible A.det] : units (matrix n n α) :=
@unit_of_invertible _ _ A (invertible_of_det_invertible A)

/-- A matrix whose determinant is a unit is itself a unit. This is a noncomputable version of
`matrix.units_of_det_invertible`, with the inverse defeq to `matrix.nonsing_inv`. -/
noncomputable def nonsing_inv_unit (h : is_unit A.det) : units (matrix n n α) :=
{ val     := A,
  inv     := A⁻¹,
  val_inv := by { rw matrix.mul_eq_mul, apply A.mul_nonsing_inv h, },
  inv_val := by { rw matrix.mul_eq_mul, apply A.nonsing_inv_mul h, } }

lemma unit_of_det_invertible_eq_nonsing_inv_unit [invertible A.det] :
  unit_of_det_invertible A = nonsing_inv_unit A (is_unit_of_invertible _) :=
by { ext, refl }

/-- When lowered to a prop, `matrix.det_invertible_of_invertible` and
`matrix.invertible_of_det_invertible` form an `iff`. -/
lemma is_unit_iff_is_unit_det : is_unit A ↔ is_unit A.det :=
begin
  split; rintros ⟨x, hx⟩; refine @is_unit_of_invertible _ _ _ (id _),
  { haveI : invertible A := hx.rec x.invertible,
    apply det_invertible_of_invertible, },
  { haveI : invertible A.det := hx.rec x.invertible,
    apply invertible_of_det_invertible, },
end

/- `is_unit_of_invertible A`
   converts the "stronger" condition `invertible A` to proposition `is_unit A`. -/

/-- `matrix.is_unit_det_of_invertible` converts `invertible A` to `is_unit A.det`. -/
lemma is_unit_det_of_invertible [invertible A] : is_unit A.det :=
@is_unit_of_invertible _ _ _(det_invertible_of_invertible A)

@[simp]
lemma inv_eq_nonsing_inv_of_invertible [invertible A] : ⅟ A = A⁻¹ :=
begin
  suffices : is_unit A,
  { rw [←this.mul_left_inj, inv_of_mul_self, matrix.mul_eq_mul, nonsing_inv_mul],
    rwa ←is_unit_iff_is_unit_det },
  exact is_unit_of_invertible _
end

variables {A} {B}

/- `is_unit.invertible` lifts the proposition `is_unit A` to a constructive inverse of `A`. -/

/-- "Lift" the proposition `is_unit A.det` to a constructive inverse of `A`. -/
noncomputable def invertible_of_is_unit_det  (h : is_unit A.det) : invertible A :=
⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

lemma is_unit_det_of_left_inverse (h : B ⬝ A = 1) : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_left_inverse _ _ h)

lemma is_unit_det_of_right_inverse (h : A ⬝ B = 1) : is_unit A.det :=
@is_unit_of_invertible _ _ _ (det_invertible_of_right_inverse _ _ h)

lemma nonsing_inv_left_right (h : A ⬝ B = 1) : B ⬝ A = 1 :=
begin
  have h' : is_unit B.det := is_unit_det_of_left_inverse h,
  calc B ⬝ A = (B ⬝ A) ⬝ (B ⬝ B⁻¹) : by simp only [h', matrix.mul_one, mul_nonsing_inv]
        ... = B ⬝ ((A ⬝ B) ⬝ B⁻¹) : by simp only [matrix.mul_assoc]
        ... = B ⬝ B⁻¹ : by simp only [h, matrix.one_mul]
        ... = 1 : mul_nonsing_inv B h',
end

lemma nonsing_inv_right_left (h : B ⬝ A = 1) : A ⬝ B = 1 :=
nonsing_inv_left_right h

/-- If matrix A is left invertible, then its inverse equals its left inverse. -/
lemma inv_eq_left_inv (h : B ⬝ A = 1) : A⁻¹ = B :=
begin
  have h1 :=  (is_unit_det_of_left_inverse h),
  have h2 := matrix.invertible_of_is_unit_det h1,
  have := @inv_of_eq_left_inv (matrix n n α) (infer_instance) A B h2 h,
  simp* at *,
end

/-- If matrix A is right invertible, then its inverse equals its right inverse. -/
lemma inv_eq_right_inv (h : A ⬝ B = 1) : A⁻¹ = B :=
begin
  have h1 :=  (is_unit_det_of_right_inverse h),
  have h2 := matrix.invertible_of_is_unit_det h1,
  have := @inv_of_eq_right_inv (matrix n n α) (infer_instance) A B h2 h,
  simp* at *,
end

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertible_of_left_inverse (h: B ⬝ A = 1) : invertible A :=
⟨B, h, nonsing_inv_right_left h⟩

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertible_of_right_inverse (h: A ⬝ B = 1) : invertible A :=
⟨B, nonsing_inv_left_right h, h⟩

variables {C: matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
lemma left_inv_eq_left_inv (h: B ⬝ A = 1) (g: C ⬝ A = 1) : B = C :=
by rw [←(inv_eq_left_inv h), ←(inv_eq_left_inv g)]

/-- The right inverse of matrix A is unique when existing. -/
lemma right_inv_eq_right_inv (h: A ⬝ B = 1) (g: A ⬝ C = 1) : B = C :=
by rw [←(inv_eq_right_inv h), ←(inv_eq_right_inv g)]

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
lemma right_inv_eq_left_inv (h: A ⬝ B = 1) (g: C ⬝ A = 1) : B = C :=
by rw [←(inv_eq_right_inv h), ←(inv_eq_left_inv g)]

variable (A)

@[simp] lemma mul_inv_of_invertible [invertible A] : A ⬝ A⁻¹ = 1 :=
mul_nonsing_inv A (is_unit_det_of_invertible A)

@[simp] lemma inv_mul_of_invertible [invertible A] : A⁻¹ ⬝ A = 1 :=
nonsing_inv_mul A (is_unit_det_of_invertible A)

end inv

/-- One form of Cramer's rule -/
@[simp] lemma det_smul_inv_mul_vec_eq_cramer (A : matrix n n α) (b : n → α) (h : is_unit A.det) :
  A.det • A⁻¹.mul_vec b = cramer A b :=
begin
  rw [cramer_eq_adjugate_mul_vec, A.nonsing_inv_apply h, ← smul_mul_vec_assoc],
  conv_lhs { congr, congr, rw ← h.unit_spec, },
  rw [←units.smul_def, smul_inv_smul],
end

/-- A stronger form of **Cramer's rule** that allows us to solve some instances of `A ⬝ x = b` even
if the determinant is not a unit. A sufficient (but still not necessary) condition is that `A.det`
divides `b`. -/
@[simp] lemma mul_vec_cramer (A : matrix n n α) (b : n → α) :
  A.mul_vec (cramer A b) = A.det • b :=
by rw [cramer_eq_adjugate_mul_vec, mul_vec_mul_vec, mul_adjugate, smul_mul_vec_assoc, mul_vec_one]

end matrix
