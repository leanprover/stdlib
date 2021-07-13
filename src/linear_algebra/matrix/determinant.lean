/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Tim Baanen
-/
import data.matrix.pequiv
import data.fintype.card
import group_theory.perm.fin
import group_theory.perm.sign
import algebra.algebra.basic
import tactic.ring
import linear_algebra.alternating
import linear_algebra.pi

/-!
# Determinant of a matrix

This file defines the determinant of a matrix, `matrix.det`, and its essential properties.

## Main definitions

 - `matrix.det`: the determinant of a square matrix, as a sum over permutations
 - `matrix.det_row_multilinear`: the determinant, as an `alternating_map` in the rows of the matrix

## Main results

 - `det_mul`: the determinant of `A ⬝ B` is the product of determinants
 - `det_zero_of_row_eq`: the determinant is zero if there is a repeated row
 - `det_block_diagonal`: the determinant of a block diagonal matrix is a product
   of the blocks' determinants

## Implementation notes

It is possible to configure `simp` to compute determinants. See the file
`test/matrix.lean` for some examples.

-/

universes u v w z
open equiv equiv.perm finset function

namespace matrix
open_locale matrix big_operators

variables {m n : Type*} [decidable_eq n] [fintype n] [decidable_eq m] [fintype m]
variables {R : Type v} [comm_ring R]

local notation `ε` σ:max := ((sign σ : ℤ ) : R)


/-- `det` is an `alternating_map` in the rows of the matrix. -/
def det_row_multilinear : alternating_map R (n → R) R n :=
((multilinear_map.mk_pi_algebra R n R).comp_linear_map (linear_map.proj)).alternatization

/-- The determinant of a matrix given by the Leibniz formula. -/
abbreviation det (M : matrix n n R) : R :=
det_row_multilinear M

lemma det_apply (M : matrix n n R) :
  M.det = ∑ σ : perm n, σ.sign • ∏ i, M (σ i) i :=
multilinear_map.alternatization_apply _ M

-- This is what the old definition was. We use it to avoid having to change the old proofs below
lemma det_apply' (M : matrix n n R) :
  M.det = ∑ σ : perm n, ε σ * ∏ i, M (σ i) i :=
by simp [det_apply, units.smul_def]

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = ∏ i, d i :=
begin
  rw det_apply',
  refine (finset.sum_eq_single 1 _ _).trans _,
  { intros σ h1 h2,
    cases not_forall.1 (mt equiv.ext h2) with x h3,
    convert mul_zero _,
    apply finset.prod_eq_zero,
    { change x ∈ _, simp },
    exact if_neg h3 },
  { simp },
  { simp }
end

@[simp] lemma det_zero (h : nonempty n) : det (0 : matrix n n R) = 0 :=
(det_row_multilinear : alternating_map R (n → R) R n).map_zero

@[simp] lemma det_one : det (1 : matrix n n R) = 1 :=
by rw [← diagonal_one]; simp [-diagonal_one]

lemma det_eq_one_of_card_eq_zero {A : matrix n n R} (h : fintype.card n = 0) : det A = 1 :=
begin
  have perm_eq : (univ : finset (perm n)) = {1} :=
  univ_eq_singleton_of_card_one (1 : perm n) (by simp [card_univ, fintype.card_perm, h]),
  simp [det_apply, card_eq_zero.mp h, perm_eq],
end

/-- Specialize `det_eq_one_of_card_eq_zero` to `fin 0`.

This is especially useful in combination with the `det_succ_` lemmas,
for computing the determinant of a matrix given in the `![...]` notation.
-/
@[simp] lemma det_fin_zero {A : matrix (fin 0) (fin 0) R}: det A = 1 :=
det_eq_one_of_card_eq_zero (fintype.card_fin _)

/-- If `n` has only one element, the determinant of an `n` by `n` matrix is just that element.
Although `unique` implies `decidable_eq` and `fintype`, the instances might
not be syntactically equal. Thus, we need to fill in the args explicitly. -/
@[simp]
lemma det_unique {n : Type*} [unique n] [decidable_eq n] [fintype n] (A : matrix n n R) :
  det A = A (default n) (default n) :=
by simp [det_apply, univ_unique]

lemma det_eq_elem_of_card_eq_one {A : matrix n n R} (h : fintype.card n = 1) (k : n) :
  det A = A k k :=
begin
  have h1 : (univ : finset (perm n)) = {1},
  { apply univ_eq_singleton_of_card_one (1 : perm n),
    simp [card_univ, fintype.card_perm, h] },
  have h2 := univ_eq_singleton_of_card_one k h,
  simp [det_apply, h1, h2],
end

lemma det_mul_aux {M N : matrix n n R} {p : n → n} (H : ¬bijective p) :
  ∑ σ : perm n, (ε σ) * ∏ x, (M (σ x) (p x) * N (p x) x) = 0 :=
begin
  obtain ⟨i, j, hpij, hij⟩ : ∃ i j, p i = p j ∧ i ≠ j,
  { rw [← fintype.injective_iff_bijective, injective] at H,
    push_neg at H,
    exact H },
  exact sum_involution
    (λ σ _, σ * swap i j)
    (λ σ _,
      have ∏ x, M (σ x) (p x) = ∏ x, M ((σ * swap i j) x) (p x),
        from fintype.prod_equiv (swap i j) _ _ (by simp [apply_swap_eq_self hpij]),
      by simp [this, sign_swap hij, prod_mul_distrib])
    (λ σ _ _, (not_congr mul_swap_eq_iff).mpr hij)
    (λ _ _, mem_univ _)
    (λ σ _, mul_swap_involutive i j σ)
end

@[simp] lemma det_mul (M N : matrix n n R) : det (M ⬝ N) = det M * det N :=
calc det (M ⬝ N) = ∑ p : n → n, ∑ σ : perm n, ε σ * ∏ i, (M (σ i) (p i) * N (p i) i) :
  by simp only [det_apply', mul_apply, prod_univ_sum, mul_sum,
    fintype.pi_finset_univ]; rw [finset.sum_comm]
... = ∑ p in (@univ (n → n) _).filter bijective, ∑ σ : perm n,
    ε σ * ∏ i, (M (σ i) (p i) * N (p i) i) :
  eq.symm $ sum_subset (filter_subset _ _)
    (λ f _ hbij, det_mul_aux $ by simpa only [true_and, mem_filter, mem_univ] using hbij)
... = ∑ τ : perm n, ∑ σ : perm n, ε σ * ∏ i, (M (σ i) (τ i) * N (τ i) i) :
  sum_bij (λ p h, equiv.of_bijective p (mem_filter.1 h).2) (λ _ _, mem_univ _)
    (λ _ _, rfl) (λ _ _ _ _ h, by injection h)
    (λ b _, ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, coe_fn_injective rfl⟩)
... = ∑ σ : perm n, ∑ τ : perm n, (∏ i, N (σ i) i) * ε τ * (∏ j, M (τ j) (σ j)) :
  by simp only [mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
... = ∑ σ : perm n, ∑ τ : perm n, (((∏ i, N (σ i) i) * (ε σ * ε τ)) * ∏ i, M (τ i) i) :
  sum_congr rfl (λ σ _, fintype.sum_equiv (equiv.mul_right σ⁻¹) _ _
    (λ τ,
      have ∏ j, M (τ j) (σ j) = ∏ j, M ((τ * σ⁻¹) j) j,
        by { rw ← σ⁻¹.prod_comp, simp only [equiv.perm.coe_mul, apply_inv_self] },
      have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
        calc ε σ * ε (τ * σ⁻¹) = ε ((τ * σ⁻¹) * σ) :
          by { rw [mul_comm, sign_mul (τ * σ⁻¹)], simp only [int.cast_mul, units.coe_mul] }
        ... = ε τ : by simp only [inv_mul_cancel_right],
      by { simp_rw [equiv.coe_mul_right, h], simp only [this] }))
... = det M * det N : by simp only [det_apply', finset.mul_sum, mul_comm, mul_left_comm]

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

/-- On square matrices, `mul_comm` applies under `det`. -/
lemma det_mul_comm (M N : matrix m m R) : det (M ⬝ N) = det (N ⬝ M) :=
by rw [det_mul, det_mul, mul_comm]

/-- On square matrices, `mul_left_comm` applies under `det`. -/
lemma det_mul_left_comm (M N P : matrix m m R) : det (M ⬝ (N ⬝ P)) = det (N ⬝ (M ⬝ P)) :=
by rw [←matrix.mul_assoc, ←matrix.mul_assoc, det_mul, det_mul_comm M N, ←det_mul]

/-- On square matrices, `mul_right_comm` applies under `det`. -/
lemma det_mul_right_comm (M N P : matrix m m R) :
  det (M ⬝ N ⬝ P) = det (M ⬝ P ⬝ N) :=
by rw [matrix.mul_assoc, matrix.mul_assoc, det_mul, det_mul_comm N P, ←det_mul]

lemma det_units_conj (M : units (matrix m m R)) (N : matrix m m R) :
  det (↑M ⬝ N ⬝ ↑M⁻¹ : matrix m m R) = det N :=
by rw [det_mul_right_comm, ←mul_eq_mul, ←mul_eq_mul, units.mul_inv, one_mul]

lemma det_units_conj' (M : units (matrix m m R)) (N : matrix m m R) :
  det (↑M⁻¹ ⬝ N ⬝ ↑M : matrix m m R) = det N := det_units_conj M⁻¹ N

/-- Transposing a matrix preserves the determinant. -/
@[simp] lemma det_transpose (M : matrix n n R) : Mᵀ.det = M.det :=
begin
  rw [det_apply', det_apply'],
  refine fintype.sum_bijective _ inv_involutive.bijective _ _ _,
  intros σ,
  rw sign_inv,
  congr' 1,
  apply fintype.prod_equiv σ,
  intros,
  simp
end


/-- Permuting the columns changes the sign of the determinant. -/
lemma det_permute (σ : perm n) (M : matrix n n R) : matrix.det (λ i, M (σ i)) = σ.sign * M.det :=
((det_row_multilinear : alternating_map R (n → R) R n).map_perm M σ).trans
  (by simp [units.smul_def])

/-- Permuting rows and columns with the same equivalence has no effect. -/
@[simp]
lemma det_minor_equiv_self (e : n ≃ m) (A : matrix m m R) :
  det (A.minor e e) = det A :=
begin
  rw [det_apply', det_apply'],
  apply fintype.sum_equiv (equiv.perm_congr e),
  intro σ,
  rw equiv.perm.sign_perm_congr e σ,
  congr' 1,
  apply fintype.prod_equiv e,
  intro i,
  rw [equiv.perm_congr_apply, equiv.symm_apply_apply, minor_apply],
end

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`; this one is unsuitable because
`matrix.reindex_apply` unfolds `reindex` first.
-/
lemma det_reindex_self (e : m ≃ n) (A : matrix m m R) : det (reindex e e A) = det A :=
det_minor_equiv_self e.symm A

/-- The determinant of a permutation matrix equals its sign. -/
@[simp] lemma det_permutation (σ : perm n) :
  matrix.det (σ.to_pequiv.to_matrix : matrix n n R) = σ.sign :=
by rw [←matrix.mul_one (σ.to_pequiv.to_matrix : matrix n n R), pequiv.to_pequiv_mul_matrix,
  det_permute, det_one, mul_one]

@[simp] lemma det_smul {A : matrix n n R} {c : R} : det (c • A) = c ^ fintype.card n * det A :=
calc det (c • A) = det (matrix.mul (diagonal (λ _, c)) A) : by rw [smul_eq_diagonal_mul]
             ... = det (diagonal (λ _, c)) * det A        : det_mul _ _
             ... = c ^ fintype.card n * det A             : by simp [card_univ]

/-- Multiplying each row by a fixed `v i` multiplies the determinant by
the product of the `v`s. -/
lemma det_mul_row (v : n → R) (A : matrix n n R) :
  det (λ i j, v j * A i j) = (∏ i, v i) * det A :=
calc det (λ i j, v j * A i j) = det (A ⬝ diagonal v) : congr_arg det $ by { ext, simp [mul_comm] }
                          ... = (∏ i, v i) * det A : by rw [det_mul, det_diagonal, mul_comm]

/-- Multiplying each column by a fixed `v j` multiplies the determinant by
the product of the `v`s. -/
lemma det_mul_column (v : n → R) (A : matrix n n R) :
  det (λ i j, v i * A i j) = (∏ i, v i) * det A :=
multilinear_map.map_smul_univ _ v A

section hom_map

variables {S : Type w} [comm_ring S]

lemma ring_hom.map_det {M : matrix n n R} {f : R →+* S} :
  f M.det = matrix.det (f.map_matrix M) :=
by simp [matrix.det_apply', f.map_sum, f.map_prod]

lemma alg_hom.map_det [algebra R S] {T : Type z} [comm_ring T] [algebra R T]
  {M : matrix n n S} {f : S →ₐ[R] T} :
  f M.det = matrix.det ((f : S →+* T).map_matrix M) :=
by rw [← alg_hom.coe_to_ring_hom, ring_hom.map_det]

end hom_map

section det_zero
/-!
### `det_zero` section

Prove that a matrix with a repeated column has determinant equal to zero.
-/

lemma det_eq_zero_of_row_eq_zero {A : matrix n n R} (i : n) (h : ∀ j, A i j = 0) : det A = 0 :=
(det_row_multilinear : alternating_map R (n → R) R n).map_coord_zero i (funext h)

lemma det_eq_zero_of_column_eq_zero {A : matrix n n R} (j : n) (h : ∀ i, A i j = 0) : det A = 0 :=
by { rw ← det_transpose, exact det_eq_zero_of_row_eq_zero j h, }

variables {M : matrix n n R} {i j : n}

/-- If a matrix has a repeated row, the determinant will be zero. -/
theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
(det_row_multilinear : alternating_map R (n → R) R n).map_eq_zero_of_eq M hij i_ne_j

/-- If a matrix has a repeated column, the determinant will be zero. -/
theorem det_zero_of_column_eq (i_ne_j : i ≠ j) (hij : ∀ k, M k i = M k j) : M.det = 0 :=
by { rw [← det_transpose, det_zero_of_row_eq i_ne_j], exact funext hij }

end det_zero

lemma det_update_row_add (M : matrix n n R) (j : n) (u v : n → R) :
  det (update_row M j $ u + v) = det (update_row M j u) + det (update_row M j v) :=
(det_row_multilinear : alternating_map R (n → R) R n).map_add M j u v

lemma det_update_column_add (M : matrix n n R) (j : n) (u v : n → R) :
  det (update_column M j $ u + v) = det (update_column M j u) + det (update_column M j v) :=
begin
  rw [← det_transpose, ← update_row_transpose, det_update_row_add],
  simp [update_row_transpose, det_transpose]
end

lemma det_update_row_smul (M : matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_row M j $ s • u) = s * det (update_row M j u) :=
(det_row_multilinear : alternating_map R (n → R) R n).map_smul M j s u

lemma det_update_column_smul (M : matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_column M j $ s • u) = s * det (update_column M j u) :=
begin
  rw [← det_transpose, ← update_row_transpose, det_update_row_smul],
  simp [update_row_transpose, det_transpose]
end

section det_eq

/-! ### `det_eq` section

Lemmas showing the determinant is invariant under a variety of operations.
-/
lemma det_eq_of_eq_mul_det_one {A B : matrix n n R}
  (C : matrix n n R) (hC : det C = 1) (hA : A = B ⬝ C) : det A = det B :=
calc det A = det (B ⬝ C) : congr_arg _ hA
       ... = det B * det C : det_mul _ _
       ... = det B : by rw [hC, mul_one]

lemma det_eq_of_eq_det_one_mul {A B : matrix n n R}
  (C : matrix n n R) (hC : det C = 1) (hA : A = C ⬝ B) : det A = det B :=
calc det A = det (C ⬝ B) : congr_arg _ hA
       ... = det C * det B : det_mul _ _
       ... = det B : by rw [hC, one_mul]

lemma det_update_row_add_self (A : matrix n n R) {i j : n} (hij : i ≠ j) :
  det (update_row A i (A i + A j)) = det A :=
by simp [det_update_row_add,
    det_zero_of_row_eq hij ((update_row_self).trans (update_row_ne hij.symm).symm)]

lemma det_update_column_add_self (A : matrix n n R) {i j : n} (hij : i ≠ j) :
  det (update_column A i (λ k, A k i + A k j)) = det A :=
by { rw [← det_transpose, ← update_row_transpose, ← det_transpose A],
     exact det_update_row_add_self Aᵀ hij }

lemma det_update_row_add_smul_self (A : matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
  det (update_row A i (A i + c • A j)) = det A :=
by simp [det_update_row_add, det_update_row_smul,
  det_zero_of_row_eq hij ((update_row_self).trans (update_row_ne hij.symm).symm)]

lemma det_update_column_add_smul_self (A : matrix n n R) {i j : n} (hij : i ≠ j) (c : R) :
  det (update_column A i (λ k, A k i + c • A k j)) = det A :=
by { rw [← det_transpose, ← update_row_transpose, ← det_transpose A],
      exact det_update_row_add_smul_self Aᵀ hij c }

lemma det_eq_of_forall_row_eq_smul_add_const_aux
  {A B : matrix n n R} {s : finset n} : ∀ (c : n → R) (hs : ∀ i, i ∉ s → c i = 0)
  (k : n) (hk : k ∉ s) (A_eq : ∀ i j, A i j = B i j + c i * B k j),
  det A = det B :=
begin
  revert B,
  refine s.induction_on _ _,
  { intros A c hs k hk A_eq,
    have : ∀ i, c i = 0,
    { intros i,
      specialize hs i,
      contrapose! hs,
      simp [hs] },
    congr,
    ext i j,
    rw [A_eq, this, zero_mul, add_zero], },
  { intros i s hi ih B c hs k hk A_eq,
    have hAi : A i = B i + c i • B k := funext (A_eq i),
    rw [@ih (update_row B i (A i)) (function.update c i 0), hAi,
        det_update_row_add_smul_self],
    { exact mt (λ h, show k ∈ insert i s, from h ▸ finset.mem_insert_self _ _) hk },
    { intros i' hi',
      rw function.update_apply,
      split_ifs with hi'i, { refl },
      { exact hs i' (λ h, hi' ((finset.mem_insert.mp h).resolve_left hi'i)) } },
    { exact λ h, hk (finset.mem_insert_of_mem h) },
    { intros i' j',
      rw [update_row_apply, function.update_apply],
      split_ifs with hi'i,
      { simp [hi'i] },
      rw [A_eq, update_row_ne (λ (h : k = i), hk $ h ▸ finset.mem_insert_self k s)] } }
end

/-- If you add multiples of row `B k` to other rows, the determinant doesn't change. -/
lemma det_eq_of_forall_row_eq_smul_add_const
  {A B : matrix n n R} (c : n → R) (k : n) (hk : c k = 0)
  (A_eq : ∀ i j, A i j = B i j + c i * B k j) :
  det A = det B :=
det_eq_of_forall_row_eq_smul_add_const_aux c
  (λ i, not_imp_comm.mp $ λ hi, finset.mem_erase.mpr
    ⟨mt (λ (h : i = k), show c i = 0, from h.symm ▸ hk) hi, finset.mem_univ i⟩)
  k (finset.not_mem_erase k finset.univ) A_eq

lemma det_eq_of_forall_row_eq_smul_add_pred_aux {n : ℕ} (k : fin (n + 1)) :
  ∀ (c : fin n → R) (hc : ∀ (i : fin n), k < i.succ → c i = 0)
    {M N : matrix (fin n.succ) (fin n.succ) R}
    (h0 : ∀ j, M 0 j = N 0 j)
    (hsucc : ∀ (i : fin n) j, M i.succ j = N i.succ j + c i * M i.cast_succ j),
    det M = det N :=
begin
  refine fin.induction _ (λ k ih, _) k;
    intros c hc M N h0 hsucc,
  { congr,
    ext i j,
    refine fin.cases (h0 j) (λ i, _) i,
    rw [hsucc, hc i (fin.succ_pos _), zero_mul, add_zero] },

  set M' := update_row M k.succ (N k.succ) with hM',
  have hM : M = update_row M' k.succ (M' k.succ + c k • M k.cast_succ),
  { ext i j,
    by_cases hi : i = k.succ,
    { simp [hi, hM', hsucc, update_row_self] },
    rw [update_row_ne hi, hM', update_row_ne hi] },

  have k_ne_succ : k.cast_succ ≠ k.succ := (fin.cast_succ_lt_succ k).ne,
  have M_k : M k.cast_succ = M' k.cast_succ := (update_row_ne k_ne_succ).symm,

  rw [hM, M_k, det_update_row_add_smul_self M' k_ne_succ.symm, ih (function.update c k 0)],
  { intros i hi,
    rw [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ, fin.coe_succ, nat.lt_succ_iff] at hi,
    rw function.update_apply,
    split_ifs with hik, { refl },
    exact hc _ (fin.succ_lt_succ_iff.mpr (lt_of_le_of_ne hi (ne.symm hik))) },
  { rwa [hM', update_row_ne (fin.succ_ne_zero _).symm] },
  intros i j,
  rw function.update_apply,
  split_ifs with hik,
  { rw [zero_mul, add_zero, hM', hik, update_row_self] },
  rw [hM', update_row_ne ((fin.succ_injective _).ne hik), hsucc],
  by_cases hik2 : k < i,
  { simp [hc i (fin.succ_lt_succ_iff.mpr hik2)] },
  rw update_row_ne,
  apply ne_of_lt,
  rwa [fin.lt_iff_coe_lt_coe, fin.coe_cast_succ, fin.coe_succ, nat.lt_succ_iff, ← not_lt]
end

/-- If you add multiples of previous rows to the next row, the determinant doesn't change. -/
lemma det_eq_of_forall_row_eq_smul_add_pred {n : ℕ}
  {A B : matrix (fin (n + 1)) (fin (n + 1)) R} (c : fin n → R)
  (A_zero : ∀ j, A 0 j = B 0 j)
  (A_succ : ∀ (i : fin n) j, A i.succ j = B i.succ j + c i * A i.cast_succ j) :
  det A = det B :=
det_eq_of_forall_row_eq_smul_add_pred_aux (fin.last _) c
  (λ i hi, absurd hi (not_lt_of_ge (fin.le_last _)))
  A_zero A_succ

/-- If you add multiples of previous columns to the next columns, the determinant doesn't change. -/
lemma det_eq_of_forall_col_eq_smul_add_pred {n : ℕ}
  {A B : matrix (fin (n + 1)) (fin (n + 1)) R} (c : fin n → R)
  (A_zero : ∀ i, A i 0 = B i 0)
  (A_succ : ∀ i (j : fin n), A i j.succ = B i j.succ + c j * A i j.cast_succ) :
  det A = det B :=
by { rw [← det_transpose A, ← det_transpose B],
     exact det_eq_of_forall_row_eq_smul_add_pred c A_zero (λ i j, A_succ j i) }

end det_eq

@[simp] lemma det_block_diagonal {o : Type*} [fintype o] [decidable_eq o] (M : o → matrix n n R) :
  (block_diagonal M).det = ∏ k, (M k).det :=
begin
  -- Rewrite the determinants as a sum over permutations.
  simp_rw [det_apply'],
  -- The right hand side is a product of sums, rewrite it as a sum of products.
  rw finset.prod_sum,
  simp_rw [finset.mem_univ, finset.prod_attach_univ, finset.univ_pi_univ],
  -- We claim that the only permutations contributing to the sum are those that
  -- preserve their second component.
  let preserving_snd : finset (equiv.perm (n × o)) :=
    finset.univ.filter (λ σ, ∀ x, (σ x).snd = x.snd),
  have mem_preserving_snd : ∀ {σ : equiv.perm (n × o)},
    σ ∈ preserving_snd ↔ ∀ x, (σ x).snd = x.snd :=
    λ σ, finset.mem_filter.trans ⟨λ h, h.2, λ h, ⟨finset.mem_univ _, h⟩⟩,
  rw ← finset.sum_subset (finset.subset_univ preserving_snd) _,
  -- And that these are in bijection with `o → equiv.perm m`.
  rw (finset.sum_bij (λ (σ : ∀ (k : o), k ∈ finset.univ → equiv.perm n) _,
                        prod_congr_left (λ k, σ k (finset.mem_univ k))) _ _ _ _).symm,
  { intros σ _,
    rw mem_preserving_snd,
    rintros ⟨k, x⟩,
    simp only [prod_congr_left_apply] },
  { intros σ _,
    rw [finset.prod_mul_distrib, ←finset.univ_product_univ, finset.prod_product, finset.prod_comm],
    simp only [sign_prod_congr_left, units.coe_prod, int.cast_prod, block_diagonal_apply_eq,
      prod_congr_left_apply] },
  { intros σ σ' _ _ eq,
    ext x hx k,
    simp only at eq,
    have : ∀ k x, prod_congr_left (λ k, σ k (finset.mem_univ _)) (k, x) =
                  prod_congr_left (λ k, σ' k (finset.mem_univ _)) (k, x) :=
      λ k x, by rw eq,
    simp only [prod_congr_left_apply, prod.mk.inj_iff] at this,
    exact (this k x).1 },
  { intros σ hσ,
    rw mem_preserving_snd at hσ,
    have hσ' : ∀ x, (σ⁻¹ x).snd = x.snd,
    { intro x, conv_rhs { rw [← perm.apply_inv_self σ x, hσ] } },
    have mk_apply_eq : ∀ k x, ((σ (x, k)).fst, k) = σ (x, k),
    { intros k x,
      ext,
      { simp only},
      { simp only [hσ] } },
    have mk_inv_apply_eq : ∀ k x, ((σ⁻¹ (x, k)).fst, k) = σ⁻¹ (x, k),
    { intros k x,
      conv_lhs { rw ← perm.apply_inv_self σ (x, k) },
      ext,
      { simp only [apply_inv_self] },
      { simp only [hσ'] } },
    refine ⟨λ k _, ⟨λ x, (σ (x, k)).fst, λ x, (σ⁻¹ (x, k)).fst, _, _⟩, _, _⟩,
    { intro x,
      simp only [mk_apply_eq, inv_apply_self] },
    { intro x,
      simp only [mk_inv_apply_eq, apply_inv_self] },
    { apply finset.mem_univ },
    { ext ⟨k, x⟩,
      { simp only [coe_fn_mk, prod_congr_left_apply] },
      { simp only [prod_congr_left_apply, hσ] } } },
  { intros σ _ hσ,
    rw mem_preserving_snd at hσ,
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ,
    rw [finset.prod_eq_zero (finset.mem_univ (k, x)), mul_zero],
    rw [← @prod.mk.eta _ _ (σ (k, x)), block_diagonal_apply_ne],
    exact hkx }
end

/-- The determinant of a 2x2 block matrix with the lower-left block equal to zero is the product of
the determinants of the diagonal blocks. For the generalization to any number of blocks, see
`matrix.upper_block_triangular_det`. -/
lemma upper_two_block_triangular_det
  (A : matrix m m R) (B : matrix m n R) (D : matrix n n R) :
  (matrix.from_blocks A B 0 D).det = A.det * D.det :=
begin
  classical,
  simp_rw det_apply',
  convert
    (sum_subset (subset_univ ((sum_congr_hom m n).range : set (perm (m ⊕ n))).to_finset) _).symm,
  rw sum_mul_sum,
  simp_rw univ_product_univ,
  rw (sum_bij (λ (σ : perm m × perm n) _, equiv.sum_congr σ.fst σ.snd) _ _ _ _).symm,
  { intros σ₁₂ h,
    simp only [],
    erw [set.mem_to_finset, monoid_hom.mem_range],
    use σ₁₂,
    simp only [sum_congr_hom_apply] },
  { simp only [forall_prop_of_true, prod.forall, mem_univ],
    intros σ₁ σ₂,
    rw fintype.prod_sum_type,
    simp_rw [equiv.sum_congr_apply, sum.map_inr, sum.map_inl, from_blocks_apply₁₁,
      from_blocks_apply₂₂],
    have hr : ∀ (a b c d : R), (a * b) * (c * d) = a * c * (b * d), { intros, ac_refl },
    rw hr,
    congr,
    rw [sign_sum_congr, units.coe_mul, int.cast_mul] },
  { intros σ₁ σ₂ h₁ h₂,
    dsimp only [],
    intro h,
    have h2 : ∀ x, perm.sum_congr σ₁.fst σ₁.snd x = perm.sum_congr σ₂.fst σ₂.snd x,
    { intro x, exact congr_fun (congr_arg to_fun h) x },
    simp only [sum.map_inr, sum.map_inl, perm.sum_congr_apply, sum.forall] at h2,
    ext,
    { exact h2.left x },
    { exact h2.right x }},
  { intros σ hσ,
    erw [set.mem_to_finset, monoid_hom.mem_range] at hσ,
    obtain ⟨σ₁₂, hσ₁₂⟩ := hσ,
    use σ₁₂,
    rw ←hσ₁₂,
    simp },
  { intros σ hσ hσn,
    have h1 : ¬ (∀ x, ∃ y, sum.inl y = σ (sum.inl x)),
    { by_contradiction,
      rw set.mem_to_finset at hσn,
      apply absurd (mem_sum_congr_hom_range_of_perm_maps_to_inl _) hσn,
      rintros x ⟨a, ha⟩,
      rw [←ha], exact h a },
    obtain ⟨a, ha⟩ := not_forall.mp h1,
    cases hx : σ (sum.inl a) with a2 b,
    { have hn := (not_exists.mp ha) a2,
      exact absurd hx.symm hn },
    { rw [finset.prod_eq_zero (finset.mem_univ (sum.inl a)), mul_zero],
      rw [hx, from_blocks_apply₂₁], refl }}
end

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column 0. -/
lemma det_succ_column_zero {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) :
  det A = ∑ i : fin n.succ, (-1) ^ (i : ℕ) * A i 0 *
    det (A.minor i.succ_above fin.succ) :=
begin
  rw [matrix.det_apply, finset.univ_perm_fin_succ, ← finset.univ_product_univ],
  simp only [finset.sum_map, equiv.to_embedding_apply, finset.sum_product, matrix.minor],
  refine finset.sum_congr rfl (λ i _, fin.cases _ (λ i, _) i),
  { simp only [fin.prod_univ_succ, matrix.det_apply, finset.mul_sum,
        equiv.perm.decompose_fin_symm_apply_zero, fin.coe_zero, one_mul,
        equiv.perm.decompose_fin.symm_sign, equiv.swap_self, if_true, id.def, eq_self_iff_true,
        equiv.perm.decompose_fin_symm_apply_succ, fin.succ_above_zero, equiv.coe_refl, pow_zero,
        mul_smul_comm] },
  -- `univ_perm_fin_succ` gives a different embedding of `perm (fin n)` into
  -- `perm (fin n.succ)` than the determinant of the submatrix we want,
  -- permute `A` so that we get the correct one.
  have : (-1 : R) ^ (i : ℕ) = i.cycle_range.sign,
  { simp [fin.sign_cycle_range] },
  rw [fin.coe_succ, pow_succ, this, mul_assoc, mul_assoc, mul_left_comm ↑(equiv.perm.sign _),
      ← det_permute, matrix.det_apply, finset.mul_sum, finset.mul_sum],
  -- now we just need to move the corresponding parts to the same place
  refine finset.sum_congr rfl (λ σ _, _),
  rw [equiv.perm.decompose_fin.symm_sign, if_neg (fin.succ_ne_zero i)],
  calc ((-1) * σ.sign : ℤ) • ∏ i', A (equiv.perm.decompose_fin.symm (fin.succ i, σ) i') i'
      = ((-1) * σ.sign : ℤ) • (A (fin.succ i) 0 *
        ∏ i', A (((fin.succ i).succ_above) (fin.cycle_range i (σ i'))) i'.succ) :
    by simp only [fin.prod_univ_succ, fin.succ_above_cycle_range,
      equiv.perm.decompose_fin_symm_apply_zero, equiv.perm.decompose_fin_symm_apply_succ]
  ... = (-1) * (A (fin.succ i) 0 * (σ.sign : ℤ) •
        ∏ i', A (((fin.succ i).succ_above) (fin.cycle_range i (σ i'))) i'.succ) :
    by simp only [mul_assoc, mul_comm, neg_mul_eq_neg_mul_symm, one_mul, gsmul_eq_mul, neg_inj,
      neg_smul, fin.succ_above_cycle_range],
end

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row 0. -/
lemma det_succ_row_zero {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) :
  det A = ∑ j : fin n.succ, (-1) ^ (j : ℕ) * A 0 j *
    det (A.minor fin.succ j.succ_above) :=
by { rw [← det_transpose A, det_succ_column_zero],
     refine finset.sum_congr rfl (λ i _, _),
     rw [← det_transpose],
     simp only [transpose_apply, transpose_minor, transpose_transpose] }

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along row `i`. -/
lemma det_succ_row {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) (i : fin n.succ) :
  det A = ∑ j : fin n.succ, (-1) ^ (i + j : ℕ) * A i j *
    det (A.minor i.succ_above j.succ_above) :=
begin
  simp_rw [pow_add, mul_assoc, ← mul_sum],
  have : det A = (-1 : R) ^ (i : ℕ) * (i.cycle_range⁻¹).sign * det A,
  { calc det A = ↑((-1 : units ℤ) ^ (i : ℕ) * (-1 : units ℤ) ^ (i : ℕ) : units ℤ) * det A :
             by simp
           ... = (-1 : R) ^ (i : ℕ) * (i.cycle_range⁻¹).sign * det A :
             by simp [-int.units_mul_self] },
  rw [this, mul_assoc],
  congr,
  rw [← det_permute, det_succ_row_zero],
  refine finset.sum_congr rfl (λ j _, _),
  rw [mul_assoc, matrix.minor, matrix.minor],
  congr,
  { rw [equiv.perm.inv_def, fin.cycle_range_symm_zero] },
  { ext i' j',
    rw [equiv.perm.inv_def, fin.cycle_range_symm_succ] },
end

/-- Laplacian expansion of the determinant of an `n+1 × n+1` matrix along column `j`. -/
lemma det_succ_column {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) (j : fin n.succ) :
  det A = ∑ i : fin n.succ, (-1) ^ (i + j : ℕ) * A i j *
    det (A.minor i.succ_above j.succ_above) :=
by { rw [← det_transpose, det_succ_row _ j],
     refine finset.sum_congr rfl (λ i _, _),
     rw [add_comm, ← det_transpose, transpose_apply, transpose_minor, transpose_transpose] }

end matrix
