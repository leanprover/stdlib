/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Tim Baanen
-/
import data.matrix.pequiv
import linear_algebra.alternating

universes u v w z
open equiv equiv.perm finset function

namespace matrix
open_locale matrix big_operators

variables {n : Type u} [decidable_eq n] [fintype n] {R : Type v} [comm_ring R]

local notation `ε` σ:max := ((sign σ : ℤ ) : R)

/-- The determinant of a matrix given by the Leibniz formula. -/
definition det (M : matrix n n R) : R :=
∑ σ : perm n, ε σ * ∏ i, M (σ i) i

@[simp] lemma det_diagonal {d : n → R} : det (diagonal d) = ∏ i, d i :=
begin
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
by rw [← diagonal_zero, det_diagonal, finset.prod_const, ← fintype.card,
  zero_pow (fintype.card_pos_iff.2 h)]

@[simp] lemma det_one : det (1 : matrix n n R) = 1 :=
by rw [← diagonal_one]; simp [-diagonal_one]

lemma det_eq_one_of_card_eq_zero {A : matrix n n R} (h : fintype.card n = 0) : det A = 1 :=
begin
  have perm_eq : (univ : finset (perm n)) = {1} :=
  univ_eq_singleton_of_card_one (1 : perm n) (by simp [card_univ, fintype.card_perm, h]),
  simp [det, card_eq_zero.mp h, perm_eq],
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
        from prod_bij (λ a _, swap i j a) (λ _ _, mem_univ _)
          (by simp [apply_swap_eq_self hpij])
          (λ _ _ _ _ h, (swap i j).injective h)
          (λ b _, ⟨swap i j b, mem_univ _, by simp⟩),
      by simp [this, sign_swap hij, prod_mul_distrib])
    (λ σ _ _, (not_congr mul_swap_eq_iff).mpr hij)
    (λ _ _, mem_univ _)
    (λ σ _, mul_swap_involutive i j σ)
end

@[simp] lemma det_mul (M N : matrix n n R) : det (M ⬝ N) = det M * det N :=
calc det (M ⬝ N) = ∑ p : n → n, ∑ σ : perm n, ε σ * ∏ i, (M (σ i) (p i) * N (p i) i) :
  by simp only [det, mul_apply, prod_univ_sum, mul_sum,
    fintype.pi_finset_univ]; rw [finset.sum_comm]
... = ∑ p in (@univ (n → n) _).filter bijective, ∑ σ : perm n,
    ε σ * ∏ i, (M (σ i) (p i) * N (p i) i) :
  eq.symm $ sum_subset (filter_subset _ _)
    (λ f _ hbij, det_mul_aux $ by simpa using hbij)
... = ∑ τ : perm n, ∑ σ : perm n, ε σ * ∏ i, (M (σ i) (τ i) * N (τ i) i) :
  sum_bij (λ p h, equiv.of_bijective p (mem_filter.1 h).2) (λ _ _, mem_univ _)
    (λ _ _, rfl) (λ _ _ _ _ h, by injection h)
    (λ b _, ⟨b, mem_filter.2 ⟨mem_univ _, b.bijective⟩, injective_coe_fn rfl⟩)
... = ∑ σ : perm n, ∑ τ : perm n, (∏ i, N (σ i) i) * ε τ * (∏ j, M (τ j) (σ j)) :
  by simp [mul_sum, det, mul_comm, mul_left_comm, prod_mul_distrib, mul_assoc]
... = ∑ σ : perm n, ∑ τ : perm n, (((∏ i, N (σ i) i) * (ε σ * ε τ)) * ∏ i, M (τ i) i) :
  sum_congr rfl (λ σ _, sum_bij (λ τ _, τ * σ⁻¹) (λ _ _, mem_univ _)
    (λ τ _,
      have ∏ j, M (τ j) (σ j) = ∏ j, M ((τ * σ⁻¹) j) j,
        by rw ← σ⁻¹.prod_comp; simp [mul_apply],
      have h : ε σ * ε (τ * σ⁻¹) = ε τ :=
        calc ε σ * ε (τ * σ⁻¹) = ε ((τ * σ⁻¹) * σ) :
          by rw [mul_comm, sign_mul (τ * σ⁻¹)]; simp
        ... = ε τ : by simp,
      by rw h; simp [this, mul_comm, mul_assoc, mul_left_comm])
    (λ _ _ _ _, mul_right_cancel) (λ τ _, ⟨τ * σ, by simp⟩))
... = det M * det N : by simp [det, mul_assoc, mul_sum, mul_comm, mul_left_comm]

instance : is_monoid_hom (det : matrix n n R → R) :=
{ map_one := det_one,
  map_mul := det_mul }

/-- Transposing a matrix preserves the determinant. -/
@[simp] lemma det_transpose (M : matrix n n R) : Mᵀ.det = M.det :=
begin
  apply sum_bij (λ σ _, σ⁻¹),
  { intros σ _, apply mem_univ },
  { intros σ _,
    rw [sign_inv],
    congr' 1,
    apply prod_bij (λ i _, σ i),
    { intros i _, apply mem_univ },
    { intros i _, simp },
    { intros i j _ _ h, simp at h, assumption },
    { intros i _, use σ⁻¹ i, finish } },
  { intros σ σ' _ _ h, simp at h, assumption },
  { intros σ _, use σ⁻¹, finish }
end

/-- The determinant of a permutation matrix equals its sign. -/
@[simp] lemma det_permutation (σ : perm n) :
  matrix.det (σ.to_pequiv.to_matrix : matrix n n R) = σ.sign :=
begin
  suffices : matrix.det (σ.to_pequiv.to_matrix) = ↑σ.sign * det (1 : matrix n n R), { simp [this] },
  unfold det,
  rw mul_sum,
  apply sum_bij (λ τ _, σ * τ),
  { intros τ _, apply mem_univ },
  { intros τ _,
    rw [←mul_assoc, sign_mul, coe_coe, ←int.cast_mul, ←units.coe_mul, ←mul_assoc,
        int.units_mul_self, one_mul],
    congr,
    ext i,
    apply pequiv.equiv_to_pequiv_to_matrix },
  { intros τ τ' _ _, exact (mul_right_inj σ).mp },
  { intros τ _, use σ⁻¹ * τ, use (mem_univ _), exact (mul_inv_cancel_left _ _).symm }
end

/-- Permuting the columns changes the sign of the determinant. -/
lemma det_permute (σ : perm n) (M : matrix n n R) : matrix.det (λ i, M (σ i)) = σ.sign * M.det :=
by rw [←det_permutation, ←det_mul, pequiv.to_pequiv_mul_matrix]

@[simp] lemma det_smul {A : matrix n n R} {c : R} : det (c • A) = c ^ fintype.card n * det A :=
calc det (c • A) = det (matrix.mul (diagonal (λ _, c)) A) : by rw [smul_eq_diagonal_mul]
             ... = det (diagonal (λ _, c)) * det A        : det_mul _ _
             ... = c ^ fintype.card n * det A             : by simp [card_univ]

section hom_map

variables {S : Type w} [comm_ring S]

lemma ring_hom.map_det {M : matrix n n R} {f : R →+* S} :
  f M.det = matrix.det (f.map_matrix M) :=
by simp [matrix.det, f.map_sum, f.map_prod]

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
begin
  rw [←det_transpose, det],
  convert @sum_const_zero _ _ (univ : finset (perm n)) _,
  ext σ,
  convert mul_zero ↑(sign σ),
  apply prod_eq_zero (mem_univ i),
  rw [transpose_apply],
  apply h
end

lemma det_eq_zero_of_column_eq_zero {A : matrix n n R} (j : n) (h : ∀ i, A i j = 0) : det A = 0 :=
by { rw ← det_transpose, exact det_eq_zero_of_row_eq_zero j h, }

variables {M : matrix n n R} {i j : n}

/-- If a matrix has a repeated row, the determinant will be zero. -/
theorem det_zero_of_row_eq (i_ne_j : i ≠ j) (hij : M i = M j) : M.det = 0 :=
begin
  apply finset.sum_involution
    (λ σ _, swap i j * σ)
    (λ σ _, _)
    (λ σ _ _, (not_congr swap_mul_eq_iff).mpr i_ne_j)
    (λ σ _, finset.mem_univ _)
    (λ σ _, swap_mul_involutive i j σ),
  convert add_right_neg (↑↑(sign σ) * ∏ i, M (σ i) i),
  rw neg_mul_eq_neg_mul,
  congr,
  { rw [sign_mul, sign_swap i_ne_j], norm_num },
  { ext j, rw [perm.mul_apply, apply_swap_eq_self hij], }
end

end det_zero

lemma det_update_column_add (M : matrix n n R) (j : n) (u v : n → R) :
  det (update_column M j $ u + v) = det (update_column M j u) + det (update_column M j v) :=
begin
  simp only [det],
  have : ∀ σ : perm n, ∏ i, M.update_column j (u + v) (σ i) i =
                       ∏ i, M.update_column j u (σ i) i + ∏ i, M.update_column j v (σ i) i,
  { intros σ,
    simp only [update_column_apply, prod_ite, filter_eq',
               finset.prod_singleton, finset.mem_univ, if_true, pi.add_apply, add_mul] },
  rw [← sum_add_distrib],
  apply sum_congr rfl,
  intros x _,
  rw [this, mul_add]
end

lemma det_update_row_add (M : matrix n n R) (j : n) (u v : n → R) :
  det (update_row M j $ u + v) = det (update_row M j u) + det (update_row M j v) :=
begin
  rw [← det_transpose, ← update_column_transpose, det_update_column_add],
  simp [update_column_transpose, det_transpose]
end

lemma det_update_column_smul (M : matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_column M j $ s • u) = s * det (update_column M j u) :=
begin
  simp only [det],
  have : ∀ σ : perm n, ∏ i, M.update_column j (s • u) (σ i) i = s * ∏ i, M.update_column j u (σ i) i,
  { intros σ,
    simp only [update_column_apply, prod_ite, filter_eq', finset.prod_singleton, finset.mem_univ,
               if_true, algebra.id.smul_eq_mul, pi.smul_apply],
    ring },
  rw mul_sum,
  apply sum_congr rfl,
  intros x _,
  rw this,
  ring
end

lemma det_update_row_smul (M : matrix n n R) (j : n) (s : R) (u : n → R) :
  det (update_row M j $ s • u) = s * det (update_row M j u) :=
begin
  rw [← det_transpose, ← update_column_transpose, det_update_column_smul],
  simp [update_column_transpose, det_transpose]
end

/-- `det` is an alternating multilinear map over the rows of the matrix.

See also `is_basis.det`. -/
@[simps apply]
def det_row_multilinear : alternating_map R (n → R) R n:=
{ to_fun := det,
  map_add' := det_update_row_add,
  map_smul' := det_update_row_smul,
  map_eq_zero_of_eq' := λ M i j h hij, det_zero_of_row_eq hij h }

@[simp] lemma det_block_diagonal {o : Type*} [fintype o] [decidable_eq o] (M : o → matrix n n R) :
  (block_diagonal M).det = ∏ k, (M k).det :=
begin
  -- Rewrite the determinants as a sum over permutations.
  unfold det,
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
    simp },
  { intros σ _,
    rw [finset.prod_mul_distrib, ←finset.univ_product_univ, finset.prod_product, finset.prod_comm],
    simp [sign_prod_congr_left] },
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
      ext; simp [hσ] },
    have mk_inv_apply_eq : ∀ k x, ((σ⁻¹ (x, k)).fst, k) = σ⁻¹ (x, k),
    { intros k x,
      conv_lhs { rw ← perm.apply_inv_self σ (x, k) },
      ext; simp [hσ'] },
    refine ⟨λ k _, ⟨λ x, (σ (x, k)).fst, λ x, (σ⁻¹ (x, k)).fst, _, _⟩, _, _⟩,
    { intro x,
      simp [mk_apply_eq, mk_inv_apply_eq] },
    { intro x,
      simp [mk_apply_eq, mk_inv_apply_eq] },
    { apply finset.mem_univ },
    { ext ⟨k, x⟩; simp [hσ] } },
  { intros σ _ hσ,
    rw mem_preserving_snd at hσ,
    obtain ⟨⟨k, x⟩, hkx⟩ := not_forall.mp hσ,
    rw [finset.prod_eq_zero (finset.mem_univ (k, x)), mul_zero],
    rw [← @prod.mk.eta _ _ (σ (k, x)), block_diagonal_apply_ne],
    exact hkx }
end

end matrix
