/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.analytic.composition

/-!

# Inverse of analytic functions

We construct the left and right inverse of a formal multilinear series with invertible linear term,
and we prove that they coincide.

## Main statements

* `p.left_inv i`: the formal left inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.right_inv i`: the formal right inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.left_inv_comp` says that `p.left_inv i` is indeed a left inverse to `p` when `p₁ = i`.
* `p.right_inv_comp` says that `p.right_inv i` is indeed a right inverse to `p` when `p₁ = i`.
* `p.left_inv_eq_right_inv` states that the two inverses coincide.
-/

open_locale big_operators classical topological_space
open finset filter

namespace formal_multilinear_series

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]

/-- The left inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `(left_inv p i) ∘ p = id`. For this, the linear term
`p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `q ∘ p` is `∑ qₖ (p_{j₁}, ..., p_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `qₙ (p₁, ..., p₁)`. We adjust the definition so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.
-/

noncomputable def left_inv (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  formal_multilinear_series 𝕜 F E
| 0     := 0
| 1     := (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm
| (n+2) := - ∑ c : {c : composition (n+2) // c.length < n + 2},
      have (c : composition (n+2)).length < n+2 := c.2,
      (left_inv (c : composition (n+2)).length).comp_along_composition
        (p.comp_continuous_linear_map i.symm) c

@[simp] lemma left_inv_coeff_zero (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.left_inv i 0 = 0 := rfl

@[simp] lemma left_inv_coeff_one (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.left_inv i 1 = (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm := rfl

/-- The left inverse does not depend on the zeroth coefficient of of a formal multilinear
series. -/
lemma left_inv_remove_zero (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.remove_zero.left_inv i = p.left_inv i :=
begin
  ext1 n,
  induction n using nat.strong_rec' with n IH,
  cases n, { simp }, -- if one replaces `simp` with `refl`, the proof times out in the kernel.
  cases n, { simp }, -- TODO: why?
  simp only [left_inv, neg_inj],
  refine finset.sum_congr rfl (λ c cuniv, _),
  rcases c with ⟨c, hc⟩,
  ext v,
  dsimp,
  simp [IH _ hc],
end

/-- The left inverse to a formal multilinear series is indeed a left inverse, provided its linear
term is invertible. -/
lemma left_inv_comp (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) :
  (left_inv p i).comp p = id 𝕜 E :=
begin
  ext n v,
  cases n,
  { simp only [left_inv, continuous_multilinear_map.zero_apply, id_apply_ne_one, ne.def,
      not_false_iff, zero_ne_one, comp_coeff_zero']},
  cases n,
  { simp only [left_inv, comp_coeff_one, h, id_apply_one, continuous_linear_equiv.coe_apply,
      continuous_linear_equiv.symm_apply_apply, continuous_multilinear_curry_fin1_symm_apply] },
  have A : (finset.univ : finset (composition (n+2)))
    = {c | composition.length c < n + 2}.to_finset ∪ {composition.ones (n+2)},
  { refine subset.antisymm (λ c hc, _) (subset_univ _),
    by_cases h : c.length < n + 2,
    { simp [h] },
    { simp [composition.eq_ones_iff_le_length.2 (not_lt.1 h)] } },
  have B : disjoint ({c | composition.length c < n + 2} : set (composition (n + 2))).to_finset
    {composition.ones (n+2)}, by simp,
  have C : (p.left_inv i (composition.ones (n + 2)).length)
    (λ (j : fin (composition.ones n.succ.succ).length), p 1 (λ k,
      v ((fin.cast_le (composition.length_le _)) j)))
    = p.left_inv i (n+2) (λ (j : fin (n+2)), p 1 (λ k, v j)),
  { apply formal_multilinear_series.congr _ (composition.ones_length _) (λ j hj1 hj2, _),
    exact formal_multilinear_series.congr _ rfl (λ k hk1 hk2, by congr) },
  have D : p.left_inv i (n+2) (λ (j : fin (n+2)), p 1 (λ k, v j)) =
    - ∑ (c : composition (n + 2)) in {c : composition (n + 2) | c.length < n + 2}.to_finset,
        (p.left_inv i c.length) (p.apply_composition c v),
  { simp only [left_inv, continuous_multilinear_map.neg_apply, neg_inj,
      continuous_multilinear_map.sum_apply],
    convert (sum_to_finset_eq_subtype (λ (c : composition (n+2)), c.length < n+2)
      (λ (c : composition (n+2)), (continuous_multilinear_map.comp_along_composition
        (p.comp_continuous_linear_map ↑(i.symm)) c (p.left_inv i c.length))
          (λ (j : fin (n + 2)), p 1 (λ (k : fin 1), v j)))).symm.trans _,
    simp only [comp_continuous_linear_map_apply_composition,
      continuous_multilinear_map.comp_along_composition_apply],
    congr,
    ext c,
    congr,
    ext k,
    simp [h] },
  simp [formal_multilinear_series.comp, show n + 2 ≠ 1, by dec_trivial, A, finset.sum_union B,
    apply_composition_ones, C, D],
end

/-- The right inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `p ∘ (right_inv p i) = id`. For this, the linear
term `p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `p ∘ q` is `∑ pₖ (q_{j₁}, ..., q_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `p₁ (qₙ)`. We adjust the definition of `qₙ` so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.
-/
noncomputable def right_inv (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  formal_multilinear_series 𝕜 F E
| 0     := 0
| 1     := (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm
| (n+2) :=
    let q : formal_multilinear_series 𝕜 F E := λ k, if h : k < n + 2 then right_inv k else 0 in
    - (i.symm : F →L[𝕜] E).comp_continuous_multilinear_map ((p.comp q) (n+2))

@[simp] lemma right_inv_coeff_zero (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.right_inv i 0 = 0 := rfl

@[simp] lemma right_inv_coeff_one (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.right_inv i 1 = (continuous_multilinear_curry_fin1 𝕜 F E).symm i.symm := rfl

/-- The right inverse does not depend on the zeroth coefficient of of a formal multilinear
series. -/
lemma right_inv_remove_zero (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) :
  p.remove_zero.right_inv i = p.right_inv i :=
begin
  ext1 n,
  induction n using nat.strong_rec' with n IH,
  cases n, { simp },
  cases n, { simp },
  simp only [right_inv, neg_inj],
  unfold_coes,
  congr' 1,
  rw remove_zero_comp_of_pos _ _ (show 0 < n+2, by dec_trivial),
  congr' 1,
  ext k,
  by_cases hk : k < n+2; simp [hk, IH]
end

lemma comp_right_inv_aux1 {n : ℕ} (hn : 0 < n)
  (p : formal_multilinear_series 𝕜 E F) (q : formal_multilinear_series 𝕜 F E) (v : fin n → F) :
  p.comp q n v =
    (∑ (c : composition n) in {c : composition n | 1 < c.length}.to_finset,
      p c.length (q.apply_composition c v)) + p 1 (λ i, q n v) :=
begin
  have A : (finset.univ : finset (composition n))
    = {c | 1 < composition.length c}.to_finset ∪ {composition.single n hn},
  { refine subset.antisymm (λ c hc, _) (subset_univ _),
    by_cases h : 1 < c.length,
    { simp [h] },
    { have : c.length = 1,
        by { refine (eq_iff_le_not_lt.2 ⟨ _, h⟩).symm, exact c.length_pos_of_pos hn },
      rw ← composition.eq_single_iff_length hn at this,
      simp [this] } },
  have B : disjoint ({c | 1 < composition.length c} : set (composition n)).to_finset
    {composition.single n hn}, by simp,
  have C : p (composition.single n hn).length
              (q.apply_composition (composition.single n hn) v)
            = p 1 (λ (i : fin 1), q n v),
  { apply p.congr (composition.single_length hn) (λ j hj1 hj2, _),
    simp [apply_composition_single] },
  simp [formal_multilinear_series.comp, A, finset.sum_union B, C],
end

lemma comp_right_inv_aux2
  (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) (n : ℕ) (v : fin (n + 2) → F) :
  ∑ (c : composition (n + 2)) in {c : composition (n + 2) | 1 < c.length}.to_finset,
    p c.length (apply_composition (λ (k : ℕ), ite (k < n + 2) (p.right_inv i k) 0) c v) =
  ∑ (c : composition (n + 2)) in {c : composition (n + 2) | 1 < c.length}.to_finset,
    p c.length ((p.right_inv i).apply_composition c v) :=
begin
  have N : 0 < n + 2, by dec_trivial,
  refine sum_congr rfl (λ c hc, p.congr rfl (λ j hj1 hj2, _)),
  have : ∀ k, c.blocks_fun k < n + 2,
  { simp only [set.mem_to_finset, set.mem_set_of_eq] at hc,
    simp [← composition.ne_single_iff N, composition.eq_single_iff_length, ne_of_gt hc] },
  simp [apply_composition, this],
end

/-- The right inverse to a formal multilinear series is indeed a right inverse, provided its linear
term is invertible and its constant term vanishes. -/
lemma comp_right_inv (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) (h0 : p 0 = 0) :
  p.comp (right_inv p i) = id 𝕜 F :=
begin
  ext n v,
  cases n,
  { simp only [h0, continuous_multilinear_map.zero_apply, id_apply_ne_one, ne.def, not_false_iff,
      zero_ne_one, comp_coeff_zero']},
  cases n,
  { simp only [comp_coeff_one, h, right_inv, continuous_linear_equiv.apply_symm_apply, id_apply_one,
      continuous_linear_equiv.coe_apply, continuous_multilinear_curry_fin1_symm_apply] },
  have N : 0 < n+2, by dec_trivial,
  simp [comp_right_inv_aux1 N, h, right_inv, lt_irrefl n, show n + 2 ≠ 1, by dec_trivial,
        ← sub_eq_add_neg, sub_eq_zero, comp_right_inv_aux2],
end

private lemma left_inv_eq_right_inv_aux (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) (h0 : p 0 = 0) :
  left_inv p i = right_inv p i := calc
left_inv p i = (left_inv p i).comp (id 𝕜 F) : by simp
... = (left_inv p i).comp (p.comp (right_inv p i)) : by rw comp_right_inv p i h h0
... = ((left_inv p i).comp p).comp (right_inv p i) : by rw comp_assoc
... = (id 𝕜 E).comp (right_inv p i) : by rw left_inv_comp p i h
... = right_inv p i : by simp

/-- The left inverse and the right inverse of a formal multilinear series coincide. This is not at
all obvious from their definition, but it follows from uniqueness of inverses (which comes from the
fact that composition is associative on formal multilinear series). -/
theorem left_inv_eq_right_inv (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (h : p 1 = (continuous_multilinear_curry_fin1 𝕜 E F).symm i) :
  left_inv p i = right_inv p i := calc
left_inv p i = left_inv p.remove_zero i : by rw left_inv_remove_zero
... = right_inv p.remove_zero i : by { apply left_inv_eq_right_inv_aux; simp [h] }
... = right_inv p i : by rw right_inv_remove_zero

lemma right_inv_coeff (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F) (n : ℕ) (hn : 2 ≤ n) :
  p.right_inv i n = - (i.symm : F →L[𝕜] E).comp_continuous_multilinear_map
    (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition n)),
      p.comp_along_composition (p.right_inv i) c) :=
begin
  cases n, { exact false.elim (zero_lt_two.not_le hn) },
  cases n, { exact false.elim (one_lt_two.not_le hn) },
  simp only [right_inv, neg_inj],
  congr' 1,
  ext v,
  have N : 0 < n + 2, by dec_trivial,
  have : (p 1) (λ (i : fin 1), 0) = 0 := continuous_multilinear_map.map_zero _,
  simp [comp_right_inv_aux1 N, lt_irrefl n, this, comp_right_inv_aux2]
end

lemma sum_Ico_add_one (f : ℕ → ℝ) (n : ℕ) : ∑ i in Ico n (n+1), f i = f n :=
by simp

@[simp] lemma sum_Ico_add_two (f : ℕ → ℝ) (n : ℕ) : ∑ i in Ico n (n+2), f i = f n + f (n+1) :=
by simp [Ico.succ_top, add_comm]

@[simp] lemma sum_Ico_add_three (f : ℕ → ℝ) (n : ℕ) :
  ∑ i in Ico n (n+3), f i = f n + f (n+1) + f (n+2) :=
begin
  rw [Ico.succ_top, sum_insert, sum_Ico_add_two],
  { abel },
  { simp },
  { simp }
end

lemma glouk (n : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (r a : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a) :
  ∑ k in Ico 2 (n + 1), a ^ k *
      (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
          r ^ c.length * ∏ j, p (c.blocks_fun j))
  ≤ ∑ j in Ico 2 (n + 1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j :=
calc
∑ k in Ico 2 (n + 1), a ^ k *
  (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
      r ^ c.length * ∏ j, p (c.blocks_fun j))
= ∑ k in Ico 2 (n + 1),
  (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
      ∏ j, r * (a ^ (c.blocks_fun j) * p (c.blocks_fun j))) :
begin
  simp_rw [mul_sum],
  apply sum_congr rfl (λ k hk, _),
  apply sum_congr rfl (λ c hc, _),
  rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, composition.sum_blocks_fun,
      prod_const, card_fin],
  ring,
end
... ≤ ∑ d in comp_partial_sum_target 2 (n + 1) n,
        ∏ (j : fin d.2.length), r * (a ^ d.2.blocks_fun j * p (d.2.blocks_fun j)) :
begin
  rw sum_sigma',
  refine sum_le_sum_of_subset_of_nonneg _ (λ x hx1 hx2,
    prod_nonneg (λ j hj, mul_nonneg hr (mul_nonneg (pow_nonneg ha _) (hp _)))),
  rintros ⟨k, c⟩ hd,
  simp only [set.mem_to_finset, Ico.mem, mem_sigma, set.mem_set_of_eq] at hd,
  simp only [mem_comp_partial_sum_target_iff],
  refine ⟨hd.2, c.length_le.trans_lt hd.1.2, λ j, _⟩,
  have : c ≠ composition.single k (zero_lt_two.trans_le hd.1.1),
    by simp [composition.eq_single_iff_length, ne_of_gt hd.2],
  rw composition.ne_single_iff at this,
  exact (this j).trans_le (nat.lt_succ_iff.mp hd.1.2)
end
... = ∑ e in comp_partial_sum_source 2 (n+1) n, ∏ (j : fin e.1), r * (a ^ e.2 j * p (e.2 j)) :
begin
  symmetry,
  apply comp_change_of_variables_sum,
  rintros ⟨k, blocks_fun⟩ H,
  have K : (comp_change_of_variables 2 (n + 1) n ⟨k, blocks_fun⟩ H).snd.length = k, by simp,
  congr' 2; try { rw K },
  rw fin.heq_fun_iff K.symm,
  assume j,
  rw comp_change_of_variables_blocks_fun,
end
... = ∑ j in Ico 2 (n+1), r ^ j * (∑ k in Ico 1 n, a ^ k * p k) ^ j :
begin
  rw [comp_partial_sum_source, ← sum_sigma' (Ico 2 (n + 1))
    (λ (k : ℕ), (fintype.pi_finset (λ (i : fin k), Ico 1 n) : finset (fin k → ℕ)))
    (λ n e, ∏ (j : fin n), r * (a ^ e j * p (e j)))],
  apply sum_congr rfl (λ j hj, _),
  simp only [← @multilinear_map.mk_pi_algebra_apply ℝ (fin j) _ _ ℝ],
  simp only [← multilinear_map.map_sum_finset (multilinear_map.mk_pi_algebra ℝ (fin j) ℝ)
    (λ k (m : ℕ), r * (a ^ m * p m))],
  simp only [multilinear_map.mk_pi_algebra_apply],
  dsimp,
  simp [prod_const, ← mul_sum, mul_pow],
end

lemma glouk2 {n : ℕ} (hn : 2 ≤ n + 1) (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  {r a C : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) (hC : 0 ≤ C) (hp : ∀ n, ∥p n∥ ≤ C * r ^ n) :
   (∑ k in Ico 1 (n + 1), a ^ k * ∥p.right_inv i k∥) ≤
     ∥(i.symm : F →L[𝕜] E)∥ * a + ∥(i.symm : F →L[𝕜] E)∥ * C * ∑ k in Ico 2 (n + 1),
      (r * ((∑ j in Ico 1 n, a ^ j * ∥p.right_inv i j∥))) ^ k :=
let I := ∥(i.symm : F →L[𝕜] E)∥ in calc
∑ k in Ico 1 (n + 1), a ^ k * ∥p.right_inv i k∥
    = a * I + ∑ k in Ico 2 (n + 1), a ^ k * ∥p.right_inv i k∥ :
by simp only [continuous_multilinear_curry_fin1_symm_apply_norm, pow_one, right_inv_coeff_one,
              Ico.succ_singleton, sum_singleton, ← sum_Ico_consecutive _ one_le_two hn]
... = a * I + ∑ k in Ico 2 (n + 1), a ^ k *
        ∥(i.symm : F →L[𝕜] E).comp_continuous_multilinear_map
          (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
            p.comp_along_composition (p.right_inv i) c)∥ :
begin
  congr' 1,
  apply sum_congr rfl (λ j hj, _),
  rw [right_inv_coeff _ _ _ (Ico.mem.1 hj).1, norm_neg],
end
... ≤ a * ∥(i.symm : F →L[𝕜] E)∥ + ∑ k in Ico 2 (n + 1), a ^ k * (I *
      (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
        C * r ^ c.length * ∏ j, ∥p.right_inv i (c.blocks_fun j)∥)) :
begin
  apply_rules [add_le_add, le_refl, sum_le_sum (λ j hj, _), mul_le_mul_of_nonneg_left,
    pow_nonneg, ha],
  apply (continuous_linear_map.norm_comp_continuous_multilinear_map_le _ _).trans,
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
  apply (norm_sum_le _ _).trans,
  apply sum_le_sum (λ c hc, _),
  apply (comp_along_composition_norm _ _ _).trans,
  apply mul_le_mul_of_nonneg_right (hp _),
  exact prod_nonneg (λ j hj, norm_nonneg _),
end
... = I * a + I * C * ∑ k in Ico 2 (n + 1), a ^ k *
  (∑ c in ({c | 1 < composition.length c}.to_finset : finset (composition k)),
      r ^ c.length * ∏ j, ∥p.right_inv i (c.blocks_fun j)∥) :
begin
  simp_rw [mul_assoc C, ← mul_sum, ← mul_assoc, mul_comm _ (∥↑i.symm∥), mul_assoc, ← mul_sum,
    ← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum],
  ring,
end
... ≤ I * a + I * C * ∑ k in Ico 2 (n+1), (r * ((∑ j in Ico 1 n, a ^ j * ∥p.right_inv i j∥))) ^ k :
begin
  apply_rules [add_le_add, le_refl, mul_le_mul_of_nonneg_left, norm_nonneg, hC, mul_nonneg],
  simp_rw [mul_pow],
  apply glouk n (λ k, ∥p.right_inv i k∥) (λ k, norm_nonneg _) r a hr ha,
end

theorem norm_right_inv (p : formal_multilinear_series 𝕜 E F) (i : E ≃L[𝕜] F)
  (hp : 0 < p.radius) : 0 < (p.right_inv i).radius :=
begin
  obtain ⟨C, r, Cpos, rpos, ple⟩ : ∃ C r (hC : 0 < C) (hr : 0 < r), ∀ (n : ℕ), ∥p n∥ ≤ C * r ^ n :=
    le_mul_pow_of_radius_pos p hp,
  let I := ∥(i.symm : F →L[𝕜] E)∥,
  obtain ⟨a, apos, ha1, ha2⟩ : ∃ a (apos : 0 < a),
    (2 * I * C * r^2 * (I + 1) ^ 2 * a ≤ 1) ∧ (r * (I + 1) * a ≤ 1/2),
  { have : tendsto (λ a, 2 * I * C * r^2 * (I + 1) ^ 2 * a) (𝓝 0)
      (𝓝 (2 * I * C * r^2 * (I + 1) ^ 2 * 0)) := tendsto_const_nhds.mul tendsto_id,
    have A : ∀ᶠ a in 𝓝 0, 2 * I * C * r^2 * (I + 1) ^ 2 * a < 1,
      by { apply (tendsto_order.1 this).2, simp [zero_lt_one] },
    have : tendsto (λ a, r * (I + 1) * a) (𝓝 0)
      (𝓝 (r * (I + 1) * 0)) := tendsto_const_nhds.mul tendsto_id,
    have B : ∀ᶠ a in 𝓝 0, r * (I + 1) * a < 1/2,
      by { apply (tendsto_order.1 this).2, simp [zero_lt_one] },
    have C : ∀ᶠ a in 𝓝[set.Ioi (0 : ℝ)] (0 : ℝ), (0 : ℝ) < a,
      by { filter_upwards [self_mem_nhds_within], exact λ a ha, ha },
    rcases (C.and ((A.and B).filter_mono inf_le_left)).exists with ⟨a, ha⟩,
    exact ⟨a, ha.1, ha.2.1.le, ha.2.2.le⟩ },
  let S := λ n, ∑ k in Ico 1 n, a ^ k * ∥p.right_inv i k∥,
  have IRec : ∀ n, 1 ≤ n → S n ≤ (I + 1) * a,
  { apply nat.le_induction,
    { simp only [S],
      rw [Ico.eq_empty_of_le (le_refl 1), sum_empty],
      exact mul_nonneg (add_nonneg (norm_nonneg _) zero_le_one) apos.le },
    { assume n one_le_n hn,
      have In : 2 ≤ n + 1, by linarith,
      have Snonneg : 0 ≤ S n :=
        sum_nonneg (λ x hx, mul_nonneg (pow_nonneg apos.le _) (norm_nonneg _)),
      have rSn : r * S n ≤ 1/2 := calc
        r * S n ≤ r * ((I+1) * a) : mul_le_mul_of_nonneg_left hn rpos.le
        ... ≤ 1/2 : by rwa [← mul_assoc],
      calc S (n + 1) ≤ I * a + I * C * ∑ k in Ico 2 (n + 1), (r * S n)^k :
         glouk2 In p i rpos.le apos.le Cpos.le ple
      ... = I * a + I * C * (((r * S n) ^ 2 - (r * S n) ^ (n + 1)) / (1 - r * S n)) :
        by { rw geom_sum_Ico' _ In, exact ne_of_lt (rSn.trans_lt (by norm_num)) }
      ... ≤ I * a + I * C * ((r * S n) ^ 2 / (1/2)) :
        begin
          apply_rules [add_le_add, le_refl, mul_le_mul_of_nonneg_left, mul_nonneg, norm_nonneg,
            Cpos.le],
          refine div_le_div (pow_two_nonneg _) _ (by norm_num) (by linarith),
          simp only [sub_le_self_iff],
          apply pow_nonneg (mul_nonneg rpos.le Snonneg),
        end
      ... = I * a + 2 * I * C * (r * S n) ^ 2 : by ring
      ... ≤ I * a + 2 * I * C * (r * ((I + 1) * a)) ^ 2 :
        by apply_rules [add_le_add, le_refl, mul_le_mul_of_nonneg_left, mul_nonneg, norm_nonneg,
            Cpos.le, zero_le_two, pow_le_pow_of_le_left, rpos.le]
      ... = (I + 2 * I * C * r^2 * (I + 1) ^ 2 * a) * a : by ring
      ... ≤ (I + 1) * a :
        by apply_rules [mul_le_mul_of_nonneg_right, apos.le, add_le_add, le_refl] } },
  let a' : nnreal := ⟨a, apos.le⟩,
  suffices H : (a' : ennreal) ≤ (p.right_inv i).radius,
    by { apply lt_of_lt_of_le _ H, exact_mod_cast apos },
  apply le_radius_of_bound _ ((I + 1) * a) (λ n, _),
  by_cases hn : n = 0,
  { have : ∥p.right_inv i n∥ = ∥p.right_inv i 0∥, by congr; try { rw hn },
    simp only [this, norm_zero, zero_mul, right_inv_coeff_zero],
    apply_rules [mul_nonneg, add_nonneg, norm_nonneg, zero_le_one, apos.le] },
  { have one_le_n : 1 ≤ n := bot_lt_iff_ne_bot.2 hn,
    calc ∥p.right_inv i n∥ * ↑a' ^ n = a ^ n * ∥p.right_inv i n∥ : mul_comm _ _
    ... ≤ ∑ k in Ico 1 (n + 1), a ^ k * ∥p.right_inv i k∥ :
      begin
        have : ∀ k ∈ Ico 1 (n + 1), 0 ≤ a ^ k * ∥p.right_inv i k∥ :=
          λ k hk, mul_nonneg (pow_nonneg apos.le _) (norm_nonneg _),
        exact single_le_sum this (by simp [one_le_n]),
      end
    ... ≤ (I + 1) * a : IRec (n + 1) (by dec_trivial) }
end

end formal_multilinear_series
