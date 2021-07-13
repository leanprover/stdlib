/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Riccardo Brasca
-/
import analysis.normed_space.normed_group_hom

/-!
# Quotients of seminormed groups

For any `semi_normed_group M` and any `S : add_subgroup M`, we provide a `semi_normed_group`
structure on `quotient_add_group.quotient S` (abreviated `quotient S` in the following).
If `S` is closed, we provide `normed_group (quotient S)` (regardless of whether `M` itself is
separated). The two main properties of these structures are the underlying topology is the quotient
topology and the projection is a normed group homomorphism which is norm non-increasing
(better, it has operator norm exactly one unless `S` is dense in `M`). The corresponding
universal property is that every normed group hom defined on `M` which vanishes on `S` descends
to a normed group hom defined on `quotient S`.

This file also introduces a predicate `is_quotient` characterizing normed group homs that
are isomorphic to the canonical projection onto a normed group quotient.


## Main definitions


We use `M` and `N` to denote seminormed groups and `S : add_subgroup M`.
All the following definitions are in the `add_subgroup` namespace. Hence we can access
`add_subgroup.normed_mk S` as `S.normed_mk`.

* `semi_normed_group_quotient` : The seminormed group structure on the quotient by
    an additive subgroup. This is an instance so there is no need to explictly use it.

* `normed_group_quotient` : The normed group structure on the quotient by
    a closed additive subgroup. This is an instance so there is no need to explictly use it.

* `normed_mk S` : the normed group hom from `M` to `quotient S`.

* `lift S f hf`: implements the universal property of `quotient S`. Here
    `(f : normed_group_hom M N)`, `(hf : ∀ s ∈ S, f s = 0)` and
    `lift S f hf : normed_group_hom (quotient S) N`.

* `is_quotient`: given `f : normed_group_hom M N`, `is_quotient f` means `N` is isomorphic
    to a quotient of `M` by a subgroup, with projection `f`. Technically it asserts `f` is
    surjective and the norm of `f x` is the infimum of the norms of `x + m` for `m` in `f.ker`.

## Main results

* `norm_normed_mk` : the operator norm of the projection is `1` if the subspace is not dense.

* `is_quotient.norm_lift`: Provided `f : normed_hom M N` satisfies `is_quotient f`, for every
     `n : N` and positive `ε`, there exists `m` such that `f m = n ∧ ∥m∥ < ∥n∥ + ε`.


## Implementation details

For any `semi_normed_group M` and any `S : add_subgroup M` we define a norm on `quotient S` by
`∥x∥ = Inf (norm '' {m | mk' S m = x})`. This formula is really an implementation detail, it
shouldn't be needed outside of this file setting up the theory.

Since `quotient S` is automatically a topological space (as any quotient of a topological space),
one needs to be careful while defining the `semi_normed_group` instance to avoid having two
different topologies on this quotient. This is not purely a technological issue.
Mathematically there is something to prove. The main point is proved in the auxiliary lemma
`quotient_nhd_basis` that has no use beyond this verification and states that zero in the quotient
admits as basis of neighborhoods in the quotient topology the sets `{x | ∥x∥ < ε}` for positive `ε`.

Once this mathematical point it settled, we have two topologies that are propositionaly equal. This
is not good enough for the type class system. As usual we ensure *definitional* equality
using forgetful inheritance, see Note [forgetful inheritance]. A (semi)-normed group structure
includes a uniform space structure which includes a topological space structure, together
with propositional fields asserting compatibility conditions.
The usual way to define a `semi_normed_group` is to let Lean build a uniform space structure
using the provided norm, and then trivially build a proof that the norm and uniform structure are
compatible. Here the uniform structure is provided using `topological_add_group.to_uniform_space`
which uses the topological structure and the group structure to build the uniform structure. This
uniform structure induces the correct topological structure by construction, but the fact that it
is compatible with the norm is not obvious; this is where the mathematical content explained in
the previous paragraph kicks in.

-/

noncomputable theory


open quotient_add_group metric set
open_locale topological_space nnreal

variables {M N : Type*} [semi_normed_group M] [semi_normed_group N]

/-- The definition of the norm on the quotient by an additive subgroup. -/
noncomputable
instance norm_on_quotient (S : add_subgroup M) : has_norm (quotient S) :=
{ norm := λ x, Inf (norm '' {m | mk' S m = x}) }

lemma image_norm_nonempty {S : add_subgroup M} :
  ∀ x : quotient S, (norm '' {m | mk' S m = x}).nonempty :=
begin
  rintro ⟨m⟩,
  rw set.nonempty_image_iff,
  use m,
  change mk' S m = _,
  refl
end

lemma bdd_below_image_norm (s : set M) : bdd_below (norm '' s) :=
begin
  use 0,
  rintro _ ⟨x, hx, rfl⟩,
  apply norm_nonneg
end

/-- The norm on the quotient satisfies `∥-x∥ = ∥x∥`. -/
lemma quotient_norm_neg {S : add_subgroup M} (x : quotient S) : ∥-x∥ = ∥x∥ :=
begin
  suffices : norm '' {m | mk' S m = x} = norm '' {m | mk' S m = -x},
    by simp only [this, norm],
  ext r,
  split,
  { rintros ⟨m, hm : mk' S m = x, rfl⟩,
    subst hm,
    rw ← norm_neg,
    exact ⟨-m, by simp only [(mk' S).map_neg, set.mem_set_of_eq], rfl⟩ },
  { rintros ⟨m, hm : mk' S m = -x, rfl⟩,
    use -m,
    simp [hm] }
end

lemma quotient_norm_sub_rev {S : add_subgroup M} (x y: quotient S) : ∥x - y∥ = ∥y - x∥ :=
by rw [show x - y = -(y - x), by abel, quotient_norm_neg]

/-- The norm of the projection is smaller or equal to the norm of the original element. -/
lemma quotient_norm_mk_le (S : add_subgroup M) (m : M) :
  ∥mk' S m∥ ≤ ∥m∥ :=
begin
  apply real.Inf_le,
  use 0,
  { rintros _ ⟨n, h, rfl⟩,
    apply norm_nonneg },
  { apply set.mem_image_of_mem,
    rw set.mem_set_of_eq }
end

/-- The norm of the image under the natural morphism to the quotient. -/
lemma quotient_norm_mk_eq (S : add_subgroup M) (m : M) :
  ∥mk' S m∥ = Inf ((λ x, ∥m + x∥) '' S) :=
begin
  change Inf _ = _,
  congr' 1,
  ext r,
  simp_rw [coe_mk', eq_iff_sub_mem],
  split,
  { rintros ⟨y, h, rfl⟩,
    use [y - m, h],
    simp },
  { rintros ⟨y, h, rfl⟩,
    use m + y,
    simpa using h },
end

/-- The quotient norm is nonnegative. -/
lemma quotient_norm_nonneg (S : add_subgroup M) : ∀ x : quotient S, 0 ≤ ∥x∥ :=
begin
  rintros ⟨m⟩,
  change 0 ≤ ∥mk' S m∥,
  apply real.lb_le_Inf _ (image_norm_nonempty _),
  rintros _ ⟨n, h, rfl⟩,
  apply norm_nonneg
end

/-- The quotient norm is nonnegative. -/
lemma norm_mk_nonneg (S : add_subgroup M) (m : M) : 0 ≤ ∥mk' S m∥ :=
quotient_norm_nonneg S _

/-- The norm of the image of `m : M` in the quotient by `S` is zero if and only if `m` belongs
to the closure of `S`. -/
lemma quotient_norm_eq_zero_iff (S : add_subgroup M) (m : M) :
  ∥mk' S m∥ = 0 ↔ m ∈ closure (S : set M) :=
begin
  have : 0 ≤ ∥mk' S m∥ := norm_mk_nonneg S m,
  rw [← this.le_iff_eq, quotient_norm_mk_eq, real.Inf_le_iff],
  simp_rw [zero_add],
  { calc (∀ ε > (0 : ℝ), ∃ r ∈ (λ x, ∥m + x∥) '' (S : set M), r < ε) ↔
        (∀ ε > 0, (∃ x ∈ S, ∥m + x∥ < ε)) : by simp [set.bex_image_iff]
     ... ↔ ∀ ε > 0, (∃ x ∈ S, ∥m + -x∥ < ε) : _
     ... ↔ ∀ ε > 0, (∃ x ∈ S, x ∈ metric.ball m ε) : by simp [dist_eq_norm, ← sub_eq_add_neg,
                                                              norm_sub_rev]
     ... ↔ m ∈ closure ↑S : by simp [metric.mem_closure_iff, dist_comm],
    apply forall_congr, intro ε, apply forall_congr, intro  ε_pos,
    rw [← S.exists_neg_mem_iff_exists_mem],
    simp },
  { use 0,
    rintro _ ⟨x, x_in, rfl⟩,
    apply norm_nonneg },
  rw set.nonempty_image_iff,
  use [0, S.zero_mem]
end

/-- For any `x : quotient S` and any `0 < ε`, there is `m : M` such that `mk' S m = x`
and `∥m∥ < ∥x∥ + ε`. -/
lemma norm_mk_lt {S : add_subgroup M} (x : quotient S) {ε : ℝ} (hε : 0 < ε) :
  ∃ (m : M), mk' S m = x ∧ ∥m∥ < ∥x∥ + ε :=
begin
  obtain ⟨_, ⟨m : M, H : mk' S m = x, rfl⟩, hnorm : ∥m∥ < ∥x∥ + ε⟩ :=
    real.lt_Inf_add_pos (bdd_below_image_norm _) (image_norm_nonempty x) hε,
  subst H,
  exact ⟨m, rfl, hnorm⟩,
end

/-- For any `m : M` and any `0 < ε`, there is `s ∈ S` such that `∥m + s∥ < ∥mk' S m∥ + ε`. -/
lemma norm_mk_lt' (S : add_subgroup M) (m : M) {ε : ℝ} (hε : 0 < ε) :
  ∃ s ∈ S, ∥m + s∥ < ∥mk' S m∥ + ε :=
begin
  obtain ⟨n : M, hn : mk' S n = mk' S m, hn' : ∥n∥ < ∥mk' S m∥ + ε⟩ :=
    norm_mk_lt (quotient_add_group.mk' S m) hε,
  erw [eq_comm, quotient_add_group.eq] at hn,
  use [- m + n, hn],
  rwa [add_neg_cancel_left]
end

/-- The quotient norm satisfies the triangle inequality. -/
lemma quotient_norm_add_le (S : add_subgroup M) (x y : quotient S) : ∥x + y∥ ≤ ∥x∥ + ∥y∥ :=
begin
  refine le_of_forall_pos_le_add (λ ε hε, _),
  replace hε := half_pos hε,
  obtain ⟨m, rfl, hm : ∥m∥ < ∥mk' S m∥ + ε / 2⟩ := norm_mk_lt x hε,
  obtain ⟨n, rfl, hn : ∥n∥ < ∥mk' S n∥ + ε / 2⟩ := norm_mk_lt y hε,
  calc ∥mk' S m + mk' S n∥ = ∥mk' S (m +  n)∥ : by rw (mk' S).map_add
  ... ≤ ∥m + n∥ : quotient_norm_mk_le S (m + n)
  ... ≤ ∥m∥ + ∥n∥ : norm_add_le _ _
  ... ≤ ∥mk' S m∥ + ∥mk' S n∥ + ε : by linarith
end

/-- The quotient norm of `0` is `0`. -/
lemma norm_mk_zero (S : add_subgroup M) : ∥(0 : quotient S)∥ = 0 :=
begin
  erw quotient_norm_eq_zero_iff,
  exact subset_closure S.zero_mem
end

/-- If `(m : M)` has norm equal to `0` in `quotient S` for a closed subgroup `S` of `M`, then
`m ∈ S`. -/
lemma norm_zero_eq_zero (S : add_subgroup M) (hS : is_closed (S : set M)) (m : M)
  (h : ∥mk' S m∥ = 0) : m ∈ S :=
by rwa [quotient_norm_eq_zero_iff, hS.closure_eq] at h

lemma quotient_nhd_basis (S : add_subgroup M) :
  (𝓝 (0 : quotient S)).has_basis (λ ε : ℝ, 0 < ε) (λ ε, {x | ∥x∥ < ε}) :=
⟨begin
  intros U,
  split,
  { intros U_in,
    rw ← (mk' S).map_zero at U_in,
    have := preimage_nhds_coinduced U_in,
    rcases metric.mem_nhds_iff.mp this with ⟨ε, ε_pos, H⟩,
    use [ε/2, half_pos ε_pos],
    intros x x_in,
    dsimp at x_in,
    rcases norm_mk_lt x (half_pos ε_pos) with ⟨y, rfl, ry⟩,
    apply H,
    rw ball_0_eq,
    dsimp,
    linarith },
  { rintros ⟨ε, ε_pos, h⟩,
    have : (mk' S) '' (ball (0 : M) ε) ⊆ {x | ∥x∥ < ε},
    { rintros - ⟨x, x_in, rfl⟩,
      rw mem_ball_0_iff at x_in,
      exact lt_of_le_of_lt (quotient_norm_mk_le S x) x_in },
    apply filter.mem_sets_of_superset _ (set.subset.trans this h),
    clear h U this,
    apply is_open.mem_nhds,
    { change is_open ((mk' S) ⁻¹' _),
      erw quotient_add_group.preimage_image_coe,
      apply is_open_Union,
      rintros ⟨s, s_in⟩,
      exact (continuous_add_right s).is_open_preimage _ is_open_ball },
    { exact ⟨(0 : M), mem_ball_self ε_pos, (mk' S).map_zero⟩ } },
end⟩

/-- The seminormed group structure on the quotient by an additive subgroup. -/
noncomputable
instance add_subgroup.semi_normed_group_quotient (S : add_subgroup M) :
  semi_normed_group (quotient S) :=
{ dist               := λ x y, ∥x - y∥,
  dist_self          := λ x, by simp only [norm_mk_zero, sub_self],
  dist_comm          := quotient_norm_sub_rev,
  dist_triangle      := λ x y z,
  begin
    unfold dist,
    have : x - z = (x - y) + (y - z) := by abel,
    rw this,
    exact quotient_norm_add_le S (x - y) (y - z)
  end,
  dist_eq := λ x y, rfl,
  to_uniform_space   := topological_add_group.to_uniform_space (quotient S),
  uniformity_dist    :=
  begin
    rw uniformity_eq_comap_nhds_zero',
    have := (quotient_nhd_basis S).comap (λ (p : quotient S × quotient S), p.2 - p.1),
    apply this.eq_of_same_basis,
    have : ∀ ε : ℝ, (λ (p : quotient S × quotient S), p.snd - p.fst) ⁻¹' {x | ∥x∥ < ε} =
      {p : quotient S × quotient S | ∥p.fst - p.snd∥ < ε},
    { intro ε,
      ext x,
      dsimp,
      rw quotient_norm_sub_rev },
    rw funext this,
    refine filter.has_basis_binfi_principal _ set.nonempty_Ioi,
    rintros ε (ε_pos : 0 < ε) η (η_pos : 0 < η),
    refine ⟨min ε η, lt_min ε_pos η_pos, _, _⟩,
    { suffices : ∀ (a b : quotient S), ∥a - b∥ < ε → ∥a - b∥ < η → ∥a - b∥ < ε, by simpa,
      exact λ a b h h', h },
    { simp }
  end }

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example (S : add_subgroup M) : (quotient.topological_space : topological_space $ quotient S) =
S.semi_normed_group_quotient.to_uniform_space.to_topological_space :=
rfl

/-- The quotient in the category of normed groups. -/
noncomputable
instance add_subgroup.normed_group_quotient (S : add_subgroup M) [hS : is_closed (S : set M)] :
  normed_group (quotient S) :=
{ eq_of_dist_eq_zero :=
  begin
    rintros ⟨m⟩ ⟨m'⟩ (h : ∥mk' S m - mk' S m'∥ = 0),
    erw [← (mk' S).map_sub, quotient_norm_eq_zero_iff, hS.closure_eq,
         ← quotient_add_group.eq_iff_sub_mem] at h,
    exact h
  end,
  .. add_subgroup.semi_normed_group_quotient S }

-- This is a sanity check left here on purpose to ensure that potential refactors won't destroy
-- this important property.
example (S : add_subgroup M) [is_closed (S : set M)] :
  S.semi_normed_group_quotient = normed_group.to_semi_normed_group := rfl


namespace add_subgroup

open normed_group_hom

/-- The morphism from a seminormed group to the quotient by a subgroup. -/
noncomputable
def normed_mk (S : add_subgroup M) : normed_group_hom M (quotient S) :=
{ bound' := ⟨1, λ m, by simpa [one_mul] using quotient_norm_mk_le  _ m⟩,
  .. quotient_add_group.mk' S }

/-- `S.normed_mk` agrees with `quotient_add_group.mk' S`. -/
@[simp]
lemma normed_mk.apply (S : add_subgroup M) (m : M) : normed_mk S m = quotient_add_group.mk' S m :=
rfl

/-- `S.normed_mk` is surjective. -/
lemma surjective_normed_mk (S : add_subgroup M) : function.surjective (normed_mk S) :=
surjective_quot_mk _

/-- The kernel of `S.normed_mk` is `S`. -/
lemma ker_normed_mk (S : add_subgroup M) : S.normed_mk.ker = S :=
quotient_add_group.ker_mk  _

/-- The operator norm of the projection is at most `1`. -/
lemma norm_normed_mk_le (S : add_subgroup M) : ∥S.normed_mk∥ ≤ 1 :=
normed_group_hom.op_norm_le_bound _ zero_le_one (λ m, by simp [quotient_norm_mk_le])

/-- The operator norm of the projection is `1` if the subspace is not dense. -/
lemma norm_normed_mk (S : add_subgroup M) (h : (S.topological_closure : set M) ≠ univ) :
  ∥S.normed_mk∥ = 1 :=
begin
  obtain ⟨x, hx⟩ := set.nonempty_compl.2 h,
  let y := S.normed_mk x,
  have hy : ∥y∥ ≠ 0,
  { intro h0,
    exact set.not_mem_of_mem_compl hx ((quotient_norm_eq_zero_iff S x).1 h0) },
  refine le_antisymm (norm_normed_mk_le S) (le_of_forall_pos_le_add (λ ε hε, _)),
  suffices : 1 ≤ ∥S.normed_mk∥ + min ε ((1 : ℝ)/2),
  { exact le_add_of_le_add_left this (min_le_left ε ((1 : ℝ)/2)) },
  have hδ := sub_pos.mpr (lt_of_le_of_lt (min_le_right ε ((1 : ℝ)/2)) one_half_lt_one),
  have hδpos : 0 < min ε ((1 : ℝ)/2) := lt_min hε one_half_pos,
  have hδnorm := mul_pos (div_pos hδpos hδ) (lt_of_le_of_ne (norm_nonneg y) hy.symm),
  obtain ⟨m, hm, hlt⟩ := norm_mk_lt y hδnorm,
  have hrw : ∥y∥ + min ε (1 / 2) / (1 - min ε (1 / 2)) * ∥y∥ =
    ∥y∥ * (1 + min ε (1 / 2) / (1 - min ε (1 / 2))) := by ring,
  rw [hrw] at hlt,
  have hm0 : ∥m∥ ≠ 0,
  { intro h0,
    have hnorm := quotient_norm_mk_le S m,
    rw [h0, hm] at hnorm,
    replace hnorm := le_antisymm hnorm (norm_nonneg _),
    simpa [hnorm] using hy },
  replace hlt := (div_lt_div_right (lt_of_le_of_ne (norm_nonneg m) hm0.symm)).2 hlt,
  simp only [hm0, div_self, ne.def, not_false_iff] at hlt,
  have hrw₁ : ∥y∥ * (1 + min ε (1 / 2) / (1 - min ε (1 / 2))) / ∥m∥ =
    (∥y∥ / ∥m∥) * (1 + min ε (1 / 2) / (1 - min ε (1 / 2))) := by ring,
  rw [hrw₁] at hlt,
  replace hlt := (inv_pos_lt_iff_one_lt_mul (lt_trans (div_pos hδpos hδ) (lt_one_add _))).2 hlt,
  suffices : ∥S.normed_mk∥ ≥ 1 - min ε (1 / 2),
  { exact sub_le_iff_le_add.mp this },
  calc ∥S.normed_mk∥ ≥ ∥(S.normed_mk) m∥ / ∥m∥ : ratio_le_op_norm S.normed_mk m
  ...  = ∥y∥ / ∥m∥ : by rw [normed_mk.apply, hm]
  ... ≥ (1 + min ε (1 / 2) / (1 - min ε (1 / 2)))⁻¹ : le_of_lt hlt
  ... = 1 - min ε (1 / 2) : by field_simp [(ne_of_lt hδ).symm]
end

/-- The operator norm of the projection is `0` if the subspace is dense. -/
lemma norm_trivial_quotient_mk (S : add_subgroup M)
  (h : (S.topological_closure : set M) = set.univ) : ∥S.normed_mk∥ = 0 :=
begin
  refine le_antisymm (op_norm_le_bound _ (le_refl _) (λ x, _)) (norm_nonneg _),
  have hker : x ∈ (S.normed_mk).ker.topological_closure,
  { rw [S.ker_normed_mk],
    exact set.mem_of_eq_of_mem h trivial },
  rw [ker_normed_mk] at hker,
  simp only [(quotient_norm_eq_zero_iff S x).mpr hker, normed_mk.apply, zero_mul],
end

end add_subgroup

namespace normed_group_hom

/-- `is_quotient f`, for `f : M ⟶ N` means that `N` is isomorphic to the quotient of `M`
by the kernel of `f`. -/
structure is_quotient (f : normed_group_hom M N) : Prop :=
(surjective : function.surjective f)
(norm : ∀ x, ∥f x∥ = Inf ((λ m, ∥x + m∥) '' f.ker))

/-- Given  `f : normed_group_hom M N` such that `f s = 0` for all `s ∈ S`, where,
`S : add_subgroup M` is closed, the induced morphism `normed_group_hom (quotient S) N`. -/
noncomputable
def lift {N : Type*} [semi_normed_group N] (S : add_subgroup M)
  (f : normed_group_hom M N) (hf : ∀ s ∈ S, f s = 0) :
  normed_group_hom (quotient S) N :=
{ bound' :=
  begin
    obtain ⟨c : ℝ, hcpos : (0 : ℝ) < c, hc : ∀ x, ∥f x∥ ≤ c * ∥x∥⟩ := f.bound,
    refine ⟨c, λ mbar, le_of_forall_pos_le_add (λ ε hε, _)⟩,
    obtain ⟨m : M, rfl : mk' S m = mbar, hmnorm : ∥m∥ < ∥mk' S m∥ + ε/c⟩ :=
      norm_mk_lt mbar (div_pos hε hcpos),
    calc ∥f m∥ ≤ c * ∥m∥ : hc m
    ... ≤ c*(∥mk' S m∥ + ε/c) : ((mul_lt_mul_left hcpos).mpr hmnorm).le
    ... = c * ∥mk' S m∥ + ε : by rw [mul_add, mul_div_cancel' _ hcpos.ne.symm]
  end,
  .. quotient_add_group.lift S f.to_add_monoid_hom hf }

lemma lift_mk {N : Type*} [semi_normed_group N] (S : add_subgroup M)
  (f : normed_group_hom M N) (hf : ∀ s ∈ S, f s = 0) (m : M) :
  lift S f hf (S.normed_mk m) = f m := rfl

lemma lift_unique {N : Type*} [semi_normed_group N] (S : add_subgroup M)
  (f : normed_group_hom M N) (hf : ∀ s ∈ S, f s = 0)
  (g : normed_group_hom (quotient S) N) :
  g.comp (S.normed_mk) = f → g = lift S f hf :=
begin
  intro h,
  ext,
  rcases add_subgroup.surjective_normed_mk _ x with ⟨x,rfl⟩,
  change (g.comp (S.normed_mk) x) = _,
  simpa only [h]
end

/-- `S.normed_mk` satisfies `is_quotient`. -/
lemma is_quotient_quotient (S : add_subgroup M) : is_quotient (S.normed_mk) :=
⟨S.surjective_normed_mk, λ m, by simpa [S.ker_normed_mk] using quotient_norm_mk_eq _ m⟩

lemma is_quotient.norm_lift {f : normed_group_hom M N} (hquot : is_quotient f) {ε : ℝ} (hε : 0 < ε)
  (n : N) : ∃ (m : M), f m = n ∧ ∥m∥ < ∥n∥ + ε :=
begin
  obtain ⟨m, rfl⟩ := hquot.surjective n,
  have nonemp : ((λ m', ∥m + m'∥) '' f.ker).nonempty,
  { rw set.nonempty_image_iff,
    exact ⟨0, is_add_submonoid.zero_mem⟩ },
  have bdd : bdd_below ((λ m', ∥m + m'∥) '' f.ker),
  { use 0,
    rintro _ ⟨x, hx, rfl⟩,
    apply norm_nonneg },
  rcases real.lt_Inf_add_pos bdd nonemp hε with
    ⟨_, ⟨⟨x, hx, rfl⟩, H : ∥m + x∥ < Inf ((λ (m' : M), ∥m + m'∥) '' f.ker) + ε⟩⟩,
  exact ⟨m+x, by rw [f.map_add,(normed_group_hom.mem_ker f x).mp hx, add_zero],
               by rwa hquot.norm⟩,
end

lemma is_quotient.norm_le {f : normed_group_hom M N} (hquot : is_quotient f) (m : M) :
  ∥f m∥ ≤ ∥m∥ :=
begin
  rw hquot.norm,
  apply real.Inf_le,
  { use 0,
    rintros _ ⟨m', hm', rfl⟩,
    apply norm_nonneg },
  { exact ⟨0, f.ker.zero_mem, by simp⟩ }
end

lemma lift_bound_by {N : Type*} [semi_normed_group N] (S : add_subgroup M)
  (f : normed_group_hom M N) (hf : ∀ s ∈ S, f s = 0)
  {c : ℝ≥0} (fb : f.bound_by c) :
  (lift S f hf).bound_by c :=
begin
  intros x,
  by_cases hc : c = 0,
  { simp only [hc, nnreal.coe_zero, zero_mul] at fb ⊢,
    obtain ⟨x, rfl⟩ := surjective_quot_mk _ x,
    show ∥f x∥ ≤ 0,
    calc ∥f x∥ ≤ 0 * ∥x∥ : fb x
          ... = 0 : zero_mul _ },
  { replace hc : 0 < c := pos_iff_ne_zero.mpr hc,
    apply le_of_forall_pos_le_add,
    intros ε hε,
    have aux : 0 < (ε / c) := div_pos hε hc,
    obtain ⟨x, rfl, Hx⟩ : ∃ x', S.normed_mk x' = x ∧ ∥x'∥ < ∥x∥ + (ε / c) :=
      (is_quotient_quotient _).norm_lift aux _,
    rw lift_mk,
    calc ∥f x∥ ≤ c * ∥x∥ : fb x
          ... ≤ c * (∥S.normed_mk x∥ + ε / c) : (mul_le_mul_left _).mpr Hx.le
          ... = c * _ + ε : _,
    { exact_mod_cast hc },
    { rw [mul_add, mul_div_cancel'], exact_mod_cast hc.ne' } },
end

lemma lift_norm_noninc {N : Type*} [semi_normed_group N] (S : add_subgroup M)
  (f : normed_group_hom M N) (hf : ∀ s ∈ S, f s = 0)
  (fb : f.norm_noninc) :
  (lift S f hf).norm_noninc :=
λ x, by simpa only [one_mul, nnreal.coe_one] using lift_bound_by _ _ _ fb.bound_by_one x

end normed_group_hom
