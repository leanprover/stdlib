/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.convex.basic
import analysis.normed_space.bounded_linear_maps
import analysis.specific_limits

/-!
# Tangent cone

In this file, we define two predicates `unique_diff_within_at 𝕜 s x` and `unique_diff_on 𝕜 s`
ensuring that, if a function has two derivatives, then they have to coincide. As a direct
definition of this fact (quantifying on all target types and all functions) would depend on
universes, we use a more intrinsic definition: if all the possible tangent directions to the set
`s` at the point `x` span a dense subset of the whole subset, it is easy to check that the
derivative has to be unique.

Therefore, we introduce the set of all tangent directions, named `tangent_cone_at`,
and express `unique_diff_within_at` and `unique_diff_on` in terms of it.
One should however think of this definition as an implementation detail: the only reason to
introduce the predicates `unique_diff_within_at` and `unique_diff_on` is to ensure the uniqueness
of the derivative. This is why their names reflect their uses, and not how they are defined.

## Implementation details

Note that this file is imported by `fderiv.lean`. Hence, derivatives are not defined yet. The
property of uniqueness of the derivative is therefore proved in `fderiv.lean`, but based on the
properties of the tangent cone we prove here.
-/

variables (𝕜 : Type*) [nondiscrete_normed_field 𝕜]

open filter set
open_locale topological_space

section tangent_cone

variables {E : Type*} [add_comm_monoid E] [module 𝕜 E] [topological_space E]

/-- The set of all tangent directions to the set `s` at the point `x`. -/
def tangent_cone_at (s : set E) (x : E) : set E :=
{y : E | ∃(c : ℕ → 𝕜) (d : ℕ → E), (∀ᶠ n in at_top, x + d n ∈ s) ∧
  (tendsto (λn, ∥c n∥) at_top at_top) ∧ (tendsto (λn, c n • d n) at_top (𝓝 y))}

/-- A property ensuring that the tangent cone to `s` at `x` spans a dense subset of the whole space.
The main role of this property is to ensure that the differential within `s` at `x` is unique,
hence this name. The uniqueness it asserts is proved in `unique_diff_within_at.eq` in `fderiv.lean`.
To avoid pathologies in dimension 0, we also require that `x` belongs to the closure of `s` (which
is automatic when `E` is not `0`-dimensional).
 -/
@[mk_iff] structure unique_diff_within_at (s : set E) (x : E) : Prop :=
(dense_tangent_cone : dense ((submodule.span 𝕜 (tangent_cone_at 𝕜 s x)) : set E))
(mem_closure : x ∈ closure s)

/-- A property ensuring that the tangent cone to `s` at any of its points spans a dense subset of
the whole space.  The main role of this property is to ensure that the differential along `s` is
unique, hence this name. The uniqueness it asserts is proved in `unique_diff_on.eq` in
`fderiv.lean`. -/
def unique_diff_on (s : set E) : Prop :=
∀x ∈ s, unique_diff_within_at 𝕜 s x

end tangent_cone

variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [normed_space ℝ G]
variables {𝕜} {x y : E} {s t : set E}

section tangent_cone
/- This section is devoted to the properties of the tangent cone. -/

open normed_field

lemma tangent_cone_univ : tangent_cone_at 𝕜 univ x = univ :=
begin
  refine univ_subset_iff.1 (λy hy, _),
  rcases exists_one_lt_norm 𝕜 with ⟨w, hw⟩,
  refine ⟨λn, w^n, λn, (w^n)⁻¹ • y, univ_mem_sets' (λn, mem_univ _),  _, _⟩,
  { simp only [norm_pow],
    exact tendsto_pow_at_top_at_top_of_one_lt hw },
  { convert tendsto_const_nhds,
    ext n,
    have : w ^ n * (w ^ n)⁻¹ = 1,
    { apply mul_inv_cancel,
      apply pow_ne_zero,
      simpa [norm_eq_zero] using (ne_of_lt (lt_trans zero_lt_one hw)).symm },
    rw [smul_smul, this, one_smul] }
end

lemma tangent_cone_mono (h : s ⊆ t) :
  tangent_cone_at 𝕜 s x ⊆ tangent_cone_at 𝕜 t x :=
begin
  rintros y ⟨c, d, ds, ctop, clim⟩,
  exact ⟨c, d, mem_sets_of_superset ds (λn hn, h hn), ctop, clim⟩
end

/-- Auxiliary lemma ensuring that, under the assumptions defining the tangent cone,
the sequence `d` tends to 0 at infinity. -/
lemma tangent_cone_at.lim_zero {α : Type*} (l : filter α) {c : α → 𝕜} {d : α → E}
  (hc : tendsto (λn, ∥c n∥) l at_top) (hd : tendsto (λn, c n • d n) l (𝓝 y)) :
  tendsto d l (𝓝 0) :=
begin
  have A : tendsto (λn, ∥c n∥⁻¹) l (𝓝 0) := tendsto_inv_at_top_zero.comp hc,
  have B : tendsto (λn, ∥c n • d n∥) l (𝓝 ∥y∥) :=
    (continuous_norm.tendsto _).comp hd,
  have C : tendsto (λn, ∥c n∥⁻¹ * ∥c n • d n∥) l (𝓝 (0 * ∥y∥)) := A.mul B,
  rw zero_mul at C,
  have : ∀ᶠ n in l, ∥c n∥⁻¹ * ∥c n • d n∥ = ∥d n∥,
  { apply (eventually_ne_of_tendsto_norm_at_top hc 0).mono (λn hn, _),
    rw [norm_smul, ← mul_assoc, inv_mul_cancel, one_mul],
    rwa [ne.def, norm_eq_zero] },
  have D : tendsto (λ n, ∥d n∥) l (𝓝 0) :=
    tendsto.congr' this C,
  rw tendsto_zero_iff_norm_tendsto_zero,
  exact D
end

lemma tangent_cone_mono_nhds (h : 𝓝[s] x ≤ 𝓝[t] x) :
  tangent_cone_at 𝕜 s x ⊆ tangent_cone_at 𝕜 t x :=
begin
  rintros y ⟨c, d, ds, ctop, clim⟩,
  refine ⟨c, d, _, ctop, clim⟩,
  suffices : tendsto (λ n, x + d n) at_top (𝓝[t] x),
    from tendsto_principal.1 (tendsto_inf.1 this).2,
  refine (tendsto_inf.2 ⟨_, tendsto_principal.2 ds⟩).mono_right h,
  simpa only [add_zero] using tendsto_const_nhds.add (tangent_cone_at.lim_zero at_top ctop clim)
end

/-- Tangent cone of `s` at `x` depends only on `𝓝[s] x`. -/
lemma tangent_cone_congr (h : 𝓝[s] x = 𝓝[t] x) :
  tangent_cone_at 𝕜 s x = tangent_cone_at 𝕜 t x :=
subset.antisymm
  (tangent_cone_mono_nhds $ le_of_eq h)
  (tangent_cone_mono_nhds $ le_of_eq h.symm)

/-- Intersecting with a neighborhood of the point does not change the tangent cone. -/
lemma tangent_cone_inter_nhds (ht : t ∈ 𝓝 x) :
  tangent_cone_at 𝕜 (s ∩ t) x = tangent_cone_at 𝕜 s x :=
tangent_cone_congr (nhds_within_restrict' _ ht).symm

/-- The tangent cone of a product contains the tangent cone of its left factor. -/
lemma subset_tangent_cone_prod_left {t : set F} {y : F} (ht : y ∈ closure t) :
  linear_map.inl 𝕜 E F '' (tangent_cone_at 𝕜 s x) ⊆ tangent_cone_at 𝕜 (set.prod s t) (x, y) :=
begin
  rintros _ ⟨v, ⟨c, d, hd, hc, hy⟩, rfl⟩,
  have : ∀n, ∃d', y + d' ∈ t ∧ ∥c n • d'∥ < ((1:ℝ)/2)^n,
  { assume n,
    rcases mem_closure_iff_nhds.1 ht _ (eventually_nhds_norm_smul_sub_lt (c n) y
      (pow_pos one_half_pos n)) with ⟨z, hz, hzt⟩,
    exact ⟨z - y, by simpa using hzt, by simpa using hz⟩ },
  choose d' hd' using this,
  refine ⟨c, λn, (d n, d' n), _, hc, _⟩,
  show ∀ᶠ n in at_top, (x, y) + (d n, d' n) ∈ set.prod s t,
  { filter_upwards [hd],
    assume n hn,
    simp [hn, (hd' n).1] },
  { apply tendsto.prod_mk_nhds hy _,
    refine squeeze_zero_norm (λn, (hd' n).2.le) _,
    exact tendsto_pow_at_top_nhds_0_of_lt_1 one_half_pos.le one_half_lt_one }
end

/-- The tangent cone of a product contains the tangent cone of its right factor. -/
lemma subset_tangent_cone_prod_right {t : set F} {y : F}
  (hs : x ∈ closure s) :
  linear_map.inr 𝕜 E F '' (tangent_cone_at 𝕜 t y) ⊆ tangent_cone_at 𝕜 (set.prod s t) (x, y) :=
begin
  rintros _ ⟨w, ⟨c, d, hd, hc, hy⟩, rfl⟩,
  have : ∀n, ∃d', x + d' ∈ s ∧ ∥c n • d'∥ < ((1:ℝ)/2)^n,
  { assume n,
    rcases mem_closure_iff_nhds.1 hs _ (eventually_nhds_norm_smul_sub_lt (c n) x
      (pow_pos one_half_pos n)) with ⟨z, hz, hzs⟩,
    exact ⟨z - x, by simpa using hzs, by simpa using hz⟩ },
  choose d' hd' using this,
  refine ⟨c, λn, (d' n, d n), _, hc, _⟩,
  show ∀ᶠ n in at_top, (x, y) + (d' n, d n) ∈ set.prod s t,
  { filter_upwards [hd],
    assume n hn,
    simp [hn, (hd' n).1] },
  { apply tendsto.prod_mk_nhds _ hy,
    refine squeeze_zero_norm (λn, (hd' n).2.le) _,
    exact tendsto_pow_at_top_nhds_0_of_lt_1 one_half_pos.le one_half_lt_one }
end

/-- The tangent cone of a product contains the tangent cone of each factor. -/
lemma maps_to_tangent_cone_pi {ι : Type*} [decidable_eq ι] {E : ι → Type*}
  [Π i, normed_group (E i)] [Π i, normed_space 𝕜 (E i)]
  {s : Π i, set (E i)} {x : Π i, E i} {i : ι} (hi : ∀ j ≠ i, x j ∈ closure (s j)) :
  maps_to (linear_map.single i : E i →ₗ[𝕜] Π j, E j) (tangent_cone_at 𝕜 (s i) (x i))
    (tangent_cone_at 𝕜 (set.pi univ s) x) :=
begin
  rintros w ⟨c, d, hd, hc, hy⟩,
  have : ∀ n (j ≠ i), ∃ d', x j + d' ∈ s j ∧ ∥c n • d'∥ < (1 / 2 : ℝ) ^ n,
  { assume n j hj,
    rcases mem_closure_iff_nhds.1 (hi j hj) _ (eventually_nhds_norm_smul_sub_lt (c n) (x j)
      (pow_pos one_half_pos n)) with ⟨z, hz, hzs⟩,
    exact ⟨z - x j, by simpa using hzs, by simpa using hz⟩ },
  choose! d' hd's hcd',
  refine ⟨c, λ n, function.update (d' n) i (d n), hd.mono (λ n hn j hj', _), hc,
    tendsto_pi.2 $ λ j, _⟩,
  { rcases em (j = i) with rfl|hj; simp * },
  { rcases em (j = i) with rfl|hj,
    { simp [hy] },
    { suffices : tendsto (λ n, c n • d' n j) at_top (𝓝 0), by simpa [hj],
      refine squeeze_zero_norm (λ n, (hcd' n j hj).le) _,
      exact tendsto_pow_at_top_nhds_0_of_lt_1 one_half_pos.le one_half_lt_one } }
end

/-- If a subset of a real vector space contains a segment, then the direction of this
segment belongs to the tangent cone at its endpoints. -/
lemma mem_tangent_cone_of_segment_subset {s : set G} {x y : G} (h : segment x y ⊆ s) :
  y - x ∈ tangent_cone_at ℝ s x :=
begin
  let c := λn:ℕ, (2:ℝ)^n,
  let d := λn:ℕ, (c n)⁻¹ • (y-x),
  refine ⟨c, d, filter.univ_mem_sets' (λn, h _), _, _⟩,
  show x + d n ∈ segment x y,
  { rw segment_eq_image,
    refine ⟨(c n)⁻¹, ⟨_, _⟩, _⟩,
    { rw inv_nonneg, apply pow_nonneg, norm_num },
    { apply inv_le_one, apply one_le_pow_of_one_le, norm_num },
    { simp only [d, sub_smul, smul_sub, one_smul], abel } },
  show filter.tendsto (λ (n : ℕ), ∥c n∥) filter.at_top filter.at_top,
  { have : (λ (n : ℕ), ∥c n∥) = c,
      by { ext n, exact abs_of_nonneg (pow_nonneg (by norm_num) _) },
    rw this,
    exact tendsto_pow_at_top_at_top_of_one_lt (by norm_num) },
  show filter.tendsto (λ (n : ℕ), c n • d n) filter.at_top (𝓝 (y - x)),
  { have : (λ (n : ℕ), c n • d n) = (λn, y - x),
    { ext n,
      simp only [d, smul_smul],
      rw [mul_inv_cancel, one_smul],
      exact pow_ne_zero _ (by norm_num) },
    rw this,
    apply tendsto_const_nhds }
end

end tangent_cone

section unique_diff
/-!
### Properties of `unique_diff_within_at` and `unique_diff_on`

This section is devoted to properties of the predicates
`unique_diff_within_at` and `unique_diff_on`. -/

lemma unique_diff_on.unique_diff_within_at {s : set E} {x} (hs : unique_diff_on 𝕜 s) (h : x ∈ s) :
  unique_diff_within_at 𝕜 s x :=
hs x h

lemma unique_diff_within_at_univ : unique_diff_within_at 𝕜 univ x :=
by { rw [unique_diff_within_at_iff, tangent_cone_univ], simp }

lemma unique_diff_on_univ : unique_diff_on 𝕜 (univ : set E) :=
λx hx, unique_diff_within_at_univ

lemma unique_diff_on_empty : unique_diff_on 𝕜 (∅ : set E) :=
λ x hx, hx.elim

lemma unique_diff_within_at.mono_nhds (h : unique_diff_within_at 𝕜 s x)
  (st : 𝓝[s] x ≤ 𝓝[t] x) :
  unique_diff_within_at 𝕜 t x :=
begin
  simp only [unique_diff_within_at_iff] at *,
  rw [mem_closure_iff_nhds_within_ne_bot] at h ⊢,
  exact ⟨h.1.mono $ submodule.span_mono $ tangent_cone_mono_nhds st,
    h.2.mono st⟩
end

lemma unique_diff_within_at.mono (h : unique_diff_within_at 𝕜 s x) (st : s ⊆ t) :
  unique_diff_within_at 𝕜 t x :=
h.mono_nhds $ nhds_within_mono _ st

lemma unique_diff_within_at_congr (st : 𝓝[s] x = 𝓝[t] x) :
  unique_diff_within_at 𝕜 s x ↔ unique_diff_within_at 𝕜 t x :=
⟨λ h, h.mono_nhds $ le_of_eq st, λ h, h.mono_nhds $ le_of_eq st.symm⟩

lemma unique_diff_within_at_inter (ht : t ∈ 𝓝 x) :
  unique_diff_within_at 𝕜 (s ∩ t) x ↔ unique_diff_within_at 𝕜 s x :=
unique_diff_within_at_congr $ (nhds_within_restrict' _ ht).symm

lemma unique_diff_within_at.inter (hs : unique_diff_within_at 𝕜 s x) (ht : t ∈ 𝓝 x) :
  unique_diff_within_at 𝕜 (s ∩ t) x :=
(unique_diff_within_at_inter ht).2 hs

lemma unique_diff_within_at_inter' (ht : t ∈ 𝓝[s] x) :
  unique_diff_within_at 𝕜 (s ∩ t) x ↔ unique_diff_within_at 𝕜 s x :=
unique_diff_within_at_congr $ (nhds_within_restrict'' _ ht).symm

lemma unique_diff_within_at.inter' (hs : unique_diff_within_at 𝕜 s x) (ht : t ∈ 𝓝[s] x) :
  unique_diff_within_at 𝕜 (s ∩ t) x :=
(unique_diff_within_at_inter' ht).2 hs

lemma unique_diff_within_at_of_mem_nhds (h : s ∈ 𝓝 x) : unique_diff_within_at 𝕜 s x :=
by simpa only [univ_inter] using unique_diff_within_at_univ.inter h

lemma is_open.unique_diff_within_at (hs : is_open s) (xs : x ∈ s) : unique_diff_within_at 𝕜 s x :=
unique_diff_within_at_of_mem_nhds (is_open.mem_nhds hs xs)

lemma unique_diff_on.inter (hs : unique_diff_on 𝕜 s) (ht : is_open t) : unique_diff_on 𝕜 (s ∩ t) :=
λx hx, (hs x hx.1).inter (is_open.mem_nhds ht hx.2)

lemma is_open.unique_diff_on (hs : is_open s) : unique_diff_on 𝕜 s :=
λx hx, is_open.unique_diff_within_at hs hx

/-- The product of two sets of unique differentiability at points `x` and `y` has unique
differentiability at `(x, y)`. -/
lemma unique_diff_within_at.prod {t : set F} {y : F}
  (hs : unique_diff_within_at 𝕜 s x) (ht : unique_diff_within_at 𝕜 t y) :
  unique_diff_within_at 𝕜 (set.prod s t) (x, y) :=
begin
  rw [unique_diff_within_at_iff] at ⊢ hs ht,
  rw [closure_prod_eq],
  refine ⟨_, hs.2, ht.2⟩,
  have : _ ≤ submodule.span 𝕜 (tangent_cone_at 𝕜 (s.prod t) (x, y)) :=
    submodule.span_mono (union_subset (subset_tangent_cone_prod_left ht.2)
      (subset_tangent_cone_prod_right hs.2)),
  rw [linear_map.span_inl_union_inr, set_like.le_def] at this,
  exact (hs.1.prod ht.1).mono this
end

lemma unique_diff_within_at.univ_pi (ι : Type*) [fintype ι] (E : ι → Type*)
  [Π i, normed_group (E i)] [Π i, normed_space 𝕜 (E i)]
  (s : Π i, set (E i)) (x : Π i, E i) (h : ∀ i, unique_diff_within_at 𝕜 (s i) (x i)) :
  unique_diff_within_at 𝕜 (set.pi univ s) x :=
begin
  classical,
  simp only [unique_diff_within_at_iff, closure_pi_set] at h ⊢,
  refine ⟨(dense_pi univ (λ i _, (h i).1)).mono _, λ i _, (h i).2⟩,
  norm_cast,
  simp only [← submodule.supr_map_single, supr_le_iff, linear_map.map_span, submodule.span_le,
    ← maps_to'],
  exact λ i, (maps_to_tangent_cone_pi $ λ j hj, (h j).2).mono subset.rfl submodule.subset_span
end

lemma unique_diff_within_at.pi (ι : Type*) [fintype ι] (E : ι → Type*)
  [Π i, normed_group (E i)] [Π i, normed_space 𝕜 (E i)]
  (s : Π i, set (E i)) (x : Π i, E i) (I : set ι)
  (h : ∀ i ∈ I, unique_diff_within_at 𝕜 (s i) (x i)) :
  unique_diff_within_at 𝕜 (set.pi I s) x :=
begin
  classical,
  rw [← set.univ_pi_piecewise],
  refine unique_diff_within_at.univ_pi _ _ _ _ (λ i, _),
  by_cases hi : i ∈ I; simp [*, unique_diff_within_at_univ],
end

/-- The product of two sets of unique differentiability is a set of unique differentiability. -/
lemma unique_diff_on.prod {t : set F} (hs : unique_diff_on 𝕜 s) (ht : unique_diff_on 𝕜 t) :
  unique_diff_on 𝕜 (set.prod s t) :=
λ ⟨x, y⟩ h, unique_diff_within_at.prod (hs x h.1) (ht y h.2)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
lemma unique_diff_on.pi (ι : Type*) [fintype ι] (E : ι → Type*)
  [Π i, normed_group (E i)] [Π i, normed_space 𝕜 (E i)]
  (s : Π i, set (E i)) (I : set ι) (h : ∀ i ∈ I, unique_diff_on 𝕜 (s i)) :
  unique_diff_on 𝕜 (set.pi I s) :=
λ x hx, unique_diff_within_at.pi _ _ _ _ _ $ λ i hi, h i hi (x i) (hx i hi)

/-- The finite product of a family of sets of unique differentiability is a set of unique
differentiability. -/
lemma unique_diff_on.univ_pi (ι : Type*) [fintype ι] (E : ι → Type*)
  [Π i, normed_group (E i)] [Π i, normed_space 𝕜 (E i)]
  (s : Π i, set (E i)) (h : ∀ i, unique_diff_on 𝕜 (s i)) :
  unique_diff_on 𝕜 (set.pi univ s) :=
unique_diff_on.pi _ _ _ _ $ λ i _, h i

/-- In a real vector space, a convex set with nonempty interior is a set of unique
differentiability. -/
theorem unique_diff_on_convex {s : set G} (conv : convex s) (hs : (interior s).nonempty) :
  unique_diff_on ℝ s :=
begin
  assume x xs,
  rcases hs with ⟨y, hy⟩,
  suffices : y - x ∈ interior (tangent_cone_at ℝ s x),
  { refine ⟨dense.of_closure _, subset_closure xs⟩,
    simp [(submodule.span ℝ (tangent_cone_at ℝ s x)).eq_top_of_nonempty_interior'
      ⟨y - x, interior_mono submodule.subset_span this⟩] },
  rw [mem_interior_iff_mem_nhds] at hy ⊢,
  apply mem_sets_of_superset ((is_open_map_sub_right x).image_mem_nhds hy),
  rintros _ ⟨z, zs, rfl⟩,
  exact mem_tangent_cone_of_segment_subset (conv.segment_subset xs zs)
end

lemma unique_diff_on_Ici (a : ℝ) : unique_diff_on ℝ (Ici a) :=
unique_diff_on_convex (convex_Ici a) $ by simp only [interior_Ici, nonempty_Ioi]

lemma unique_diff_on_Iic (a : ℝ) : unique_diff_on ℝ (Iic a) :=
unique_diff_on_convex (convex_Iic a) $ by simp only [interior_Iic, nonempty_Iio]

lemma unique_diff_on_Ioi (a : ℝ) : unique_diff_on ℝ (Ioi a) :=
is_open_Ioi.unique_diff_on

lemma unique_diff_on_Iio (a : ℝ) : unique_diff_on ℝ (Iio a) :=
is_open_Iio.unique_diff_on

lemma unique_diff_on_Icc {a b : ℝ} (hab : a < b) : unique_diff_on ℝ (Icc a b) :=
unique_diff_on_convex (convex_Icc a b) $ by simp only [interior_Icc, nonempty_Ioo, hab]

lemma unique_diff_on_Ico (a b : ℝ) : unique_diff_on ℝ (Ico a b) :=
if hab : a < b
then unique_diff_on_convex (convex_Ico a b) $ by simp only [interior_Ico, nonempty_Ioo, hab]
else by simp only [Ico_eq_empty hab, unique_diff_on_empty]

lemma unique_diff_on_Ioc (a b : ℝ) : unique_diff_on ℝ (Ioc a b) :=
if hab : a < b
then unique_diff_on_convex (convex_Ioc a b) $ by simp only [interior_Ioc, nonempty_Ioo, hab]
else by simp only [Ioc_eq_empty hab, unique_diff_on_empty]

lemma unique_diff_on_Ioo (a b : ℝ) : unique_diff_on ℝ (Ioo a b) :=
is_open_Ioo.unique_diff_on

/-- The real interval `[0, 1]` is a set of unique differentiability. -/
lemma unique_diff_on_Icc_zero_one : unique_diff_on ℝ (Icc (0:ℝ) 1) :=
unique_diff_on_Icc zero_lt_one

end unique_diff
