/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.specific_functions
import geometry.manifold.diffeomorph
import geometry.manifold.instances.real

/-!
# Smooth bump functions on a smooth manifold

In this file we define `smooth_bump_function I c` to be a bundled smooth "bump" function centered at
`c`. It is a structure that consists of two real numbers `0 < r < R` with small enough `R`. We
define a coercion to function for this type, and for `f : smooth_bump_function I c`, the function
`⇑f` written in the extended chart at `c` has the following properties:

* `f x = 1` in the closed euclidean ball of radius `f.r` centered at `c`;
* `f x = 0` outside of the euclidean ball of radius `f.R` centered at `c`;
* `0 ≤ f x ≤ 1` for all `x`.

The actual statements involve (pre)images under `ext_chart_at I f` and are given as lemmas in the
`smooth_bump_function` namespace.

## Tags

manifold, smooth bump function
-/

universes uι uE uH uM
variables {ι : Type uι}
{E : Type uE} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{H : Type uH} [topological_space H] (I : model_with_corners ℝ E H)
{M : Type uM} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

open function filter finite_dimensional set
open_locale topological_space manifold classical filter big_operators

noncomputable theory

/-!
### Smooth bump function

In this section we define a structure for a bundled smooth bump function and prove its properties.
-/

/-- Given a smooth manifold modelled on a finite dimensional space `E`,
`f : smooth_bump_function I M` is a smooth function on `M` such that in the extended chart `e` at
`f.c`:

* `f x = 1` in the closed euclidean ball of radius `f.r` centered at `f.c`;
* `f x = 0` outside of the euclidean ball of radius `f.R` centered at `f.c`;
* `0 ≤ f x ≤ 1` for all `x`.

The structure contains data required to construct a function with these properties. The function is
available as `⇑f` or `f x`. Formal statements of the properties listed above involve some
(pre)images under `ext_chart_at I f.c` and are given as lemmas in the `smooth_bump_function`
namespace. -/
structure smooth_bump_function (c : M) extends times_cont_diff_bump (ext_chart_at I c c) :=
(closed_ball_subset :
  (euclidean.closed_ball (ext_chart_at I c c) R) ∩ range I ⊆ (ext_chart_at I c).target)

variable {M}

namespace smooth_bump_function

open euclidean (renaming dist -> eudist)

variables {c : M} (f : smooth_bump_function I c) {x : M} {I}

/-- The function defined by `f : smooth_bump_function c`. Use automatic coercion to function
instead. -/
def to_fun : M → ℝ :=
indicator (chart_at H c).source (f.to_times_cont_diff_bump ∘ ext_chart_at I c)

instance : has_coe_to_fun (smooth_bump_function I c) := ⟨_, to_fun⟩

lemma coe_def :
  ⇑f = indicator (chart_at H c).source (f.to_times_cont_diff_bump ∘ ext_chart_at I c) :=
rfl

lemma R_pos : 0 < f.R := f.to_times_cont_diff_bump.R_pos

lemma ball_subset :
  ball (ext_chart_at I c c) f.R ∩ range I ⊆ (ext_chart_at I c).target :=
subset.trans (inter_subset_inter_left _ ball_subset_closed_ball) f.closed_ball_subset

lemma eq_on_source :
  eq_on f (f.to_times_cont_diff_bump ∘ ext_chart_at I c) (chart_at H c).source :=
eq_on_indicator

lemma eventually_eq_of_mem_source (hx : x ∈ (chart_at H c).source) :
  f =ᶠ[𝓝 x] f.to_times_cont_diff_bump ∘ ext_chart_at I c :=
f.eq_on_source.eventually_eq_of_mem $ is_open.mem_nhds (chart_at H c).open_source hx

lemma one_of_dist_le (hs : x ∈ (chart_at H c).source)
  (hd : eudist (ext_chart_at I c x) (ext_chart_at I c c) ≤ f.r) :
  f x = 1 :=
by simp only [f.eq_on_source hs, (∘), f.to_times_cont_diff_bump.one_of_mem_closed_ball hd]

lemma support_eq_inter_preimage :
  support f =
    (chart_at H c).source ∩ (ext_chart_at I c ⁻¹' ball (ext_chart_at I c c) f.R) :=
by rw [coe_def, support_indicator, (∘), support_comp_eq_preimage, ← ext_chart_at_source I,
  ← (ext_chart_at I c).symm_image_target_inter_eq',
  ← (ext_chart_at I c).symm_image_target_inter_eq', f.to_times_cont_diff_bump.support_eq]

lemma open_support : is_open (support f) :=
by { rw support_eq_inter_preimage, exact ext_chart_preimage_open_of_open I c is_open_ball }

lemma support_eq_symm_image :
  support f = (ext_chart_at I c).symm '' (ball (ext_chart_at I c c) f.R ∩ range I) :=
begin
  rw [f.support_eq_inter_preimage, ← ext_chart_at_source I,
    ← (ext_chart_at I c).symm_image_target_inter_eq', inter_comm],
  congr' 1 with y,
  exact and.congr_right_iff.2
    (λ hy, ⟨λ h, ext_chart_at_target_subset_range _ _ h, λ h, f.ball_subset ⟨hy, h⟩⟩)
end

lemma support_subset_source : support f ⊆ (chart_at H c).source :=
by { rw [f.support_eq_inter_preimage, ← ext_chart_at_source I], exact inter_subset_left _ _ }

lemma image_eq_inter_preimage_of_subset_support {s : set M} (hs : s ⊆ support f) :
  ext_chart_at I c '' s =
    closed_ball (ext_chart_at I c c) f.R ∩ range I ∩ (ext_chart_at I c).symm ⁻¹' s :=
begin
  rw [support_eq_inter_preimage, subset_inter_iff, ← ext_chart_at_source I,
    ← image_subset_iff] at hs,
  cases hs with hse hsf,
  apply subset.antisymm,
  { refine subset_inter (subset_inter (subset.trans hsf ball_subset_closed_ball) _) _,
    { rintro _ ⟨x, -, rfl⟩, exact mem_range_self _ },
    { rw [(ext_chart_at I c).image_eq_target_inter_inv_preimage hse],
      exact inter_subset_right _ _ } },
  { refine subset.trans (inter_subset_inter_left _ f.closed_ball_subset) _,
    rw [(ext_chart_at I c).image_eq_target_inter_inv_preimage hse] }
end

lemma mem_Icc : f x ∈ Icc (0 : ℝ) 1 :=
begin
  have : f x = 0 ∨ f x = _, from indicator_eq_zero_or_self _ _ _,
  cases this; rw this,
  exacts [left_mem_Icc.2 zero_le_one,
    ⟨f.to_times_cont_diff_bump.nonneg, f.to_times_cont_diff_bump.le_one⟩]
end

lemma nonneg : 0 ≤ f x := f.mem_Icc.1

lemma le_one : f x ≤ 1 := f.mem_Icc.2

lemma eventually_eq_one_of_dist_lt (hs : x ∈ (chart_at H c).source)
  (hd : eudist (ext_chart_at I c x) (ext_chart_at I c c) < f.r) :
  f =ᶠ[𝓝 x] 1 :=
begin
  filter_upwards [is_open.mem_nhds (ext_chart_preimage_open_of_open I c is_open_ball) ⟨hs, hd⟩],
  rintro z ⟨hzs, hzd : _ < _⟩,
  exact f.one_of_dist_le hzs hzd.le
end

lemma eventually_eq_one : f =ᶠ[𝓝 c] 1 :=
f.eventually_eq_one_of_dist_lt (mem_chart_source _ _) $
by { rw [euclidean.dist, dist_self], exact f.r_pos }

@[simp] lemma eq_one : f c = 1 := f.eventually_eq_one.eq_of_nhds

lemma support_mem_nhds : support f ∈ 𝓝 c :=
f.eventually_eq_one.mono $ λ x hx, by { rw hx, exact one_ne_zero }

lemma closure_support_mem_nhds : closure (support f) ∈ 𝓝 c :=
mem_sets_of_superset f.support_mem_nhds subset_closure

lemma c_mem_support : c ∈ support f := mem_of_mem_nhds f.support_mem_nhds

lemma nonempty_support : (support f).nonempty := ⟨c, f.c_mem_support⟩

lemma compact_symm_image_closed_ball :
  is_compact ((ext_chart_at I c).symm '' (closed_ball (ext_chart_at I c c) f.R ∩ range I)) :=
(compact_ball.inter_right I.closed_range).image_of_continuous_on $
  (ext_chart_at_continuous_on_symm _ _).mono f.closed_ball_subset

/-- Given a smooth bump function `f : smooth_bump_function I c`, the closed ball of radius `f.R` is
known to include the support of `f`. These closed balls (in the model normed space `E`) intersected
with `set.range I` form a basis of `𝓝[range I] (ext_chart_at I c c)`. -/
lemma nhds_within_range_basis :
  (𝓝[range I] (ext_chart_at I c c)).has_basis (λ f : smooth_bump_function I c, true)
    (λ f, closed_ball (ext_chart_at I c c) f.R ∩ range I) :=
begin
  refine ((nhds_within_has_basis euclidean.nhds_basis_closed_ball _).restrict_subset
      (ext_chart_at_target_mem_nhds_within _ _)).to_has_basis' _ _,
  { rintro R ⟨hR0, hsub⟩,
    exact ⟨⟨⟨⟨R / 2, R, half_pos hR0, half_lt_self hR0⟩⟩, hsub⟩, trivial, subset.rfl⟩ },
  { exact λ f _, inter_mem_sets (mem_nhds_within_of_mem_nhds $ closed_ball_mem_nhds f.R_pos)
      self_mem_nhds_within }
end

lemma closed_image_of_closed {s : set M} (hsc : is_closed s) (hs : s ⊆ support f) :
  is_closed (ext_chart_at I c '' s) :=
begin
  rw f.image_eq_inter_preimage_of_subset_support hs,
  refine continuous_on.preimage_closed_of_closed
    ((ext_chart_continuous_on_symm _ _).mono f.closed_ball_subset) _ hsc,
  exact is_closed.inter is_closed_closed_ball I.closed_range
end

/-- If `f` is a smooth bump function and `s` closed subset of the support of `f` (i.e., of the open
ball of radius `f.R`), then there exists `0 < r < f.R` such that `s` is a subset of the open ball of
radius `r`. Formally, `s ⊆ e.source ∩ e ⁻¹' (ball (e c) r)`, where `e = ext_chart_at I c`. -/
lemma exists_r_pos_lt_subset_ball {s : set M} (hsc : is_closed s) (hs : s ⊆ support f) :
  ∃ r (hr : r ∈ Ioo 0 f.R), s ⊆
    (chart_at H c).source ∩ ext_chart_at I c ⁻¹' (ball (ext_chart_at I c c) r) :=
begin
  set e := ext_chart_at I c,
  have : is_closed (e '' s) := f.closed_image_of_closed hsc hs,
  rw [support_eq_inter_preimage, subset_inter_iff, ← image_subset_iff] at hs,
  rcases euclidean.exists_pos_lt_subset_ball f.R_pos this hs.2 with ⟨r, hrR, hr⟩,
  exact ⟨r, hrR, subset_inter hs.1 (image_subset_iff.1 hr)⟩
end

/-- Replace `r` with another value in the interval `(0, f.R)`. -/
def update_r (r : ℝ) (hr : r ∈ Ioo 0 f.R) : smooth_bump_function I c :=
⟨⟨⟨r, f.R, hr.1, hr.2⟩⟩, f.closed_ball_subset⟩

@[simp] lemma update_r_R {r : ℝ} (hr : r ∈ Ioo 0 f.R) : (f.update_r r hr).R = f.R := rfl

@[simp] lemma update_r_r {r : ℝ} (hr : r ∈ Ioo 0 f.R) : (f.update_r r hr).r = r := rfl

@[simp] lemma support_update_r {r : ℝ} (hr : r ∈ Ioo 0 f.R) :
  support (f.update_r r hr) = support f :=
by simp only [support_eq_inter_preimage, update_r_R]

instance : inhabited (smooth_bump_function I c) :=
classical.inhabited_of_nonempty nhds_within_range_basis.nonempty

variables [t2_space M]

lemma closed_symm_image_closed_ball :
  is_closed ((ext_chart_at I c).symm '' (closed_ball (ext_chart_at I c c) f.R ∩ range I)) :=
f.compact_symm_image_closed_ball.is_closed

lemma closure_support_subset_symm_image_closed_ball :
  closure (support f) ⊆
    (ext_chart_at I c).symm '' (closed_ball (ext_chart_at I c c) f.R ∩ range I) :=
begin
  rw support_eq_symm_image,
  exact closure_minimal (image_subset _ $ inter_subset_inter_left _ ball_subset_closed_ball)
    f.closed_symm_image_closed_ball
end

lemma closure_support_subset_ext_chart_at_source :
  closure (support f) ⊆ (ext_chart_at I c).source :=
calc closure (support f)
    ⊆ (ext_chart_at I c).symm '' (closed_ball (ext_chart_at I c c) f.R ∩ range I) :
  f.closure_support_subset_symm_image_closed_ball
... ⊆ (ext_chart_at I c).symm '' (ext_chart_at I c).target :
  image_subset _ f.closed_ball_subset
... = (ext_chart_at I c).source :
  (ext_chart_at I c).symm_image_target_eq_source

lemma closure_support_subset_chart_at_source :
  closure (support f) ⊆ (chart_at H c).source :=
by simpa only [ext_chart_at_source] using f.closure_support_subset_ext_chart_at_source

lemma compact_closure_support : is_compact (closure $ support f) :=
compact_of_is_closed_subset f.compact_symm_image_closed_ball is_closed_closure
 f.closure_support_subset_symm_image_closed_ball

variables (I c)

/-- The closures of supports of smooth bump functions centered at `c` form a basis of `𝓝 c`.
In other words, each of these closures is a neighborhood of `c` and each neighborhood of `c`
includes `closure (support f)` for some `f : smooth_bump_function I c`. -/
lemma nhds_basis_closure_support :
  (𝓝 c).has_basis (λ f : smooth_bump_function I c, true) (λ f, closure $ support f) :=
begin
  have : (𝓝 c).has_basis (λ f : smooth_bump_function I c, true)
    (λ f, (ext_chart_at I c).symm '' (closed_ball (ext_chart_at I c c) f.R ∩ range I)),
  { rw [← ext_chart_at_symm_map_nhds_within_range I c],
    exact nhds_within_range_basis.map _ },
  refine this.to_has_basis' (λ f hf, ⟨f, trivial, f.closure_support_subset_symm_image_closed_ball⟩)
    (λ f _, f.closure_support_mem_nhds),
end

variable {c}

/-- Given `s ∈ 𝓝 c`, the supports of smooth bump functions `f : smooth_bump_function I c` such that
`closure (support f) ⊆ s` form a basis of `𝓝 c`.  In other words, each of these supports is a
neighborhood of `c` and each neighborhood of `c` includes `support f` for some `f :
smooth_bump_function I c` such that `closure (support f) ⊆ s`. -/
lemma nhds_basis_support {s : set M} (hs : s ∈ 𝓝 c) :
  (𝓝 c).has_basis (λ f : smooth_bump_function I c, closure (support f) ⊆ s) (λ f, support f) :=
((nhds_basis_closure_support I c).restrict_subset hs).to_has_basis'
  (λ f hf, ⟨f, hf.2, subset_closure⟩) (λ f hf, f.support_mem_nhds)

variables [smooth_manifold_with_corners I M] {I}

/-- A smooth bump function is infinitely smooth. -/
protected lemma smooth : smooth I 𝓘(ℝ) f :=
begin
  refine times_cont_mdiff_of_support (λ x hx, _),
  have : x ∈ (chart_at H c).source := f.closure_support_subset_chart_at_source hx,
  refine times_cont_mdiff_at.congr_of_eventually_eq _
    (f.eq_on_source.eventually_eq_of_mem $ is_open.mem_nhds (chart_at _ _).open_source this),
  exact f.to_times_cont_diff_bump.times_cont_diff_at.times_cont_mdiff_at.comp _
    (times_cont_mdiff_at_ext_chart_at' this)
end

protected lemma smooth_at {x} : smooth_at I 𝓘(ℝ) f x := f.smooth.smooth_at

protected lemma continuous : continuous f := f.smooth.continuous

/-- If `f : smooth_bump_function I c` is a smooth bump function and `g : M → G` is a function smooth
on the source of the chart at `c`, then `f • g` is smooth on the whole manifold. -/
lemma smooth_smul {G} [normed_group G] [normed_space ℝ G]
  {g : M → G} (hg : smooth_on I 𝓘(ℝ, G) g (chart_at H c).source) :
  smooth I 𝓘(ℝ, G) (λ x, f x • g x) :=
begin
  apply times_cont_mdiff_of_support (λ x hx, _),
  have : x ∈ (chart_at H c).source,
  calc x ∈ closure (support (λ x, f x • g x)) : hx
     ... ⊆ closure (support f) : closure_mono (support_smul_subset_left _ _)
     ... ⊆ (chart_at _ c).source : f.closure_support_subset_chart_at_source,
  exact f.smooth_at.smul ((hg _ this).times_cont_mdiff_at $
    is_open.mem_nhds (chart_at _ _).open_source this)
end

end smooth_bump_function
