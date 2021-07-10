/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.specific_functions
import geometry.manifold.diffeomorph
import geometry.manifold.instances.real
import topology.partition_of_unity

/-!
# Smooth bump functions on a smooth manifold

In this file we define `smooth_bump_function I c` to be a bundled smooth "bump" function centered at
`c`. It is a structure that consists of two real numbers `0 < r < R` with small enough `R`. We
define a coercion to function for this type, and for `f : smooth_bump_function I c`, the function
`⇑f` written in the extended chart at `f.c` has the following properties:

* `f x = 1` in the closed euclidean ball of radius `f.r` centered at `f.c`;
* `f x = 0` outside of the euclidean ball of radius `f.R` centered at `f.c`;
* `0 ≤ f x ≤ 1` for all `x`.

The actual statements involve (pre)images under `ext_chart_at I f.c` and are given as lemmas in the
`smooth_bump_function` namespace.

We also define `smooth_bump_covering` of a set `s : set M` to be a collection of
`smooth_bump_function`s such that their supports is a locally finite family of sets, and for each
point `x ∈ s` there exists a bump function `f i` in the collection such that `f i =ᶠ[𝓝 x] 1`. This
structure is the main building block in the construction of a smooth partition of unity (see TODO),
and can be used instead of a partition of unity in some proofs.

We say that `f : smooth_bump_covering I M s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `closure (support (f i)) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.

We prove that on a smooth finitely dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering I M s`
subordinate to `U`. Then we use this fact to prove a version of the Whitney embedding theorem: any
compact real manifold can be embedded into `ℝ^n` for large enough `n`.

## TODO

* Prove the weak Whitney embedding theorem: any `σ`-compact smooth `m`-dimensional manifold can be
  embedded into `ℝ^(2m+1)`. This requires a version of Sard's theorem: for a locally Lipschitz
  continuous map `f : ℝ^m → ℝ^n`, `m < n`, the range has Hausdorff dimension at most `m`, hence it
  has measure zero.

* Deduce some corollaries from existence of a smooth partition of unity.

  - Prove that for any disjoint closed sets `s`, `t` there exists a smooth function `f` suth that
  `f` equals zero on `s` and `f` equals one on `t`.

  - Build a framework for to transfer local definitions to global using partition of unity and use
    it to define, e.g., the integral of a differential form over a manifold.

## Tags

manifold, smooth bump function, partition of unity, Whitney theorem
-/

universes uι uE uF uH uM
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
(pre)images under `ext_chart_at I f.c` and are given as lemmas in the `msmooth_bump_function`
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

/-!
### Covering by supports of smooth bump functions

In this section we define `smooth_bump_covering I M s` to be a collection of `smooth_bump_function`s
such that their supports is a locally finite family of sets and for each `x ∈ s` some function `f i`
from the collection is equal to `1` in a neighborhood of `x`. A covering of this type is useful to
construct a smooth partition of unity and can be used instead of a partition of unity in some
proofs.

We prove that on a smooth finite dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering I M s`
subordinate to `U`. Then we use this fact to prove a version of the Whitney embedding theorem: any
compact real manifold can be embedded into `ℝ^n` for large enough `n`.
-/

variables (ι M)

/-- We say that a collection of `smooth_bump_function`s is a `smooth_bump_covering` of a set `s` if

* `(f i).c ∈ s` for all `i`;
* the family `λ i, support (f i)` is locally finite;
* for each point `x ∈ s` there exists `i` such that `f i =ᶠ[𝓝 x] 1`;
  in other words, `x` belongs to the interior of `{y | f i y = 1}`;

If `M` is a finite dimensional real manifold which is a sigma-compact Hausdorff topological space,
then a choice of `smooth_bump_covering` is available as `smooth_bump_covering.choice_set`, see also
`smooth_bump_covering.choice` for the case `s = univ` and
`smooth_bump_covering.exists_is_subordinate` for a lemma providing a covering subordinate to a given
`U : M → set M`.

This covering can be used, e.g., to construct a partition of unity and to prove the weak
Whitney embedding theorem. -/
structure smooth_bump_covering (s : set M := univ) :=
(ι : Type uM)
(c : ι → M)
(to_fun : Π i, smooth_bump_function I (c i))
(c_mem' : ∀ i, c i ∈ s)
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(eventually_eq_one' : ∀ x ∈ s, ∃ i, to_fun i =ᶠ[𝓝 x] 1)

/-- We say that that a collection of functions form a smooth partition of unity on a set `s` if

* all functions are infinitely smooth and nonnegative;
* the family `λ i, support (f i)` is locally finite;
* for all `x ∈ s` the sum `∑ᶠ i, f i x` equals one;
* for all `x`, the sum `∑ᶠ i, f i x` is less than or equal to one. -/
structure smooth_partition_of_unity (s : set M := univ) :=
(to_fun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(nonneg' : ∀ i x, 0 ≤ to_fun i x)
(sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, to_fun i x = 1)
(sum_le_one' : ∀ x, ∑ᶠ i, to_fun i x ≤ 1)

variables {ι M I}

namespace smooth_partition_of_unity

variables {s : set M} (f : smooth_partition_of_unity ι I M s)

instance {s : set M} : has_coe_to_fun (smooth_partition_of_unity ι I M s) :=
⟨λ _, ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, smooth_partition_of_unity.to_fun⟩

protected lemma locally_finite : locally_finite (λ i, support (f i)) :=
f.locally_finite'

lemma nonneg (i : ι) (x : M) : 0 ≤ f i x := f.nonneg' i x

lemma sum_eq_one {x} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 := f.sum_eq_one' x hx

lemma sum_le_one (x : M) : ∑ᶠ i, f i x ≤ 1 := f.sum_le_one' x

/-- Reinterpret a smooth partition of unity as a continuous partition of unity. -/
def to_partition_of_unity : partition_of_unity ι M s :=
{ to_fun := λ i, f i, .. f }

lemma smooth_sum : smooth I 𝓘(ℝ) (λ x, ∑ᶠ i, f i x) :=
smooth_finsum (λ i, (f i).smooth) f.locally_finite

lemma le_one (i : ι) (x : M) : f i x ≤ 1 := f.to_partition_of_unity.le_one i x

lemma sum_nonneg (x : M) : 0 ≤ ∑ᶠ i, f i x := f.to_partition_of_unity.sum_nonneg x

/-- A smooth partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same
type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def is_subordinate (f : smooth_partition_of_unity ι I M s) (U : ι → set M) :=
∀ i, closure (support (f i)) ⊆ U i

@[simp] lemma is_subordinate_to_partition_of_unity {f : smooth_partition_of_unity ι I M s}
  {U : ι → set M} :
  f.to_partition_of_unity.is_subordinate U ↔ f.is_subordinate U :=
iff.rfl

alias is_subordinate_to_partition_of_unity ↔
  _ smooth_partition_of_unity.is_subordinate.to_partition_of_unity

end smooth_partition_of_unity

namespace bump_covering

variables {s : set M}

lemma smooth_to_partition_of_unity (f : bump_covering ι M s)
  (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) (i : ι) :
  smooth I 𝓘(ℝ) (f.to_partition_of_unity i) :=
(hf i).mul $ smooth_finprod_cond (λ j _, smooth_const.sub (hf j)) $
  by { simp only [mul_support_one_sub], exact f.locally_finite }

/-- A `bump_covering` such that all functions in this covering are smooth generates a smooth
partition of unity. -/
def to_smooth_partition_of_unity (f : bump_covering ι M s) (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) :
  smooth_partition_of_unity ι I M s :=
{ to_fun := λ i, ⟨f.to_partition_of_unity i,
    f.smooth_to_partition_of_unity hf i⟩,
  .. f.to_partition_of_unity }

@[simp] lemma to_smooth_partition_of_unity_to_partition_of_unity (f : bump_covering ι M s)
  (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) :
  (f.to_smooth_partition_of_unity hf).to_partition_of_unity = f.to_partition_of_unity :=
rfl

@[simp] lemma coe_to_smooth_partition_of_unity (f : bump_covering ι M s)
  (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) (i : ι) :
  ⇑(f.to_smooth_partition_of_unity hf i) = f.to_partition_of_unity i :=
rfl

lemma is_subordinate.to_smooth_partition_of_unity {f : bump_covering ι M s}
  {U : ι → set M} (h : f.is_subordinate U) (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) :
  (f.to_smooth_partition_of_unity hf).is_subordinate U :=
h.to_partition_of_unity

end bump_covering

namespace smooth_bump_covering

variables {s : set M} {U : M → set M} (fs : smooth_bump_covering I M s) {I}

instance : has_coe_to_fun (smooth_bump_covering I M s) := ⟨_, to_fun⟩

@[simp] lemma coe_mk (ι : Type uM) (c : ι → M) (to_fun : Π i, smooth_bump_function I (c i))
  (h₁ h₂ h₃) : ⇑(mk ι c to_fun h₁ h₂ h₃ : smooth_bump_covering I M s) = to_fun :=
rfl

/-- 
We say that `f : smooth_bump_covering I M s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `closure (support (f i)) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.
-/
def is_subordinate {s : set M} (f : smooth_bump_covering I M s) (U : M → set M) :=
∀ i, closure (support $ f i) ⊆ U (f.c i)

lemma is_subordinate.support_subset {fs : smooth_bump_covering I M s} {U : M → set M}
  (h : fs.is_subordinate U) (i : fs.ι) :
  support (fs i) ⊆ U (fs.c i) :=
subset.trans subset_closure (h i)

variable (I)

/-- Let `M` be a smooth manifold with corners modelled on a finite dimensional real vector space.
Suppose also that `M` is a Hausdorff `σ`-compact topological space. Let `s` be a closed set
in `M` and `U : M → set M` be a collection of sets such that `U x ∈ 𝓝 x` for every `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`. -/
lemma exists_is_subordinate [t2_space M] [sigma_compact_space M] (hs : is_closed s)
  (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
  ∃ f : smooth_bump_covering I M s, f.is_subordinate U :=
begin
  -- First we deduce some missing instances
  haveI : locally_compact_space H := I.locally_compact,
  haveI : locally_compact_space M := charted_space.locally_compact H,
  haveI : normal_space M := normal_of_paracompact_t2,
  -- Next we choose a covering by supports of smooth bump functions
  have hB := λ x hx, smooth_bump_function.nhds_basis_support I (hU x hx),
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis_set hs hB
    with ⟨ι, c, f, hf, hsub', hfin⟩, choose hcs hfU using hf,
  /- Then we use the shrinking lemma to get a covering by smaller open -/
  rcases exists_subset_Union_closed_subset hs (λ i, (f i).open_support)
    (λ x hx, hfin.point_finite x) hsub' with ⟨V, hsV, hVc, hVf⟩,
  choose r hrR hr using λ i, (f i).exists_r_pos_lt_subset_ball (hVc i) (hVf i),
  refine ⟨⟨ι, c, λ i, (f i).update_r (r i) (hrR i), hcs, _, λ x hx, _⟩, λ i, _⟩,
  { simpa only [smooth_bump_function.support_update_r] },
  { refine (mem_Union.1 $ hsV hx).imp (λ i hi, _),
    exact ((f i).update_r _ _).eventually_eq_one_of_dist_lt
      ((f i).support_subset_source $ hVf _ hi) (hr i hi).2 },
  { simpa only [coe_mk, smooth_bump_function.support_update_r] using hfU i }
end

/-- Choice of a covering of a closed set `s` by supports of smooth bump functions. -/
def choice_set [t2_space M] [sigma_compact_space M] (s : set M) (hs : is_closed s) :
  smooth_bump_covering I M s :=
(exists_is_subordinate I hs (λ x hx, univ_mem_sets)).some

instance [t2_space M] [sigma_compact_space M] {s : set M} [is_closed s] :
  inhabited (smooth_bump_covering I M s) :=
⟨choice_set I s ‹_›⟩

variable (M)

/-- Choice of a covering of a manifold by supports of smooth bump functions. -/
def choice [t2_space M] [sigma_compact_space M] :
  smooth_bump_covering I M :=
choice_set I univ is_closed_univ

variables {I M}

protected lemma locally_finite : locally_finite (λ i, support (fs i)) := fs.locally_finite'

protected lemma point_finite (x : M) : {i | fs i x ≠ 0}.finite :=
fs.locally_finite.point_finite x

lemma mem_chart_at_source_of_eq_one {i : fs.ι} {x : M} (h : fs i x = 1) :
  x ∈ (chart_at H (fs.c i)).source :=
(fs i).support_subset_source $ by simp [h]

lemma mem_ext_chart_at_source_of_eq_one {i : fs.ι} {x : M} (h : fs i x = 1) :
  x ∈ (ext_chart_at I (fs.c i)).source :=
by { rw ext_chart_at_source, exact fs.mem_chart_at_source_of_eq_one h }

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : M) (hx : x ∈ s) : fs.ι := (fs.eventually_eq_one' x hx).some

lemma eventually_eq_one (x : M) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
(fs.eventually_eq_one' x hx).some_spec

lemma apply_ind (x : M) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
(fs.eventually_eq_one x hx).eq_of_nhds

lemma mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (fs $ fs.ind x hx) :=
by simp [fs.apply_ind x hx]

lemma mem_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (chart_at H (fs.c (fs.ind x hx))).source :=
fs.mem_chart_at_source_of_eq_one (fs.apply_ind x hx)

lemma mem_ext_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (ext_chart_at I (fs.c (fs.ind x hx))).source :=
fs.mem_ext_chart_at_source_of_eq_one (fs.apply_ind x hx)

instance fintype_ι_of_compact [compact_space M] : fintype fs.ι :=
fs.locally_finite.fintype_of_compact $ λ i, (fs i).nonempty_support

variable [t2_space M]

/-- Reinterpret a `smooth_bump_covering` as a continuous `bump_covering`. -/
def to_bump_covering : bump_covering fs.ι M s :=
{ to_fun := λ i, ⟨fs i, (fs i).continuous⟩,
  locally_finite' := fs.locally_finite,
  nonneg' := λ i x, (fs i).nonneg,
  le_one' := λ i x, (fs i).le_one,
  eventually_eq_one' := fs.eventually_eq_one' }

@[simp] lemma is_subordinate_to_bump_covering {f : smooth_bump_covering I M s} {U : M → set M} :
  f.to_bump_covering.is_subordinate (λ i, U (f.c i)) ↔ f.is_subordinate U :=
iff.rfl

alias is_subordinate_to_bump_covering ↔
  _ smooth_bump_covering.is_subordinate.to_bump_covering

/-- Every `smooth_bump_covering` defines a smooth partition of unity. -/
def to_smooth_partition_of_unity : smooth_partition_of_unity fs.ι I M s :=
fs.to_bump_covering.to_smooth_partition_of_unity (λ i, (fs i).smooth)

lemma to_smooth_partition_of_unity_apply (i : fs.ι) (x : M) :
  fs.to_smooth_partition_of_unity i x = fs i x * ∏ᶠ j (hj : well_ordering_rel j i), (1 - fs j x) :=
rfl

lemma to_smooth_partition_of_unity_eq_mul_prod (i : fs.ι) (x : M) (t : finset fs.ι)
  (ht : ∀ j, well_ordering_rel j i → fs j x ≠ 0 → j ∈ t) :
  fs.to_smooth_partition_of_unity i x =
    fs i x * ∏ j in t.filter (λ j, well_ordering_rel j i), (1 - fs j x) :=
fs.to_bump_covering.to_partition_of_unity_eq_mul_prod i x t ht

lemma exists_finset_to_smooth_partition_of_unity_eventually_eq (i : fs.ι) (x : M) :
  ∃ t : finset fs.ι, fs.to_smooth_partition_of_unity i =ᶠ[𝓝 x]
    fs i * ∏ j in t.filter (λ j, well_ordering_rel j i), (1 - fs j) :=
fs.to_bump_covering.exists_finset_to_partition_of_unity_eventually_eq i x

lemma to_smooth_partition_of_unity_zero_of_zero {i : fs.ι} {x : M} (h : fs i x = 0) :
  fs.to_smooth_partition_of_unity i x = 0 :=
fs.to_bump_covering.to_partition_of_unity_zero_of_zero h

lemma support_to_smooth_partition_of_unity_subset (i : fs.ι) :
  support (fs.to_smooth_partition_of_unity i) ⊆ support (fs i) :=
fs.to_bump_covering.support_to_partition_of_unity_subset i

lemma is_subordinate.to_smooth_partition_of_unity {f : smooth_bump_covering I M s} {U : M → set M}
  (h : f.is_subordinate U) :
  f.to_smooth_partition_of_unity.is_subordinate (λ i, U (f.c i)) :=
h.to_bump_covering.to_partition_of_unity

lemma sum_to_smooth_partition_of_unity_eq (x : M) :
  ∑ᶠ i, fs.to_smooth_partition_of_unity i x = 1 - ∏ᶠ i, (1 - fs i x) :=
fs.to_bump_covering.sum_to_partition_of_unity_eq x

section embedding

/-!
### Whitney embedding theorem

In this section we prove a version of the Whitney embedding theorem: for any compact real manifold
`M`, for sufficiently large `n` there exists a smooth embedding `M → ℝ^n`.
-/

variables [fintype fs.ι] (f : smooth_bump_covering I M) [fintype f.ι]

/-- Smooth embedding of `M` into `(E × ℝ) ^ f.ι`. -/
def embedding_pi_tangent : C^∞⟮I, M; 𝓘(ℝ, fs.ι → (E × ℝ)), fs.ι → (E × ℝ)⟯ :=
{ to_fun := λ x i, (fs i x • ext_chart_at I (fs.c i) x, fs i x),
  times_cont_mdiff_to_fun := times_cont_mdiff_pi_space.2 $ λ i,
    ((fs i).smooth_smul times_cont_mdiff_on_ext_chart_at).prod_mk_space ((fs i).smooth) }

local attribute [simp] lemma embedding_pi_tangent_coe :
  ⇑fs.embedding_pi_tangent = λ x i, (fs i x • ext_chart_at I (fs.c i) x, fs i x) :=
rfl

lemma embedding_pi_tangent_inj_on : inj_on fs.embedding_pi_tangent s :=
begin
  intros x hx y hy h,
  simp only [embedding_pi_tangent_coe, funext_iff] at h,
  obtain ⟨h₁, h₂⟩ := prod.mk.inj_iff.1 (h (fs.ind x hx)),
  rw [fs.apply_ind x hx] at h₂,
  rw [← h₂, fs.apply_ind x hx, one_smul, one_smul] at h₁,
  have := fs.mem_ext_chart_at_source_of_eq_one h₂.symm,
  exact (ext_chart_at I (fs.c _)).inj_on (fs.mem_ext_chart_at_ind_source x hx) this h₁
end

lemma embedding_pi_tangent_injective :
  injective f.embedding_pi_tangent :=
injective_iff_inj_on_univ.2 f.embedding_pi_tangent_inj_on

lemma comp_embedding_pi_tangent_mfderiv (x : M) (hx : x ∈ s) :
  ((continuous_linear_map.fst ℝ E ℝ).comp
    (@continuous_linear_map.proj ℝ _ fs.ι (λ _, E × ℝ) _ _
      (λ _, infer_instance) (fs.ind x hx))).comp
      (mfderiv I 𝓘(ℝ, fs.ι → (E × ℝ)) fs.embedding_pi_tangent x) =
  mfderiv I I (chart_at H (fs.c (fs.ind x hx))) x :=
begin
  set L := ((continuous_linear_map.fst ℝ E ℝ).comp
    (@continuous_linear_map.proj ℝ _ fs.ι (λ _, E × ℝ) _ _ (λ _, infer_instance) (fs.ind x hx))),
  have := (L.has_mfderiv_at.comp x (fs.embedding_pi_tangent.mdifferentiable_at.has_mfderiv_at)),
  convert has_mfderiv_at_unique this _,
  refine (has_mfderiv_at_ext_chart_at I (fs.mem_chart_at_ind_source x hx)).congr_of_eventually_eq _,
  refine (fs.eventually_eq_one x hx).mono (λ y hy, _),
  simp only [embedding_pi_tangent_coe, continuous_linear_map.coe_comp', (∘),
    continuous_linear_map.coe_fst', continuous_linear_map.proj_apply],
  rw [hy, pi.one_apply, one_smul]
end

lemma embedding_pi_tangent_ker_mfderiv (x : M) (hx : x ∈ s) :
  (mfderiv I 𝓘(ℝ, fs.ι → (E × ℝ)) fs.embedding_pi_tangent x).ker = ⊥ :=
begin
  apply bot_unique,
  rw [← (mdifferentiable_chart I (fs.c (fs.ind x hx))).ker_mfderiv_eq_bot
    (fs.mem_chart_at_ind_source x hx), ← comp_embedding_pi_tangent_mfderiv],
  exact linear_map.ker_le_ker_comp _ _
end

lemma embedding_pi_tangent_injective_mfderiv (x : M) (hx : x ∈ s) :
  injective (mfderiv I 𝓘(ℝ, fs.ι → (E × ℝ)) fs.embedding_pi_tangent x) :=
linear_map.ker_eq_bot.1 (fs.embedding_pi_tangent_ker_mfderiv x hx)

end embedding

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be immersed into the `n`-dimensional
Euclidean space. -/
lemma exists_immersion_euclidean (f : smooth_bump_covering I M)
  [fintype f.ι] :
  ∃ (n : ℕ) (e : M → euclidean_space ℝ (fin n)), smooth I (𝓡 n) e ∧
    injective e ∧ ∀ x : M, injective (mfderiv I (𝓡 n) e x) :=
begin
  set F := euclidean_space ℝ (fin $ finrank ℝ (f.ι → (E × ℝ))),
  letI : finite_dimensional ℝ (E × ℝ) := by apply_instance,
  set eEF : (f.ι → (E × ℝ)) ≃L[ℝ] F :=
    continuous_linear_equiv.of_finrank_eq finrank_euclidean_space_fin.symm,
  refine ⟨_, eEF ∘ f.embedding_pi_tangent,
    eEF.to_diffeomorph.smooth.comp f.embedding_pi_tangent.smooth,
    eEF.injective.comp f.embedding_pi_tangent_injective, λ x, _⟩,
  rw [mfderiv_comp _ eEF.differentiable_at.mdifferentiable_at
    f.embedding_pi_tangent.mdifferentiable_at, eEF.mfderiv_eq],
  exact eEF.injective.comp (f.embedding_pi_tangent_injective_mfderiv _ trivial)
end

end smooth_bump_covering

/-- Baby version of the Whitney weak embedding theorem: if `M` admits a finite covering by
supports of bump functions, then for some `n` it can be embedded into the `n`-dimensional
Euclidean space. -/
lemma exists_embedding_euclidean_of_compact [t2_space M] [compact_space M] :
  ∃ (n : ℕ) (e : M → euclidean_space ℝ (fin n)), smooth I (𝓡 n) e ∧
    closed_embedding e ∧ ∀ x : M, injective (mfderiv I (𝓡 n) e x) :=
begin
  rcases (smooth_bump_covering.choice I M).exists_immersion_euclidean
    with ⟨n, e, hsmooth, hinj, hinj_mfderiv⟩,
  exact ⟨n, e, hsmooth, hsmooth.continuous.closed_embedding hinj, hinj_mfderiv⟩
end

/-- Given two disjoint closed sets in a Hausdorff σ-compact finite dimensional manifold, there
exists an infinitely smooth function that is equal to `0` on one of them and is equal to one on the
other. -/
lemma exists_smooth_zero_one_of_closed [t2_space M] [sigma_compact_space M] {s t : set M}
  (hs : is_closed s) (ht : is_closed t) (hd : disjoint s t) :
  ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, eq_on f 0 s ∧ eq_on f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
begin
  have : ∀ x ∈ t, sᶜ ∈ 𝓝 x, from λ x hx, hs.is_open_compl.mem_nhds (disjoint_right.1 hd hx),
  rcases smooth_bump_covering.exists_is_subordinate I ht this with ⟨f, hf⟩,
  set g := f.to_smooth_partition_of_unity,
  refine ⟨⟨_, g.smooth_sum⟩, λ x hx, _, λ x, g.sum_eq_one, λ x, ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩,
  suffices : ∀ i, g i x = 0,
    by simp only [this, times_cont_mdiff_map.coe_fn_mk, finsum_zero, pi.zero_apply],
  refine λ i, f.to_smooth_partition_of_unity_zero_of_zero _,
  exact nmem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)
end
#lint
namespace smooth_partition_of_unity

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. -/
lemma exists_is_subordinate [t2_space M] [sigma_compact_space M] {s : set M}
  (hs : is_closed s) (U : ι → set M) (ho : ∀ i, is_open (U i)) (hU : s ⊆ ⋃ i, U i) :
  ∃ f : smooth_partition_of_unity ι I M s, f.is_subordinate U :=
begin
  haveI : locally_compact_space H := I.locally_compact,
  haveI : locally_compact_space M := charted_space.locally_compact H,
  haveI : normal_space M := normal_of_paracompact_t2,
  rcases bump_covering.exists_is_subordinate_of_prop (smooth I 𝓘(ℝ)) _ hs U ho hU
    with ⟨f, hf, hfU⟩,
  { exact ⟨f.to_smooth_partition_of_unity hf, hfU.to_smooth_partition_of_unity hf⟩ },
  { intros s t hs ht hd,
    rcases exists_smooth_zero_one_of_closed hs ht hd with ⟨f, hf⟩,
    exact ⟨f, f.smooth, hf⟩ }
end

lemma exists_is_subordinate {s : set M} {U : ι → set M} (hs : is_closed s) (ho : ∀ i, is_open (U i))
  (hU : s ⊆ ⋃ i, U i) :
  ∃ f : smooth_partition_of_unity ι I M s, f.is_subordinate U :=
be

end smooth_partition_of_unity
