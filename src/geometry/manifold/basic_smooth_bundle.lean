/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.topological_fiber_bundle
import geometry.manifold.smooth_manifold_with_corners

/-!
# Basic smooth bundles

In general, a smooth bundle is a bundle over a smooth manifold, whose fiber is a manifold, and
for which the coordinate changes are smooth. In this definition, there are charts involved at
several places: in the manifold structure of the base, in the manifold structure of the fibers, and
in the local trivializations. This makes it a complicated object in general. There is however a
specific situation where things are much simpler: when the fiber is a vector space (no need for
charts for the fibers), and when the local trivializations of the bundle and the charts of the base
coincide. Then everything is expressed in terms of the charts of the base, making for a much
simpler overall structure, which is easier to manipulate formally.

Most vector bundles that naturally occur in differential geometry are of this form:
the tangent bundle, the cotangent bundle, differential forms (used to define de Rham cohomology)
and the bundle of Riemannian metrics. Therefore, it is worth defining a specific constructor for
this kind of bundle, that we call basic smooth bundles.

A basic smooth bundle is thus a smooth bundle over a smooth manifold whose fiber is a vector space,
and which is trivial in the coordinate charts of the base. (We recall that in our notion of manifold
there is a distinguished atlas, which does not need to be maximal: we require the triviality above
this specific atlas). It can be constructed from a basic smooth bundled core, defined below,
specifying the changes in the fiber when one goes from one coordinate chart to another one. We do
not require that this changes in fiber are linear, but only diffeomorphisms.

## Main definitions

* `basic_smooth_bundle_core I M F`: assuming that `M` is a smooth manifold over the model with
  corners `I` on `(𝕜, E, H)`, and `F` is a normed vector space over `𝕜`, this structure registers,
  for each pair of charts of `M`, a smooth change of coordinates on `F`. This is the core structure
  from which one will build a smooth bundle with fiber `F` over `M`.

Let `Z` be a basic smooth bundle core over `M` with fiber `F`. We define
`Z.to_topological_fiber_bundle_core`, the (topological) fiber bundle core associated to `Z`. From
it, we get a space `Z.to_topological_fiber_bundle_core.total_space` (which as a Type is just `Σ (x :
M), F`), with the fiber bundle topology. It inherits a manifold structure (where the charts are in
bijection with the charts of the basis). We show that this manifold is smooth.

Then we use this machinery to construct the tangent bundle of a smooth manifold.

* `tangent_bundle_core I M`: the basic smooth bundle core associated to a smooth manifold `M` over a
  model with corners `I`.
* `tangent_bundle I M`     : the total space of `tangent_bundle_core I M`. It is itself a
  smooth manifold over the model with corners `I.tangent`, the product of `I` and the trivial model
  with corners on `E`.
* `tangent_space I x`      : the tangent space to `M` at `x`
* `tangent_bundle.proj I M`: the projection from the tangent bundle to the base manifold

## Implementation notes

In the definition of a basic smooth bundle core, we do not require that the coordinate changes of
the fibers are linear map, only that they are diffeomorphisms. Therefore, the fibers of the
resulting fiber bundle do not inherit a vector space structure (as an algebraic object) in general.
As the fiber, as a type, is just `F`, one can still always register the vector space structure, but
it does not make sense to do so (i.e., it will not lead to any useful theorem) unless this structure
is canonical, i.e., the coordinate changes are linear maps.

For instance, we register the vector space structure on the fibers of the tangent bundle. However,
we do not register the normed space structure coming from that of `F` (as it is not canonical, and
we also want to keep the possibility to add a Riemannian structure on the manifold later on without
having two competing normed space instances on the tangent spaces).

We require `F` to be a normed space, and not just a topological vector space, as we want to talk
about smooth functions on `F`. The notion of derivative requires a norm to be defined.

## TODO
construct the cotangent bundle, and the bundles of differential forms. They should follow
functorially from the description of the tangent bundle as a basic smooth bundle.

## Tags
Smooth fiber bundle, vector bundle, tangent space, tangent bundle
-/

noncomputable theory

universe u

open topological_space set
open_locale manifold topological_space

/-- Core structure used to create a smooth bundle above `M` (a manifold over the model with
corner `I`) with fiber the normed vector space `F` over `𝕜`, which is trivial in the chart domains
of `M`. This structure registers the changes in the fibers when one changes coordinate charts in the
base. We do not require the change of coordinates of the fibers to be linear, only smooth.
Therefore, the fibers of the resulting bundle will not inherit a canonical vector space structure
in general. -/
structure basic_smooth_bundle_core {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(F : Type*) [normed_group F] [normed_space 𝕜 F] :=
(coord_change      : atlas H M → atlas H M → H → F → F)
(coord_change_self :
  ∀ i : atlas H M, ∀ x ∈ i.1.target, ∀ v, coord_change i i x v = v)
(coord_change_comp : ∀ i j k : atlas H M,
  ∀ x ∈ ((i.1.symm.trans j.1).trans (j.1.symm.trans k.1)).source, ∀ v,
  (coord_change j k ((i.1.symm.trans j.1) x)) (coord_change i j x v) = coord_change i k x v)
(coord_change_smooth : ∀ i j : atlas H M,
  times_cont_diff_on 𝕜 ∞ (λp : E × F, coord_change i j (I.symm p.1) p.2)
  ((I '' (i.1.symm.trans j.1).source).prod (univ : set F)))

/-- The trivial basic smooth bundle core, in which all the changes of coordinates are the
identity. -/
def trivial_basic_smooth_bundle_core {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(F : Type*) [normed_group F] [normed_space 𝕜 F] : basic_smooth_bundle_core I M F :=
{ coord_change := λ i j x v, v,
  coord_change_self := λ i x hx v, rfl,
  coord_change_comp := λ i j k x hx v, rfl,
  coord_change_smooth := λ i j, times_cont_diff_snd.times_cont_diff_on }

namespace basic_smooth_bundle_core

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
(Z : basic_smooth_bundle_core I M F)

instance : inhabited (basic_smooth_bundle_core I M F) :=
⟨trivial_basic_smooth_bundle_core I M F⟩

/-- Fiber bundle core associated to a basic smooth bundle core -/
def to_topological_fiber_bundle_core : topological_fiber_bundle_core (atlas H M) M F :=
{ base_set := λi, i.1.source,
  is_open_base_set := λi, i.1.open_source,
  index_at := λx, ⟨chart_at H x, chart_mem_atlas H x⟩,
  mem_base_set_at := λx, mem_chart_source H x,
  coord_change := λi j x v, Z.coord_change i j (i.1 x) v,
  coord_change_self := λi x hx v, Z.coord_change_self i (i.1 x) (i.1.map_source hx) v,
  coord_change_comp := λi j k x ⟨⟨hx1, hx2⟩, hx3⟩ v, begin
    have := Z.coord_change_comp i j k (i.1 x) _ v,
    convert this using 2,
    { simp only [hx1] with mfld_simps },
    { simp only [hx1, hx2, hx3] with mfld_simps }
  end,
  coord_change_continuous := λi j, begin
    have A : continuous_on (λp : E × F, Z.coord_change i j (I.symm p.1) p.2)
      ((I '' (i.1.symm.trans j.1).source).prod (univ : set F)) :=
      (Z.coord_change_smooth i j).continuous_on,
    have B : continuous_on (λx : M, I (i.1 x)) i.1.source :=
      I.continuous.comp_continuous_on i.1.continuous_on,
    have C : continuous_on (λp : M × F, (⟨I (i.1 p.1), p.2⟩ : E × F))
             (i.1.source.prod univ),
    { apply continuous_on.prod _ continuous_snd.continuous_on,
      exact B.comp continuous_fst.continuous_on (prod_subset_preimage_fst _ _) },
    have C' : continuous_on (λp : M × F, (⟨I (i.1 p.1), p.2⟩ : E × F))
              ((i.1.source ∩ j.1.source).prod univ) :=
      continuous_on.mono C (prod_mono (inter_subset_left _ _) (subset.refl _)),
    have D : (i.1.source ∩ j.1.source).prod univ ⊆ (λ (p : M × F),
      (I (i.1 p.1), p.2)) ⁻¹' ((I '' (i.1.symm.trans j.1).source).prod univ),
    { rintros ⟨x, v⟩ hx,
      simp only with mfld_simps at hx,
      simp only [hx] with mfld_simps },
    convert continuous_on.comp A C' D,
    ext p,
    simp only with mfld_simps
  end }

@[simp, mfld_simps] lemma base_set (i : atlas H M) :
  (Z.to_topological_fiber_bundle_core.local_triv i).base_set = i.1.source := rfl

/-- Local chart for the total space of a basic smooth bundle -/
def chart {e : local_homeomorph M H} (he : e ∈ atlas H M) :
  local_homeomorph (Z.to_topological_fiber_bundle_core.total_space) (model_prod H F) :=
(Z.to_topological_fiber_bundle_core.local_triv ⟨e, he⟩).to_local_homeomorph.trans
  (local_homeomorph.prod e (local_homeomorph.refl F))

@[simp, mfld_simps] lemma chart_source (e : local_homeomorph M H) (he : e ∈ atlas H M) :
  (Z.chart he).source = Z.to_topological_fiber_bundle_core.proj ⁻¹' e.source :=
by { simp only [chart, mem_prod], mfld_set_tac }

@[simp, mfld_simps] lemma chart_target (e : local_homeomorph M H) (he : e ∈ atlas H M) :
  (Z.chart he).target = e.target.prod univ :=
by { simp only [chart], mfld_set_tac }

/-- The total space of a basic smooth bundle is endowed with a charted space structure, where the
charts are in bijection with the charts of the basis. -/
instance to_charted_space :
  charted_space (model_prod H F) Z.to_topological_fiber_bundle_core.total_space :=
{ atlas := ⋃(e : local_homeomorph M H) (he : e ∈ atlas H M), {Z.chart he},
  chart_at := λp, Z.chart (chart_mem_atlas H p.1),
  mem_chart_source := λp, by simp [mem_chart_source],
  chart_mem_atlas := λp, begin
    simp only [mem_Union, mem_singleton_iff, chart_mem_atlas],
    exact ⟨chart_at H p.1, chart_mem_atlas H p.1, rfl⟩
  end }

lemma mem_atlas_iff
  (f : local_homeomorph Z.to_topological_fiber_bundle_core.total_space (model_prod H F)) :
  f ∈ atlas (model_prod H F) Z.to_topological_fiber_bundle_core.total_space ↔
  ∃(e : local_homeomorph M H) (he : e ∈ atlas H M), f = Z.chart he :=
by simp only [atlas, mem_Union, mem_singleton_iff]

@[simp, mfld_simps] lemma mem_chart_source_iff
  (p q : Z.to_topological_fiber_bundle_core.total_space) :
  p ∈ (chart_at (model_prod H F) q).source ↔ p.1 ∈ (chart_at H q.1).source :=
by simp only [chart_at] with mfld_simps

@[simp, mfld_simps] lemma mem_chart_target_iff
  (p : H × F) (q : Z.to_topological_fiber_bundle_core.total_space) :
  p ∈ (chart_at (model_prod H F) q).target ↔ p.1 ∈ (chart_at H q.1).target :=
by simp only [chart_at] with mfld_simps

@[simp, mfld_simps] lemma coe_chart_at_fst (p q : Z.to_topological_fiber_bundle_core.total_space) :
  ((chart_at (model_prod H F) q) p).1 = chart_at H q.1 p.1 := rfl

@[simp, mfld_simps] lemma coe_chart_at_symm_fst
  (p : H × F) (q : Z.to_topological_fiber_bundle_core.total_space) :
  ((chart_at (model_prod H F) q).symm p).1 = ((chart_at H q.1).symm : H → M) p.1 := rfl

/-- Smooth manifold structure on the total space of a basic smooth bundle -/
instance to_smooth_manifold :
  smooth_manifold_with_corners (I.prod (𝓘(𝕜, F))) Z.to_topological_fiber_bundle_core.total_space :=
begin
  /- We have to check that the charts belong to the smooth groupoid, i.e., they are smooth on their
  source, and their inverses are smooth on the target. Since both objects are of the same kind, it
  suffices to prove the first statement in A below, and then glue back the pieces at the end. -/
  let J := model_with_corners.to_local_equiv (I.prod (𝓘(𝕜, F))),
  have A : ∀ (e e' : local_homeomorph M H) (he : e ∈ atlas H M) (he' : e' ∈ atlas H M),
    times_cont_diff_on 𝕜 ∞
    (J ∘ ((Z.chart he).symm.trans (Z.chart he')) ∘ J.symm)
    (J.symm ⁻¹' ((Z.chart he).symm.trans (Z.chart he')).source ∩ range J),
  { assume e e' he he',
    have : J.symm ⁻¹' ((chart Z he).symm.trans (chart Z he')).source ∩ range J =
      (I.symm ⁻¹' (e.symm.trans e').source ∩ range I).prod univ,
      by { simp only [J, chart, model_with_corners.prod], mfld_set_tac },
    rw this,
    -- check separately that the two components of the coordinate change are smooth
    apply times_cont_diff_on.prod,
    show times_cont_diff_on 𝕜 ∞ (λ (p : E × F), (I ∘ e' ∘ e.symm ∘ I.symm) p.1)
         ((I.symm ⁻¹' (e.symm.trans e').source ∩ range I).prod (univ : set F)),
    { -- the coordinate change on the base is just a coordinate change for `M`, smooth since
      -- `M` is smooth
      have A : times_cont_diff_on 𝕜 ∞ (I ∘ (e.symm.trans e') ∘ I.symm)
        (I.symm ⁻¹' (e.symm.trans e').source ∩ range I) :=
      (has_groupoid.compatible (times_cont_diff_groupoid ∞ I) he he').1,
      have B : times_cont_diff_on 𝕜 ∞ (λp : E × F, p.1)
        ((I.symm ⁻¹' (e.symm.trans e').source ∩ range I).prod univ) :=
      times_cont_diff_fst.times_cont_diff_on,
      exact times_cont_diff_on.comp A B (prod_subset_preimage_fst _ _) },
    show times_cont_diff_on 𝕜 ∞ (λ (p : E × F),
      Z.coord_change ⟨chart_at H (e.symm (I.symm p.1)), _⟩ ⟨e', he'⟩
         ((chart_at H (e.symm (I.symm p.1)) : M → H) (e.symm (I.symm p.1)))
      (Z.coord_change ⟨e, he⟩ ⟨chart_at H (e.symm (I.symm p.1)), _⟩
        (e (e.symm (I.symm p.1))) p.2))
      ((I.symm ⁻¹' (e.symm.trans e').source ∩ range I).prod (univ : set F)),
    { /- The coordinate change in the fiber is more complicated as its definition involves the
      reference chart chosen at each point. However, it appears with its inverse, so using the
      cocycle property one can get rid of it, and then conclude using the smoothness of the
      cocycle as given in the definition of basic smooth bundles. -/
      have := Z.coord_change_smooth ⟨e, he⟩ ⟨e', he'⟩,
      rw I.image_eq at this,
      apply times_cont_diff_on.congr this,
      rintros ⟨x, v⟩ hx,
      simp only with mfld_simps at hx,
      let f := chart_at H (e.symm (I.symm x)),
      have A : I.symm x ∈ ((e.symm.trans f).trans (f.symm.trans e')).source,
        by simp only [hx.1.1, hx.1.2] with mfld_simps,
      rw e.right_inv hx.1.1,
      have := Z.coord_change_comp ⟨e, he⟩ ⟨f, chart_mem_atlas _ _⟩ ⟨e', he'⟩ (I.symm x) A v,
      simpa only [] using this } },
  constructor,
  assume e₀ e₀' he₀ he₀',
  rcases (Z.mem_atlas_iff _).1 he₀ with ⟨e, he, rfl⟩,
  rcases (Z.mem_atlas_iff _).1 he₀' with ⟨e', he', rfl⟩,
  rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid],
  exact ⟨A e e' he he', A e' e he' he⟩
end

end basic_smooth_bundle_core

section tangent_bundle

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

/-- Basic smooth bundle core version of the tangent bundle of a smooth manifold `M` modelled over a
model with corners `I` on `(E, H)`. The fibers are equal to `E`, and the coordinate change in the
fiber corresponds to the derivative of the coordinate change in `M`. -/
def tangent_bundle_core : basic_smooth_bundle_core I M E :=
{ coord_change := λi j x v, (fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
                            (range I) (I x) : E → E) v,
  coord_change_smooth := λi j, begin
    /- To check that the coordinate change of the bundle is smooth, one should just use the
    smoothness of the charts, and thus the smoothness of their derivatives. -/
    rw I.image_eq,
    have A : times_cont_diff_on 𝕜 ∞
      (I ∘ (i.1.symm.trans j.1) ∘ I.symm)
      (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
      (has_groupoid.compatible (times_cont_diff_groupoid ∞ I) i.2 j.2).1,
    have B : unique_diff_on 𝕜 (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
      I.unique_diff_preimage_source,
    have C : times_cont_diff_on 𝕜 ∞
      (λ (p : E × E), (fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
            (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) p.1 : E → E) p.2)
      ((I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I).prod univ) :=
      times_cont_diff_on_fderiv_within_apply A B le_top,
    have D : ∀ x ∈ (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I),
      fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
            (range I) x =
      fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
            (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) x,
    { assume x hx,
      have N : I.symm ⁻¹' (i.1.symm.trans j.1).source ∈ nhds x :=
        I.continuous_symm.continuous_at.preimage_mem_nhds
          (is_open.mem_nhds (local_homeomorph.open_source _) hx.1),
      symmetry,
      rw inter_comm,
      exact fderiv_within_inter N (I.unique_diff _ hx.2) },
    apply times_cont_diff_on.congr C,
    rintros ⟨x, v⟩ hx,
    have E : x ∈ I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I,
      by simpa only [prod_mk_mem_set_prod_eq, and_true, mem_univ] using hx,
    have : I (I.symm x) = x, by simp [E.2],
    dsimp [-subtype.val_eq_coe],
    rw [this, D x E],
    refl
  end,
  coord_change_self := λi x hx v, begin
    /- Locally, a self-change of coordinate is just the identity, thus its derivative is the
    identity. One just needs to write this carefully, paying attention to the sets where the
    functions are defined. -/
    have A : I.symm ⁻¹' (i.1.symm.trans i.1).source ∩ range I ∈
      𝓝[range I] (I x),
    { rw inter_comm,
      apply inter_mem_nhds_within,
      apply I.continuous_symm.continuous_at.preimage_mem_nhds
        (is_open.mem_nhds (local_homeomorph.open_source _) _),
      simp only [hx, i.1.map_target] with mfld_simps },
    have B : ∀ᶠ y in 𝓝[range I] (I x),
      (I ∘ i.1 ∘ i.1.symm ∘ I.symm) y = (id : E → E) y,
    { filter_upwards [A],
      assume y hy,
      rw ← I.image_eq at hy,
      rcases hy with ⟨z, hz⟩,
      simp only with mfld_simps at hz,
      simp only [hz.2.symm, hz.1] with mfld_simps },
    have C : fderiv_within 𝕜 (I ∘ i.1 ∘ i.1.symm ∘ I.symm) (range I) (I x) =
             fderiv_within 𝕜 (id : E → E) (range I) (I x) :=
      filter.eventually_eq.fderiv_within_eq I.unique_diff_at_image B
      (by simp only [hx] with mfld_simps),
    rw fderiv_within_id I.unique_diff_at_image at C,
    rw C,
    refl
  end,
  coord_change_comp := λi j u x hx, begin
    /- The cocycle property is just the fact that the derivative of a composition is the product of
    the derivatives. One needs however to check that all the functions one considers are smooth, and
    to pay attention to the domains where these functions are defined, making this proof a little
    bit cumbersome although there is nothing complicated here. -/
    have M : I x ∈
      (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) :=
    ⟨by simpa only [mem_preimage, model_with_corners.left_inv] using hx, mem_range_self _⟩,
    have U : unique_diff_within_at 𝕜
      (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I) (I x) :=
      I.unique_diff_preimage_source _ M,
    have A : fderiv_within 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ (I ∘ j.1 ∘ i.1.symm ∘ I.symm))
             (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
             (I x)
      = (fderiv_within 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
             (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I)
             ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x))).comp
        (fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
             (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
             (I x)),
    { apply fderiv_within.comp _ _ _ _ U,
      show differentiable_within_at 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
        (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
        (I x),
      { have A : times_cont_diff_on 𝕜 ∞
          (I ∘ (i.1.symm.trans j.1) ∘ I.symm)
          (I.symm ⁻¹' (i.1.symm.trans j.1).source ∩ range I) :=
        (has_groupoid.compatible (times_cont_diff_groupoid ∞ I) i.2 j.2).1,
        have B : differentiable_on 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
          (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I),
        { apply (A.differentiable_on le_top).mono,
          have : ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ⊆
            (i.1.symm.trans j.1).source := inter_subset_left _ _,
          exact inter_subset_inter (preimage_mono this) (subset.refl (range I)) },
        apply B,
        simpa only [] with mfld_simps using hx },
      show differentiable_within_at 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
        (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I)
        ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)),
      { have A : times_cont_diff_on 𝕜 ∞
          (I ∘ (j.1.symm.trans u.1) ∘ I.symm)
          (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I) :=
        (has_groupoid.compatible (times_cont_diff_groupoid ∞ I) j.2 u.2).1,
        apply A.differentiable_on le_top,
        rw [local_homeomorph.trans_source] at hx,
        simp only with mfld_simps,
        exact hx.2 },
      show (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
        ⊆ (I ∘ j.1 ∘ i.1.symm ∘ I.symm) ⁻¹' (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I),
      { assume y hy,
        simp only with mfld_simps at hy,
        rw [local_homeomorph.left_inv] at hy,
        { simp only [hy] with mfld_simps },
        { exact hy.1.1.2 } } },
    have B : fderiv_within 𝕜 ((I ∘ u.1 ∘ j.1.symm ∘ I.symm)
                          ∘ (I ∘ j.1 ∘ i.1.symm ∘ I.symm))
             (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
             (I x)
             = fderiv_within 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
             (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
             (I x),
    { have E :
        ∀ y ∈ (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I),
          ((I ∘ u.1 ∘ j.1.symm ∘ I.symm) ∘ (I ∘ j.1 ∘ i.1.symm ∘ I.symm)) y =
            (I ∘ u.1 ∘ i.1.symm ∘ I.symm) y,
      { assume y hy,
        simp only [function.comp_app, model_with_corners.left_inv],
        rw [j.1.left_inv],
        exact hy.1.1.2 },
      exact fderiv_within_congr U E (E _ M) },
    have C : fderiv_within 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
             (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
             (I x) =
             fderiv_within 𝕜 (I ∘ u.1 ∘ i.1.symm ∘ I.symm)
             (range I) (I x),
    { rw inter_comm,
      apply fderiv_within_inter _ I.unique_diff_at_image,
      apply I.continuous_symm.continuous_at.preimage_mem_nhds
        (is_open.mem_nhds (local_homeomorph.open_source _) _),
      simpa only [model_with_corners.left_inv] using hx },
    have D : fderiv_within 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm)
      (I.symm ⁻¹' (j.1.symm.trans u.1).source ∩ range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)) =
      fderiv_within 𝕜 (I ∘ u.1 ∘ j.1.symm ∘ I.symm) (range I) ((I ∘ j.1 ∘ i.1.symm ∘ I.symm) (I x)),
    { rw inter_comm,
      apply fderiv_within_inter _ I.unique_diff_at_image,
      apply I.continuous_symm.continuous_at.preimage_mem_nhds
        (is_open.mem_nhds (local_homeomorph.open_source _) _),
      rw [local_homeomorph.trans_source] at hx,
      simp only with mfld_simps,
      exact hx.2 },
    have E : fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm)
               (I.symm ⁻¹' ((i.1.symm.trans j.1).trans (j.1.symm.trans u.1)).source ∩ range I)
               (I x) =
             fderiv_within 𝕜 (I ∘ j.1 ∘ i.1.symm ∘ I.symm) (range I) (I x),
    { rw inter_comm,
      apply fderiv_within_inter _ I.unique_diff_at_image,
      apply I.continuous_symm.continuous_at.preimage_mem_nhds
        (is_open.mem_nhds (local_homeomorph.open_source _) _),
      simpa only [model_with_corners.left_inv] using hx },
    rw [B, C, D, E] at A,
    simp only [A, continuous_linear_map.coe_comp'] with mfld_simps
  end }

variable {M}
include I

/-- The tangent space at a point of the manifold `M`. It is just `E`. We could use instead
`(tangent_bundle_core I M).to_topological_fiber_bundle_core.fiber x`, but we use `E` to help the
kernel.
-/
@[nolint unused_arguments]
def tangent_space (x : M) : Type* := E

omit I
variable (M)

/-- The tangent bundle to a smooth manifold, as a plain type. We could use
`(tangent_bundle_core I M).to_topological_fiber_bundle_core.total_space`, but instead we use the
(definitionally equal) `Σ (x : M), tangent_space I x`, to make sure that rcasing an element of the
tangent bundle gives a second component in the tangent space. -/
@[nolint has_inhabited_instance, reducible] -- is empty if the base manifold is empty
def tangent_bundle := Σ (x : M), tangent_space I x

/-- The projection from the tangent bundle of a smooth manifold to the manifold. As the tangent
bundle is represented internally as a sigma type, the notation `p.1` also works for the projection
of the point `p`. -/
def tangent_bundle.proj : tangent_bundle I M → M :=
λ p, p.1

variable {M}

@[simp, mfld_simps] lemma tangent_bundle.proj_apply (x : M) (v : tangent_space I x) :
  tangent_bundle.proj I M ⟨x, v⟩ = x :=
rfl

section tangent_bundle_instances

/- In general, the definition of tangent_bundle and tangent_space are not reducible, so that type
class inference does not pick wrong instances. In this section, we record the right instances for
them, noting in particular that the tangent bundle is a smooth manifold. -/
variable (M)

instance : topological_space (tangent_bundle I M) :=
(tangent_bundle_core I M).to_topological_fiber_bundle_core.to_topological_space (atlas H M)

instance : charted_space (model_prod H E) (tangent_bundle I M) :=
(tangent_bundle_core I M).to_charted_space

instance : smooth_manifold_with_corners I.tangent (tangent_bundle I M) :=
(tangent_bundle_core I M).to_smooth_manifold

local attribute [reducible] tangent_space
variables {M} (x : M)

instance : has_continuous_smul 𝕜 (tangent_space I x) := by apply_instance
instance : topological_space (tangent_space I x) := by apply_instance
instance : add_comm_group (tangent_space I x) := by apply_instance
instance : topological_add_group (tangent_space I x) := by apply_instance
instance : module 𝕜 (tangent_space I x) := by apply_instance
instance : inhabited (tangent_space I x) := ⟨0⟩

end tangent_bundle_instances

variable (M)

/-- The tangent bundle projection on the basis is a continuous map. -/
lemma tangent_bundle_proj_continuous : continuous (tangent_bundle.proj I M) :=
topological_fiber_bundle_core.continuous_proj _

/-- The tangent bundle projection on the basis is an open map. -/
lemma tangent_bundle_proj_open : is_open_map (tangent_bundle.proj I M) :=
topological_fiber_bundle_core.is_open_map_proj _

/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `equiv.sigma_equiv_prod`. -/
@[simp, mfld_simps] lemma tangent_bundle_model_space_chart_at (p : tangent_bundle I H) :
  (chart_at (model_prod H E) p).to_local_equiv = (equiv.sigma_equiv_prod H E).to_local_equiv :=
begin
  have A : ∀ x_fst, fderiv_within 𝕜 (I ∘ I.symm) (range I) (I x_fst) = continuous_linear_map.id 𝕜 E,
  { assume x_fst,
    have : fderiv_within 𝕜 (I ∘ I.symm) (range I) (I x_fst)
         = fderiv_within 𝕜 id (range I) (I x_fst),
    { refine fderiv_within_congr I.unique_diff_at_image (λy hy, _) (by simp),
      exact model_with_corners.right_inv _ hy },
    rwa fderiv_within_id I.unique_diff_at_image at this },
  ext x : 1,
  show (chart_at (model_prod H E) p : tangent_bundle I H → model_prod H E) x =
    (equiv.sigma_equiv_prod H E) x,
  { cases x,
    simp only [chart_at, basic_smooth_bundle_core.chart, tangent_bundle_core,
      basic_smooth_bundle_core.to_topological_fiber_bundle_core, A, prod.mk.inj_iff,
      continuous_linear_map.coe_id'] with mfld_simps, },
  show ∀ x, ((chart_at (model_prod H E) p).to_local_equiv).symm x =
    (equiv.sigma_equiv_prod H E).symm x,
  { rintros ⟨x_fst, x_snd⟩,
    simp only [chart_at, basic_smooth_bundle_core.chart, tangent_bundle_core,
      continuous_linear_map.coe_id', basic_smooth_bundle_core.to_topological_fiber_bundle_core, A]
      with mfld_simps },
  show ((chart_at (model_prod H E) p).to_local_equiv).source = univ,
    by simp only [chart_at] with mfld_simps,
end

@[simp, mfld_simps] lemma tangent_bundle_model_space_coe_chart_at (p : tangent_bundle I H) :
  ⇑(chart_at (model_prod H E) p) = equiv.sigma_equiv_prod H E :=
by { unfold_coes, simp only with mfld_simps }

@[simp, mfld_simps] lemma tangent_bundle_model_space_coe_chart_at_symm (p : tangent_bundle I H) :
  ((chart_at (model_prod H E) p).symm : model_prod H E → tangent_bundle I H) =
  (equiv.sigma_equiv_prod H E).symm :=
by { unfold_coes, simp only with mfld_simps }

variable (H)
/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism -/
def tangent_bundle_model_space_homeomorph : tangent_bundle I H ≃ₜ model_prod H E :=
{ continuous_to_fun :=
  begin
    let p : tangent_bundle I H := ⟨I.symm (0 : E), (0 : E)⟩,
    have : continuous (chart_at (model_prod H E) p),
    { rw continuous_iff_continuous_on_univ,
      convert local_homeomorph.continuous_on _,
      simp only with mfld_simps },
    simpa only with mfld_simps using this,
  end,
  continuous_inv_fun :=
  begin
    let p : tangent_bundle I H := ⟨I.symm (0 : E), (0 : E)⟩,
    have : continuous (chart_at (model_prod H E) p).symm,
    { rw continuous_iff_continuous_on_univ,
      convert local_homeomorph.continuous_on _,
      simp only with mfld_simps },
    simpa only with mfld_simps using this,
  end,
  .. equiv.sigma_equiv_prod H E }

@[simp, mfld_simps] lemma tangent_bundle_model_space_homeomorph_coe :
  (tangent_bundle_model_space_homeomorph H I : tangent_bundle I H → model_prod H E)
  = equiv.sigma_equiv_prod H E :=
rfl

@[simp, mfld_simps] lemma tangent_bundle_model_space_homeomorph_coe_symm :
  ((tangent_bundle_model_space_homeomorph H I).symm : model_prod H E → tangent_bundle I H)
  = (equiv.sigma_equiv_prod H E).symm :=
rfl

end tangent_bundle
