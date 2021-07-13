/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.times_cont_diff
import geometry.manifold.charted_space

/-!
# Smooth manifolds (possibly with boundary or corners)

A smooth manifold is a manifold modelled on a normed vector space, or a subset like a
half-space (to get manifolds with boundaries) for which the changes of coordinates are smooth maps.
We define a model with corners as a map `I : H → E` embedding nicely the topological space `H` in
the vector space `E` (or more precisely as a structure containing all the relevant properties).
Given such a model with corners `I` on `(E, H)`, we define the groupoid of local
homeomorphisms of `H` which are smooth when read in `E` (for any regularity `n : with_top ℕ`).
With this groupoid at hand and the general machinery of charted spaces, we thus get the notion
of `C^n` manifold with respect to any model with corners `I` on `(E, H)`. We also introduce a
specific type class for `C^∞` manifolds as these are the most commonly used.

## Main definitions

* `model_with_corners 𝕜 E H` :
  a structure containing informations on the way a space `H` embeds in a
  model vector space E over the field `𝕜`. This is all that is needed to
  define a smooth manifold with model space `H`, and model vector space `E`.
* `model_with_corners_self 𝕜 E` :
  trivial model with corners structure on the space `E` embedded in itself by the identity.
* `times_cont_diff_groupoid n I` :
  when `I` is a model with corners on `(𝕜, E, H)`, this is the groupoid of local homeos of `H`
  which are of class `C^n` over the normed field `𝕜`, when read in `E`.
* `smooth_manifold_with_corners I M` :
  a type class saying that the charted space `M`, modelled on the space `H`, has `C^∞` changes of
  coordinates with respect to the model with corners `I` on `(𝕜, E, H)`. This type class is just
  a shortcut for `has_groupoid M (times_cont_diff_groupoid ∞ I)`.
* `ext_chart_at I x`:
  in a smooth manifold with corners with the model `I` on `(E, H)`, the charts take values in `H`,
  but often we may want to use their `E`-valued version, obtained by composing the charts with `I`.
  Since the target is in general not open, we can not register them as local homeomorphisms, but
  we register them as local equivs. `ext_chart_at I x` is the canonical such local equiv around `x`.

As specific examples of models with corners, we define (in the file `real_instances.lean`)
* `model_with_corners_self ℝ (euclidean_space (fin n))` for the model space used to define
  `n`-dimensional real manifolds without boundary (with notation `𝓡 n` in the locale `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_half_space n)` for the model space
  used to define `n`-dimensional real manifolds with boundary (with notation `𝓡∂ n` in the locale
  `manifold`)
* `model_with_corners ℝ (euclidean_space (fin n)) (euclidean_quadrant n)` for the model space used
  to define `n`-dimensional real manifolds with corners

With these definitions at hand, to invoke an `n`-dimensional real manifold without boundary,
one could use

  `variables {n : ℕ} {M : Type*} [topological_space M] [charted_space (euclidean_space (fin n)) M]
   [smooth_manifold_with_corners (𝓡 n) M]`.

However, this is not the recommended way: a theorem proved using this assumption would not apply
for instance to the tangent space of such a manifold, which is modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin n))` and not on `euclidean_space (fin (2 * n))`!
In the same way, it would not apply to product manifolds, modelled on
`(euclidean_space (fin n)) × (euclidean_space (fin m))`.
The right invocation does not focus on one specific construction, but on all constructions sharing
the right properties, like

  `variables {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {I : model_with_corners ℝ E E} [I.boundaryless]
  {M : Type*} [topological_space M] [charted_space E M] [smooth_manifold_with_corners I M]`

Here, `I.boundaryless` is a typeclass property ensuring that there is no boundary (this is for
instance the case for `model_with_corners_self`, or products of these). Note that one could consider
as a natural assumption to only use the trivial model with corners `model_with_corners_self ℝ E`,
but again in product manifolds the natural model with corners will not be this one but the product
one (and they are not defeq as `(λp : E × F, (p.1, p.2))` is not defeq to the identity). So, it is
important to use the above incantation to maximize the applicability of theorems.

## Implementation notes

We want to talk about manifolds modelled on a vector space, but also on manifolds with
boundary, modelled on a half space (or even manifolds with corners). For the latter examples,
we still want to define smooth functions, tangent bundles, and so on. As smooth functions are
well defined on vector spaces or subsets of these, one could take for model space a subtype of a
vector space. With the drawback that the whole vector space itself (which is the most basic
example) is not directly a subtype of itself: the inclusion of `univ : set E` in `set E` would
show up in the definition, instead of `id`.

A good abstraction covering both cases it to have a vector
space `E` (with basic example the Euclidean space), a model space `H` (with basic example the upper
half space), and an embedding of `H` into `E` (which can be the identity for `H = E`, or
`subtype.val` for manifolds with corners). We say that the pair `(E, H)` with their embedding is a
model with corners, and we encompass all the relevant properties (in particular the fact that the
image of `H` in `E` should have unique differentials) in the definition of `model_with_corners`.

We concentrate on `C^∞` manifolds: all the definitions work equally well for `C^n` manifolds, but
later on it is a pain to carry all over the smoothness parameter, especially when one wants to deal
with `C^k` functions as there would be additional conditions `k ≤ n` everywhere. Since one deals
almost all the time with `C^∞` (or analytic) manifolds, this seems to be a reasonable choice that
one could revisit later if needed. `C^k` manifolds are still available, but they should be called
using `has_groupoid M (times_cont_diff_groupoid k I)` where `I` is the model with corners.

I have considered using the model with corners `I` as a typeclass argument, possibly `out_param`, to
get lighter notations later on, but it did not turn out right, as on `E × F` there are two natural
model with corners, the trivial (identity) one, and the product one, and they are not defeq and one
needs to indicate to Lean which one we want to use.
This means that when talking on objects on manifolds one will most often need to specify the model
with corners one is using. For instance, the tangent bundle will be `tangent_bundle I M` and the
derivative will be `mfderiv I I' f`, instead of the more natural notations `tangent_bundle 𝕜 M` and
`mfderiv 𝕜 f` (the field has to be explicit anyway, as some manifolds could be considered both as
real and complex manifolds).
-/

noncomputable theory

universes u v w u' v' w'

open set filter
open_locale manifold filter topological_space

localized "notation `∞` := (⊤ : with_top ℕ)" in manifold

section model_with_corners
/-! ### Models with corners. -/

/-- A structure containing informations on the way a space `H` embeds in a
model vector space `E` over the field `𝕜`. This is all what is needed to
define a smooth manifold with model space `H`, and model vector space `E`.
-/
@[nolint has_inhabited_instance]
structure model_with_corners (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] (H : Type*) [topological_space H]
  extends local_equiv H E :=
(source_eq          : source = univ)
(unique_diff'       : unique_diff_on 𝕜 to_local_equiv.target)
(continuous_to_fun  : continuous to_fun . tactic.interactive.continuity')
(continuous_inv_fun : continuous inv_fun . tactic.interactive.continuity')

attribute [simp, mfld_simps] model_with_corners.source_eq

/-- A vector space is a model with corners. -/
def model_with_corners_self (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] : model_with_corners 𝕜 E E :=
{ to_local_equiv := local_equiv.refl E,
  source_eq    := rfl,
  unique_diff' := unique_diff_on_univ,
  continuous_to_fun  := continuous_id,
  continuous_inv_fun := continuous_id }

localized "notation `𝓘(` 𝕜 `, ` E `)` := model_with_corners_self 𝕜 E" in manifold

localized "notation `𝓘(` 𝕜 `)` := model_with_corners_self 𝕜 𝕜" in manifold

section
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H)

namespace model_with_corners

instance : has_coe_to_fun (model_with_corners 𝕜 E H) := ⟨_, λ e, e.to_fun⟩

/-- The inverse to a model with corners, only registered as a local equiv. -/
protected def symm : local_equiv E H := I.to_local_equiv.symm

/- Register a few lemmas to make sure that `simp` puts expressions in normal form -/
@[simp, mfld_simps] lemma to_local_equiv_coe : (I.to_local_equiv : H → E) = I :=
rfl

@[simp, mfld_simps] lemma mk_coe (e : local_equiv H E) (a b c d) :
  ((model_with_corners.mk e a b c d : model_with_corners 𝕜 E H) : H → E) = (e : H → E) := rfl

@[simp, mfld_simps] lemma to_local_equiv_coe_symm : (I.to_local_equiv.symm : E → H) = I.symm := rfl

@[simp, mfld_simps] lemma mk_symm (e : local_equiv H E) (a b c d) :
  (model_with_corners.mk e a b c d : model_with_corners 𝕜 E H).symm = e.symm :=
rfl

@[continuity] protected lemma continuous : continuous I := I.continuous_to_fun

protected lemma continuous_at {x} : continuous_at I x := I.continuous.continuous_at

protected lemma continuous_within_at {s x} : continuous_within_at I s x :=
I.continuous_at.continuous_within_at

@[continuity] lemma continuous_symm : continuous I.symm := I.continuous_inv_fun

lemma continuous_at_symm {x} : continuous_at I.symm x := I.continuous_symm.continuous_at

lemma continuous_within_at_symm {s x} : continuous_within_at I.symm s x :=
I.continuous_symm.continuous_within_at

@[simp, mfld_simps] lemma target_eq : I.target = range (I : H → E) :=
by { rw [← image_univ, ← I.source_eq], exact (I.to_local_equiv.image_source_eq_target).symm }

protected lemma unique_diff : unique_diff_on 𝕜 (range I) := I.target_eq ▸ I.unique_diff'

@[simp, mfld_simps] protected lemma left_inv (x : H) : I.symm (I x) = x :=
by { refine I.left_inv' _, simp }

protected lemma left_inverse : function.left_inverse I.symm I := I.left_inv

@[simp, mfld_simps] lemma symm_comp_self : I.symm ∘ I = id :=
I.left_inverse.comp_eq_id

protected lemma right_inv_on : right_inv_on I.symm I (range I) :=
I.left_inverse.right_inv_on_range

@[simp, mfld_simps] protected lemma right_inv {x : E} (hx : x ∈ range I) : I (I.symm x) = x :=
I.right_inv_on hx

protected lemma image_eq (s : set H) : I '' s = I.symm ⁻¹' s ∩ range I :=
begin
  refine (I.to_local_equiv.image_eq_target_inter_inv_preimage _).trans _,
  { rw I.source_eq, exact subset_univ _ },
  { rw [inter_comm, I.target_eq, I.to_local_equiv_coe_symm] }
end

protected lemma closed_embedding : closed_embedding I :=
I.left_inverse.closed_embedding I.continuous_symm I.continuous

lemma closed_range : is_closed (range I) :=
I.closed_embedding.closed_range

lemma map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[range I] (I x) :=
I.closed_embedding.to_embedding.map_nhds_eq x

lemma image_mem_nhds_within {x : H} {s : set H} (hs : s ∈ 𝓝 x) :
  I '' s ∈ 𝓝[range I] (I x) :=
I.map_nhds_eq x ▸ image_mem_map hs

lemma symm_map_nhds_within_range (x : H) :
  map I.symm (𝓝[range I] (I x)) = 𝓝 x :=
by rw [← I.map_nhds_eq, map_map, I.symm_comp_self, map_id]

lemma unique_diff_preimage {s : set H} (hs : is_open s) :
  unique_diff_on 𝕜 (I.symm ⁻¹' s ∩ range I) :=
by { rw inter_comm, exact I.unique_diff.inter (hs.preimage I.continuous_inv_fun) }

lemma unique_diff_preimage_source {β : Type*} [topological_space β]
  {e : local_homeomorph H β} : unique_diff_on 𝕜 (I.symm ⁻¹' (e.source) ∩ range I) :=
I.unique_diff_preimage e.open_source

lemma unique_diff_at_image {x : H} : unique_diff_within_at 𝕜 (range I) (I x) :=
I.unique_diff _ (mem_range_self _)

protected lemma locally_compact [locally_compact_space E] (I : model_with_corners 𝕜 E H) :
  locally_compact_space H :=
begin
  have : ∀ (x : H), (𝓝 x).has_basis (λ s, s ∈ 𝓝 (I x) ∧ is_compact s)
    (λ s, I.symm '' (s ∩ range ⇑I)),
  { intro x,
    rw ← I.symm_map_nhds_within_range,
    exact ((compact_basis_nhds (I x)).inf_principal _).map _ },
  refine locally_compact_space_of_has_basis this _,
  rintro x s ⟨-, hsc⟩,
  exact (hsc.inter_right I.closed_range).image I.continuous_symm
end

open topological_space

protected lemma second_countable_topology [second_countable_topology E]
  (I : model_with_corners 𝕜 E H) : second_countable_topology H :=
I.closed_embedding.to_embedding.second_countable_topology

end model_with_corners

section
variables (𝕜 E)

/-- In the trivial model with corners, the associated local equiv is the identity. -/
@[simp, mfld_simps] lemma model_with_corners_self_local_equiv :
  (𝓘(𝕜, E)).to_local_equiv = local_equiv.refl E := rfl

@[simp, mfld_simps] lemma model_with_corners_self_coe :
  (𝓘(𝕜, E) : E → E) = id := rfl

@[simp, mfld_simps] lemma model_with_corners_self_coe_symm :
  (𝓘(𝕜, E).symm : E → E) = id := rfl

end

end

section model_with_corners_prod

/-- Given two model_with_corners `I` on `(E, H)` and `I'` on `(E', H')`, we define the model with
corners `I.prod I'` on `(E × E', model_prod H H')`. This appears in particular for the manifold
structure on the tangent bundle to a manifold modelled on `(E, H)`: it will be modelled on
`(E × E, H × E)`. See note [Manifold type tags] for explanation about `model_prod H H'`
vs `H × H'`. -/
def model_with_corners.prod
  {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
  {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H)
  {E' : Type v'} [normed_group E'] [normed_space 𝕜 E'] {H' : Type w'} [topological_space H']
  (I' : model_with_corners 𝕜 E' H') : model_with_corners 𝕜 (E × E') (model_prod H H') :=
{ to_fun := λ x, (I x.1, I' x.2),
  inv_fun := λ x, (I.symm x.1, I'.symm x.2),
  source := {x | x.1 ∈ I.source ∧ x.2 ∈ I'.source},
  source_eq    := by simp only [set_of_true] with mfld_simps,
  unique_diff' := I.unique_diff'.prod I'.unique_diff',
  continuous_to_fun := I.continuous_to_fun.prod_map I'.continuous_to_fun,
  continuous_inv_fun := I.continuous_inv_fun.prod_map I'.continuous_inv_fun,
  .. I.to_local_equiv.prod I'.to_local_equiv }

/-- Given a finite family of `model_with_corners` `I i` on `(E i, H i)`, we define the model with
corners `pi I` on `(Π i, E i, model_pi H)`. See note [Manifold type tags] for explanation about
`model_pi H`. -/
def model_with_corners.pi
  {𝕜 : Type u} [nondiscrete_normed_field 𝕜] {ι : Type v} [fintype ι]
  {E : ι → Type w} [Π i, normed_group (E i)] [Π i, normed_space 𝕜 (E i)]
  {H : ι → Type u'} [Π i, topological_space (H i)] (I : Π i, model_with_corners 𝕜 (E i) (H i)) :
  model_with_corners 𝕜 (Π i, E i) (model_pi H) :=
{ to_local_equiv := local_equiv.pi (λ i, (I i).to_local_equiv),
  source_eq := by simp only [set.pi_univ] with mfld_simps,
  unique_diff' := unique_diff_on.pi ι E _ _ (λ i _, (I i).unique_diff'),
  continuous_to_fun := continuous_pi $ λ i, (I i).continuous.comp (continuous_apply i),
  continuous_inv_fun := continuous_pi $ λ i, (I i).continuous_symm.comp (continuous_apply i) }

/-- Special case of product model with corners, which is trivial on the second factor. This shows up
as the model to tangent bundles. -/
@[reducible] def model_with_corners.tangent
  {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
  {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H) : model_with_corners 𝕜 (E × E) (model_prod H E) :=
I.prod (𝓘(𝕜, E))

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F] {F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{H : Type*} [topological_space H] {H' : Type*} [topological_space H']
{G : Type*} [topological_space G] {G' : Type*} [topological_space G']
{I : model_with_corners 𝕜 E H} {J : model_with_corners 𝕜 F G}

@[simp, mfld_simps] lemma model_with_corners_prod_to_local_equiv :
  (I.prod J).to_local_equiv = I.to_local_equiv.prod (J.to_local_equiv) :=
rfl

@[simp, mfld_simps] lemma model_with_corners_prod_coe
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') :
  (I.prod I' : _ × _ → _ × _) = prod.map I I' := rfl

@[simp, mfld_simps] lemma model_with_corners_prod_coe_symm
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H') :
  ((I.prod I').symm : _ × _ → _ × _) = prod.map I.symm I'.symm := rfl

end model_with_corners_prod

section boundaryless

/-- Property ensuring that the model with corners `I` defines manifolds without boundary. -/
class model_with_corners.boundaryless {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  (I : model_with_corners 𝕜 E H) : Prop :=
(range_eq_univ : range I = univ)

/-- The trivial model with corners has no boundary -/
instance model_with_corners_self_boundaryless (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E] : (model_with_corners_self 𝕜 E).boundaryless :=
⟨by simp⟩

/-- If two model with corners are boundaryless, their product also is -/
instance model_with_corners.range_eq_univ_prod {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
  {E : Type v} [normed_group E] [normed_space 𝕜 E] {H : Type w} [topological_space H]
  (I : model_with_corners 𝕜 E H) [I.boundaryless]
  {E' : Type v'} [normed_group E'] [normed_space 𝕜 E'] {H' : Type w'} [topological_space H']
  (I' : model_with_corners 𝕜 E' H') [I'.boundaryless] :
  (I.prod I').boundaryless :=
begin
  split,
  dsimp [model_with_corners.prod, model_prod],
  rw [← prod_range_range_eq, model_with_corners.boundaryless.range_eq_univ,
      model_with_corners.boundaryless.range_eq_univ, univ_prod_univ]
end

end boundaryless

section times_cont_diff_groupoid
/-! ### Smooth functions on models with corners -/

variables {m n : with_top ℕ} {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H]
(I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M]

variable (n)
/-- Given a model with corners `(E, H)`, we define the groupoid of `C^n` transformations of `H` as
the maps that are `C^n` when read in `E` through `I`. -/
def times_cont_diff_groupoid : structure_groupoid H :=
pregroupoid.groupoid
{ property := λf s, times_cont_diff_on 𝕜 n (I ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I),
  comp     := λf g u v hf hg hu hv huv, begin
    have : I ∘ (g ∘ f) ∘ I.symm = (I ∘ g ∘ I.symm) ∘ (I ∘ f ∘ I.symm),
      by { ext x, simp },
    rw this,
    apply times_cont_diff_on.comp hg _,
    { rintros x ⟨hx1, hx2⟩,
      simp only with mfld_simps at ⊢ hx1,
      exact hx1.2 },
    { refine hf.mono _,
      rintros x ⟨hx1, hx2⟩,
      exact ⟨hx1.1, hx2⟩ }
  end,
  id_mem   := begin
    apply times_cont_diff_on.congr (times_cont_diff_id.times_cont_diff_on),
    rintros x ⟨hx1, hx2⟩,
    rcases mem_range.1 hx2 with ⟨y, hy⟩,
    rw ← hy,
    simp only with mfld_simps,
  end,
  locality := λf u hu H, begin
    apply times_cont_diff_on_of_locally_times_cont_diff_on,
    rintros y ⟨hy1, hy2⟩,
    rcases mem_range.1 hy2 with ⟨x, hx⟩,
    rw ← hx at ⊢ hy1,
    simp only with mfld_simps at ⊢ hy1,
    rcases H x hy1 with ⟨v, v_open, xv, hv⟩,
    have : ((I.symm ⁻¹' (u ∩ v)) ∩ (range I))
        = ((I.symm ⁻¹' u) ∩ (range I) ∩ I.symm ⁻¹' v),
    { rw [preimage_inter, inter_assoc, inter_assoc],
      congr' 1,
      rw inter_comm },
    rw this at hv,
    exact ⟨I.symm ⁻¹' v, v_open.preimage I.continuous_symm, by simpa, hv⟩
  end,
  congr    := λf g u hu fg hf, begin
    apply hf.congr,
    rintros y ⟨hy1, hy2⟩,
    rcases mem_range.1 hy2 with ⟨x, hx⟩,
    rw ← hx at ⊢ hy1,
    simp only with mfld_simps at ⊢ hy1,
    rw fg _ hy1
  end }

variable {n}
/-- Inclusion of the groupoid of `C^n` local diffeos in the groupoid of `C^m` local diffeos when
`m ≤ n` -/
lemma times_cont_diff_groupoid_le (h : m ≤ n) :
  times_cont_diff_groupoid n I ≤ times_cont_diff_groupoid m I :=
begin
  rw [times_cont_diff_groupoid, times_cont_diff_groupoid],
  apply groupoid_of_pregroupoid_le,
  assume f s hfs,
  exact times_cont_diff_on.of_le hfs h
end

/-- The groupoid of `0`-times continuously differentiable maps is just the groupoid of all
local homeomorphisms -/
lemma times_cont_diff_groupoid_zero_eq :
  times_cont_diff_groupoid 0 I = continuous_groupoid H :=
begin
  apply le_antisymm le_top,
  assume u hu,
  -- we have to check that every local homeomorphism belongs to `times_cont_diff_groupoid 0 I`,
  -- by unfolding its definition
  change u ∈ times_cont_diff_groupoid 0 I,
  rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid],
  simp only [times_cont_diff_on_zero],
  split,
  { apply continuous_on.comp (@continuous.continuous_on _ _ _ _ _ univ I.continuous)
      _ (subset_univ _),
    apply continuous_on.comp u.continuous_to_fun I.continuous_symm.continuous_on
      (inter_subset_left _ _) },
  { apply continuous_on.comp (@continuous.continuous_on _ _ _ _ _ univ I.continuous)
      _ (subset_univ _),
    apply continuous_on.comp u.continuous_inv_fun I.continuous_inv_fun.continuous_on
      (inter_subset_left _ _) },
end

variable (n)
/-- An identity local homeomorphism belongs to the `C^n` groupoid. -/
lemma of_set_mem_times_cont_diff_groupoid {s : set H} (hs : is_open s) :
  local_homeomorph.of_set s hs ∈ times_cont_diff_groupoid n I :=
begin
  rw [times_cont_diff_groupoid, mem_groupoid_of_pregroupoid],
  suffices h : times_cont_diff_on 𝕜 n (I ∘ I.symm) (I.symm ⁻¹' s ∩ range I),
    by simp [h],
  have : times_cont_diff_on 𝕜 n id (univ : set E) :=
    times_cont_diff_id.times_cont_diff_on,
  exact this.congr_mono (λ x hx, by simp [hx.2]) (subset_univ _)
end

/-- The composition of a local homeomorphism from `H` to `M` and its inverse belongs to
the `C^n` groupoid. -/
lemma symm_trans_mem_times_cont_diff_groupoid (e : local_homeomorph M H) :
  e.symm.trans e ∈ times_cont_diff_groupoid n I :=
begin
  have : e.symm.trans e ≈ local_homeomorph.of_set e.target e.open_target :=
    local_homeomorph.trans_symm_self _,
  exact structure_groupoid.eq_on_source _
    (of_set_mem_times_cont_diff_groupoid n I e.open_target) this
end

variables {E' : Type*} [normed_group E'] [normed_space 𝕜 E'] {H' : Type*} [topological_space H']

/-- The product of two smooth local homeomorphisms is smooth. -/
lemma times_cont_diff_groupoid_prod
  {I : model_with_corners 𝕜 E H} {I' : model_with_corners 𝕜 E' H'}
  {e : local_homeomorph H H} {e' : local_homeomorph H' H'}
  (he : e ∈ times_cont_diff_groupoid ⊤ I) (he' : e' ∈ times_cont_diff_groupoid ⊤ I') :
  e.prod e' ∈ times_cont_diff_groupoid ⊤ (I.prod I') :=
begin
  cases he with he he_symm,
  cases he' with he' he'_symm,
  simp only at he he_symm he' he'_symm,
  split;
  simp only [local_equiv.prod_source, local_homeomorph.prod_to_local_equiv],
  { have h3 := times_cont_diff_on.prod_map he he',
    rw [← I.image_eq, ← I'.image_eq, set.prod_image_image_eq] at h3,
    rw ← (I.prod I').image_eq,
    exact h3, },
  { have h3 := times_cont_diff_on.prod_map he_symm he'_symm,
    rw [← I.image_eq, ← I'.image_eq, set.prod_image_image_eq] at h3,
    rw ← (I.prod I').image_eq,
    exact h3, }
end

/-- The `C^n` groupoid is closed under restriction. -/
instance : closed_under_restriction (times_cont_diff_groupoid n I) :=
(closed_under_restriction_iff_id_le _).mpr
begin
  apply structure_groupoid.le_iff.mpr,
  rintros e ⟨s, hs, hes⟩,
  apply (times_cont_diff_groupoid n I).eq_on_source' _ _ _ hes,
  exact of_set_mem_times_cont_diff_groupoid n I hs,
end

end times_cont_diff_groupoid

end model_with_corners

section smooth_manifold_with_corners

/-! ### Smooth manifolds with corners -/

set_option old_structure_cmd true

/-- Typeclass defining smooth manifolds with corners with respect to a model with corners, over a
field `𝕜` and with infinite smoothness to simplify typeclass search and statements later on. -/
@[ancestor has_groupoid]
class smooth_manifold_with_corners {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] extends
  has_groupoid M (times_cont_diff_groupoid ∞ I) : Prop

lemma smooth_manifold_with_corners.mk' {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M]
  [gr : has_groupoid M (times_cont_diff_groupoid ∞ I)] :
  smooth_manifold_with_corners I M := { ..gr }

lemma smooth_manifold_with_corners_of_times_cont_diff_on
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M]
  (h : ∀ (e e' : local_homeomorph M H), e ∈ atlas H M → e' ∈ atlas H M →
    times_cont_diff_on 𝕜 ⊤ (I ∘ (e.symm ≫ₕ e') ∘ I.symm)
      (I.symm ⁻¹' (e.symm ≫ₕ e').source ∩ range I)) :
  smooth_manifold_with_corners I M :=
{ compatible :=
  begin
    haveI : has_groupoid M (times_cont_diff_groupoid ∞ I) := has_groupoid_of_pregroupoid _ h,
    apply structure_groupoid.compatible,
  end }

/-- For any model with corners, the model space is a smooth manifold -/
instance model_space_smooth {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] {H : Type*} [topological_space H]
  {I : model_with_corners 𝕜 E H} :
  smooth_manifold_with_corners I H := { .. has_groupoid_model_space _ _ }

end smooth_manifold_with_corners

namespace smooth_manifold_with_corners
/- We restate in the namespace `smooth_manifolds_with_corners` some lemmas that hold for general
charted space with a structure groupoid, avoiding the need to specify the groupoid
`times_cont_diff_groupoid ∞ I` explicitly. -/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M]

/-- The maximal atlas of `M` for the smooth manifold with corners structure corresponding to the
model with corners `I`. -/
def maximal_atlas := (times_cont_diff_groupoid ∞ I).maximal_atlas M

variable {M}

lemma mem_maximal_atlas_of_mem_atlas [smooth_manifold_with_corners I M]
  {e : local_homeomorph M H} (he : e ∈ atlas H M) : e ∈ maximal_atlas I M :=
structure_groupoid.mem_maximal_atlas_of_mem_atlas _ he

lemma chart_mem_maximal_atlas [smooth_manifold_with_corners I M] (x : M) :
  chart_at H x ∈ maximal_atlas I M :=
structure_groupoid.chart_mem_maximal_atlas _ x

variable {I}

lemma compatible_of_mem_maximal_atlas
  {e e' : local_homeomorph M H} (he : e ∈ maximal_atlas I M) (he' : e' ∈ maximal_atlas I M) :
  e.symm.trans e' ∈ times_cont_diff_groupoid ∞ I :=
structure_groupoid.compatible_of_mem_maximal_atlas he he'

/-- The product of two smooth manifolds with corners is naturally a smooth manifold with corners. -/
instance prod {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  (M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M'] :
  smooth_manifold_with_corners (I.prod I') (M×M') :=
{ compatible :=
  begin
    rintros f g ⟨f1, f2, hf1, hf2, rfl⟩ ⟨g1, g2, hg1, hg2, rfl⟩,
    rw [local_homeomorph.prod_symm, local_homeomorph.prod_trans],
    have h1 := has_groupoid.compatible (times_cont_diff_groupoid ⊤ I) hf1 hg1,
    have h2 := has_groupoid.compatible (times_cont_diff_groupoid ⊤ I') hf2 hg2,
    exact times_cont_diff_groupoid_prod h1 h2,
  end }

end smooth_manifold_with_corners

lemma local_homeomorph.singleton_smooth_manifold_with_corners
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M]
  (e : local_homeomorph M H) (h : e.source = set.univ) :
  @smooth_manifold_with_corners 𝕜 _ E _ _ H _ I M _ (e.singleton_charted_space h) :=
@smooth_manifold_with_corners.mk' _ _ _ _ _ _ _ _ _ _ (id _) $
e.singleton_has_groupoid h (times_cont_diff_groupoid ∞ I)

lemma open_embedding.singleton_smooth_manifold_with_corners
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M]
  [nonempty M] {f : M → H} (h : open_embedding f) :
  @smooth_manifold_with_corners 𝕜 _ E _ _ H _ I M _ h.singleton_charted_space :=
(h.to_local_homeomorph f).singleton_smooth_manifold_with_corners I (by simp)

namespace topological_space.opens

open topological_space

variables  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  (s : opens M)

instance : smooth_manifold_with_corners I s := { ..s.has_groupoid (times_cont_diff_groupoid ∞ I) }

end topological_space.opens

section extended_charts
open_locale topological_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M] [charted_space H M]
  (x : M) {s t : set M}

/-!
### Extended charts

In a smooth manifold with corners, the model space is the space `H`. However, we will also
need to use extended charts taking values in the model vector space `E`. These extended charts are
not `local_homeomorph` as the target is not open in `E` in general, but we can still register them
as `local_equiv`.
-/

/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
@[simp, mfld_simps] def ext_chart_at (x : M) : local_equiv M E :=
(chart_at H x).to_local_equiv.trans I.to_local_equiv

lemma ext_chart_at_coe : ⇑(ext_chart_at I x) = I ∘ chart_at H x := rfl

lemma ext_chart_at_coe_symm :
  ⇑(ext_chart_at I x).symm = (chart_at H x).symm ∘ I.symm := rfl

lemma ext_chart_at_source : (ext_chart_at I x).source = (chart_at H x).source :=
by rw [ext_chart_at, local_equiv.trans_source, I.source_eq, preimage_univ, inter_univ]

lemma ext_chart_at_open_source : is_open (ext_chart_at I x).source :=
by { rw ext_chart_at_source, exact (chart_at H x).open_source }

lemma mem_ext_chart_source : x ∈ (ext_chart_at I x).source :=
by simp only [ext_chart_at_source, mem_chart_source]

lemma ext_chart_at_to_inv :
  (ext_chart_at I x).symm ((ext_chart_at I x) x) = x :=
(ext_chart_at I x).left_inv (mem_ext_chart_source I x)

lemma ext_chart_at_source_mem_nhds' {x' : M} (h : x' ∈ (ext_chart_at I x).source) :
  (ext_chart_at I x).source ∈ 𝓝 x' :=
is_open.mem_nhds (ext_chart_at_open_source I x) h

lemma ext_chart_at_source_mem_nhds : (ext_chart_at I x).source ∈ 𝓝 x :=
ext_chart_at_source_mem_nhds' I x (mem_ext_chart_source I x)

lemma ext_chart_at_source_mem_nhds_within' {x' : M} (h : x' ∈ (ext_chart_at I x).source) :
  (ext_chart_at I x).source ∈ 𝓝[s] x' :=
mem_nhds_within_of_mem_nhds (ext_chart_at_source_mem_nhds' I x h)

lemma ext_chart_at_source_mem_nhds_within :
  (ext_chart_at I x).source ∈ 𝓝[s] x :=
mem_nhds_within_of_mem_nhds (ext_chart_at_source_mem_nhds I x)

lemma ext_chart_at_continuous_on :
  continuous_on (ext_chart_at I x) (ext_chart_at I x).source :=
begin
  refine I.continuous.comp_continuous_on _,
  rw ext_chart_at_source,
  exact (chart_at H x).continuous_on
end

lemma ext_chart_at_continuous_at' {x' : M} (h : x' ∈ (ext_chart_at I x).source) :
  continuous_at (ext_chart_at I x) x' :=
(ext_chart_at_continuous_on I x).continuous_at $ ext_chart_at_source_mem_nhds' I x h

lemma ext_chart_at_continuous_at : continuous_at (ext_chart_at I x) x :=
ext_chart_at_continuous_at' _ _ (mem_ext_chart_source I x)

lemma ext_chart_at_continuous_on_symm :
  continuous_on (ext_chart_at I x).symm (ext_chart_at I x).target :=
begin
  apply continuous_on.comp (chart_at H x).continuous_on_symm I.continuous_symm.continuous_on,
  simp [ext_chart_at, local_equiv.trans_target]
end

lemma ext_chart_at_map_nhds' {x y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x) (𝓝 y) = 𝓝[range I] (ext_chart_at I x y) :=
begin
  rw [ext_chart_at_coe, (∘), ← I.map_nhds_eq, ← (chart_at H x).map_nhds_eq, map_map],
  rwa ext_chart_at_source at hy
end

lemma ext_chart_at_map_nhds :
  map (ext_chart_at I x) (𝓝 x) = 𝓝[range I] (ext_chart_at I x x) :=
ext_chart_at_map_nhds' I $ mem_ext_chart_source I x

lemma ext_chart_at_target_mem_nhds_within' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  (ext_chart_at I x).target ∈ 𝓝[range I] (ext_chart_at I x y) :=
begin
  rw [← local_equiv.image_source_eq_target, ← ext_chart_at_map_nhds' I hy],
  exact image_mem_map (ext_chart_at_source_mem_nhds' _ _ hy)
end

lemma ext_chart_at_target_mem_nhds_within :
  (ext_chart_at I x).target ∈ 𝓝[range I] (ext_chart_at I x x) :=
ext_chart_at_target_mem_nhds_within' I x (mem_ext_chart_source I x)

lemma ext_chart_at_target_subset_range : (ext_chart_at I x).target ⊆ range I :=
by simp only with mfld_simps

lemma nhds_within_ext_chart_target_eq' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  𝓝[(ext_chart_at I x).target] (ext_chart_at I x y) =
  𝓝[range I] (ext_chart_at I x y) :=
(nhds_within_mono _ (ext_chart_at_target_subset_range _ _)).antisymm $
  nhds_within_le_of_mem (ext_chart_at_target_mem_nhds_within' _ _ hy)

lemma nhds_within_ext_chart_target_eq :
  𝓝[(ext_chart_at I x).target] ((ext_chart_at I x) x) =
  𝓝[range I] ((ext_chart_at I x) x) :=
nhds_within_ext_chart_target_eq' I x (mem_ext_chart_source I x)

lemma ext_chart_continuous_at_symm'' {y : E} (h : y ∈ (ext_chart_at I x).target) :
  continuous_at (ext_chart_at I x).symm y :=
continuous_at.comp ((chart_at H x).continuous_at_symm h.2) (I.continuous_symm.continuous_at)

lemma ext_chart_continuous_at_symm' {x' : M} (h : x' ∈ (ext_chart_at I x).source) :
  continuous_at (ext_chart_at I x).symm (ext_chart_at I x x') :=
ext_chart_continuous_at_symm'' I _ $ (ext_chart_at I x).map_source h

lemma ext_chart_continuous_at_symm :
  continuous_at (ext_chart_at I x).symm ((ext_chart_at I x) x) :=
ext_chart_continuous_at_symm' I x (mem_ext_chart_source I x)

lemma ext_chart_continuous_on_symm :
  continuous_on (ext_chart_at I x).symm (ext_chart_at I x).target :=
λ y hy, (ext_chart_continuous_at_symm'' _ _ hy).continuous_within_at

lemma ext_chart_preimage_open_of_open' {s : set E} (hs : is_open s) :
  is_open ((ext_chart_at I x).source ∩ ext_chart_at I x ⁻¹' s) :=
(ext_chart_at_continuous_on I x).preimage_open_of_open (ext_chart_at_open_source _ _) hs

lemma ext_chart_preimage_open_of_open {s : set E} (hs : is_open s) :
  is_open ((chart_at H x).source ∩ ext_chart_at I x ⁻¹' s) :=
by { rw ← ext_chart_at_source I, exact ext_chart_preimage_open_of_open' I x hs }

lemma ext_chart_at_map_nhds_within_eq_image' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x) (𝓝[s] y) =
    𝓝[ext_chart_at I x '' ((ext_chart_at I x).source ∩ s)] (ext_chart_at I x y) :=
by set e := ext_chart_at I x;
calc map e (𝓝[s] y) = map e (𝓝[e.source ∩ s] y) :
  congr_arg (map e) (nhds_within_inter_of_mem (ext_chart_at_source_mem_nhds_within' I x hy)).symm
... = 𝓝[e '' (e.source ∩ s)] (e y) :
  ((ext_chart_at I x).left_inv_on.mono $ inter_subset_left _ _).map_nhds_within_eq
    ((ext_chart_at I x).left_inv hy)
    (ext_chart_continuous_at_symm' I x hy).continuous_within_at
    (ext_chart_at_continuous_at' I x hy).continuous_within_at

lemma ext_chart_at_map_nhds_within_eq_image :
  map (ext_chart_at I x) (𝓝[s] x) =
    𝓝[ext_chart_at I x '' ((ext_chart_at I x).source ∩ s)] (ext_chart_at I x x) :=
ext_chart_at_map_nhds_within_eq_image' I x (mem_ext_chart_source I x)

lemma ext_chart_at_map_nhds_within' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x) (𝓝[s] y) =
    𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] (ext_chart_at I x y) :=
by rw [ext_chart_at_map_nhds_within_eq_image' I x hy, nhds_within_inter,
  ← nhds_within_ext_chart_target_eq' _ _ hy, ← nhds_within_inter,
  (ext_chart_at I x).image_source_inter_eq', inter_comm]

lemma ext_chart_at_map_nhds_within :
  map (ext_chart_at I x) (𝓝[s] x) =
    𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] (ext_chart_at I x x) :=
ext_chart_at_map_nhds_within' I x (mem_ext_chart_source I x)

lemma ext_chart_at_symm_map_nhds_within' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x).symm
    (𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] (ext_chart_at I x y)) = 𝓝[s] y :=
begin
  rw [← ext_chart_at_map_nhds_within' I x hy, map_map, map_congr, map_id],
  exact (ext_chart_at I x).left_inv_on.eq_on.eventually_eq_of_mem
    (ext_chart_at_source_mem_nhds_within' _ _ hy)
end

lemma ext_chart_at_symm_map_nhds_within_range' {y : M} (hy : y ∈ (ext_chart_at I x).source) :
  map (ext_chart_at I x).symm (𝓝[range I] (ext_chart_at I x y)) = 𝓝 y :=
by rw [← nhds_within_univ, ← ext_chart_at_symm_map_nhds_within' I x hy, preimage_univ, univ_inter]

lemma ext_chart_at_symm_map_nhds_within :
  map (ext_chart_at I x).symm
    (𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] (ext_chart_at I x x)) = 𝓝[s] x :=
ext_chart_at_symm_map_nhds_within' I x (mem_ext_chart_source I x)

lemma ext_chart_at_symm_map_nhds_within_range :
  map (ext_chart_at I x).symm (𝓝[range I] (ext_chart_at I x x)) = 𝓝 x :=
ext_chart_at_symm_map_nhds_within_range' I x (mem_ext_chart_source I x)

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
lemma ext_chart_preimage_mem_nhds_within' {x' : M} (h : x' ∈ (ext_chart_at I x).source)
  (ht : t ∈ 𝓝[s] x') :
  (ext_chart_at I x).symm ⁻¹' t ∈
    𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] ((ext_chart_at I x) x') :=
by rwa [← ext_chart_at_symm_map_nhds_within' I x h, mem_map] at ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of the
base point is a neighborhood of the preimage, within a set. -/
lemma ext_chart_preimage_mem_nhds_within (ht : t ∈ 𝓝[s] x) :
  (ext_chart_at I x).symm ⁻¹' t ∈
    𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] ((ext_chart_at I x) x) :=
ext_chart_preimage_mem_nhds_within' I x (mem_ext_chart_source I x) ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
is a neighborhood of the preimage. -/
lemma ext_chart_preimage_mem_nhds (ht : t ∈ 𝓝 x) :
  (ext_chart_at I x).symm ⁻¹' t ∈ 𝓝 ((ext_chart_at I x) x) :=
begin
  apply (ext_chart_continuous_at_symm I x).preimage_mem_nhds,
  rwa (ext_chart_at I x).left_inv (mem_ext_chart_source _ _)
end

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
lemma ext_chart_preimage_inter_eq :
  ((ext_chart_at I x).symm ⁻¹' (s ∩ t) ∩ range I)
  = ((ext_chart_at I x).symm ⁻¹' s ∩ range I) ∩ ((ext_chart_at I x).symm ⁻¹' t) :=
by mfld_set_tac

end extended_charts

/-- In the case of the manifold structure on a vector space, the extended charts are just the
identity.-/
lemma ext_chart_model_space_eq_id (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (x : E) :
  ext_chart_at (model_with_corners_self 𝕜 E) x = local_equiv.refl E :=
by simp only with mfld_simps
