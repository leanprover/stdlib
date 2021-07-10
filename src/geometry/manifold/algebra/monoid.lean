/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/

import geometry.manifold.times_cont_mdiff_map

/-!
# Smooth monoid
A smooth monoid is a monoid that is also a smooth manifold, in which multiplication is a smooth map
of the product manifold `G` × `G` into `G`.

In this file we define the basic structures to talk about smooth monoids: `has_smooth_mul` and its
additive counterpart `has_smooth_add`. These structures are general enough to also talk about smooth
semigroups.
-/

open_locale manifold

section

set_option old_structure_cmd true

/--
1. All smooth algebraic structures on `G` are `Prop`-valued classes that extend
`smooth_manifold_with_corners I G`. This way we save users from adding both
`[smooth_manifold_with_corners I G]` and `[has_smooth_mul I G]` to the assumptions. While many API
lemmas hold true without the `smooth_manifold_with_corners I G` assumption, we're not aware of a
mathematically interesting monoid on a topological manifold such that (a) the space is not a
`smooth_manifold_with_corners`; (b) the multiplication is smooth at `(a, b)` in the charts
`ext_chart_at I a`, `ext_chart_at I b`, `ext_chart_at I (a * b)`.

2. Because of `model_prod` we can't assume, e.g., that a `lie_group` is modelled on `𝓘(𝕜, E)`. So,
we formulate the definitions and lemmas for any model.

3. While smoothness of an operation implies its continuity, lemmas like
`has_continuous_mul_of_smooth` can't be instances becausen otherwise Lean would have to search for
`has_smooth_mul I G` with unknown `𝕜`, `E`, `H`, and `I : model_with_corners 𝕜 E H`. If users needs
`[has_continuous_mul G]` in a proof about a smooth monoid, then they need to either add
`[has_continuous_mul G]` as an assumption (worse) or use `haveI` in the proof (better). -/
library_note "Design choices about smooth algebraic structures"

/-- Basic hypothesis to talk about a smooth (Lie) additive monoid or a smooth additive
semigroup. A smooth additive monoid over `α`, for example, is obtained by requiring both the
instances `add_monoid α` and `has_smooth_add α`. -/
-- See note [Design choices about smooth algebraic structures]
@[ancestor smooth_manifold_with_corners]
class has_smooth_add {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [has_add G] [topological_space G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
(smooth_add : smooth (I.prod I) I (λ p : G×G, p.1 + p.2))

/-- Basic hypothesis to talk about a smooth (Lie) monoid or a smooth semigroup.
A smooth monoid over `G`, for example, is obtained by requiring both the instances `monoid G`
and `has_smooth_mul I G`. -/
-- See note [Design choices about smooth algebraic structures]
@[ancestor smooth_manifold_with_corners, to_additive]
class has_smooth_mul {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {H : Type*} [topological_space H]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] (I : model_with_corners 𝕜 E H)
  (G : Type*) [has_mul G] [topological_space G] [charted_space H G]
  extends smooth_manifold_with_corners I G : Prop :=
(smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2))

end

section has_smooth_mul

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{G : Type*} [has_mul G] [topological_space G] [charted_space H G] [has_smooth_mul I G]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H' M]

section

variables (I)

@[to_additive]
lemma smooth_mul : smooth (I.prod I) I (λ p : G×G, p.1 * p.2) :=
has_smooth_mul.smooth_mul

/-- If the multiplication is smooth, then it is continuous. This is not an instance for technical
reasons, see note [Design choices about smooth algebraic structures]. -/
@[to_additive
"If the addition is smooth, then it is continuous. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]."]
lemma has_continuous_mul_of_smooth : has_continuous_mul G :=
⟨(smooth_mul I).continuous⟩

end

@[to_additive]
lemma smooth.mul {f : M → G} {g : M → G} (hf : smooth I' I f) (hg : smooth I' I g) :
  smooth I' I (f * g) :=
(smooth_mul I).comp (hf.prod_mk hg)

@[to_additive]
lemma smooth_mul_left {a : G} : smooth I I (λ b : G, a * b) :=
smooth_const.mul smooth_id

@[to_additive]
lemma smooth_mul_right {a : G} : smooth I I (λ b : G, b * a) :=
smooth_id.mul smooth_const

@[to_additive]
lemma smooth_on.mul {f : M → G} {g : M → G} {s : set M}
  (hf : smooth_on I' I f s) (hg : smooth_on I' I g s) :
  smooth_on I' I (f * g) s :=
((smooth_mul I).comp_smooth_on (hf.prod_mk hg) : _)

variables (I) (g h : G)

/-- Left multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smooth_left_mul` with the notation `𝑳` usually use `L` instead of `𝑳` in the
names. -/
def smooth_left_mul : C^∞⟮I, G; I, G⟯ := ⟨(left_mul g), smooth_mul_left⟩

/-- Right multiplication by `g`. It is meant to mimic the usual notation in Lie groups.
Lemmas involving `smooth_right_mul` with the notation `𝑹` usually use `R` instead of `𝑹` in the
names. -/
def smooth_right_mul : C^∞⟮I, G; I, G⟯ := ⟨(right_mul g), smooth_mul_right⟩

/- Left multiplication. The abbreviation is `MIL`. -/
localized "notation `𝑳` := smooth_left_mul" in lie_group

/- Right multiplication. The abbreviation is `MIR`. -/
localized "notation `𝑹` := smooth_right_mul" in lie_group

open_locale lie_group

@[simp] lemma L_apply : (𝑳 I g) h = g * h := rfl
@[simp] lemma R_apply : (𝑹 I g) h = h * g := rfl

@[simp] lemma L_mul {G : Type*} [semigroup G] [topological_space G] [charted_space H G]
  [has_smooth_mul I G] (g h : G) : 𝑳 I (g * h) = (𝑳 I g).comp (𝑳 I h) :=
by { ext, simp only [times_cont_mdiff_map.comp_apply, L_apply, mul_assoc] }

@[simp] lemma R_mul {G : Type*} [semigroup G] [topological_space G] [charted_space H G]
  [has_smooth_mul I G] (g h : G) : 𝑹 I (g * h) = (𝑹 I h).comp (𝑹 I g) :=
by { ext, simp only [times_cont_mdiff_map.comp_apply, R_apply, mul_assoc] }

section

variables {G' : Type*} [monoid G'] [topological_space G'] [charted_space H G']
  [has_smooth_mul I G'] (g' : G')

lemma smooth_left_mul_one : (𝑳 I g') 1 = g' := mul_one g'
lemma smooth_right_mul_one : (𝑹 I g') 1 = g' := one_mul g'

end

/- Instance of product -/
@[to_additive]
instance has_smooth_mul.prod {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  (G : Type*) [topological_space G] [charted_space H G]
  [has_mul G] [has_smooth_mul I G]
  {E' : Type*} [normed_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
  (G' : Type*) [topological_space G'] [charted_space H' G']
  [has_mul G'] [has_smooth_mul I' G'] :
  has_smooth_mul (I.prod I') (G×G') :=
{ smooth_mul := ((smooth_fst.comp smooth_fst).smooth.mul (smooth_fst.comp smooth_snd)).prod_mk
    ((smooth_snd.comp smooth_fst).smooth.mul (smooth_snd.comp smooth_snd)),
  .. smooth_manifold_with_corners.prod G G' }

end has_smooth_mul

section monoid

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{G : Type*} [monoid G] [topological_space G] [charted_space H G] [has_smooth_mul I G]
{H' : Type*} [topological_space H']
{E' : Type*} [normed_group E'] [normed_space 𝕜 E'] {I' : model_with_corners 𝕜 E' H'}
{G' : Type*} [monoid G'] [topological_space G'] [charted_space H' G'] [has_smooth_mul I' G']

lemma smooth_pow : ∀ n : ℕ, smooth I I (λ a : G, a ^ n)
| 0 := by { simp only [pow_zero], exact smooth_const }
| (k+1) := by simpa [pow_succ] using smooth_id.mul (smooth_pow _)

/-- Morphism of additive smooth monoids. -/
structure smooth_add_monoid_morphism
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
  (G : Type*) [topological_space G] [charted_space H G] [add_monoid G] [has_smooth_add I G]
  (G' : Type*) [topological_space G'] [charted_space H' G'] [add_monoid G'] [has_smooth_add I' G']
  extends G →+ G' :=
(smooth_to_fun : smooth I I' to_fun)

/-- Morphism of smooth monoids. -/
@[to_additive] structure smooth_monoid_morphism
  (I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
  (G : Type*) [topological_space G] [charted_space H G] [monoid G] [has_smooth_mul I G]
  (G' : Type*) [topological_space G'] [charted_space H' G'] [monoid G'] [has_smooth_mul I' G']
  extends G →* G' :=
(smooth_to_fun : smooth I I' to_fun)

@[to_additive]
instance : has_one (smooth_monoid_morphism I I' G G') :=
⟨{ smooth_to_fun := smooth_const, to_monoid_hom := 1 }⟩

@[to_additive]
instance : inhabited (smooth_monoid_morphism I I' G G') := ⟨1⟩

@[to_additive]
instance : has_coe_to_fun (smooth_monoid_morphism I I' G G') := ⟨_, λ a, a.to_fun⟩

end monoid

section comm_monoid

open_locale big_operators

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{H : Type*} [topological_space H]
{E : Type*} [normed_group E] [normed_space 𝕜 E] {I : model_with_corners 𝕜 E H}
{G : Type*} [comm_monoid G] [topological_space G] [charted_space H G] [has_smooth_mul I G]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M : Type*} [topological_space M] [charted_space H' M]

@[to_additive]
lemma smooth_finset_prod' {ι} {s : finset ι} {f : ι → M → G} (h : ∀ i ∈ s, smooth I' I (f i)) :
  smooth I' I (∏ i in s, f i) :=
finset.prod_induction _ _ (λ f g hf hg, hf.mul hg)
  (@smooth_const _ _ _ _ _ _ _ I' _ _ _ _ _ _ _ _ I _ _ _ 1) h

@[to_additive]
lemma smooth_finset_prod {ι} {s : finset ι} {f : ι → M → G} (h : ∀ i ∈ s, smooth I' I (f i)) :
  smooth I' I (λ x, ∏ i in s, f i x) :=
by { simp only [← finset.prod_apply], exact smooth_finset_prod' h }

open function filter

@[to_additive]
lemma smooth_finprod {ι} {f : ι → M → G} (h : ∀ i, smooth I' I (f i))
  (hfin : locally_finite (λ i, mul_support (f i))) :
  smooth I' I (λ x, ∏ᶠ i, f i x) :=
begin
  intro x,
  rcases hfin x with ⟨U, hxU, hUf⟩,
  have : smooth_at I' I (λ x, ∏ i in hUf.to_finset, f i x) x,
    from smooth_finset_prod (λ i hi, h i) x,
  refine this.congr_of_eventually_eq (mem_sets_of_superset hxU $ λ y hy, _),
  refine finprod_eq_prod_of_mul_support_subset _ (λ i hi, _),
  rw [hUf.coe_to_finset],
  exact ⟨y, hi, hy⟩
end

@[to_additive]
lemma smooth_finprod_cond {ι} {f : ι → M → G} {p : ι → Prop} (hc : ∀ i, p i → smooth I' I (f i))
  (hf : locally_finite (λ i, mul_support (f i))) :
  smooth I' I (λ x, ∏ᶠ i (hi : p i), f i x) :=
begin
  simp only [← finprod_subtype_eq_finprod_cond],
  exact smooth_finprod (λ i, hc i i.2) (hf.comp_injective subtype.coe_injective)
end

end comm_monoid
