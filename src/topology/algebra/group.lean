/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/

import order.filter.pointwise
import group_theory.quotient_group
import topology.algebra.monoid
import topology.homeomorph

/-!
# Theory of topological groups

This file defines the following typeclasses:

* `topological_group`, `topological_add_group`: multiplicative and additive topological groups,
  i.e., groups with continuous `(*)` and `(⁻¹)` / `(+)` and `(-)`;

* `has_continuous_sub G` means that `G` has a continuous subtraction operation.

There is an instance deducing `has_continuous_sub` from `topological_group` but we use a separate
typeclass because, e.g., `ℕ` and `ℝ≥0` have continuous subtraction but are not additive groups.

We also define `homeomorph` versions of several `equiv`s: `homeomorph.mul_left`,
`homeomorph.mul_right`, `homeomorph.inv`, and prove a few facts about neighbourhood filters in
groups.

## Tags

topological space, group, topological group
-/

open classical set filter topological_space function
open_locale classical topological_space filter

universes u v w x
variables {α : Type u} {β : Type v} {G : Type w} {H : Type x}

section continuous_mul_group

/-!
### Groups with continuous multiplication

In this section we prove a few statements about groups with continuous `(*)`.
-/

variables [topological_space G] [group G] [has_continuous_mul G]

/-- Multiplication from the left in a topological group as a homeomorphism. -/
@[to_additive "Addition from the left in a topological additive group as a homeomorphism."]
protected def homeomorph.mul_left (a : G) : G ≃ₜ G :=
{ continuous_to_fun  := continuous_const.mul continuous_id,
  continuous_inv_fun := continuous_const.mul continuous_id,
  .. equiv.mul_left a }

@[simp, to_additive]
lemma homeomorph.coe_mul_left (a : G) : ⇑(homeomorph.mul_left a) = (*) a := rfl

@[to_additive]
lemma homeomorph.mul_left_symm (a : G) : (homeomorph.mul_left a).symm = homeomorph.mul_left a⁻¹ :=
by { ext, refl }

@[to_additive]
lemma is_open_map_mul_left (a : G) : is_open_map (λ x, a * x) :=
(homeomorph.mul_left a).is_open_map

@[to_additive]
lemma is_closed_map_mul_left (a : G) : is_closed_map (λ x, a * x) :=
(homeomorph.mul_left a).is_closed_map

/-- Multiplication from the right in a topological group as a homeomorphism. -/
@[to_additive "Addition from the right in a topological additive group as a homeomorphism."]
protected def homeomorph.mul_right (a : G) :
  G ≃ₜ G :=
{ continuous_to_fun  := continuous_id.mul continuous_const,
  continuous_inv_fun := continuous_id.mul continuous_const,
  .. equiv.mul_right a }

@[to_additive]
lemma is_open_map_mul_right (a : G) : is_open_map (λ x, x * a) :=
(homeomorph.mul_right a).is_open_map

@[to_additive]
lemma is_closed_map_mul_right (a : G) : is_closed_map (λ x, x * a) :=
(homeomorph.mul_right a).is_closed_map

@[to_additive]
lemma is_open_map_div_right (a : G) : is_open_map (λ x, x / a) :=
by simpa only [div_eq_mul_inv] using is_open_map_mul_right (a⁻¹)

@[to_additive]
lemma is_closed_map_div_right (a : G) : is_closed_map (λ x, x / a) :=
by simpa only [div_eq_mul_inv] using is_closed_map_mul_right (a⁻¹)

@[to_additive]
lemma discrete_topology_of_open_singleton_one (h : is_open ({1} : set G)) : discrete_topology G :=
begin
  rw ← singletons_open_iff_discrete,
  intro g,
  suffices : {g} = (λ (x : G), g⁻¹ * x) ⁻¹' {1},
  { rw this, exact (continuous_mul_left (g⁻¹)).is_open_preimage _ h, },
  simp only [mul_one, set.preimage_mul_left_singleton, eq_self_iff_true,
    inv_inv, set.singleton_eq_singleton_iff],
end
end continuous_mul_group

section topological_group

/-!
### Topological groups

A topological group is a group in which the multiplication and inversion operations are
continuous. Topological additive groups are defined in the same way. Equivalently, we can require
that the division operation `λ x y, x * y⁻¹` (resp., subtraction) is continuous.
-/

/-- A topological (additive) group is a group in which the addition and negation operations are
continuous. -/
class topological_add_group (G : Type u) [topological_space G] [add_group G]
  extends has_continuous_add G : Prop :=
(continuous_neg : continuous (λa:G, -a))

/-- A topological group is a group in which the multiplication and inversion operations are
continuous. -/
@[to_additive]
class topological_group (G : Type*) [topological_space G] [group G]
  extends has_continuous_mul G : Prop :=
(continuous_inv : continuous (has_inv.inv : G → G))

variables [topological_space G] [group G] [topological_group G]

export topological_group (continuous_inv)
export topological_add_group (continuous_neg)

@[to_additive]
lemma continuous_on_inv {s : set G} : continuous_on has_inv.inv s :=
continuous_inv.continuous_on

@[to_additive]
lemma continuous_within_at_inv {s : set G} {x : G} : continuous_within_at has_inv.inv s x :=
continuous_inv.continuous_within_at

@[to_additive]
lemma continuous_at_inv {x : G} : continuous_at has_inv.inv x :=
continuous_inv.continuous_at

@[to_additive]
lemma tendsto_inv (a : G) : tendsto has_inv.inv (𝓝 a) (𝓝 (a⁻¹)) :=
continuous_at_inv

/-- If a function converges to a value in a multiplicative topological group, then its inverse
converges to the inverse of this value. For the version in normed fields assuming additionally
that the limit is nonzero, use `tendsto.inv'`. -/
@[to_additive]
lemma filter.tendsto.inv {f : α → G} {l : filter α} {y : G} (h : tendsto f l (𝓝 y)) :
  tendsto (λ x, (f x)⁻¹) l (𝓝 y⁻¹) :=
(continuous_inv.tendsto y).comp h

variables [topological_space α] {f : α → G} {s : set α} {x : α}

@[continuity, to_additive]
lemma continuous.inv (hf : continuous f) : continuous (λx, (f x)⁻¹) :=
continuous_inv.comp hf

attribute [continuity] continuous.neg -- TODO

@[to_additive]
lemma continuous_on.inv (hf : continuous_on f s) : continuous_on (λx, (f x)⁻¹) s :=
continuous_inv.comp_continuous_on hf

@[to_additive]
lemma continuous_within_at.inv (hf : continuous_within_at f s x) :
  continuous_within_at (λ x, (f x)⁻¹) s x :=
hf.inv

@[instance, to_additive]
instance [topological_space H] [group H] [topological_group H] :
  topological_group (G × H) :=
{ continuous_inv := continuous_inv.prod_map continuous_inv }

variable (G)

/-- Inversion in a topological group as a homeomorphism. -/
@[to_additive "Negation in a topological group as a homeomorphism."]
protected def homeomorph.inv : G ≃ₜ G :=
{ continuous_to_fun  := continuous_inv,
  continuous_inv_fun := continuous_inv,
  .. equiv.inv G }

@[to_additive]
lemma nhds_one_symm : comap has_inv.inv (𝓝 (1 : G)) = 𝓝 (1 : G) :=
((homeomorph.inv G).comap_nhds_eq _).trans (congr_arg nhds one_inv)

/-- The map `(x, y) ↦ (x, xy)` as a homeomorphism. This is a shear mapping. -/
@[to_additive "The map `(x, y) ↦ (x, x + y)` as a homeomorphism.
This is a shear mapping."]
protected def homeomorph.shear_mul_right : G × G ≃ₜ G × G :=
{ continuous_to_fun  := continuous_fst.prod_mk continuous_mul,
  continuous_inv_fun := continuous_fst.prod_mk $ continuous_fst.inv.mul continuous_snd,
  .. equiv.prod_shear (equiv.refl _) equiv.mul_left }

@[simp, to_additive]
lemma homeomorph.shear_mul_right_coe :
  ⇑(homeomorph.shear_mul_right G) = λ z : G × G, (z.1, z.1 * z.2) :=
rfl

@[simp, to_additive]
lemma homeomorph.shear_mul_right_symm_coe :
  ⇑(homeomorph.shear_mul_right G).symm = λ z : G × G, (z.1, z.1⁻¹ * z.2) :=
rfl

variable {G}

@[to_additive]
lemma inv_closure (s : set G) : (closure s)⁻¹ = closure s⁻¹ :=
(homeomorph.inv G).preimage_closure s

@[to_additive exists_nhds_half_neg]
lemma exists_nhds_split_inv {s : set G} (hs : s ∈ 𝓝 (1 : G)) :
  ∃ V ∈ 𝓝 (1 : G), ∀ (v ∈ V) (w ∈ V), v / w ∈ s :=
have ((λp : G × G, p.1 * p.2⁻¹) ⁻¹' s) ∈ 𝓝 ((1, 1) : G × G),
  from continuous_at_fst.mul continuous_at_snd.inv (by simpa),
by simpa only [div_eq_mul_inv, nhds_prod_eq, mem_prod_self_iff, prod_subset_iff, mem_preimage]
  using this

@[to_additive]
lemma nhds_translation_mul_inv (x : G) : comap (λ y : G, y * x⁻¹) (𝓝 1) = 𝓝 x :=
((homeomorph.mul_right x⁻¹).comap_nhds_eq 1).trans $ show 𝓝 (1 * x⁻¹⁻¹) = 𝓝 x, by simp

@[simp, to_additive] lemma map_mul_left_nhds (x y : G) : map ((*) x) (𝓝 y) = 𝓝 (x * y) :=
(homeomorph.mul_left x).map_nhds_eq y

@[to_additive] lemma map_mul_left_nhds_one (x : G) : map ((*) x) (𝓝 1) = 𝓝 x := by simp

@[to_additive]
lemma topological_group.ext {G : Type*} [group G] {t t' : topological_space G}
  (tg : @topological_group G t _) (tg' : @topological_group G t' _)
  (h : @nhds G t 1 = @nhds G t' 1) : t = t' :=
eq_of_nhds_eq_nhds $ λ x, by
  rw [← @nhds_translation_mul_inv G t _ _ x , ← @nhds_translation_mul_inv G t' _ _ x , ← h]

/-- The topological closure of a subgroup as a subgroup. -/
@[to_additive "The topological closure of an additive subgroup as an additive subgroup."]
def subgroup.topological_closure (H : subgroup G) : subgroup G :=
{ carrier := closure H,
  one_mem' := subset_closure H.one_mem,
  mul_mem' := λ a b ha hb, H.to_submonoid.top_closure_mul_self_subset ⟨a, b, ha, hb, rfl⟩,
  inv_mem' := begin
    change closure (H : set G) ⊆ (λ x : G, x⁻¹) ⁻¹' (closure H),
    conv_rhs { rw show (H : set G) = (λ x : G, x⁻¹) '' H, by ext ; simp },
    exact closure_subset_preimage_closure_image (continuous_inv : continuous (λ x : G, _)),
  end }

@[to_additive]
lemma topological_group.of_nhds_aux {G : Type*} [group G] [topological_space G]
  (hinv : tendsto (λ (x : G), x⁻¹) (𝓝 1) (𝓝 1))
  (hleft : ∀ (x₀ : G), 𝓝 x₀ = map (λ (x : G), x₀ * x) (𝓝 1))
  (hconj : ∀ (x₀ : G), map (λ (x : G), x₀ * x * x₀⁻¹) (𝓝 1) ≤ 𝓝 1) : continuous (λ x : G, x⁻¹) :=
begin
  rw continuous_iff_continuous_at,
  rintros x₀,
  have key : (λ x, (x₀*x)⁻¹) = (λ x, x₀⁻¹*x) ∘ (λ x, x₀*x*x₀⁻¹) ∘ (λ x, x⁻¹),
    by {ext ; simp[mul_assoc] },
  calc map (λ x, x⁻¹) (𝓝 x₀)
      = map (λ x, x⁻¹) (map (λ x, x₀*x) $ 𝓝 1) : by rw hleft
  ... = map (λ x, (x₀*x)⁻¹) (𝓝 1) : by rw filter.map_map
  ... = map (((λ x, x₀⁻¹*x) ∘ (λ x, x₀*x*x₀⁻¹)) ∘ (λ x, x⁻¹)) (𝓝 1) : by rw key
  ... = map ((λ x, x₀⁻¹*x) ∘ (λ x, x₀*x*x₀⁻¹)) _ : by rw ← filter.map_map
  ... ≤ map ((λ x, x₀⁻¹ * x) ∘ λ x, x₀ * x * x₀⁻¹) (𝓝 1) : map_mono hinv
  ... = map (λ x, x₀⁻¹ * x) (map (λ x, x₀ * x * x₀⁻¹) (𝓝 1)) : filter.map_map
  ... ≤ map (λ x, x₀⁻¹ * x) (𝓝 1) : map_mono (hconj x₀)
  ... = 𝓝 x₀⁻¹ : (hleft _).symm
end

@[to_additive]
lemma topological_group.of_nhds_one' {G : Type*} [group G] [topological_space G]
  (hmul : tendsto (uncurry ((*) : G → G → G)) ((𝓝 1) ×ᶠ 𝓝 1) (𝓝 1))
  (hinv : tendsto (λ x : G, x⁻¹) (𝓝 1) (𝓝 1))
  (hleft : ∀ x₀ : G, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1))
  (hright : ∀ x₀ : G, 𝓝 x₀ = map (λ x, x*x₀) (𝓝 1)) : topological_group G :=
begin
  refine { continuous_mul := (has_continuous_mul.of_nhds_one hmul hleft hright).continuous_mul,
           continuous_inv := topological_group.of_nhds_aux hinv hleft _ },
  intros x₀,
  suffices : map (λ (x : G), x₀ * x * x₀⁻¹) (𝓝 1) = 𝓝 1, by simp [this, le_refl],
  rw [show (λ x, x₀ * x * x₀⁻¹) = (λ x, x₀ * x) ∘ λ x, x*x₀⁻¹, by {ext, simp [mul_assoc] },
      ← filter.map_map, ← hright, hleft x₀⁻¹, filter.map_map],
  convert map_id,
  ext,
  simp
end

@[to_additive]
lemma topological_group.of_nhds_one {G : Type u} [group G] [topological_space G]
  (hmul : tendsto (uncurry ((*) : G → G → G)) ((𝓝 1) ×ᶠ 𝓝 1) (𝓝 1))
  (hinv : tendsto (λ x : G, x⁻¹) (𝓝 1) (𝓝 1))
  (hleft : ∀ x₀ : G, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1))
  (hconj : ∀ x₀ : G, tendsto (λ x, x₀*x*x₀⁻¹) (𝓝 1) (𝓝 1)) : topological_group G :=
 { continuous_mul := begin
    rw continuous_iff_continuous_at,
    rintros ⟨x₀, y₀⟩,
    have key : (λ (p : G × G), x₀ * p.1 * (y₀ * p.2)) =
      ((λ x, x₀*y₀*x) ∘ (uncurry (*)) ∘ (prod.map (λ x, y₀⁻¹*x*y₀) id)),
      by { ext, simp [uncurry, prod.map, mul_assoc] },
    specialize hconj y₀⁻¹, rw inv_inv at hconj,
    calc map (λ (p : G × G), p.1 * p.2) (𝓝 (x₀, y₀))
        = map (λ (p : G × G), p.1 * p.2) ((𝓝 x₀) ×ᶠ 𝓝 y₀)
            : by rw nhds_prod_eq
    ... = map (λ (p : G × G), x₀ * p.1 * (y₀ * p.2)) ((𝓝 1) ×ᶠ (𝓝 1))
            : by rw [hleft x₀, hleft y₀, prod_map_map_eq, filter.map_map]
    ... = map (((λ x, x₀*y₀*x) ∘ (uncurry (*))) ∘ (prod.map (λ x, y₀⁻¹*x*y₀) id))((𝓝 1) ×ᶠ (𝓝 1))
            : by rw key
    ... = map ((λ x, x₀*y₀*x) ∘ (uncurry (*))) ((map  (λ x, y₀⁻¹*x*y₀) $ 𝓝 1) ×ᶠ (𝓝 1))
            : by rw [← filter.map_map, ← prod_map_map_eq', map_id]
    ... ≤ map ((λ x, x₀*y₀*x) ∘ (uncurry (*))) ((𝓝 1) ×ᶠ (𝓝 1))
            : map_mono (filter.prod_mono hconj $ le_refl _)
    ... = map (λ x, x₀*y₀*x) (map (uncurry (*)) ((𝓝 1) ×ᶠ (𝓝 1)))   : by rw filter.map_map
    ... ≤ map (λ x, x₀*y₀*x) (𝓝 1)   : map_mono hmul
    ... = 𝓝 (x₀*y₀)   : (hleft _).symm
  end,
  continuous_inv := topological_group.of_nhds_aux hinv hleft hconj}

@[to_additive]
lemma topological_group.of_comm_of_nhds_one {G : Type*} [comm_group G] [topological_space G]
  (hmul : tendsto (uncurry ((*) : G → G → G)) ((𝓝 1) ×ᶠ 𝓝 1) (𝓝 1))
  (hinv : tendsto (λ x : G, x⁻¹) (𝓝 1) (𝓝 1))
  (hleft : ∀ x₀ : G, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1)) : topological_group G :=
topological_group.of_nhds_one hmul hinv hleft (by simpa using tendsto_id)

end topological_group

section quotient_topological_group
variables [topological_space G] [group G] [topological_group G] (N : subgroup G) (n : N.normal)

@[to_additive]
instance {G : Type*} [group G] [topological_space G] (N : subgroup G) :
  topological_space (quotient_group.quotient N) :=
quotient.topological_space

open quotient_group

@[to_additive]
lemma quotient_group.is_open_map_coe : is_open_map (coe : G →  quotient N) :=
begin
  intros s s_op,
  change is_open ((coe : G →  quotient N) ⁻¹' (coe '' s)),
  rw quotient_group.preimage_image_coe N s,
  exact is_open_Union (λ n, is_open_map_mul_right n s s_op)
end

@[to_additive]
instance topological_group_quotient [N.normal] : topological_group (quotient N) :=
{ continuous_mul := begin
    have cont : continuous ((coe : G → quotient N) ∘ (λ (p : G × G), p.fst * p.snd)) :=
      continuous_quot_mk.comp continuous_mul,
    have quot : quotient_map (λ p : G × G, ((p.1:quotient N), (p.2:quotient N))),
    { apply is_open_map.to_quotient_map,
      { exact (quotient_group.is_open_map_coe N).prod (quotient_group.is_open_map_coe N) },
      { exact continuous_quot_mk.prod_map continuous_quot_mk },
      { exact (surjective_quot_mk _).prod_map (surjective_quot_mk _) } },
    exact (quotient_map.continuous_iff quot).2 cont,
  end,
  continuous_inv := begin
    have : continuous ((coe : G → quotient N) ∘ (λ (a : G), a⁻¹)) :=
      continuous_quot_mk.comp continuous_inv,
    convert continuous_quotient_lift _ this,
  end }

attribute [instance] topological_add_group_quotient

end quotient_topological_group

/-- A typeclass saying that `λ p : G × G, p.1 - p.2` is a continuous function. This property
automatically holds for topological additive groups but it also holds, e.g., for `ℝ≥0`. -/
class has_continuous_sub (G : Type*) [topological_space G] [has_sub G] : Prop :=
(continuous_sub : continuous (λ p : G × G, p.1 - p.2))

@[priority 100] -- see Note [lower instance priority]
instance topological_add_group.to_has_continuous_sub [topological_space G] [add_group G]
  [topological_add_group G] :
  has_continuous_sub G :=
⟨by { simp only [sub_eq_add_neg], exact continuous_fst.add continuous_snd.neg }⟩

export has_continuous_sub (continuous_sub)

section has_continuous_sub

variables [topological_space G] [has_sub G] [has_continuous_sub G]

lemma filter.tendsto.sub {f g : α → G} {l : filter α} {a b : G} (hf : tendsto f l (𝓝 a))
  (hg : tendsto g l (𝓝 b)) :
  tendsto (λx, f x - g x) l (𝓝 (a - b)) :=
(continuous_sub.tendsto (a, b)).comp (hf.prod_mk_nhds hg)

variables [topological_space α] {f g : α → G} {s : set α} {x : α}

@[continuity] lemma continuous.sub (hf : continuous f) (hg : continuous g) :
  continuous (λ x, f x - g x) :=
continuous_sub.comp (hf.prod_mk hg : _)

lemma continuous_within_at.sub (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (λ x, f x - g x) s x :=
hf.sub hg

lemma continuous_on.sub (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λx, f x - g x) s :=
λ x hx, (hf x hx).sub (hg x hx)

end has_continuous_sub

lemma nhds_translation [topological_space G] [add_group G] [topological_add_group G] (x : G) :
  comap (λy:G, y - x) (𝓝 0) = 𝓝 x :=
by simpa only [sub_eq_add_neg] using nhds_translation_add_neg x

/-- additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class add_group_with_zero_nhd (G : Type u) extends add_comm_group G :=
(Z [] : filter G)
(zero_Z : pure 0 ≤ Z)
(sub_Z : tendsto (λp:G×G, p.1 - p.2) (Z ×ᶠ Z) Z)

namespace add_group_with_zero_nhd
variables (G) [add_group_with_zero_nhd G]

local notation `Z` := add_group_with_zero_nhd.Z

@[priority 100] -- see Note [lower instance priority]
instance : topological_space G :=
topological_space.mk_of_nhds $ λa, map (λx, x + a) (Z G)

variables {G}

lemma neg_Z : tendsto (λa:G, - a) (Z G) (Z G) :=
have tendsto (λa, (0:G)) (Z G) (Z G),
  by refine le_trans (assume h, _) zero_Z; simp [univ_mem_sets'] {contextual := tt},
have tendsto (λa:G, 0 - a) (Z G) (Z G), from
  sub_Z.comp (tendsto.prod_mk this tendsto_id),
by simpa

lemma add_Z : tendsto (λp:G×G, p.1 + p.2) (Z G ×ᶠ Z G) (Z G) :=
suffices tendsto (λp:G×G, p.1 - -p.2) (Z G ×ᶠ Z G) (Z G),
  by simpa [sub_eq_add_neg],
sub_Z.comp (tendsto.prod_mk tendsto_fst (neg_Z.comp tendsto_snd))

lemma exists_Z_half {s : set G} (hs : s ∈ Z G) : ∃ V ∈ Z G, ∀ (v ∈ V) (w ∈ V), v + w ∈ s :=
begin
  have : ((λa:G×G, a.1 + a.2) ⁻¹' s) ∈ Z G ×ᶠ Z G := add_Z (by simpa using hs),
  rcases mem_prod_self_iff.1 this with ⟨V, H, H'⟩,
  exact ⟨V, H, prod_subset_iff.1 H'⟩
end

lemma nhds_eq (a : G) : 𝓝 a = map (λx, x + a) (Z G) :=
topological_space.nhds_mk_of_nhds _ _
  (assume a, calc pure a = map (λx, x + a) (pure 0) : by simp
    ... ≤ _ : map_mono zero_Z)
  (assume b s hs,
    let ⟨t, ht, eqt⟩ := exists_Z_half hs in
    have t0 : (0:G) ∈ t, by simpa using zero_Z ht,
    begin
      refine ⟨(λx:G, x + b) '' t, image_mem_map ht, _, _⟩,
      { refine set.image_subset_iff.2 (assume b hbt, _),
        simpa using eqt 0 t0 b hbt },
      { rintros _ ⟨c, hb, rfl⟩,
        refine (Z G).sets_of_superset ht (assume x hxt, _),
        simpa [add_assoc] using eqt _ hxt _ hb }
    end)

lemma nhds_zero_eq_Z : 𝓝 0 = Z G := by simp [nhds_eq]; exact filter.map_id

@[priority 100] -- see Note [lower instance priority]
instance : has_continuous_add G :=
⟨ continuous_iff_continuous_at.2 $ assume ⟨a, b⟩,
  begin
    rw [continuous_at, nhds_prod_eq, nhds_eq, nhds_eq, nhds_eq, filter.prod_map_map_eq,
      tendsto_map'_iff],
    suffices :  tendsto ((λx:G, (a + b) + x) ∘ (λp:G×G,p.1 + p.2)) (Z G ×ᶠ Z G)
      (map (λx:G, (a + b) + x) (Z G)),
    { simpa [(∘), add_comm, add_left_comm] },
    exact tendsto_map.comp add_Z
  end ⟩

@[priority 100] -- see Note [lower instance priority]
instance : topological_add_group G :=
⟨continuous_iff_continuous_at.2 $ assume a,
  begin
    rw [continuous_at, nhds_eq, nhds_eq, tendsto_map'_iff],
    suffices : tendsto ((λx:G, x - a) ∘ (λx:G, -x)) (Z G) (map (λx:G, x - a) (Z G)),
    { simpa [(∘), add_comm, sub_eq_add_neg] using this },
    exact tendsto_map.comp neg_Z
  end⟩

end add_group_with_zero_nhd

section filter_mul

section
variables [topological_space G] [group G] [topological_group G]

@[to_additive]
lemma is_open.mul_left {s t : set G} : is_open t → is_open (s * t) := λ ht,
begin
  have : ∀a, is_open ((λ (x : G), a * x) '' t) :=
    assume a, is_open_map_mul_left a t ht,
  rw ← Union_mul_left_image,
  exact is_open_Union (λa, is_open_Union $ λha, this _),
end

@[to_additive]
lemma is_open.mul_right {s t : set G} : is_open s → is_open (s * t) := λ hs,
begin
  have : ∀a, is_open ((λ (x : G), x * a) '' s),
    assume a, apply is_open_map_mul_right, exact hs,
  rw ← Union_mul_right_image,
  exact is_open_Union (λa, is_open_Union $ λha, this _),
end

variables (G)

lemma topological_group.t1_space (h : @is_closed G _ {1}) : t1_space G :=
⟨assume x, by { convert is_closed_map_mul_right x _ h, simp }⟩

lemma topological_group.regular_space [t1_space G] : regular_space G :=
⟨assume s a hs ha,
 let f := λ p : G × G, p.1 * (p.2)⁻¹ in
 have hf : continuous f := continuous_fst.mul continuous_snd.inv,
 -- a ∈ -s implies f (a, 1) ∈ -s, and so (a, 1) ∈ f⁻¹' (-s);
 -- and so can find t₁ t₂ open such that a ∈ t₁ × t₂ ⊆ f⁻¹' (-s)
 let ⟨t₁, t₂, ht₁, ht₂, a_mem_t₁, one_mem_t₂, t_subset⟩ :=
   is_open_prod_iff.1 ((is_open_compl_iff.2 hs).preimage hf) a (1:G) (by simpa [f]) in
 begin
   use [s * t₂, ht₂.mul_left, λ x hx, ⟨x, 1, hx, one_mem_t₂, mul_one _⟩],
   rw [nhds_within, inf_principal_eq_bot, mem_nhds_sets_iff],
   refine ⟨t₁, _, ht₁, a_mem_t₁⟩,
   rintros x hx ⟨y, z, hy, hz, yz⟩,
   have : x * z⁻¹ ∈ sᶜ := (prod_subset_iff.1 t_subset) x hx z hz,
   have : x * z⁻¹ ∈ s, rw ← yz, simpa,
   contradiction
 end⟩

local attribute [instance] topological_group.regular_space

lemma topological_group.t2_space [t1_space G] : t2_space G := regular_space.t2_space G

end

section

/-! Some results about an open set containing the product of two sets in a topological group. -/

variables [topological_space G] [group G] [topological_group G]

/-- Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of `1`
  such that `KV ⊆ U`. -/
@[to_additive "Given a compact set `K` inside an open set `U`, there is a open neighborhood `V` of
`0` such that `K + V ⊆ U`."]
lemma compact_open_separated_mul {K U : set G} (hK : is_compact K) (hU : is_open U) (hKU : K ⊆ U) :
  ∃ V : set G, is_open V ∧ (1 : G) ∈ V ∧ K * V ⊆ U :=
begin
  let W : G → set G := λ x, (λ y, x * y) ⁻¹' U,
  have h1W : ∀ x, is_open (W x) := λ x, hU.preimage (continuous_mul_left x),
  have h2W : ∀ x ∈ K, (1 : G) ∈ W x := λ x hx, by simp only [mem_preimage, mul_one, hKU hx],
  choose V hV using λ x : K, exists_open_nhds_one_mul_subset (mem_nhds_sets (h1W x) (h2W x.1 x.2)),
  let X : K → set G := λ x, (λ y, (x : G)⁻¹ * y) ⁻¹' (V x),
  obtain ⟨t, ht⟩ : ∃ t : finset ↥K, K ⊆ ⋃ i ∈ t, X i,
  { refine hK.elim_finite_subcover X (λ x, (hV x).1.preimage (continuous_mul_left x⁻¹)) _,
    intros x hx, rw [mem_Union], use ⟨x, hx⟩, rw [mem_preimage], convert (hV _).2.1,
    simp only [mul_left_inv, subtype.coe_mk] },
  refine ⟨⋂ x ∈ t, V x, is_open_bInter (finite_mem_finset _) (λ x hx, (hV x).1), _, _⟩,
  { simp only [mem_Inter], intros x hx, exact (hV x).2.1 },
  rintro _ ⟨x, y, hx, hy, rfl⟩, simp only [mem_Inter] at hy,
  have := ht hx, simp only [mem_Union, mem_preimage] at this, rcases this with ⟨z, h1z, h2z⟩,
  have : (z : G)⁻¹ * x * y ∈ W z := (hV z).2.2 (mul_mem_mul h2z (hy z h1z)),
  rw [mem_preimage] at this, convert this using 1, simp only [mul_assoc, mul_inv_cancel_left]
end

/-- A compact set is covered by finitely many left multiplicative translates of a set
  with non-empty interior. -/
@[to_additive "A compact set is covered by finitely many left additive translates of a set
  with non-empty interior."]
lemma compact_covered_by_mul_left_translates {K V : set G} (hK : is_compact K)
  (hV : (interior V).nonempty) : ∃ t : finset G, K ⊆ ⋃ g ∈ t, (λ h, g * h) ⁻¹' V :=
begin
  obtain ⟨t, ht⟩ : ∃ t : finset G, K ⊆ ⋃ x ∈ t, interior (((*) x) ⁻¹' V),
  { refine hK.elim_finite_subcover (λ x, interior $ ((*) x) ⁻¹' V) (λ x, is_open_interior) _,
    cases hV with g₀ hg₀,
    refine λ g hg, mem_Union.2 ⟨g₀ * g⁻¹, _⟩,
    refine preimage_interior_subset_interior_preimage (continuous_const.mul continuous_id) _,
    rwa [mem_preimage, inv_mul_cancel_right] },
  exact ⟨t, subset.trans ht $ bUnion_subset_bUnion_right $ λ g hg, interior_subset⟩
end

/-- Every locally compact separable topological group is σ-compact.
  Note: this is not true if we drop the topological group hypothesis. -/
@[priority 100] instance separable_locally_compact_group.sigma_compact_space
  [separable_space G] [locally_compact_space G] : sigma_compact_space G :=
begin
  obtain ⟨L, hLc, hL1⟩ := exists_compact_mem_nhds (1 : G),
  refine ⟨⟨λ n, (λ x, x * dense_seq G n) ⁻¹' L, _, _⟩⟩,
  { intro n, exact (homeomorph.mul_right _).compact_preimage.mpr hLc },
  { refine Union_eq_univ_iff.2 (λ x, _),
    obtain ⟨_, ⟨n, rfl⟩, hn⟩ : (range (dense_seq G) ∩ (λ y, x * y) ⁻¹' L).nonempty,
    { rw [← (homeomorph.mul_left x).apply_symm_apply 1] at hL1,
      exact (dense_range_dense_seq G).inter_nhds_nonempty
        ((homeomorph.mul_left x).continuous.continuous_at $ hL1) },
    exact ⟨n, hn⟩ }
end

end

section
variables [topological_space G] [comm_group G] [topological_group G]

@[to_additive]
lemma nhds_mul (x y : G) : 𝓝 (x * y) = 𝓝 x * 𝓝 y :=
filter_eq $ set.ext $ assume s,
begin
  rw [← nhds_translation_mul_inv x, ← nhds_translation_mul_inv y, ← nhds_translation_mul_inv (x*y)],
  split,
  { rintros ⟨t, ht, ts⟩,
    rcases exists_nhds_one_split ht with ⟨V, V1, h⟩,
    refine ⟨(λa, a * x⁻¹) ⁻¹' V, (λa, a * y⁻¹) ⁻¹' V,
            ⟨V, V1, subset.refl _⟩, ⟨V, V1, subset.refl _⟩, _⟩,
    rintros a ⟨v, w, v_mem, w_mem, rfl⟩,
    apply ts,
    simpa [mul_comm, mul_assoc, mul_left_comm] using h (v * x⁻¹) v_mem (w * y⁻¹) w_mem },
  { rintros ⟨a, c, ⟨b, hb, ba⟩, ⟨d, hd, dc⟩, ac⟩,
    refine ⟨b ∩ d, inter_mem_sets hb hd, assume v, _⟩,
    simp only [preimage_subset_iff, mul_inv_rev, mem_preimage] at *,
    rintros ⟨vb, vd⟩,
    refine ac ⟨v * y⁻¹, y, _, _, _⟩,
    { rw ← mul_assoc _ _ _ at vb, exact ba _ vb },
    { apply dc y, rw mul_right_inv, exact mem_of_nhds hd },
    { simp only [inv_mul_cancel_right] } }
end

@[to_additive]
lemma nhds_is_mul_hom : is_mul_hom (λx:G, 𝓝 x) := ⟨λ_ _, nhds_mul _ _⟩

end

end filter_mul

open additive multiplicative

instance additive.topological_add_group {G} [h : topological_space G]
  [group G] [topological_group G] : topological_add_group (additive G) :=
{ continuous_neg := by simpa using
    show continuous (λ a : additive G, of_mul (a.to_mul⁻¹)), by continuity,
  ..additive.has_continuous_add }

instance multiplicative.topological_group {G} [h : topological_space G]
  [add_group G] [topological_add_group G] : topological_group (multiplicative G) :=
{ continuous_inv := by simpa using
    show continuous (λ a : multiplicative G, of_add (-a.to_add)), by continuity,
  ..multiplicative.has_continuous_mul }
