/-
-- Copyright (c) 2020 Bhavik Mehta. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Bhavik Mehta, Scott Morrison
-/
import category_theory.limits.shapes.finite_products
import category_theory.limits.preserves.shapes.products
import category_theory.limits.preserves.shapes.equalizers

/-!
# Constructing limits from products and equalizers.

If a category has all products, and all equalizers, then it has all limits.
Similarly, if it has all finite products, and all equalizers, then it has all finite limits.

If a functor preserves all products and equalizers, then it preserves all limits.
Similarly, if it preserves all finite products and equalizers, then it preserves all finite limits.

# TODO

Provide the dual results.
Show the analogous results for functors which reflect or create (co)limits.
-/

open category_theory
open opposite

namespace category_theory.limits

universes v u u₂
variables {C : Type u} [category.{v} C]

variables {J : Type v} [small_category J]

-- We hide the "implementation details" inside a namespace
namespace has_limit_of_has_products_of_has_equalizers

variables {F : J ⥤ C}
          {c₁ : fan F.obj}
          {c₂ : fan (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2)}
          (s t : c₁.X ⟶ c₂.X)
          (hs : ∀ (f : Σ p : J × J, p.1 ⟶ p.2), s ≫ c₂.π.app f = c₁.π.app f.1.1 ≫ F.map f.2)
          (ht : ∀ (f : Σ p : J × J, p.1 ⟶ p.2), t ≫ c₂.π.app f = c₁.π.app f.1.2)
          (i : fork s t)

include hs ht
/--
(Implementation) Given the appropriate product and equalizer cones, build the cone for `F` which is
limiting if the given cones are also.
-/
@[simps]
def build_limit : cone F :=
{ X := i.X,
  π := { app := λ j, i.ι ≫ c₁.π.app _,
         naturality' := λ j₁ j₂ f, by { dsimp, simp [← hs ⟨⟨_, _⟩, f⟩, i.condition_assoc, ht] } } }

variable {i}
/--
(Implementation) Show the cone constructed in `build_limit` is limiting, provided the cones used in
its construction are.
-/
def build_is_limit (t₁ : is_limit c₁) (t₂ : is_limit c₂) (hi : is_limit i) :
  is_limit (build_limit s t hs ht i) :=
{ lift := λ q,
  begin
    refine hi.lift (fork.of_ι _ _),
    { refine t₁.lift (fan.mk _ (λ j, _)),
      apply q.π.app j },
    { apply t₂.hom_ext,
      simp [hs, ht] },
  end,
  uniq' := λ q m w, hi.hom_ext (i.equalizer_ext (t₁.hom_ext (by simpa using w))) }

end has_limit_of_has_products_of_has_equalizers

open has_limit_of_has_products_of_has_equalizers

/--
Given the existence of the appropriate (possibly finite) products and equalizers, we know a limit of
`F` exists.
(This assumes the existence of all equalizers, which is technically stronger than needed.)
-/
lemma has_limit_of_equalizer_and_product (F : J ⥤ C)
  [has_limit (discrete.functor F.obj)]
  [has_limit (discrete.functor (λ f : (Σ p : J × J, p.1 ⟶ p.2), F.obj f.1.2))]
  [has_equalizers C] : has_limit F :=
has_limit.mk
{ cone := _,
  is_limit :=
    build_is_limit
      (pi.lift (λ f, limit.π _ _ ≫ F.map f.2))
      (pi.lift (λ f, limit.π _ f.1.2))
      (by simp)
      (by simp)
      (limit.is_limit _)
      (limit.is_limit _)
      (limit.is_limit _) }

/--
Any category with products and equalizers has all limits.

See https://stacks.math.columbia.edu/tag/002N.
-/
lemma limits_from_equalizers_and_products
  [has_products C] [has_equalizers C] : has_limits C :=
{ has_limits_of_shape := λ J 𝒥,
  { has_limit := λ F, by exactI has_limit_of_equalizer_and_product F } }

/--
Any category with finite products and equalizers has all finite limits.

See https://stacks.math.columbia.edu/tag/002O.
-/
lemma finite_limits_from_equalizers_and_finite_products
  [has_finite_products C] [has_equalizers C] : has_finite_limits C :=
λ J _ _, { has_limit := λ F, by exactI has_limit_of_equalizer_and_product F }

variables {D : Type u₂} [category.{v} D]
noncomputable theory

section

variables [has_limits_of_shape (discrete J) C]
          [has_limits_of_shape (discrete (Σ p : J × J, p.1 ⟶ p.2)) C]
          [has_equalizers C]
variables (G : C ⥤ D)
          [preserves_limits_of_shape walking_parallel_pair G]
          [preserves_limits_of_shape (discrete J) G]
          [preserves_limits_of_shape (discrete (Σ p : J × J, p.1 ⟶ p.2)) G]

/-- If a functor preserves equalizers and the appropriate products, it preserves limits. -/
def preserves_limit_of_preserves_equalizers_and_product :
  preserves_limits_of_shape J G :=
{ preserves_limit := λ K,
  begin
    let P := ∏ K.obj,
    let Q := ∏ (λ (f : (Σ (p : J × J), p.fst ⟶ p.snd)), K.obj f.1.2),
    let s : P ⟶ Q := pi.lift (λ f, limit.π _ _ ≫ K.map f.2),
    let t : P ⟶ Q := pi.lift (λ f, limit.π _ f.1.2),
    let I := equalizer s t,
    let i : I ⟶ P := equalizer.ι s t,
    apply preserves_limit_of_preserves_limit_cone
      (build_is_limit s t (by simp) (by simp)
        (limit.is_limit _)
        (limit.is_limit _)
        (limit.is_limit _)),
    refine is_limit.of_iso_limit (build_is_limit _ _ _ _ _ _ _) _,
    { exact fan.mk _ (λ j, G.map (pi.π _ j)) },
    { exact fan.mk (G.obj Q) (λ f, G.map (pi.π _ f)) },
    { apply G.map s },
    { apply G.map t },
    { intro f,
      dsimp,
      simp only [←G.map_comp, limit.lift_π, fan.mk_π_app] },
    { intro f,
      dsimp,
      simp only [←G.map_comp, limit.lift_π, fan.mk_π_app] },
    { apply fork.of_ι (G.map i) _,
      simp only [← G.map_comp, equalizer.condition] },
    { apply is_limit_of_has_product_of_preserves_limit },
    { apply is_limit_of_has_product_of_preserves_limit },
    { apply is_limit_fork_map_of_is_limit,
      apply equalizer_is_equalizer },
    refine cones.ext (iso.refl _) _,
    intro j,
    dsimp,
    simp, -- See note [dsimp, simp].
  end }
end

/-- If G preserves equalizers and finite products, it preserves finite limits. -/
def preserves_finite_limits_of_preserves_equalizers_and_finite_products
  [has_equalizers C] [has_finite_products C]
  (G : C ⥤ D) [preserves_limits_of_shape walking_parallel_pair G]
  [∀ J [fintype J], preserves_limits_of_shape (discrete J) G]
  (J : Type v) [small_category J] [fin_category J] :
preserves_limits_of_shape J G :=
preserves_limit_of_preserves_equalizers_and_product G

/-- If G preserves equalizers and products, it preserves all limits. -/
def preserves_limits_of_preserves_equalizers_and_products
  [has_equalizers C] [has_products C]
  (G : C ⥤ D) [preserves_limits_of_shape walking_parallel_pair G]
  [∀ J, preserves_limits_of_shape (discrete J) G] :
preserves_limits G :=
{ preserves_limits_of_shape := λ J 𝒥,
  by exactI preserves_limit_of_preserves_equalizers_and_product G }

end category_theory.limits
