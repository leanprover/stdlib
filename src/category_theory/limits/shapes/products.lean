/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.limits.has_limits
import category_theory.discrete_category

/-!
# Categorical (co)products

This file defines (co)products as special cases of (co)limits.

A product is the categorical generalization of the object `Π i, f i` where `f : ι → C`. It is a
limit cone over the diagram formed by `f`, implemented by converting `f` into a functor
`discrete ι ⥤ C`.

A coproduct is the dual concept.

## Main definitions

* a `fan` is a cone over a discrete category
* `fan.mk` constructs a fan from an indexed collection of maps
* a `pi` is a `limit (discrete.functor f)`

Each of these has a dual.

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbreviation`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.
-/

noncomputable theory

universes v u u₂

open category_theory

namespace category_theory.limits

variables {β : Type v}
variables {C : Type u} [category.{v} C]

-- We don't need an analogue of `pair` (for binary products), `parallel_pair` (for equalizers),
-- or `(co)span`, since we already have `discrete.functor`.

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
abbreviation fan (f : β → C) := cone (discrete.functor f)
/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
abbreviation cofan (f : β → C) := cocone (discrete.functor f)

/-- A fan over `f : β → C` consists of a collection of maps from an object `P` to every `f b`. -/
@[simps]
def fan.mk {f : β → C} (P : C) (p : Π b, P ⟶ f b) : fan f :=
{ X := P,
  π := { app := p } }

/-- A cofan over `f : β → C` consists of a collection of maps from every `f b` to an object `P`. -/
@[simps]
def cofan.mk {f : β → C} (P : C) (p : Π b, f b ⟶ P) : cofan f :=
{ X := P,
  ι := { app := p } }

/-- An abbreviation for `has_limit (discrete.functor f)`. -/
abbreviation has_product (f : β → C) := has_limit (discrete.functor f)

/-- An abbreviation for `has_colimit (discrete.functor f)`. -/
abbreviation has_coproduct (f : β → C) := has_colimit (discrete.functor f)

section
variables (C)

/-- An abbreviation for `has_limits_of_shape (discrete f)`. -/
abbreviation has_products_of_shape (β : Type v) := has_limits_of_shape.{v} (discrete β)
/-- An abbreviation for `has_colimits_of_shape (discrete f)`. -/
abbreviation has_coproducts_of_shape (β : Type v) := has_colimits_of_shape.{v} (discrete β)
end

/-- `pi_obj f` computes the product of a family of elements `f`.
(It is defined as an abbreviation for `limit (discrete.functor f)`,
so for most facts about `pi_obj f`, you will just use general facts about limits.) -/
abbreviation pi_obj (f : β → C) [has_product f] := limit (discrete.functor f)
/-- `sigma_obj f` computes the coproduct of a family of elements `f`.
(It is defined as an abbreviation for `colimit (discrete.functor f)`,
so for most facts about `sigma_obj f`, you will just use general facts about colimits.) -/
abbreviation sigma_obj (f : β → C) [has_coproduct f] := colimit (discrete.functor f)

notation `∏ ` f:20 := pi_obj f
notation `∐ ` f:20 := sigma_obj f

/-- The `b`-th projection from the pi object over `f` has the form `∏ f ⟶ f b`. -/
abbreviation pi.π (f : β → C) [has_product f] (b : β) : ∏ f ⟶ f b :=
limit.π (discrete.functor f) b
/-- The `b`-th inclusion into the sigma object over `f` has the form `f b ⟶ ∐ f`. -/
abbreviation sigma.ι (f : β → C) [has_coproduct f] (b : β) : f b ⟶ ∐ f :=
colimit.ι (discrete.functor f) b

/-- The fan constructed of the projections from the product is limiting. -/
def product_is_product (f : β → C) [has_product f] :
  is_limit (fan.mk _ (pi.π f)) :=
is_limit.of_iso_limit (limit.is_limit (discrete.functor f)) (cones.ext (iso.refl _) (by tidy))

/-- The cofan constructed of the inclusions from the coproduct is colimiting. -/
def coproduct_is_coproduct (f : β → C) [has_coproduct f] :
  is_colimit (cofan.mk _ (sigma.ι f)) :=
is_colimit.of_iso_colimit (colimit.is_colimit (discrete.functor f)) (cocones.ext (iso.refl _)
  (by tidy))

/-- A collection of morphisms `P ⟶ f b` induces a morphism `P ⟶ ∏ f`. -/
abbreviation pi.lift {f : β → C} [has_product f] {P : C} (p : Π b, P ⟶ f b) : P ⟶ ∏ f :=
limit.lift _ (fan.mk P p)
/-- A collection of morphisms `f b ⟶ P` induces a morphism `∐ f ⟶ P`. -/
abbreviation sigma.desc {f : β → C} [has_coproduct f] {P : C} (p : Π b, f b ⟶ P) : ∐ f ⟶ P :=
colimit.desc _ (cofan.mk P p)

/--
Construct a morphism between categorical products (indexed by the same type)
from a family of morphisms between the factors.
-/
abbreviation pi.map {f g : β → C} [has_product f] [has_product g]
  (p : Π b, f b ⟶ g b) : ∏ f ⟶ ∏ g :=
lim_map (discrete.nat_trans p)
/--
Construct an isomorphism between categorical products (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbreviation pi.map_iso {f g : β → C} [has_products_of_shape β C]
  (p : Π b, f b ≅ g b) : ∏ f ≅ ∏ g :=
lim.map_iso (discrete.nat_iso p)
/--
Construct a morphism between categorical coproducts (indexed by the same type)
from a family of morphisms between the factors.
-/
abbreviation sigma.map {f g : β → C} [has_coproduct f] [has_coproduct g]
  (p : Π b, f b ⟶ g b) : ∐ f ⟶ ∐ g :=
colim_map (discrete.nat_trans p)
/--
Construct an isomorphism between categorical coproducts (indexed by the same type)
from a family of isomorphisms between the factors.
-/
abbreviation sigma.map_iso {f g : β → C} [has_coproducts_of_shape β C]
  (p : Π b, f b ≅ g b) : ∐ f ≅ ∐ g :=
colim.map_iso (discrete.nat_iso p)

section comparison

variables {D : Type u₂} [category.{v} D] (G : C ⥤ D)
variables (f : β → C)

/-- The comparison morphism for the product of `f`. This is an iso iff `G` preserves the product
of `f`, see `preserves_product.of_iso_comparison`. -/
def pi_comparison [has_product f] [has_product (λ b, G.obj (f b))] :
  G.obj (∏ f) ⟶ ∏ (λ b, G.obj (f b)) :=
pi.lift (λ b, G.map (pi.π f b))

@[simp, reassoc]
lemma pi_comparison_comp_π [has_product f] [has_product (λ b, G.obj (f b))] (b : β) :
  pi_comparison G f ≫ pi.π _ b = G.map (pi.π f b) :=
limit.lift_π _ b

@[simp, reassoc]
lemma map_lift_pi_comparison [has_product f] [has_product (λ b, G.obj (f b))]
  (P : C) (g : Π j, P ⟶ f j) :
  G.map (pi.lift g) ≫ pi_comparison G f = pi.lift (λ j, G.map (g j)) :=
by { ext, simp [← G.map_comp] }

/-- The comparison morphism for the coproduct of `f`. This is an iso iff `G` preserves the coproduct
of `f`, see `preserves_coproduct.of_iso_comparison`. -/
def sigma_comparison [has_coproduct f] [has_coproduct (λ b, G.obj (f b))] :
  ∐ (λ b, G.obj (f b)) ⟶ G.obj (∐ f) :=
sigma.desc (λ b, G.map (sigma.ι f b))

@[simp, reassoc]
lemma ι_comp_sigma_comparison [has_coproduct f] [has_coproduct (λ b, G.obj (f b))] (b : β) :
  sigma.ι _ b ≫ sigma_comparison G f = G.map (sigma.ι f b) :=
colimit.ι_desc _ b

@[simp, reassoc]
lemma sigma_comparison_map_desc [has_coproduct f] [has_coproduct (λ b, G.obj (f b))]
  (P : C) (g : Π j, f j ⟶ P) :
  sigma_comparison G f ≫ G.map (sigma.desc g) = sigma.desc (λ j, G.map (g j)) :=
by { ext, simp [← G.map_comp] }

end comparison

variables (C)

/-- An abbreviation for `Π J, has_limits_of_shape (discrete J) C` -/
abbreviation has_products := Π (J : Type v), has_limits_of_shape (discrete J) C
/-- An abbreviation for `Π J, has_colimits_of_shape (discrete J) C` -/
abbreviation has_coproducts := Π (J : Type v), has_colimits_of_shape (discrete J) C

end category_theory.limits
