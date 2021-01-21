/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import category_theory.eq_to_hom

/-!
# Categories of indexed families of objects.

We define the pointwise category structure on indexed families of objects in a category
(and also the dependent generalization).

-/

namespace category_theory

universes w₀ w₁ w₂ v₁ v₂ u₁ u₂

variables {I : Type w₀} (C : I → Type u₁) [Π i, category.{v₁} (C i)]

/--
`pi C` gives the cartesian product of an indexed family of categories.
-/
instance pi : category.{max w₀ v₁} (Π i, C i) :=
{ hom := λ X Y, Π i, X i ⟶ Y i,
  id := λ X i, 𝟙 (X i),
  comp := λ X Y Z f g i, f i ≫ g i }

/--
This provides some assistance to typeclass search in a common situation,
which otherwise fails. (Without this `category_theory.pi.has_limit_of_has_limit_comp_eval` fails.)
-/
abbreviation pi' {I : Type v₁} (C : I → Type u₁) [Π i, category.{v₁} (C i)] :
  category.{v₁} (Π i, C i) :=
category_theory.pi C

attribute [instance] pi'

namespace pi

@[simp] lemma id_apply (X : Π i, C i) (i) : (𝟙 X : Π i, X i ⟶ X i) i = 𝟙 (X i) := rfl
@[simp] lemma comp_apply {X Y Z : Π i, C i} (f : X ⟶ Y) (g : Y ⟶ Z) (i) :
  (f ≫ g : Π i, X i ⟶ Z i) i = f i ≫ g i := rfl

/--
The evaluation functor at `i : I`, sending an `I`-indexed family of objects to the object over `i`.
-/
@[simps]
def eval (i : I) : (Π i, C i) ⥤ C i :=
{ obj := λ f, f i,
  map := λ f g α, α i, }

section
variables {J : Type w₁}

/--
Pull back an `I`-indexed family of objects to an `J`-indexed family, along a function `J → I`.
-/
@[simps]
def comap (h : J → I) : (Π i, C i) ⥤ (Π j, C (h j)) :=
{ obj := λ f i, f (h i),
  map := λ f g α i, α (h i), }

variables (I)
/--
The natural isomorphism between
pulling back a grading along the identity function,
and the identity functor. -/
@[simps]
def comap_id : comap C (id : I → I) ≅ 𝟭 (Π i, C i) :=
{ hom := { app := λ X, 𝟙 X },
  inv := { app := λ X, 𝟙 X } }.

variables {I}
variables {K : Type w₂}

/--
The natural isomorphism comparing between
pulling back along two successive functions, and
pulling back along their composition
-/
@[simps]
def comap_comp (f : K → J) (g : J → I) : comap C g ⋙ comap (C ∘ g) f ≅ comap C (g ∘ f) :=
{ hom := { app := λ X b, 𝟙 (X (g (f b))) },
  inv := { app := λ X b, 𝟙 (X (g (f b))) } }

/-- The natural isomorphism between pulling back then evaluating, and just evaluating. -/
@[simps]
def comap_eval_iso_eval (h : J → I) (j : J) : comap C h ⋙ eval (C ∘ h) j ≅ eval C (h j) :=
nat_iso.of_components (λ f, iso.refl _) (by tidy)

end

section
variables {J : Type w₀} {D : J → Type u₁} [Π j, category.{v₁} (D j)]

instance sum_elim_category : Π (s : I ⊕ J), category.{v₁} (sum.elim C D s)
| (sum.inl i) := by { dsimp, apply_instance, }
| (sum.inr j) := by { dsimp, apply_instance, }

/--
The bifunctor combining an `I`-indexed family of objects with a `J`-indexed family of objects
to obtain an `I ⊕ J`-indexed family of objects.
-/
@[simps]
def sum : (Π i, C i) ⥤ (Π j, D j) ⥤ (Π s : I ⊕ J, sum.elim C D s) :=
{ obj := λ f,
  { obj := λ g s, sum.rec f g s,
    map := λ g g' α s, sum.rec (λ i, 𝟙 (f i)) α s },
  map := λ f f' α,
  { app := λ g s, sum.rec α (λ j, 𝟙 (g j)) s, }}

end

end pi

namespace functor

variables {C}
variables {D : I → Type u₁} [∀ i, category.{v₁} (D i)]

/--
Assemble an `I`-indexed family of functors into a functor between the pi types.
-/
@[simps]
def pi (F : Π i, C i ⥤ D i) : (Π i, C i) ⥤ (Π i, D i) :=
{ obj := λ f i, (F i).obj (f i),
  map := λ f g α i, (F i).map (α i) }

-- One could add some natural isomorphisms showing
-- how `functor.pi` commutes with `pi.eval` and `pi.comap`.

end functor

namespace nat_trans

variables {C}
variables {D : I → Type u₁} [∀ i, category.{v₁} (D i)]
variables {F G : Π i, C i ⥤ D i}

/--
Assemble an `I`-indexed family of natural transformations into a single natural transformation.
-/
@[simps]
def pi (α : Π i, F i ⟶ G i) : functor.pi F ⟶ functor.pi G :=
{ app := λ f i, (α i).app (f i), }

end nat_trans

end category_theory
