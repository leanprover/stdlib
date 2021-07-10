/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl
-/
import category_theory.fully_faithful
import data.equiv.basic

/-!
# The category `Type`.

In this section we set up the theory so that Lean's types and functions between them
can be viewed as a `large_category` in our framework.

Lean can not transparently view a function as a morphism in this category, and needs a hint in
order to be able to type check. We provide the abbreviation `as_hom f` to guide type checking,
as well as a corresponding notation `↾ f`. (Entered as `\upr `.) The notation is enabled using
`open_locale category_theory.Type`.

We provide various simplification lemmas for functors and natural transformations valued in `Type`.

We define `ulift_functor`, from `Type u` to `Type (max u v)`, and show that it is fully faithful
(but not, of course, essentially surjective).

We prove some basic facts about the category `Type`:
*  epimorphisms are surjections and monomorphisms are injections,
* `iso` is both `iso` and `equiv` to `equiv` (at least within a fixed universe),
* every type level `is_lawful_functor` gives a categorical functor `Type ⥤ Type`
  (the corresponding fact about monads is in `src/category_theory/monad/types.lean`).
-/

namespace category_theory

-- morphism levels before object levels. See note [category_theory universes].
universes v v' w u u'

/- The `@[to_additive]` attribute is just a hint that expressions involving this instance can
  still be additivized. -/
@[to_additive category_theory.types]
instance types : large_category (Type u) :=
{ hom     := λ a b, (a → b),
  id      := λ a, id,
  comp    := λ _ _ _ f g, g ∘ f }

lemma types_hom {α β : Type u} : (α ⟶ β) = (α → β) := rfl
lemma types_id (X : Type u) : 𝟙 X = id := rfl
lemma types_comp {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f := rfl

@[simp]
lemma types_id_apply (X : Type u) (x : X) : ((𝟙 X) : X → X) x = x := rfl
@[simp]
lemma types_comp_apply {X Y Z : Type u} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := rfl

@[simp]
lemma hom_inv_id_apply {X Y : Type u} (f : X ≅ Y) (x : X) : f.inv (f.hom x) = x :=
congr_fun f.hom_inv_id x
@[simp]
lemma inv_hom_id_apply {X Y : Type u} (f : X ≅ Y) (y : Y) : f.hom (f.inv y) = y :=
congr_fun f.inv_hom_id y

/-- `as_hom f` helps Lean type check a function as a morphism in the category `Type`. -/
-- Unfortunately without this wrapper we can't use `category_theory` idioms, such as `is_iso f`.
abbreviation as_hom {α β : Type u} (f : α → β) : α ⟶ β := f
-- If you don't mind some notation you can use fewer keystrokes:
localized "notation  `↾` f : 200 := as_hom f" in category_theory.Type -- type as \upr in VScode

section -- We verify the expected type checking behaviour of `as_hom`.
variables (α β γ : Type u) (f : α → β) (g : β → γ)

example : α → γ := ↾f ≫ ↾g
example [is_iso ↾f] : mono ↾f := by apply_instance
example [is_iso ↾f] : ↾f ≫ inv ↾f = 𝟙 α := by simp
end

namespace functor
variables {J : Type u} [category.{v} J]

/--
The sections of a functor `J ⥤ Type` are
the choices of a point `u j : F.obj j` for each `j`,
such that `F.map f (u j) = u j` for every morphism `f : j ⟶ j'`.

We later use these to define limits in `Type` and in many concrete categories.
-/
def sections (F : J ⥤ Type w) : set (Π j, F.obj j) :=
{ u | ∀ {j j'} (f : j ⟶ j'), F.map f (u j) = u j'}
end functor

namespace functor_to_types
variables {C : Type u} [category.{v} C] (F G H : C ⥤ Type w) {X Y Z : C}
variables (σ : F ⟶ G) (τ : G ⟶ H)

@[simp] lemma map_comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) :
  (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) :=
by simp [types_comp]

@[simp] lemma map_id_apply (a : F.obj X) : (F.map (𝟙 X)) a = a :=
by simp [types_id]

lemma naturality (f : X ⟶ Y) (x : F.obj X) : σ.app Y ((F.map f) x) = (G.map f) (σ.app X x) :=
congr_fun (σ.naturality f) x

@[simp] lemma comp (x : F.obj X) : (σ ≫ τ).app X x = τ.app X (σ.app X x) := rfl

variables {D : Type u'} [𝒟 : category.{u'} D] (I J : D ⥤ C) (ρ : I ⟶ J) {W : D}

@[simp] lemma hcomp (x : (I ⋙ F).obj W) :
  (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x) :=
rfl

@[simp] lemma map_inv_map_hom_apply (f : X ≅ Y) (x : F.obj X) : F.map f.inv (F.map f.hom x) = x :=
congr_fun (F.map_iso f).hom_inv_id x
@[simp] lemma map_hom_map_inv_apply (f : X ≅ Y) (y : F.obj Y) : F.map f.hom (F.map f.inv y) = y :=
congr_fun (F.map_iso f).inv_hom_id y

@[simp] lemma hom_inv_id_app_apply (α : F ≅ G) (X) (x) : α.inv.app X (α.hom.app X x) = x :=
congr_fun (α.hom_inv_id_app X) x
@[simp] lemma inv_hom_id_app_apply (α : F ≅ G) (X) (x) : α.hom.app X (α.inv.app X x) = x :=
congr_fun (α.inv_hom_id_app X) x

end functor_to_types

/--
The isomorphism between a `Type` which has been `ulift`ed to the same universe,
and the original type.
-/
def ulift_trivial (V : Type u) : ulift.{u} V ≅ V := by tidy

/--
The functor embedding `Type u` into `Type (max u v)`.
Write this as `ulift_functor.{5 2}` to get `Type 2 ⥤ Type 5`.
-/
def ulift_functor : Type u ⥤ Type (max u v) :=
{ obj := λ X, ulift.{v} X,
  map := λ X Y f, λ x : ulift.{v} X, ulift.up (f x.down) }

@[simp] lemma ulift_functor_map {X Y : Type u} (f : X ⟶ Y) (x : ulift.{v} X) :
  ulift_functor.map f x = ulift.up (f x.down) := rfl

instance ulift_functor_full : full.{u} ulift_functor :=
{ preimage := λ X Y f x, (f (ulift.up x)).down }
instance ulift_functor_faithful : faithful ulift_functor :=
{ map_injective' := λ X Y f g p, funext $ λ x,
    congr_arg ulift.down ((congr_fun p (ulift.up x)) : ((ulift.up (f x)) = (ulift.up (g x)))) }

/-- Any term `x` of a type `X` corresponds to a morphism `punit ⟶ X`. -/
-- TODO We should connect this to a general story about concrete categories
-- whose forgetful functor is representable.
def hom_of_element {X : Type u} (x : X) : punit ⟶ X := λ _, x

lemma hom_of_element_eq_iff {X : Type u} (x y : X) :
  hom_of_element x = hom_of_element y ↔ x = y :=
⟨λ H, congr_fun H punit.star, by cc⟩

/--
A morphism in `Type` is a monomorphism if and only if it is injective.

See https://stacks.math.columbia.edu/tag/003C.
-/
lemma mono_iff_injective {X Y : Type u} (f : X ⟶ Y) : mono f ↔ function.injective f :=
begin
  split,
  { intros H x x' h,
    resetI,
    rw ←hom_of_element_eq_iff at ⊢ h,
    exact (cancel_mono f).mp h },
  { refine λ H, ⟨λ Z g h H₂, _⟩,
    ext z,
    replace H₂ := congr_fun H₂ z,
    exact H H₂ }
end

/--
A morphism in `Type` is an epimorphism if and only if it is surjective.

See https://stacks.math.columbia.edu/tag/003C.
-/
lemma epi_iff_surjective {X Y : Type u} (f : X ⟶ Y) : epi f ↔ function.surjective f :=
begin
  split,
  { intros H,
    let g : Y ⟶ ulift Prop := λ y, ⟨true⟩,
    let h : Y ⟶ ulift Prop := λ y, ⟨∃ x, f x = y⟩,
    suffices : f ≫ g = f ≫ h,
    { resetI,
      rw cancel_epi at this,
      intro y,
      replace this := congr_fun this y,
      replace this : true = ∃ x, f x = y := congr_arg ulift.down this,
      rw ←this,
      trivial },
    ext x,
    change true ↔ ∃ x', f x' = f x,
    rw true_iff,
    exact ⟨x, rfl⟩ },
  { intro H,
    constructor,
    intros Z g h H₂,
    apply funext,
    rw ←forall_iff_forall_surj H,
    intro x,
    exact (congr_fun H₂ x : _) }
end

section

/-- `of_type_functor m` converts from Lean's `Type`-based `category` to `category_theory`. This
allows us to use these functors in category theory. -/
def of_type_functor (m : Type u → Type v) [_root_.functor m] [is_lawful_functor m] :
  Type u ⥤ Type v :=
{ obj       := m,
  map       := λα β, _root_.functor.map,
  map_id'   := assume α, _root_.functor.map_id,
  map_comp' := assume α β γ f g, funext $ assume a, is_lawful_functor.comp_map f g _ }

variables (m : Type u → Type v) [_root_.functor m] [is_lawful_functor m]

@[simp]
lemma of_type_functor_obj : (of_type_functor m).obj = m := rfl

@[simp]
lemma of_type_functor_map {α β} (f : α → β) :
  (of_type_functor m).map f = (_root_.functor.map f : m α → m β) := rfl

end

end category_theory

-- Isomorphisms in Type and equivalences.

namespace equiv

universe u

variables {X Y : Type u}

/--
Any equivalence between types in the same universe gives
a categorical isomorphism between those types.
-/
def to_iso (e : X ≃ Y) : X ≅ Y :=
{ hom := e.to_fun,
  inv := e.inv_fun,
  hom_inv_id' := funext e.left_inv,
  inv_hom_id' := funext e.right_inv }

@[simp] lemma to_iso_hom {e : X ≃ Y} : e.to_iso.hom = e := rfl
@[simp] lemma to_iso_inv {e : X ≃ Y} : e.to_iso.inv = e.symm := rfl

end equiv

universe u

namespace category_theory.iso
open category_theory

variables {X Y : Type u}

/--
Any isomorphism between types gives an equivalence.
-/
def to_equiv (i : X ≅ Y) : X ≃ Y :=
{ to_fun := i.hom,
  inv_fun := i.inv,
  left_inv := λ x, congr_fun i.hom_inv_id x,
  right_inv := λ y, congr_fun i.inv_hom_id y }

@[simp] lemma to_equiv_fun (i : X ≅ Y) : (i.to_equiv : X → Y) = i.hom := rfl
@[simp] lemma to_equiv_symm_fun (i : X ≅ Y) : (i.to_equiv.symm : Y → X) = i.inv := rfl

@[simp] lemma to_equiv_id (X : Type u) : (iso.refl X).to_equiv = equiv.refl X := rfl
@[simp] lemma to_equiv_comp {X Y Z : Type u} (f : X ≅ Y) (g : Y ≅ Z) :
  (f ≪≫ g).to_equiv = f.to_equiv.trans (g.to_equiv) := rfl

end category_theory.iso

namespace category_theory

/-- A morphism in `Type u` is an isomorphism if and only if it is bijective. -/
lemma is_iso_iff_bijective {X Y : Type u} (f : X ⟶ Y) : is_iso f ↔ function.bijective f :=
iff.intro
  (λ i, (by exactI as_iso f : X ≅ Y).to_equiv.bijective)
  (λ b, is_iso.of_iso (equiv.of_bijective f b).to_iso)

end category_theory

-- We prove `equiv_iso_iso` and then use that to sneakily construct `equiv_equiv_iso`.
-- (In this order the proofs are handled by `obviously`.)

/-- Equivalences (between types in the same universe) are the same as (isomorphic to) isomorphisms
of types. -/
@[simps] def equiv_iso_iso {X Y : Type u} : (X ≃ Y) ≅ (X ≅ Y) :=
{ hom := λ e, e.to_iso,
  inv := λ i, i.to_equiv, }

/-- Equivalences (between types in the same universe) are the same as (equivalent to) isomorphisms
of types. -/
def equiv_equiv_iso {X Y : Type u} : (X ≃ Y) ≃ (X ≅ Y) :=
(equiv_iso_iso).to_equiv

@[simp] lemma equiv_equiv_iso_hom {X Y : Type u} (e : X ≃ Y) :
  equiv_equiv_iso e = e.to_iso := rfl

@[simp] lemma equiv_equiv_iso_inv {X Y : Type u} (e : X ≅ Y) :
  equiv_equiv_iso.symm e = e.to_equiv := rfl
