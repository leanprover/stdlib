/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin, Bhavik Mehta
-/
import category_theory.equivalence
import data.equiv.basic

namespace category_theory
open category

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ u₁ u₂ u₃

local attribute [elab_simple] whisker_left whisker_right

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/--
`F ⊣ G` represents the data of an adjunction between two functors
`F : C ⥤ D` and `G : D ⥤ C`. `F` is the left adjoint and `G` is the right adjoint.

To construct an `adjunction` between two functors, it's often easier to instead use the
constructors `mk_of_hom_equiv` or `mk_of_unit_counit`. To construct a left adjoint,
there are also constructors `left_adjoint_of_equiv` and `adjunction_of_equiv_left` (as
well as their duals) which can be simpler in practice.

Uniqueness of adjoints is shown in `category_theory.adjunction.opposites`.

See https://stacks.math.columbia.edu/tag/0037.
-/
structure adjunction (F : C ⥤ D) (G : D ⥤ C) :=
(hom_equiv : Π (X Y), (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
(unit : 𝟭 C ⟶ F.comp G)
(counit : G.comp F ⟶ 𝟭 D)
(hom_equiv_unit' : Π {X Y f}, (hom_equiv X Y) f = (unit : _ ⟶ _).app X ≫ G.map f . obviously)
(hom_equiv_counit' : Π {X Y g}, (hom_equiv X Y).symm g = F.map g ≫ counit.app Y . obviously)

infix ` ⊣ `:15 := adjunction

/-- A class giving a chosen right adjoint to the functor `left`. -/
class is_left_adjoint (left : C ⥤ D) :=
(right : D ⥤ C)
(adj : left ⊣ right)

/-- A class giving a chosen left adjoint to the functor `right`. -/
class is_right_adjoint (right : D ⥤ C) :=
(left : C ⥤ D)
(adj : left ⊣ right)

/-- Extract the left adjoint from the instance giving the chosen adjoint. -/
def left_adjoint (R : D ⥤ C) [is_right_adjoint R] : C ⥤ D :=
is_right_adjoint.left R
/-- Extract the right adjoint from the instance giving the chosen adjoint. -/
def right_adjoint (L : C ⥤ D) [is_left_adjoint L] : D ⥤ C :=
is_left_adjoint.right L

/-- The adjunction associated to a functor known to be a left adjoint. -/
def adjunction.of_left_adjoint (left : C ⥤ D) [is_left_adjoint left] :
  adjunction left (right_adjoint left) :=
is_left_adjoint.adj
/-- The adjunction associated to a functor known to be a right adjoint. -/
def adjunction.of_right_adjoint (right : C ⥤ D) [is_right_adjoint right] :
  adjunction (left_adjoint right) right :=
is_right_adjoint.adj

namespace adjunction

restate_axiom hom_equiv_unit'
restate_axiom hom_equiv_counit'

section

variables {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {X' X : C} {Y Y' : D}

@[simp, priority 10] lemma hom_equiv_naturality_left_symm (f : X' ⟶ X) (g : X ⟶ G.obj Y) :
  (adj.hom_equiv X' Y).symm (f ≫ g) = F.map f ≫ (adj.hom_equiv X Y).symm g :=
by rw [hom_equiv_counit, F.map_comp, assoc, adj.hom_equiv_counit.symm]

@[simp] lemma hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
  (adj.hom_equiv X' Y) (F.map f ≫ g) = f ≫ (adj.hom_equiv X Y) g :=
by rw [← equiv.eq_symm_apply]; simp [-hom_equiv_unit]

@[simp, priority 10] lemma hom_equiv_naturality_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') :
  (adj.hom_equiv X Y') (f ≫ g) = (adj.hom_equiv X Y) f ≫ G.map g :=
by rw [hom_equiv_unit, G.map_comp, ← assoc, ←hom_equiv_unit]

@[simp] lemma hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
  (adj.hom_equiv X Y').symm (f ≫ G.map g) = (adj.hom_equiv X Y).symm f ≫ g :=
by rw [equiv.symm_apply_eq]; simp [-hom_equiv_counit]

@[simp] lemma left_triangle :
  (whisker_right adj.unit F) ≫ (whisker_left F adj.counit) = nat_trans.id _ :=
begin
  ext, dsimp,
  erw [← adj.hom_equiv_counit, equiv.symm_apply_eq, adj.hom_equiv_unit],
  simp
end

@[simp] lemma right_triangle :
  (whisker_left G adj.unit) ≫ (whisker_right adj.counit G) = nat_trans.id _ :=
begin
  ext, dsimp,
  erw [← adj.hom_equiv_unit, ← equiv.eq_symm_apply, adj.hom_equiv_counit],
  simp
end

@[simp, reassoc] lemma left_triangle_components :
  F.map (adj.unit.app X) ≫ adj.counit.app (F.obj X) = 𝟙 (F.obj X) :=
congr_arg (λ (t : nat_trans _ (𝟭 C ⋙ F)), t.app X) adj.left_triangle

@[simp, reassoc] lemma right_triangle_components {Y : D} :
  adj.unit.app (G.obj Y) ≫ G.map (adj.counit.app Y) = 𝟙 (G.obj Y) :=
congr_arg (λ (t : nat_trans _ (G ⋙ 𝟭 C)), t.app Y) adj.right_triangle

@[simp, reassoc] lemma counit_naturality {X Y : D} (f : X ⟶ Y) :
  F.map (G.map f) ≫ (adj.counit).app Y = (adj.counit).app X ≫ f :=
adj.counit.naturality f

@[simp, reassoc] lemma unit_naturality {X Y : C} (f : X ⟶ Y) :
  (adj.unit).app X ≫ G.map (F.map f) = f ≫ (adj.unit).app Y :=
(adj.unit.naturality f).symm

lemma hom_equiv_apply_eq {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
  adj.hom_equiv A B f = g ↔ f = (adj.hom_equiv A B).symm g :=
⟨λ h, by {cases h, simp}, λ h, by {cases h, simp}⟩

lemma eq_hom_equiv_apply {A : C} {B : D} (f : F.obj A ⟶ B) (g : A ⟶ G.obj B) :
  g = adj.hom_equiv A B f ↔ (adj.hom_equiv A B).symm g = f :=
⟨λ h, by {cases h, simp}, λ h, by {cases h, simp}⟩

end

end adjunction

namespace adjunction

/--
This is an auxiliary data structure useful for constructing adjunctions.
See `adjunction.mk_of_hom_equiv`.
This structure won't typically be used anywhere else.
-/
@[nolint has_inhabited_instance]
structure core_hom_equiv (F : C ⥤ D) (G : D ⥤ C) :=
(hom_equiv : Π (X Y), (F.obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
(hom_equiv_naturality_left_symm' : Π {X' X Y} (f : X' ⟶ X) (g : X ⟶ G.obj Y),
  (hom_equiv X' Y).symm (f ≫ g) = F.map f ≫ (hom_equiv X Y).symm g . obviously)
(hom_equiv_naturality_right' : Π {X Y Y'} (f : F.obj X ⟶ Y) (g : Y ⟶ Y'),
  (hom_equiv X Y') (f ≫ g) = (hom_equiv X Y) f ≫ G.map g . obviously)

namespace core_hom_equiv

restate_axiom hom_equiv_naturality_left_symm'
restate_axiom hom_equiv_naturality_right'
attribute [simp, priority 10] hom_equiv_naturality_left_symm hom_equiv_naturality_right

variables {F : C ⥤ D} {G : D ⥤ C} (adj : core_hom_equiv F G) {X' X : C} {Y Y' : D}

@[simp] lemma hom_equiv_naturality_left (f : X' ⟶ X) (g : F.obj X ⟶ Y) :
  (adj.hom_equiv X' Y) (F.map f ≫ g) = f ≫ (adj.hom_equiv X Y) g :=
by rw [← equiv.eq_symm_apply]; simp

@[simp] lemma hom_equiv_naturality_right_symm (f : X ⟶ G.obj Y) (g : Y ⟶ Y') :
  (adj.hom_equiv X Y').symm (f ≫ G.map g) = (adj.hom_equiv X Y).symm f ≫ g :=
by rw [equiv.symm_apply_eq]; simp

end core_hom_equiv

/--
This is an auxiliary data structure useful for constructing adjunctions.
See `adjunction.mk_of_hom_equiv`.
This structure won't typically be used anywhere else.
-/
@[nolint has_inhabited_instance]
structure core_unit_counit (F : C ⥤ D) (G : D ⥤ C) :=
(unit : 𝟭 C ⟶ F.comp G)
(counit : G.comp F ⟶ 𝟭 D)
(left_triangle' : whisker_right unit F ≫ (functor.associator F G F).hom ≫ whisker_left F counit =
  nat_trans.id (𝟭 C ⋙ F) . obviously)
(right_triangle' : whisker_left G unit ≫ (functor.associator G F G).inv ≫ whisker_right counit G =
  nat_trans.id (G ⋙ 𝟭 C) . obviously)

namespace core_unit_counit

restate_axiom left_triangle'
restate_axiom right_triangle'
attribute [simp] left_triangle right_triangle

end core_unit_counit

variables {F : C ⥤ D} {G : D ⥤ C}

/-- Construct an adjunction between `F` and `G` out of a natural bijection between each
`F.obj X ⟶ Y` and `X ⟶ G.obj Y`. -/
@[simps]
def mk_of_hom_equiv (adj : core_hom_equiv F G) : F ⊣ G :=
{ unit :=
  { app := λ X, (adj.hom_equiv X (F.obj X)) (𝟙 (F.obj X)),
    naturality' :=
    begin
      intros,
      erw [← adj.hom_equiv_naturality_left, ← adj.hom_equiv_naturality_right],
      dsimp, simp  -- See note [dsimp, simp].
    end },
  counit :=
  { app := λ Y, (adj.hom_equiv _ _).inv_fun (𝟙 (G.obj Y)),
    naturality' :=
    begin
      intros,
      erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm],
      dsimp, simp
    end },
  hom_equiv_unit' := λ X Y f, by erw [← adj.hom_equiv_naturality_right]; simp,
  hom_equiv_counit' := λ X Y f, by erw [← adj.hom_equiv_naturality_left_symm]; simp,
  .. adj }

/-- Construct an adjunction between functors `F` and `G` given a unit and counit for the adjunction
satisfying the triangle identities. -/
@[simps]
def mk_of_unit_counit (adj : core_unit_counit F G) : F ⊣ G :=
{ hom_equiv := λ X Y,
  { to_fun := λ f, adj.unit.app X ≫ G.map f,
    inv_fun := λ g, F.map g ≫ adj.counit.app Y,
    left_inv := λ f, begin
      change F.map (_ ≫ _) ≫ _ = _,
      rw [F.map_comp, assoc, ←functor.comp_map, adj.counit.naturality, ←assoc],
      convert id_comp f,
      have t := congr_arg (λ t : nat_trans _ _, t.app _) adj.left_triangle,
      dsimp at t,
      simp only [id_comp] at t,
      exact t,
    end,
    right_inv := λ g, begin
      change _ ≫ G.map (_ ≫ _) = _,
      rw [G.map_comp, ←assoc, ←functor.comp_map, ←adj.unit.naturality, assoc],
      convert comp_id g,
      have t := congr_arg (λ t : nat_trans _ _, t.app _) adj.right_triangle,
      dsimp at t,
      simp only [id_comp] at t,
      exact t,
  end },
  .. adj }

/-- The adjunction between the identity functor on a category and itself. -/
def id : 𝟭 C ⊣ 𝟭 C :=
{ hom_equiv := λ X Y, equiv.refl _,
  unit := 𝟙 _,
  counit := 𝟙 _ }

-- Satisfy the inhabited linter.
instance : inhabited (adjunction (𝟭 C) (𝟭 C)) := ⟨id⟩

/-- If F and G are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equiv_homset_left_of_nat_iso
  {F F' : C ⥤ D} (iso : F ≅ F') {X : C} {Y : D} :
  (F.obj X ⟶ Y) ≃ (F'.obj X ⟶ Y) :=
{ to_fun := λ f, iso.inv.app _ ≫ f,
  inv_fun := λ g, iso.hom.app _ ≫ g,
  left_inv := λ f, by simp,
  right_inv := λ g, by simp }

/-- If G and H are naturally isomorphic functors, establish an equivalence of hom-sets. -/
@[simps]
def equiv_homset_right_of_nat_iso
  {G G' : D ⥤ C} (iso : G ≅ G') {X : C} {Y : D} :
  (X ⟶ G.obj Y) ≃ (X ⟶ G'.obj Y) :=
{ to_fun := λ f, f ≫ iso.hom.app _,
  inv_fun := λ g, g ≫ iso.inv.app _,
  left_inv := λ f, by simp,
  right_inv := λ g, by simp }

/-- Transport an adjunction along an natural isomorphism on the left. -/
def of_nat_iso_left
  {F G : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) (iso : F ≅ G) :
  G ⊣ H :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, (equiv_homset_left_of_nat_iso iso.symm).trans (adj.hom_equiv X Y) }

/-- Transport an adjunction along an natural isomorphism on the right. -/
def of_nat_iso_right
  {F : C ⥤ D} {G H : D ⥤ C} (adj : F ⊣ G) (iso : G ≅ H) :
  F ⊣ H :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, (adj.hom_equiv X Y).trans (equiv_homset_right_of_nat_iso iso) }

/-- Transport being a right adjoint along a natural isomorphism. -/
def right_adjoint_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [r : is_right_adjoint F] :
  is_right_adjoint G :=
{ left := r.left,
  adj := of_nat_iso_right r.adj h }

/-- Transport being a left adjoint along a natural isomorphism. -/
def left_adjoint_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [r : is_left_adjoint F] : is_left_adjoint G :=
{ right := r.right,
  adj := of_nat_iso_left r.adj h }

section
variables {E : Type u₃} [ℰ : category.{v₃} E] (H : D ⥤ E) (I : E ⥤ D)

/--
Composition of adjunctions.

See https://stacks.math.columbia.edu/tag/0DV0.
-/
def comp (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) : F ⋙ H ⊣ I ⋙ G :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Z, (adj₂.hom_equiv _ _).trans (adj₁.hom_equiv _ _) }

/-- If `F` and `G` are left adjoints then `F ⋙ G` is a left adjoint too. -/
instance left_adjoint_of_comp {E : Type u₃} [ℰ : category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
  [Fl : is_left_adjoint F] [Gl : is_left_adjoint G] : is_left_adjoint (F ⋙ G) :=
{ right := Gl.right ⋙ Fl.right,
  adj := comp _ _ Fl.adj Gl.adj }

/-- If `F` and `G` are right adjoints then `F ⋙ G` is a right adjoint too. -/
instance right_adjoint_of_comp {E : Type u₃} [ℰ : category.{v₃} E] {F : C ⥤ D} {G : D ⥤ E}
  [Fr : is_right_adjoint F] [Gr : is_right_adjoint G] : is_right_adjoint (F ⋙ G) :=
{ left := Gr.left ⋙ Fr.left,
  adj := comp _ _ Gr.adj Fr.adj }

end

section construct_left
-- Construction of a left adjoint. In order to construct a left
-- adjoint to a functor G : D → C, it suffices to give the object part
-- of a functor F : C → D together with isomorphisms Hom(FX, Y) ≃
-- Hom(X, GY) natural in Y. The action of F on morphisms can be
-- constructed from this data.
variables {F_obj : C → D} {G}
variables (e : Π X Y, (F_obj X ⟶ Y) ≃ (X ⟶ G.obj Y))
variables (he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g)
include he

private lemma he' {X Y Y'} (f g) : (e X Y').symm (f ≫ G.map g) = (e X Y).symm f ≫ g :=
by intros; rw [equiv.symm_apply_eq, he]; simp

/-- Construct a left adjoint functor to `G`, given the functor's value on objects `F_obj` and
a bijection `e` between `F_obj X ⟶ Y` and `X ⟶ G.obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X Y' (h ≫ g) = e X Y h ≫ G.map g`.
Dual to `right_adjoint_of_equiv`. -/
@[simps]
def left_adjoint_of_equiv : C ⥤ D :=
{ obj := F_obj,
  map := λ X X' f, (e X (F_obj X')).symm (f ≫ e X' (F_obj X') (𝟙 _)),
  map_comp' := λ X X' X'' f f', begin
    rw [equiv.symm_apply_eq, he, equiv.apply_symm_apply],
    conv { to_rhs, rw [assoc, ←he, id_comp, equiv.apply_symm_apply] },
    simp
  end }

/-- Show that the functor given by `left_adjoint_of_equiv` is indeed left adjoint to `G`. Dual
to `adjunction_of_equiv_right`. -/
@[simps]
def adjunction_of_equiv_left : left_adjoint_of_equiv e he ⊣ G :=
mk_of_hom_equiv
{ hom_equiv := e,
  hom_equiv_naturality_left_symm' :=
  begin
    intros,
    erw [← he' e he, ← equiv.apply_eq_iff_eq],
    simp [(he _ _ _ _ _).symm]
  end }

end construct_left

section construct_right
-- Construction of a right adjoint, analogous to the above.
variables {F} {G_obj : D → C}
variables (e : Π X Y, (F.obj X ⟶ Y) ≃ (X ⟶ G_obj Y))
variables (he : ∀ X' X Y f g, e X' Y (F.map f ≫ g) = f ≫ e X Y g)
include he

private lemma he' {X' X Y} (f g) : F.map f ≫ (e X Y).symm g = (e X' Y).symm (f ≫ g) :=
by intros; rw [equiv.eq_symm_apply, he]; simp

/-- Construct a right adjoint functor to `F`, given the functor's value on objects `G_obj` and
a bijection `e` between `F.obj X ⟶ Y` and `X ⟶ G_obj Y` satisfying a naturality law
`he : ∀ X Y Y' g h, e X' Y (F.map f ≫ g) = f ≫ e X Y g`.
Dual to `left_adjoint_of_equiv`. -/
@[simps]
def right_adjoint_of_equiv : D ⥤ C :=
{ obj := G_obj,
  map := λ Y Y' g, (e (G_obj Y) Y') ((e (G_obj Y) Y).symm (𝟙 _) ≫ g),
  map_comp' := λ Y Y' Y'' g g', begin
    rw [← equiv.eq_symm_apply, ← he' e he, equiv.symm_apply_apply],
    conv { to_rhs, rw [← assoc, he' e he, comp_id, equiv.symm_apply_apply] },
    simp
  end }

/-- Show that the functor given by `right_adjoint_of_equiv` is indeed right adjoint to `F`. Dual
to `adjunction_of_equiv_left`. -/
@[simps]
def adjunction_of_equiv_right : F ⊣ right_adjoint_of_equiv e he :=
mk_of_hom_equiv
{ hom_equiv := e,
  hom_equiv_naturality_left_symm' := by intros; rw [equiv.symm_apply_eq, he]; simp,
  hom_equiv_naturality_right' :=
  begin
    intros X Y Y' g h,
    erw [←he, equiv.apply_eq_iff_eq, ←assoc, he' e he, comp_id, equiv.symm_apply_apply]
  end }

end construct_right

/--
If the unit and counit of a given adjunction are (pointwise) isomorphisms, then we can upgrade the
adjunction to an equivalence.
-/
@[simps]
noncomputable
def to_equivalence (adj : F ⊣ G) [∀ X, is_iso (adj.unit.app X)] [∀ Y, is_iso (adj.counit.app Y)] :
  C ≌ D :=
{ functor := F,
  inverse := G,
  unit_iso := nat_iso.of_components (λ X, as_iso (adj.unit.app X)) (by simp),
  counit_iso := nat_iso.of_components (λ Y, as_iso (adj.counit.app Y)) (by simp) }

/--
If the unit and counit for the adjunction corresponding to a right adjoint functor are (pointwise)
isomorphisms, then the functor is an equivalence of categories.
-/
@[simps]
noncomputable
def is_right_adjoint_to_is_equivalence [is_right_adjoint G]
  [∀ X, is_iso ((adjunction.of_right_adjoint G).unit.app X)]
  [∀ Y, is_iso ((adjunction.of_right_adjoint G).counit.app Y)] :
  is_equivalence G :=
is_equivalence.of_equivalence_inverse (adjunction.of_right_adjoint G).to_equivalence

end adjunction

open adjunction

namespace equivalence

/-- The adjunction given by an equivalence of categories. (To obtain the opposite adjunction,
simply use `e.symm.to_adjunction`. -/
def to_adjunction (e : C ≌ D) : e.functor ⊣ e.inverse :=
mk_of_unit_counit ⟨e.unit, e.counit,
  by { ext, dsimp, simp only [id_comp], exact e.functor_unit_comp _, },
  by { ext, dsimp, simp only [id_comp], exact e.unit_inverse_comp _, }⟩

end equivalence

namespace functor

/-- An equivalence `E` is left adjoint to its inverse. -/
def adjunction (E : C ⥤ D) [is_equivalence E] : E ⊣ E.inv :=
(E.as_equivalence).to_adjunction

/-- If `F` is an equivalence, it's a left adjoint. -/
@[priority 10]
instance left_adjoint_of_equivalence {F : C ⥤ D} [is_equivalence F] : is_left_adjoint F :=
{ right := _,
  adj := functor.adjunction F }

@[simp]
lemma right_adjoint_of_is_equivalence {F : C ⥤ D} [is_equivalence F] : right_adjoint F = inv F :=
rfl

/-- If `F` is an equivalence, it's a right adjoint. -/
@[priority 10]
instance right_adjoint_of_equivalence {F : C ⥤ D} [is_equivalence F] : is_right_adjoint F :=
{ left := _,
  adj := functor.adjunction F.inv }

@[simp]
lemma left_adjoint_of_is_equivalence {F : C ⥤ D} [is_equivalence F] : left_adjoint F = inv F :=
rfl

end functor

end category_theory
