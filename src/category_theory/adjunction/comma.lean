/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction.basic
import category_theory.limits.constructions.weakly_initial
import category_theory.limits.preserves.basic
import category_theory.limits.creates
import category_theory.limits.comma
import category_theory.punit

/-!
# Properties of comma categories relating to adjunctions

This file shows that for a functor `G : D ⥤ C` the data of an initial object in each
`structured_arrow` category on `G` is equivalent to a left adjoint to `G`, as well as the dual.

Specifically, `adjunction_of_structured_arrow_initials` gives the left adjoint assuming the
appropriate initial objects exist, and `mk_initial_of_left_adjoint` constructs the initial objects
provided a left adjoint.

The duals are also shown.
-/
universes v u₁ u₂

noncomputable theory

namespace category_theory
open limits

variables {C : Type u₁} {D : Type u₂} [category.{v} C] [category.{v} D] (G : D ⥤ C)

section of_initials
variables [∀ A, has_initial (structured_arrow A G)]

/--
Implementation: If each structured arrow category on `G` has an initial object, an equivalence
which is helpful for constructing a left adjoint to `G`.
-/
@[simps]
def left_adjoint_of_structured_arrow_initials_aux (A : C) (B : D) :
  ((⊥_ (structured_arrow A G)).right ⟶ B) ≃ (A ⟶ G.obj B) :=
{ to_fun := λ g, (⊥_ (structured_arrow A G)).hom ≫ G.map g,
  inv_fun := λ f, comma_morphism.right (initial.to (structured_arrow.mk f)),
  left_inv := λ g,
  begin
    let B' : structured_arrow A G :=
      structured_arrow.mk ((⊥_ (structured_arrow A G)).hom ≫ G.map g),
    let g' : ⊥_ (structured_arrow A G) ⟶ B' := structured_arrow.hom_mk g rfl,
    have : initial.to _ = g',
    { apply colimit.hom_ext, rintro ⟨⟩ },
    change comma_morphism.right (initial.to B') = _,
    rw this,
    refl
  end,
  right_inv := λ f,
  begin
    let B' : structured_arrow A G := { right := B, hom := f },
    apply (comma_morphism.w (initial.to B')).symm.trans (category.id_comp _),
  end }

/--
If each structured arrow category on `G` has an initial object, construct a left adjoint to `G`. It
is shown that it is a left adjoint in `adjunction_of_structured_arrow_initials`.
-/
def left_adjoint_of_structured_arrow_initials : C ⥤ D :=
adjunction.left_adjoint_of_equiv (left_adjoint_of_structured_arrow_initials_aux G) (λ _ _, by simp)

/--
If each structured arrow category on `G` has an initial object, we have a constructed left adjoint
to `G`.
-/
def adjunction_of_structured_arrow_initials :
  left_adjoint_of_structured_arrow_initials G ⊣ G :=
adjunction.adjunction_of_equiv_left _ _

/-- If each structured arrow category on `G` has an initial object, `G` is a right adjoint. -/
def is_right_adjoint_of_structured_arrow_initials : is_right_adjoint G :=
{ left := _, adj := adjunction_of_structured_arrow_initials G }

end of_initials

section of_terminals
variables [∀ A, has_terminal (costructured_arrow G A)]

/--
Implementation: If each costructured arrow category on `G` has a terminal object, an equivalence
which is helpful for constructing a right adjoint to `G`.
-/
@[simps]
def right_adjoint_of_costructured_arrow_terminals_aux (B : D) (A : C) :
  (G.obj B ⟶ A) ≃ (B ⟶ (⊤_ (costructured_arrow G A)).left) :=
{ to_fun := λ g, comma_morphism.left (terminal.from (costructured_arrow.mk g)),
  inv_fun := λ g, G.map g ≫ (⊤_ (costructured_arrow G A)).hom,
  left_inv := by tidy,
  right_inv := λ g,
  begin
    let B' : costructured_arrow G A :=
      costructured_arrow.mk (G.map g ≫ (⊤_ (costructured_arrow G A)).hom),
    let g' : B' ⟶ ⊤_ (costructured_arrow G A) := costructured_arrow.hom_mk g rfl,
    have : terminal.from _ = g',
    { apply limit.hom_ext, rintro ⟨⟩ },
    change comma_morphism.left (terminal.from B') = _,
    rw this,
    refl
  end }

/--
If each costructured arrow category on `G` has a terminal object, construct a right adjoint to `G`.
It is shown that it is a right adjoint in `adjunction_of_structured_arrow_initials`.
-/
def right_adjoint_of_costructured_arrow_terminals : C ⥤ D :=
adjunction.right_adjoint_of_equiv (right_adjoint_of_costructured_arrow_terminals_aux G)
  (λ B₁ B₂ A f g, by { rw ←equiv.eq_symm_apply, simp })

/--
If each costructured arrow category on `G` has a terminal object, we have a constructed right
adjoint to `G`.
-/
def adjunction_of_costructured_arrow_terminals :
  G ⊣ right_adjoint_of_costructured_arrow_terminals G :=
adjunction.adjunction_of_equiv_right _ _

/-- If each costructured arrow category on `G` has an terminal object, `G` is a left adjoint. -/
def is_right_adjoint_of_costructured_arrow_terminals : is_left_adjoint G :=
{ right := right_adjoint_of_costructured_arrow_terminals G,
  adj := adjunction.adjunction_of_equiv_right _ _ }

end of_terminals

section
variables {F : C ⥤ D}

/-- Given a left adjoint to `G`, we can construct an initial object in each structured arrow
category on `G`. -/
def mk_initial_of_left_adjoint (h : F ⊣ G) (A : C) :
  is_initial (structured_arrow.mk (h.unit.app A) : structured_arrow A G) :=
{ desc := λ B, structured_arrow.hom_mk ((h.hom_equiv _ _).symm B.X.hom) (by tidy),
  uniq' := λ s m w,
  begin
    ext,
    dsimp,
    rw [equiv.eq_symm_apply, adjunction.hom_equiv_unit],
    apply structured_arrow.w m,
  end }

/-- Given a right adjoint to `F`, we can construct a terminal object in each costructured arrow
category on `F`. -/
def mk_terminal_of_right_adjoint (h : F ⊣ G) (A : D) :
  is_terminal (costructured_arrow.mk (h.counit.app A) : costructured_arrow F A) :=
{ lift := λ B, costructured_arrow.hom_mk (h.hom_equiv _ _ B.X.hom) (by tidy),
  uniq' := λ s m w,
  begin
    ext,
    dsimp,
    rw [h.eq_hom_equiv_apply, adjunction.hom_equiv_counit],
    exact costructured_arrow.w m,
  end }

end

end category_theory
