/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Adam Topaz
-/

import data.fintype.basic
import data.fin
import category_theory.concrete_category.bundled
import category_theory.concrete_category
import category_theory.full_subcategory
import category_theory.skeletal

/-!
# The category of finite types.

We define the category of finite types, denoted `Fintype` as
(bundled) types with a `fintype` instance.

We also define `Fintype.skeleton`, the standard skeleton of `Fintype` whose objects are `fin n`
for `n : ℕ`. We prove that the obvious inclusion functor `Fintype.skeleton ⥤ Fintype` is an
equivalence of categories in `Fintype.skeleton.equivalence`.
We prove that `Fintype.skeleton` is a skeleton of `Fintype` in `Fintype.is_skeleton`.
-/

open_locale classical
open category_theory

/-- The category of finite types. -/
@[derive has_coe_to_sort]
def Fintype := bundled fintype

namespace Fintype

/-- Construct a bundled `Fintype` from the underlying type and typeclass. -/
def of (X : Type*) [fintype X] : Fintype := bundled.of X
instance : inhabited Fintype := ⟨⟨pempty⟩⟩
instance {X : Fintype} : fintype X := X.2

instance : category Fintype := induced_category.category bundled.α

/-- The fully faithful embedding of `Fintype` into the category of types. -/
@[derive [full, faithful], simps]
def incl : Fintype ⥤ Type* := induced_functor _

instance : concrete_category Fintype := ⟨incl⟩

/--
The "standard" skeleton for `Fintype`. This is the full subcategory of `Fintype` spanned by objects
of the form `fin n` for `n : ℕ`. We parameterize the objects of `Fintype.skeleton` directly as `ℕ`,
as the type `fin m ≃ fin n` is nonempty if and only if `n = m`.
-/
def skeleton := ℕ

namespace skeleton

/-- Given any natural number `n`, this creates the associated object of `Fintype.skeleton`. -/
def mk : ℕ → skeleton := id

instance : inhabited skeleton := ⟨mk 0⟩

/-- Given any object of `Fintype.skeleton`, this returns the associated natural number. -/
def to_nat : skeleton → ℕ := id

instance : category skeleton :=
{ hom := λ X Y, fin X → fin Y,
  id := λ _, id,
  comp := λ _ _ _ f g, g ∘ f }

lemma is_skeletal : skeletal skeleton := λ X Y ⟨h⟩, fin.equiv_iff_eq.mp $ nonempty.intro $
{ to_fun := h.1,
  inv_fun := h.2,
  left_inv := λ _, by {change (h.hom ≫ h.inv) _ = _, simpa},
  right_inv := λ _, by {change (h.inv ≫ h.hom) _ = _, simpa} }

/-- The canonical fully faithful embedding of `Fintype.skeleton` into `Fintype`. -/
def incl : skeleton ⥤ Fintype :=
{ obj := λ X, Fintype.of (fin X),
  map := λ _ _ f, f }

instance : full incl := { preimage := λ _ _ f, f }
instance : faithful incl := {}
instance : ess_surj incl :=
{ mem_ess_image := λ X,
  let F := fintype.equiv_fin X in
  ⟨fintype.card X, ⟨⟨F.symm, F, F.self_comp_symm, F.symm_comp_self⟩⟩⟩ }

noncomputable instance : is_equivalence incl :=
equivalence.of_fully_faithfully_ess_surj _

/-- The equivalence between `Fintype.skeleton` and `Fintype`. -/
noncomputable def equivalence : skeleton ≌ Fintype := incl.as_equivalence

@[simp] lemma incl_mk_nat_card (n : ℕ) : fintype.card (incl.obj (mk n)) = n := finset.card_fin n

end skeleton

/-- `Fintype.skeleton` is a skeleton of `Fintype`. -/
noncomputable def is_skeleton : is_skeleton_of Fintype skeleton skeleton.incl :=
{ skel := skeleton.is_skeletal,
  eqv := by apply_instance }

end Fintype
