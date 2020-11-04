/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.limits

/-!
# The colimit of `coyoneda.obj X` is `punit`

We calculate the colimit of `Y ↦ (X ⟶ Y)`, which is just `punit`.

(This is used later in characterising cofinal functors.)
-/

open opposite
open category_theory
open category_theory.limits

universes v u
variables {C : Type v} [small_category.{v} C]

namespace category_theory

namespace coyoneda

/--
The colimit cocone over `coyoneda.obj X`, with cocone point `punit`.
-/
@[simps]
def colimit_cocone (X : Cᵒᵖ) : cocone (coyoneda.obj X) :=
{ X := punit,
  ι := { app := by tidy, } }

/--
The proposed colimit cocone over `coyoneda.obj X` is a colimit cocone.
-/
@[simps]
def colimit_cocone_is_colimit (X : Cᵒᵖ) : is_colimit (colimit_cocone X) :=
{ desc := λ s x, s.ι.app (unop X) (𝟙 _),
  fac' := λ s Y, by { ext f, convert congr_fun (s.w f).symm (𝟙 (unop X)), refl, simp, },
  uniq' := λ s m w, by { ext ⟨⟩, rw ← w, simp, } }

instance (X : Cᵒᵖ) : has_colimit (coyoneda.obj X) :=
has_colimit.mk { cocone := _, is_colimit := colimit_cocone_is_colimit X }

/--
The colimit of `coyoneda.obj X` is isomorphic to `punit`.
-/
noncomputable
def colimit_coyoneda_iso (X : Cᵒᵖ) : colimit (coyoneda.obj X) ≅ punit :=
colimit.iso_colimit_cocone { cocone := _, is_colimit := colimit_cocone_is_colimit X }

end coyoneda

end category_theory
