/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.const
import category_theory.discrete_category
import category_theory.equivalence

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

namespace functor
variables (C : Type u) [category.{v} C]

/-- The constant functor sending everything to `punit.star`. -/
def star : C ⥤ discrete punit :=
(functor.const _).obj punit.star

variable {C}
/-- Any two functors to `discrete punit` are isomorphic. -/
def punit_ext (F G : C ⥤ discrete punit) : F ≅ G :=
nat_iso.of_components (λ _, eq_to_iso dec_trivial) (λ _ _ _, dec_trivial)

/--
Any two functors to `discrete punit` are *equal*.
You probably want to use `punit_ext` instead of this.
-/
def punit_ext' (F G : C ⥤ discrete punit) : F = G :=
functor.ext (λ _, dec_trivial) (λ _ _ _, dec_trivial)

abbreviation from_punit (X : C) : discrete punit ⥤ C :=
(functor.const _).obj X

@[simps]
def equiv : (discrete punit ⥤ C) ≌ C :=
{ functor :=
  { obj := λ F, F.obj punit.star,
    map := λ F G θ, θ.app punit.star },
  inverse := functor.const _,
  unit_iso :=
  begin
    apply nat_iso.of_components _ _,
    intro X,
    apply discrete.nat_iso,
    rintro ⟨⟩,
    apply iso.refl _,
    intros,
    ext ⟨⟩,
    simp,
  end,
  counit_iso :=
  begin
    refine nat_iso.of_components iso.refl _,
    intros X Y f,
    dsimp, simp,
  end
}

end functor

end category_theory
