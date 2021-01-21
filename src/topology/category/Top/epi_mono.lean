/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
import topology.category.Top.adjunctions

universe u

open category_theory
open Top

namespace Top

lemma epi_iff_surjective {X Y : Top.{u}} (f : X ⟶ Y) : epi f ↔ function.surjective f :=
begin
  suffices : epi f ↔ epi ((forget Top).map f),
  { rw [this, category_theory.epi_iff_surjective], refl },
  split,
  { apply left_adjoint_preserves_epi adj₂ },
  { apply faithful_reflects_epi }
end

lemma mono_iff_injective {X Y : Top.{u}} (f : X ⟶ Y) : mono f ↔ function.injective f :=
begin
  suffices : mono f ↔ mono ((forget Top).map f),
  { rw [this, category_theory.mono_iff_injective], refl },
  split,
  { apply right_adjoint_preserves_mono adj₁ },
  { apply faithful_reflects_mono }
end

end Top
