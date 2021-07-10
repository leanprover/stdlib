/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import linear_algebra.basic
import order.atoms

/-!
# Simple Modules

## Main Definitions
  * `is_simple_module` indicates that a module has no proper submodules
  (the only submodules are `⊥` and `⊤`).
  * `is_semisimple_module` indicates that every submodule has a complement, or equivalently,
    the module is a direct sum of simple modules.
  * A `division_ring` structure on the endomorphism ring of a simple module.

## Main Results
  * Schur's Lemma: `bijective_or_eq_zero` shows that a linear map between simple modules
  is either bijective or 0, leading to a `division_ring` structure on the endomorphism ring.

## TODO
  * Artin-Wedderburn Theory
  * Unify with the work on Schur's Lemma in a category theory context

-/

variables (R : Type*) [ring R] (M : Type*) [add_comm_group M] [module R M]

/-- A module is simple when it has only two submodules, `⊥` and `⊤`. -/
abbreviation is_simple_module := (is_simple_lattice (submodule R M))

/-- A module is semisimple when every submodule has a complement, or equivalently, the module
  is a direct sum of simple modules. -/
abbreviation is_semisimple_module := (is_complemented (submodule R M))

-- Making this an instance causes the linter to complain of "dangerous instances"
theorem is_simple_module.nontrivial [is_simple_module R M] : nontrivial M :=
⟨⟨0, begin
  have h : (⊥ : submodule R M) ≠ ⊤ := bot_ne_top,
  contrapose! h,
  ext,
  simp [submodule.mem_bot,submodule.mem_top, h x],
end⟩⟩

variables {R} {M} {m : submodule R M} {N : Type*} [add_comm_group N] [module R N]

theorem is_simple_module_iff_is_atom :
  is_simple_module R m ↔ is_atom m :=
begin
  rw ← set.is_simple_lattice_Iic_iff_is_atom,
  apply order_iso.is_simple_lattice_iff,
  exact submodule.map_subtype.rel_iso m,
end

namespace is_simple_module

variable [hm : is_simple_module R m]

@[simp]
lemma is_atom : is_atom m := is_simple_module_iff_is_atom.1 hm

end is_simple_module

theorem is_semisimple_of_Sup_simples_eq_top
  (h : Sup {m : submodule R M | is_simple_module R m} = ⊤) :
  is_semisimple_module R M :=
is_complemented_of_Sup_atoms_eq_top (by simp_rw [← h, is_simple_module_iff_is_atom])

namespace is_semisimple_module

variable [is_semisimple_module R M]

theorem Sup_simples_eq_top : Sup {m : submodule R M | is_simple_module R m} = ⊤ :=
begin
  simp_rw is_simple_module_iff_is_atom,
  exact Sup_atoms_eq_top,
end

instance is_semisimple_submodule {m : submodule R M} : is_semisimple_module R m :=
begin
  have f : submodule R m ≃o set.Iic m := submodule.map_subtype.rel_iso m,
  exact f.is_complemented_iff.2 is_modular_lattice.is_complemented_Iic,
end

end is_semisimple_module

theorem is_semisimple_iff_top_eq_Sup_simples :
  Sup {m : submodule R M | is_simple_module R m} = ⊤ ↔ is_semisimple_module R M :=
⟨is_semisimple_of_Sup_simples_eq_top, by { introI, exact is_semisimple_module.Sup_simples_eq_top }⟩

namespace linear_map

theorem injective_or_eq_zero [is_simple_module R M] (f : M →ₗ[R] N) :
  function.injective f ∨ f = 0 :=
begin
  rw [← ker_eq_bot, ← ker_eq_top],
  apply eq_bot_or_eq_top,
end

theorem injective_of_ne_zero [is_simple_module R M] {f : M →ₗ[R] N} (h : f ≠ 0) :
  function.injective f :=
f.injective_or_eq_zero.resolve_right h

theorem surjective_or_eq_zero [is_simple_module R N] (f : M →ₗ[R] N) :
  function.surjective f ∨ f = 0 :=
begin
  rw [← range_eq_top, ← range_eq_bot, or_comm],
  apply eq_bot_or_eq_top,
end

theorem surjective_of_ne_zero [is_simple_module R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
  function.surjective f :=
f.surjective_or_eq_zero.resolve_right h

/-- **Schur's Lemma** for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero [is_simple_module R M] [is_simple_module R N]
  (f : M →ₗ[R] N) :
  function.bijective f ∨ f = 0 :=
begin
  by_cases h : f = 0,
  { right,
    exact h },
  exact or.intro_left _ ⟨injective_of_ne_zero h, surjective_of_ne_zero h⟩,
end

theorem bijective_of_ne_zero [is_simple_module R M] [is_simple_module R N]
  {f : M →ₗ[R] N} (h : f ≠ 0):
  function.bijective f :=
f.bijective_or_eq_zero.resolve_right h

/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
noncomputable instance [decidable_eq (module.End R M)] [is_simple_module R M] :
  division_ring (module.End R M) :=
{ inv := λ f, if h : f = 0 then 0 else (linear_map.inverse f
    (equiv.of_bijective _ (bijective_of_ne_zero h)).inv_fun
    (equiv.of_bijective _ (bijective_of_ne_zero h)).left_inv
    (equiv.of_bijective _ (bijective_of_ne_zero h)).right_inv),
  exists_pair_ne := ⟨0, 1, begin
    haveI := is_simple_module.nontrivial R M,
    have h := exists_pair_ne M,
    contrapose! h,
    intros x y,
    simp_rw [ext_iff, one_apply, zero_apply] at h,
    rw [← h x, h y],
  end⟩,
  mul_inv_cancel := begin
    intros a a0,
    change (a * (dite _ _ _)) = 1,
    ext,
    rw [dif_neg a0, mul_eq_comp, one_apply, comp_apply],
    exact (equiv.of_bijective _ (bijective_of_ne_zero a0)).right_inv x,
  end,
  inv_zero := dif_pos rfl,
.. (linear_map.endomorphism_ring : ring (module.End R M))}

end linear_map
