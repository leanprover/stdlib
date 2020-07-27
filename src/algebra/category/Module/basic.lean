/-
Copyright (c) 2019 Robert A. Spencer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert A. Spencer, Markus Himmel
-/
import algebra.category.Group.basic
import category_theory.concrete_category
import category_theory.limits.shapes.kernels
import category_theory.preadditive
import linear_algebra.basic

open category_theory
open category_theory.limits
open category_theory.limits.walking_parallel_pair

universe u

variables (R : Type u) [ring R]

/-- The category of R-modules and their morphisms. -/
structure Module :=
(carrier : Type u)
[is_add_comm_group : add_comm_group carrier]
[is_module : module R carrier]

attribute [instance] Module.is_add_comm_group Module.is_module

namespace Module

-- TODO revisit this after #1438 merges, to check coercions and instances are handled consistently
instance : has_coe_to_sort (Module R) :=
{ S := Type u, coe := Module.carrier }

instance : category (Module R) :=
{ hom   := λ M N, M →ₗ[R] N,
  id    := λ M, 1,
  comp  := λ A B C f g, g.comp f }

instance : concrete_category (Module R) :=
{ forget := { obj := λ R, R, map := λ R S f, (f : R → S) },
  forget_faithful := { } }

instance has_forget_to_AddCommGroup : has_forget₂ (Module R) AddCommGroup :=
{ forget₂ :=
  { obj := λ M, AddCommGroup.of M,
    map := λ M₁ M₂ f, linear_map.to_add_monoid_hom f } }

/-- The object in the category of R-modules associated to an R-module -/
def of (X : Type u) [add_comm_group X] [module R X] : Module R := ⟨X⟩

instance : inhabited (Module R) := ⟨of R punit⟩

@[simp]
lemma of_apply (X : Type u) [add_comm_group X] [module R X] : (of R X : Type u) = X := rfl

variables {R}

/-- Forgetting to the underlying type and then building the bundled object returns the original module. -/
@[simps]
def of_self_iso (M : Module R) : Module.of R M ≅ M :=
{ hom := 𝟙 M, inv := 𝟙 M }

instance : subsingleton (of R punit) :=
by { rw of_apply R punit, apply_instance }

instance : has_zero_object (Module R) :=
{ zero := of R punit,
  unique_to := λ X,
  { default := (0 : punit →ₗ[R] X),
    uniq := λ _, linear_map.ext $ λ x,
      have h : x = 0, from subsingleton.elim _ _,
      by simp only [h, linear_map.map_zero]},
  unique_from := λ X,
  { default := (0 : X →ₗ[R] punit),
    uniq := λ _, linear_map.ext $ λ x, subsingleton.elim _ _ } }

variables {R} {M N U : Module R}

@[simp] lemma id_apply (m : M) : (𝟙 M : M → M) m = m := rfl

@[simp] lemma coe_comp (f : M ⟶ N) (g : N ⟶ U) :
  ((f ≫ g) : M → U) = g ∘ f := rfl

end Module

variables {R}
variables {X₁ X₂ : Type u}

/-- Reinterpreting a linear map in the category of `R`-modules. -/
def Module.as_hom [add_comm_group X₁] [module R X₁] [add_comm_group X₂] [module R X₂] :
  (X₁ →ₗ[R] X₂) → (Module.of R X₁ ⟶ Module.of R X₂) := id

/-- Build an isomorphism in the category `Module R` from a `linear_equiv` between `module`s. -/
@[simps]
def linear_equiv.to_Module_iso
  {g₁ : add_comm_group X₁} {g₂ : add_comm_group X₂} {m₁ : module R X₁} {m₂ : module R X₂} (e : X₁ ≃ₗ[R] X₂) :
  Module.of R X₁ ≅ Module.of R X₂ :=
{ hom := (e : X₁ →ₗ[R] X₂),
  inv := (e.symm : X₂ →ₗ[R] X₁),
  hom_inv_id' := begin ext, exact e.left_inv x, end,
  inv_hom_id' := begin ext, exact e.right_inv x, end, }

@[simps]
def linear_equiv.to_Module_iso' {M N : Module R} (i : M ≃ₗ[R] N) : M ≅ N :=
{ hom := i,
  inv := i.symm,
  hom_inv_id' := linear_map.ext $ λ x, by simp,
  inv_hom_id' := linear_map.ext $ λ x, by simp }

namespace category_theory.iso

/-- Build a `linear_equiv` from an isomorphism in the category `Module R`. -/
@[simps]
def to_linear_equiv {X Y : Module R} (i : X ≅ Y) : X ≃ₗ[R] Y :=
{ to_fun    := i.hom,
  inv_fun   := i.inv,
  left_inv  := by tidy,
  right_inv := by tidy,
  map_add'  := by tidy,
  map_smul' := by tidy, }.

end category_theory.iso

/-- linear equivalences between `module`s are the same as (isomorphic to) isomorphisms in `Module` -/
@[simps]
def linear_equiv_iso_Module_iso {X Y : Type u} [add_comm_group X] [add_comm_group Y] [module R X] [module R Y] :
  (X ≃ₗ[R] Y) ≅ (Module.of R X ≅ Module.of R Y) :=
{ hom := λ e, e.to_Module_iso,
  inv := λ i, i.to_linear_equiv, }

namespace Module

section preadditive

instance : preadditive (Module R) :=
{ add_comp' := λ P Q R f f' g,
    show (f + f') ≫ g = f ≫ g + f' ≫ g, by { ext, simp },
  comp_add' := λ P Q R f g g',
    show f ≫ (g + g') = f ≫ g + f ≫ g', by { ext, simp } }

end preadditive

section epi_mono
variables {M N : Module R} (f : M ⟶ N)

lemma ker_eq_bot_of_mono [mono f] : f.ker = ⊥ :=
linear_map.ker_eq_bot_of_cancel $ λ u v, (@cancel_mono _ _ _ _ _ f _ (as_hom u) (as_hom v)).1

lemma range_eq_top_of_epi [epi f] : f.range = ⊤ :=
linear_map.range_eq_top_of_cancel $ λ u v, (@cancel_epi _ _ _ _ _ f _ (as_hom u) (as_hom v)).1

lemma mono_of_ker_eq_bot (hf : f.ker = ⊥) : mono f :=
⟨λ Z u v h, begin
  ext,
  apply (linear_map.ker_eq_bot.1 hf),
  rw [←linear_map.comp_apply, ←linear_map.comp_apply],
  congr,
  exact h
end⟩

lemma epi_of_range_eq_top (hf : f.range = ⊤) : epi f :=
⟨λ Z u v h, begin
  ext,
  cases linear_map.range_eq_top.1 hf x with y hy,
  rw [←hy, ←linear_map.comp_apply, ←linear_map.comp_apply],
  congr,
  exact h
end⟩

end epi_mono

end Module

instance (M : Type u) [add_comm_group M] [module R M] : has_coe (submodule R M) (Module R) :=
⟨ λ N, Module.of R N ⟩
