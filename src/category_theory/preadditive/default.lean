/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.shapes.kernels
import algebra.big_operators.basic

/-!
# Preadditive categories

A preadditive category is a category in which `X ⟶ Y` is an abelian group in such a way that
composition of morphisms is linear in both variables.

This file contains a definition of preadditive category that directly encodes the definition given
above. The definition could also be phrased as follows: A preadditive category is a category
enriched over the category of Abelian groups. Once the general framework to state this in Lean is
available, the contents of this file should become obsolete.

## Main results

* Definition of preadditive categories and basic properties
* In a preadditive category, `f : Q ⟶ R` is mono if and only if `g ≫ f = 0 → g = 0` for all
  composable `g`.
* A preadditive category with kernels has equalizers.

## Implementation notes

The simp normal form for negation and composition is to push negations as far as possible to
the outside. For example, `f ≫ (-g)` and `(-f) ≫ g` both become `-(f ≫ g)`, and `(-f) ≫ (-g)`
is simplified to `f ≫ g`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]

## Tags

additive, preadditive, Hom group, Ab-category, Ab-enriched
-/

universes v u

open category_theory.limits
open add_monoid_hom

namespace category_theory

variables (C : Type u) [category.{v} C]

/-- A category is called preadditive if `P ⟶ Q` is an abelian group such that composition is
    linear in both variables. -/
class preadditive :=
(hom_group : Π P Q : C, add_comm_group (P ⟶ Q) . tactic.apply_instance)
(add_comp' : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R),
  (f + f') ≫ g = f ≫ g + f' ≫ g . obviously)
(comp_add' : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R),
  f ≫ (g + g') = f ≫ g + f ≫ g' . obviously)

attribute [instance] preadditive.hom_group
restate_axiom preadditive.add_comp'
restate_axiom preadditive.comp_add'
attribute [simp,reassoc] preadditive.add_comp
attribute [reassoc] preadditive.comp_add -- (the linter doesn't like `simp` on this lemma)
attribute [simp] preadditive.comp_add

end category_theory

open category_theory

namespace category_theory.preadditive

section preadditive
variables {C : Type u} [category.{v} C] [preadditive C]

/-- Composition by a fixed left argument as a group homomorphism -/
def left_comp {P Q : C} (R : C) (f : P ⟶ Q) : (Q ⟶ R) →+ (P ⟶ R) :=
mk' (λ g, f ≫ g) $ λ g g', by simp

/-- Composition by a fixed right argument as a group homomorphism -/
def right_comp (P : C) {Q R : C} (g : Q ⟶ R) : (P ⟶ Q) →+ (P ⟶ R) :=
mk' (λ f, f ≫ g) $ λ f f', by simp

@[simp, reassoc] lemma sub_comp {P Q R : C} (f f' : P ⟶ Q) (g : Q ⟶ R) :
  (f - f') ≫ g = f ≫ g - f' ≫ g :=
map_sub (right_comp P g) f f'

-- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma.
@[reassoc, simp] lemma comp_sub {P Q R : C} (f : P ⟶ Q) (g g' : Q ⟶ R) :
  f ≫ (g - g') = f ≫ g - f ≫ g' :=
map_sub (left_comp R f) g g'

@[simp, reassoc] lemma neg_comp {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : (-f) ≫ g = -(f ≫ g) :=
map_neg (right_comp _ _) _

/- The redundant simp lemma linter says that simp can prove the reassoc version of this lemma. -/
@[reassoc, simp] lemma comp_neg {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : f ≫ (-g) = -(f ≫ g) :=
map_neg (left_comp _ _) _

@[reassoc] lemma neg_comp_neg {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : (-f) ≫ (-g) = f ≫ g :=
by simp

section big_operators

open_locale big_operators

@[reassoc] lemma comp_sum {P Q R : C} {J : Type*} {s : finset J} (f : P ⟶ Q) (g : J → (Q ⟶ R)) :
  f ≫ ∑ j in s, g j = ∑ j in s, f ≫ g j :=
begin
  change left_comp R f _ = _,
  rw [add_monoid_hom.map_sum],
  refl,
end

@[reassoc] lemma sum_comp {P Q R : C} {J : Type*} {s : finset J} (f : J → (P ⟶ Q)) (g : Q ⟶ R) :
  (∑ j in s, f j) ≫ g  = ∑ j in s, f j ≫ g :=
begin
  change right_comp P g _ = _,
  rw [add_monoid_hom.map_sum],
  refl,
end

end big_operators

instance {P Q : C} {f : P ⟶ Q} [epi f] : epi (-f) :=
⟨λ R g g' H, by rwa [neg_comp, neg_comp, ←comp_neg, ←comp_neg, cancel_epi, neg_inj] at H⟩

instance {P Q : C} {f : P ⟶ Q} [mono f] : mono (-f) :=
⟨λ R g g' H, by rwa [comp_neg, comp_neg, ←neg_comp, ←neg_comp, cancel_mono, neg_inj] at H⟩

@[priority 100]
instance preadditive_has_zero_morphisms : has_zero_morphisms C :=
{ has_zero := infer_instance,
  comp_zero' := λ P Q f R, map_zero $ left_comp R f,
  zero_comp' := λ P Q R f, map_zero $ right_comp P f }

lemma mono_of_cancel_zero {Q R : C} (f : Q ⟶ R) (h : ∀ {P : C} (g : P ⟶ Q), g ≫ f = 0 → g = 0) :
  mono f :=
⟨λ P g g' hg, sub_eq_zero.1 $ h _ $ (map_sub (right_comp P f) g g').trans $ sub_eq_zero.2 hg⟩

lemma mono_iff_cancel_zero {Q R : C} (f : Q ⟶ R) :
  mono f ↔ ∀ (P : C) (g : P ⟶ Q), g ≫ f = 0 → g = 0 :=
⟨λ m P g, by exactI zero_of_comp_mono _, mono_of_cancel_zero f⟩

lemma mono_of_kernel_zero {X Y : C} {f : X ⟶ Y} [has_limit (parallel_pair f 0)]
  (w : kernel.ι f = 0) : mono f :=
mono_of_cancel_zero f (λ P g h, by rw [←kernel.lift_ι f g h, w, limits.comp_zero])

lemma epi_of_cancel_zero {P Q : C} (f : P ⟶ Q) (h : ∀ {R : C} (g : Q ⟶ R), f ≫ g = 0 → g = 0) :
  epi f :=
⟨λ R g g' hg, sub_eq_zero.1 $ h _ $ (map_sub (left_comp R f) g g').trans $ sub_eq_zero.2 hg⟩

lemma epi_iff_cancel_zero {P Q : C} (f : P ⟶ Q) :
  epi f ↔ ∀ (R : C) (g : Q ⟶ R), f ≫ g = 0 → g = 0 :=
⟨λ e R g, by exactI zero_of_epi_comp _, epi_of_cancel_zero f⟩

lemma epi_of_cokernel_zero {X Y : C} (f : X ⟶ Y) [has_colimit (parallel_pair f 0 )]
  (w : cokernel.π f = 0) : epi f :=
epi_of_cancel_zero f (λ P g h, by rw [←cokernel.π_desc f g h, w, limits.zero_comp])

end preadditive

section equalizers
variables {C : Type u} [category.{v} C] [preadditive C]

section
variables {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y)

/-- A kernel of `f - g` is an equalizer of `f` and `g`. -/
lemma has_limit_parallel_pair [has_kernel (f - g)] :
  has_limit (parallel_pair f g) :=
has_limit.mk { cone := fork.of_ι (kernel.ι (f - g)) (sub_eq_zero.1 $
    by { rw ←comp_sub, exact kernel.condition _ }),
  is_limit := fork.is_limit.mk _
    (λ s, kernel.lift (f - g) (fork.ι s) $
      by { rw comp_sub, apply sub_eq_zero.2, exact fork.condition _ })
    (λ s, by simp)
    (λ s m h, by { ext, simpa using h walking_parallel_pair.zero }) }

end

section

/-- If a preadditive category has all kernels, then it also has all equalizers. -/
lemma has_equalizers_of_has_kernels [has_kernels C] : has_equalizers C :=
@has_equalizers_of_has_limit_parallel_pair _ _ (λ _ _ f g, has_limit_parallel_pair f g)

end

section
variables {X Y : C} (f : X ⟶ Y) (g : X ⟶ Y)

/-- A cokernel of `f - g` is a coequalizer of `f` and `g`. -/
lemma has_colimit_parallel_pair [has_cokernel (f - g)] :
  has_colimit (parallel_pair f g) :=
has_colimit.mk { cocone := cofork.of_π (cokernel.π (f - g)) (sub_eq_zero.1 $
    by { rw ←sub_comp, exact cokernel.condition _ }),
  is_colimit := cofork.is_colimit.mk _
    (λ s, cokernel.desc (f - g) (cofork.π s) $
      by { rw sub_comp, apply sub_eq_zero.2, exact cofork.condition _ })
    (λ s, by simp)
    (λ s m h, by { ext, simpa using h walking_parallel_pair.one }) }

end

section

/-- If a preadditive category has all cokernels, then it also has all coequalizers. -/
lemma has_coequalizers_of_has_cokernels [has_cokernels C] : has_coequalizers C :=
@has_coequalizers_of_has_colimit_parallel_pair _ _ (λ _ _ f g, has_colimit_parallel_pair f g)

end

end equalizers
end category_theory.preadditive
