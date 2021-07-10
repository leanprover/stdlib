/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.algebra.basic

/-!
# Morphisms of non-unital algebras

This file defines morphisms between two types, each of which carries:
 * an addition,
 * an additive zero,
 * a multiplication,
 * a scalar action.

The multiplications are not assumed to be associative or unital, or even to be compatible with the
scalar actions. In a typical application, the operations will satisfy compatibility conditions
making them into algebras (albeit possibly non-associative and/or non-unital) but such conditions
are not required to make this definition.

This notion of morphism should be useful for any category of non-unital algebras. The motivating
application at the time it was introduced was to be able to state the adjunction property for
magma algebras. These are non-unital, non-associative algebras obtained by applying the
group-algebra construction except where we take a type carrying just `has_mul` instead of `group`.

For a plausible future application, one could take the non-unital algebra of compactly-supported
functions on a non-compact topological space. A proper map between a pair of such spaces
(contravariantly) induces a morphism between their algebras of compactly-supported functions which
will be a `non_unital_alg_hom`.

TODO: add `non_unital_alg_equiv` when needed.

## Main definitions

  * `non_unital_alg_hom`
  * `alg_hom.to_non_unital_alg_hom`

## Tags

non-unital, algebra, morphism
-/

universes u v w w₁ w₂ w₃

variables (R : Type u) (A : Type v) (B : Type w) (C : Type w₁)

set_option old_structure_cmd true

/-- A morphism respecting addition, multiplication, and scalar multiplication. When these arise from
algebra structures, this is the same as a not-necessarily-unital morphism of algebras. -/
structure non_unital_alg_hom [monoid R]
  [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
  [non_unital_non_assoc_semiring B] [distrib_mul_action R B]
  extends A →+[R] B, mul_hom A B

attribute [nolint doc_blame] non_unital_alg_hom.to_distrib_mul_action_hom
attribute [nolint doc_blame] non_unital_alg_hom.to_mul_hom

namespace non_unital_alg_hom

variables {R A B C} [monoid R]
variables [non_unital_non_assoc_semiring A] [distrib_mul_action R A]
variables [non_unital_non_assoc_semiring B] [distrib_mul_action R B]
variables [non_unital_non_assoc_semiring C] [distrib_mul_action R C]

/-- see Note [function coercion] -/
instance : has_coe_to_fun (non_unital_alg_hom R A B) := ⟨_, to_fun⟩

@[simp] lemma to_fun_eq_coe (f : non_unital_alg_hom R A B) : f.to_fun = ⇑f := rfl

initialize_simps_projections non_unital_alg_hom (to_fun → apply)

lemma coe_injective :
  @function.injective (non_unital_alg_hom R A B) (A → B) coe_fn :=
by rintro ⟨f, _⟩ ⟨g, _⟩ ⟨h⟩; congr

@[ext] lemma ext {f g : non_unital_alg_hom R A B} (h : ∀ x, f x = g x) : f = g :=
coe_injective $ funext h

lemma ext_iff {f g : non_unital_alg_hom R A B} : f = g ↔ ∀ x, f x = g x :=
⟨by { rintro rfl x, refl }, ext⟩

lemma congr_fun {f g : non_unital_alg_hom R A B} (h : f = g) (x : A) : f x = g x := h ▸ rfl

@[simp] lemma coe_mk (f : A → B) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : non_unital_alg_hom R A B) : A → B) = f :=
rfl

@[simp] lemma mk_coe (f : non_unital_alg_hom R A B) (h₁ h₂ h₃ h₄) :
  (⟨f, h₁, h₂, h₃, h₄⟩ : non_unital_alg_hom R A B) = f :=
by { ext, refl, }

instance : has_coe (non_unital_alg_hom R A B) (A →+[R] B) :=
⟨to_distrib_mul_action_hom⟩

instance : has_coe (non_unital_alg_hom R A B) (mul_hom A B) := ⟨to_mul_hom⟩

@[simp] lemma to_distrib_mul_action_hom_eq_coe (f : non_unital_alg_hom R A B) :
  f.to_distrib_mul_action_hom = ↑f :=
rfl

@[simp] lemma to_mul_hom_eq_coe (f : non_unital_alg_hom R A B) : f.to_mul_hom = ↑f :=
rfl

@[simp, norm_cast] lemma coe_to_distrib_mul_action_hom (f : non_unital_alg_hom R A B) :
  ((f : A →+[R] B) : A → B) = f :=
rfl

@[simp, norm_cast] lemma coe_to_mul_hom (f : non_unital_alg_hom R A B) :
  ((f : mul_hom A B) : A → B) = f :=
rfl

lemma to_distrib_mul_action_hom_injective {f g : non_unital_alg_hom R A B}
  (h : (f : A →+[R] B) = (g : A →+[R] B)) : f = g :=
by { ext a, exact distrib_mul_action_hom.congr_fun h a, }

lemma to_mul_hom_injective {f g : non_unital_alg_hom R A B}
  (h : (f : mul_hom A B) = (g : mul_hom A B)) : f = g :=
by { ext a, exact mul_hom.congr_fun h a, }

@[norm_cast] lemma coe_distrib_mul_action_hom_mk (f : non_unital_alg_hom R A B) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : non_unital_alg_hom R A B) : A →+[R] B) =
  ⟨f, h₁, h₂, h₃⟩ :=
by { ext, refl, }

@[norm_cast] lemma coe_mul_hom_mk (f : non_unital_alg_hom R A B) (h₁ h₂ h₃ h₄) :
  ((⟨f, h₁, h₂, h₃, h₄⟩ : non_unital_alg_hom R A B) : mul_hom A B) = ⟨f, h₄⟩ :=
by { ext, refl, }

@[simp] lemma map_smul (f : non_unital_alg_hom R A B) (c : R) (x : A) :
  f (c • x) = c • f x :=
f.to_distrib_mul_action_hom.map_smul c x

@[simp] lemma map_add (f : non_unital_alg_hom R A B) (x y : A) :
  f (x + y) = (f x) + (f y) :=
f.to_distrib_mul_action_hom.map_add x y

@[simp] lemma map_mul (f : non_unital_alg_hom R A B) (x y : A) :
  f (x * y) = (f x) * (f y) :=
f.to_mul_hom.map_mul x y

@[simp] lemma map_zero (f : non_unital_alg_hom R A B) : f 0 = 0 :=
f.to_distrib_mul_action_hom.map_zero

instance : has_zero (non_unital_alg_hom R A B) :=
⟨{ map_mul' := by simp,
   .. (0 : A →+[R] B) }⟩

instance : has_one (non_unital_alg_hom R A A) :=
⟨{ map_mul' := by simp,
   .. (1 : A →+[R] A) }⟩

@[simp] lemma coe_zero : ((0 : non_unital_alg_hom R A B) : A → B) = 0 := rfl

@[simp] lemma coe_one : ((1 : non_unital_alg_hom R A A) : A → A) = id := rfl

lemma zero_apply (a : A) : (0 : non_unital_alg_hom R A B) a = 0 := rfl

lemma one_apply (a : A) : (1 : non_unital_alg_hom R A A) a = a := rfl

instance : inhabited (non_unital_alg_hom R A B) := ⟨0⟩

/-- The composition of morphisms is a morphism. -/
def comp (f : non_unital_alg_hom R B C) (g : non_unital_alg_hom R A B) : non_unital_alg_hom R A C :=
{ .. (f : mul_hom B C).comp (g : mul_hom A B),
  .. (f : B →+[R] C).comp (g : A →+[R] B) }

@[simp, norm_cast] lemma coe_comp (f : non_unital_alg_hom R B C) (g : non_unital_alg_hom R A B) :
  (f.comp g : A → C) = (f : B → C) ∘ (g : A → B) :=
rfl

lemma comp_apply (f : non_unital_alg_hom R B C) (g : non_unital_alg_hom R A B) (x : A) :
  f.comp g x = f (g x) :=
rfl

/-- The inverse of a bijective morphism is a morphism. -/
def inverse (f : non_unital_alg_hom R A B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  non_unital_alg_hom R B A :=
{ .. (f : mul_hom A B).inverse g h₁ h₂,
  .. (f : A →+[R] B).inverse g h₁ h₂ }

@[simp] lemma coe_inverse (f : non_unital_alg_hom R A B) (g : B → A)
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  (inverse f g h₁ h₂ : B → A) = g :=
rfl

end non_unital_alg_hom

namespace alg_hom

variables {R A B} [comm_semiring R] [semiring A] [semiring B] [algebra R A] [algebra R B]

/-- A unital morphism of algebras is a `non_unital_alg_hom`. -/
def to_non_unital_alg_hom (f : A →ₐ[R] B) : non_unital_alg_hom R A B :=
{ map_smul' := f.map_smul, .. f, }

instance non_unital_alg_hom.has_coe : has_coe (A →ₐ[R] B) (non_unital_alg_hom R A B) :=
⟨to_non_unital_alg_hom⟩

@[simp] lemma to_non_unital_alg_hom_eq_coe (f : A →ₐ[R] B) : f.to_non_unital_alg_hom = f :=
rfl

@[simp, norm_cast] lemma coe_to_non_unital_alg_hom (f : A →ₐ[R] B) :
  ((f : non_unital_alg_hom R A B) : A → B) = f :=
rfl

end alg_hom
