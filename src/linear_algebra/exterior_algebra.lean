/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser.
-/

import algebra.ring_quot
import linear_algebra.tensor_algebra
import group_theory.perm.sign

/-!
# Exterior Algebras

We construct the exterior algebra of a semimodule `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-semimodule `M` is denoted as `exterior_algebra R M`.
It is endowed with the structure of an `R`-algebra.

Given a linear morphism `f : M → A` from a semimodule `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `exterior_algebra.lift R f cond`.

The canonical linear map `M → exterior_algebra R M` is denoted `exterior_algebra.ι R`.

## Theorems

The main theorems proved ensure that `exterior_algebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is  fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.

## Implementation details

The exterior algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `exterior_algebra.rel R M` on `tensor_algebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `0`.
2. The exterior algebra is the quotient of the tensor algebra by this relation.

-/

variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_monoid M] [semimodule R M]


namespace alg_hom

variables {A : Type*} [semiring A] [algebra R A]
variables {B : Type*} [semiring B] [algebra R B]
variables {R}

@[simp]
lemma to_fun_eq_coe (f : A →ₐ[R] B) : f.to_fun = ⇑f := rfl

end alg_hom

namespace exterior_algebra
open tensor_algebra

/-- `rel` relates each `ι m * ι m`, for `m : M`, with `0`.

The exterior algebra of `M` is defined as the quotient modulo this relation.
-/
inductive rel : tensor_algebra R M → tensor_algebra R M → Prop
| of (m : M) : rel ((ι R m) * (ι R m)) 0

end exterior_algebra

/--
The exterior algebra of an `R`-semimodule `M`.
-/
@[derive [inhabited, semiring, algebra R]]
def exterior_algebra := ring_quot (exterior_algebra.rel R M)

namespace exterior_algebra

structure hom (A : Type*) [semiring A] [algebra R A] extends linear_map R M A :=
(square_eq_zero' : ∀ x, to_fun x * to_fun x = 0)

infixr ` →ₗₑ `:25 := hom _
notation M ` →ₗₑ[`:25 R:25 `] `:0 A:0 := hom R M A

namespace hom

variables (A : Type*) [semiring A] [algebra R A]

instance : has_coe_to_fun (M →ₗₑ[R] A) :=
⟨λ _, M → A, λ x, hom.to_linear_map x⟩

variables {R M A} (f : M →ₗₑ[R] A)

@[simp] lemma coe_to_linear_map : ⇑(f.to_linear_map) = f := rfl

@[simp] lemma coe_mk (f : M →ₗ[R] A) (h₁) :
  ((hom.mk f h₁ : M →ₗₑ[R] A) : M → A) = f := rfl

lemma square_eq_zero : ∀ x : M, f x * f x = 0 :=
f.square_eq_zero'

variables {A₂ : Type*} [semiring A₂] [algebra R A₂] (g : A →ₐ[R] A₂) (h : M →ₗₑ[R] A)

def comp  : M →ₗₑ[R] A₂ :=
{ square_eq_zero' := λ x, by simp [← alg_hom.map_mul, h.square_eq_zero],
  ..(g.to_linear_map.comp h.to_linear_map)}

@[simp] lemma comp_apply (x : M) : hom.comp g h x = g (h x) := rfl

@[norm_cast]
lemma comp_coe : (g : A → A₂) ∘ (h : M → A) = hom.comp g h := rfl

end hom

variables {M}


/--
The canonical linear map `M →ₗ[R] exterior_algebra R M`.
-/
def ι : M →ₗₑ[R] (exterior_algebra R M) :=
{ square_eq_zero' := λ m, begin
    dsimp [linear_map.to_fun_eq_coe],
    rw [←alg_hom.map_mul, ←alg_hom.map_zero _],
    exact ring_quot.mk_alg_hom_rel R (rel.of m),
  end,
  ..(ring_quot.mk_alg_hom R _).to_linear_map.comp (tensor_algebra.ι R)}


variables {R}

variables (R) {A : Type*} [semiring A] [algebra R A]

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `exterior_algebra R M` to `A`.
-/
def lift (f : M →ₗₑ[R] A) : exterior_algebra R M →ₐ[R] A :=
ring_quot.lift_alg_hom R (tensor_algebra.lift R f.to_linear_map)
  (λ x y h, by {
    induction h,
    rw [alg_hom.map_zero, alg_hom.map_mul, tensor_algebra.lift_ι_apply],
    rw [f.coe_to_linear_map, f.square_eq_zero], })

@[simp]
theorem ι_comp_lift (f : M →ₗₑ[R] A) :
  (lift R f) ∘ (ι R) = f :=
by { ext, simp [lift, ι] }

@[simp]
theorem lift_ι_apply (f : M →ₗₑ[R] A) (x) :
  lift R f (ι R x) = f x :=
by { dsimp [lift, ι], simp, }

@[simp]
theorem lift_unique (f : M →ₗₑ[R] A)
  (g : exterior_algebra R M →ₐ[R] A) : hom.comp g (ι R) = f ↔ g = lift R f :=
begin
  refine ⟨λ h, _, λ hyp, by sorry⟩,
  sorry
end

attribute [irreducible] exterior_algebra ι lift

variables {R M}

@[simp]
theorem comp_ι_square_zero (g : exterior_algebra R M →ₐ[R] A)
  (m : M) : g (ι R m) * g (ι R m) = 0 :=
by rw [←alg_hom.map_mul, (ι R).square_eq_zero, alg_hom.map_zero]

@[simp]
theorem lift_comp_ι (g : exterior_algebra R M →ₐ[R] A) :
  lift R (hom.comp g (ι R)) = g :=
by { symmetry, rw ←lift_unique, }

@[ext]
theorem hom_ext {f g : exterior_algebra R M →ₐ[R] A} :
  hom.comp f (ι R) = hom.comp g (ι R) → f = g :=
begin
  intro hyp,
  let h := hom.comp g (ι R),
  have : g = lift R h, by rw ←lift_unique,
  rw [this, ←lift_unique, hyp],
end


section wip

-- This looks dangerous!
def bad_coe : has_coe (M →ₗₑ[R] A) (M → A) := ⟨λ f, f⟩

local attribute [instance] bad_coe

instance : has_universal_property R M (exterior_algebra R M) (λ A _ _, by exactI M →ₗₑ[R] A) := {
  -- homomorphisms are regular functions
  hom_comp := λ _ _ _ f g, by exactI hom.comp f g,
  hom_comp_eq := λ _ _ _ f g, rfl,
  hom_ext' := λ _ _ _ f g, ⟨λ h, by sorry, λ h, h ▸ rfl⟩,
  -- connect the boilerplate
  ι := ι R,
  lift := λ _ _ _ f, by exactI lift R f,
  lift_unique := λ _ _ _ f g, by exactI lift_unique R f g }

end wip


end exterior_algebra
