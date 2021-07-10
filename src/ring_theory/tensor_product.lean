/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johan Commelin
-/

import linear_algebra.tensor_product
import algebra.algebra.tower

/-!
# The tensor product of R-algebras

Let `R` be a (semi)ring and `A` an `R`-algebra.
In this file we:

- Define the `A`-module structure on `A ⊗ M`, for an `R`-module `M`.
- Define the `R`-algebra structure on `A ⊗ B`, for another `R`-algebra `B`.
  and provide the structure isomorphisms
  * `R ⊗[R] A ≃ₐ[R] A`
  * `A ⊗[R] R ≃ₐ[R] A`
  * `A ⊗[R] B ≃ₐ[R] B ⊗[R] A`
  * `((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C))`

## Main declaration

- `linear_map.base_change A f` is the `A`-linear map `A ⊗ f`, for an `R`-linear map `f`.

## Implementation notes

The heterobasic definitions below such as:
 * `tensor_product.algebra_tensor_module.curry`
 * `tensor_product.algebra_tensor_module.uncurry`
 * `tensor_product.algebra_tensor_module.lcurry`
 * `tensor_product.algebra_tensor_module.lift`
 * `tensor_product.algebra_tensor_module.lift.equiv`
 * `tensor_product.algebra_tensor_module.mk`
 * `tensor_product.algebra_tensor_module.assoc`

are just more general versions of the definitions already in `linear_algebra/tensor_product`. We
could thus consider replacing the less general definitions with these ones. If we do this, we
probably should still implement the less general ones as abbreviations to the more general ones with
fewer type arguments.
-/

universes u v₁ v₂ v₃ v₄

open_locale tensor_product
open tensor_product

namespace tensor_product

variables {R A M N P : Type*}

/-!
### The `A`-module structure on `A ⊗[R] M`
-/

open linear_map
open algebra (lsmul)

namespace algebra_tensor_module

section semiring
variables [comm_semiring R] [semiring A] [algebra R A]
variables [add_comm_monoid M] [module R M] [module A M] [is_scalar_tower R A M]
variables [add_comm_monoid N] [module R N]
variables [add_comm_monoid P] [module R P] [module A P] [is_scalar_tower R A P]

lemma smul_eq_lsmul_rtensor (a : A) (x : M ⊗[R] N) : a • x = (lsmul R M a).rtensor N x := rfl

/-- Heterobasic version of `tensor_product.curry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps] def curry (f : (M ⊗[R] N) →ₗ[A] P) : M →ₗ[A] (N →ₗ[R] P) :=
{ map_smul' := λ c x, linear_map.ext $ λ y, f.map_smul c (x ⊗ₜ y),
  .. curry (f.restrict_scalars R) }

lemma restrict_scalars_curry (f : (M ⊗[R] N) →ₗ[A] P) :
  restrict_scalars R (curry f) = curry (f.restrict_scalars R) :=
rfl

/-- Just as `tensor_product.mk_compr₂_inj` is marked `ext` instead of `tensor_product.ext`, this is
a better `ext` lemma than `tensor_product.algebra_tensor_module.ext` below.

See note [partially-applied ext lemmas]. -/
@[ext] lemma curry_injective :
  function.injective (curry : (M ⊗ N →ₗ[A] P) → (M →ₗ[A] N →ₗ[R] P)) :=
λ x y h, linear_map.restrict_scalars_injective R $ curry_injective $
  (congr_arg (linear_map.restrict_scalars R) h : _)

theorem ext {g h : (M ⊗[R] N) →ₗ[A] P}
  (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
curry_injective $ linear_map.ext₂ H

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A] [algebra R A]
variables [add_comm_monoid M] [module R M] [module A M] [is_scalar_tower R A M]
variables [add_comm_monoid N] [module R N]
variables [add_comm_monoid P] [module R P] [module A P] [is_scalar_tower R A P]

/-- Heterobasic version of `tensor_product.lift`:

Constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P` with the
property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps] def lift (f : M →ₗ[A] (N →ₗ[R] P)) : (M ⊗[R] N) →ₗ[A] P :=
{ map_smul' := λ c, show ∀ x : M ⊗[R] N, (lift (f.restrict_scalars R)).comp (lsmul R _ c) x =
      (lsmul R _ c).comp (lift (f.restrict_scalars R)) x,
    from ext_iff.1 $ tensor_product.ext $ λ x y,
    by simp only [comp_apply, algebra.lsmul_coe, smul_tmul', lift.tmul, coe_restrict_scalars_eq_coe,
        f.map_smul, smul_apply],
  .. lift (f.restrict_scalars R) }

@[simp] lemma lift_tmul (f : M →ₗ[A] (N →ₗ[R] P)) (x : M) (y : N) :
  lift f (x ⊗ₜ y) = f x y :=
lift.tmul' x y

variables (R A M N P)
/-- Heterobasic version of `tensor_product.uncurry`:

Linearly constructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P`
with the property that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is
the given bilinear map `M →[A] N →[R] P`. -/
@[simps] def uncurry : (M →ₗ[A] (N →ₗ[R] P)) →ₗ[A] ((M ⊗[R] N) →ₗ[A] P) :=
{ to_fun := lift,
  map_add' := λ f g, ext $ λ x y, by simp only [lift_tmul, add_apply],
  map_smul' := λ c f, ext $ λ x y, by simp only [lift_tmul, smul_apply] }

/-- Heterobasic version of `tensor_product.lcurry`:

Given a linear map `M ⊗[R] N →[A] P`, compose it with the canonical
bilinear map `M →[A] N →[R] M ⊗[R] N` to form a bilinear map `M →[A] N →[R] P`. -/
@[simps] def lcurry : ((M ⊗[R] N) →ₗ[A] P) →ₗ[A] (M →ₗ[A] (N →ₗ[R] P)) :=
{ to_fun := curry,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl }

/-- Heterobasic version of `tensor_product.lift.equiv`:

A linear equivalence constructing a linear map `M ⊗[R] N →[A] P` given a
bilinear map `M →[A] N →[R] P` with the property that its composition with the
canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is the given bilinear map `M →[A] N →[R] P`. -/
def lift.equiv : (M →ₗ[A] (N →ₗ[R] P)) ≃ₗ[A] ((M ⊗[R] N) →ₗ[A] P) :=
linear_equiv.of_linear (uncurry R A M N P) (lcurry R A M N P)
  (linear_map.ext $ λ f, ext $ λ x y, lift_tmul _ x y)
  (linear_map.ext $ λ f, linear_map.ext $ λ x, linear_map.ext $ λ y, lift_tmul f x y)

variables (R A M N P)
/-- Heterobasic version of `tensor_product.mk`:

The canonical bilinear map `M →[A] N →[R] M ⊗[R] N`. -/
@[simps] def mk : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=
{ map_smul' := λ c x, rfl,
  .. mk R M N }

/-- Heterobasic version of `tensor_product.assoc`:

Linear equivalence between `(M ⊗[A] N) ⊗[R] P` and `M ⊗[A] (N ⊗[R] P)`. -/
def assoc : ((M ⊗[A] P) ⊗[R] N) ≃ₗ[A] (M ⊗[A] (P ⊗[R] N)) :=
linear_equiv.of_linear
  (lift $ tensor_product.uncurry A _ _ _ $ comp (lcurry R A _ _ _) $
    tensor_product.mk A M (P ⊗[R] N))
  (tensor_product.uncurry A _ _ _ $ comp (uncurry R A _ _ _) $
    by apply tensor_product.curry; exact (mk R A _ _))
  (by { ext, refl, })
  (by { ext, refl, })

end comm_semiring

end algebra_tensor_module

end tensor_product

namespace linear_map
open tensor_product

/-!
### The base-change of a linear map of `R`-modules to a linear map of `A`-modules
-/

section semiring

variables {R A B M N : Type*} [comm_semiring R]
variables [semiring A] [algebra R A] [semiring B] [algebra R B]
variables [add_comm_monoid M] [module R M] [add_comm_monoid N] [module R N]
variables (r : R) (f g : M →ₗ[R] N)

variables (A)

/-- `base_change A f` for `f : M →ₗ[R] N` is the `A`-linear map `A ⊗[R] M →ₗ[A] A ⊗[R] N`. -/
def base_change (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N :=
{ to_fun := f.ltensor A,
  map_add' := (f.ltensor A).map_add,
  map_smul' := λ a x,
    show (f.ltensor A) (rtensor M (algebra.lmul R A a) x) =
      (rtensor N ((algebra.lmul R A) a)) ((ltensor A f) x),
    by simp only [← comp_apply, ltensor_comp_rtensor, rtensor_comp_ltensor] }

variables {A}

@[simp] lemma base_change_tmul (a : A) (x : M) :
  f.base_change A (a ⊗ₜ x) = a ⊗ₜ (f x) := rfl

lemma base_change_eq_ltensor :
  (f.base_change A : A ⊗ M → A ⊗ N) = f.ltensor A := rfl

@[simp] lemma base_change_add :
  (f + g).base_change A = f.base_change A + g.base_change A :=
by { ext, simp [base_change_eq_ltensor], }

@[simp] lemma base_change_zero : base_change A (0 : M →ₗ[R] N) = 0 :=
by { ext, simp [base_change_eq_ltensor], }

@[simp] lemma base_change_smul : (r • f).base_change A = r • (f.base_change A) :=
by { ext, simp [base_change_tmul], }

variables (R A M N)
/-- `base_change` as a linear map. -/
@[simps] def base_change_hom : (M →ₗ[R] N) →ₗ[R] A ⊗[R] M →ₗ[A] A ⊗[R] N :=
{ to_fun := base_change A,
  map_add' := base_change_add,
  map_smul' := base_change_smul }

end semiring

section ring

variables {R A B M N : Type*} [comm_ring R]
variables [ring A] [algebra R A] [ring B] [algebra R B]
variables [add_comm_group M] [module R M] [add_comm_group N] [module R N]
variables (f g : M →ₗ[R] N)

@[simp] lemma base_change_sub :
  (f - g).base_change A = f.base_change A - g.base_change A :=
by { ext, simp [base_change_eq_ltensor], }

@[simp] lemma base_change_neg : (-f).base_change A = -(f.base_change A) :=
by { ext, simp [base_change_eq_ltensor], }

end ring

end linear_map

namespace algebra
namespace tensor_product

section semiring

variables {R : Type u} [comm_semiring R]
variables {A : Type v₁} [semiring A] [algebra R A]
variables {B : Type v₂} [semiring B] [algebra R B]

/-!
### The `R`-algebra structure on `A ⊗[R] B`
-/

/--
(Implementation detail)
The multiplication map on `A ⊗[R] B`,
for a fixed pure tensor in the first argument,
as an `R`-linear map.
-/
def mul_aux (a₁ : A) (b₁ : B) : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) :=
tensor_product.map (lmul_left R a₁) (lmul_left R b₁)

@[simp]
lemma mul_aux_apply (a₁ a₂ : A) (b₁ b₂ : B) :
  (mul_aux a₁ b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
rfl

/--
(Implementation detail)
The multiplication map on `A ⊗[R] B`,
as an `R`-bilinear map.
-/
def mul : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) :=
tensor_product.lift $ linear_map.mk₂ R mul_aux
  (λ x₁ x₂ y, tensor_product.ext $ λ x' y',
    by simp only [mul_aux_apply, linear_map.add_apply, add_mul, add_tmul])
  (λ c x y, tensor_product.ext $ λ x' y',
    by simp only [mul_aux_apply, linear_map.smul_apply, smul_tmul', smul_mul_assoc])
  (λ x y₁ y₂, tensor_product.ext $ λ x' y',
    by simp only [mul_aux_apply, linear_map.add_apply, add_mul, tmul_add])
  (λ c x y, tensor_product.ext $ λ x' y',
    by simp only [mul_aux_apply, linear_map.smul_apply, smul_tmul, smul_tmul', smul_mul_assoc])

@[simp]
lemma mul_apply (a₁ a₂ : A) (b₁ b₂ : B) :
  mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
rfl

lemma mul_assoc' (mul : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) →ₗ[R] (A ⊗[R] B))
  (h : ∀ (a₁ a₂ a₃ : A) (b₁ b₂ b₃ : B),
    mul (mul (a₁ ⊗ₜ[R] b₁) (a₂ ⊗ₜ[R] b₂)) (a₃ ⊗ₜ[R] b₃) =
      mul (a₁ ⊗ₜ[R] b₁) (mul (a₂ ⊗ₜ[R] b₂) (a₃ ⊗ₜ[R] b₃))) :
  ∀ (x y z : A ⊗[R] B), mul (mul x y) z = mul x (mul y z) :=
begin
    intros,
    apply tensor_product.induction_on x,
    { simp, },
    apply tensor_product.induction_on y,
    { simp, },
    apply tensor_product.induction_on z,
    { simp, },
    { intros, simp [h], },
    { intros, simp [linear_map.map_add, *], },
    { intros, simp [linear_map.map_add, *], },
    { intros, simp [linear_map.map_add, *], },
end

lemma mul_assoc (x y z : A ⊗[R] B) : mul (mul x y) z = mul x (mul y z) :=
mul_assoc' mul (by { intros, simp only [mul_apply, mul_assoc], }) x y z

lemma one_mul (x : A ⊗[R] B) : mul (1 ⊗ₜ 1) x = x :=
begin
  apply tensor_product.induction_on x;
  simp {contextual := tt},
end

lemma mul_one (x : A ⊗[R] B) : mul x (1 ⊗ₜ 1) = x :=
begin
  apply tensor_product.induction_on x;
  simp {contextual := tt},
end

instance : semiring (A ⊗[R] B) :=
{ zero := 0,
  add := (+),
  one := 1 ⊗ₜ 1,
  mul := λ a b, mul a b,
  one_mul := one_mul,
  mul_one := mul_one,
  mul_assoc := mul_assoc,
  zero_mul := by simp,
  mul_zero := by simp,
  left_distrib := by simp,
  right_distrib := by simp,
  .. (by apply_instance : add_comm_monoid (A ⊗[R] B)) }.

lemma one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) := rfl

@[simp]
lemma tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :
  (a₁ ⊗ₜ[R] b₁) * (a₂ ⊗ₜ[R] b₂) = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=
rfl

@[simp]
lemma tmul_pow (a : A) (b : B) (k : ℕ) :
  (a ⊗ₜ[R] b)^k = (a^k) ⊗ₜ[R] (b^k) :=
begin
  induction k with k ih,
  { simp [one_def], },
  { simp [pow_succ, ih], }
end


/--
The algebra map `R →+* (A ⊗[R] B)` giving `A ⊗[R] B` the structure of an `R`-algebra.
-/
def tensor_algebra_map : R →+* (A ⊗[R] B) :=
{ to_fun := λ r, algebra_map R A r ⊗ₜ[R] 1,
  map_one' := by { simp, refl },
  map_mul' := by simp,
  map_zero' := by simp [zero_tmul],
  map_add' := by simp [add_tmul], }

instance : algebra R (A ⊗[R] B) :=
{ commutes' := λ r x,
  begin
    apply tensor_product.induction_on x,
    { simp, },
    { intros a b, simp [tensor_algebra_map, algebra.commutes], },
    { intros y y' h h', simp at h h', simp [mul_add, add_mul, h, h'], },
  end,
  smul_def' := λ r x,
  begin
    apply tensor_product.induction_on x,
    { simp [smul_zero], },
    { intros a b,
      rw [tensor_algebra_map, ←tmul_smul, ←smul_tmul, algebra.smul_def r a],
      simp, },
    { intros, dsimp, simp [smul_add, mul_add, *], },
  end,
  .. tensor_algebra_map,
  .. (by apply_instance : module R (A ⊗[R] B)) }.

@[simp]
lemma algebra_map_apply (r : R) :
  (algebra_map R (A ⊗[R] B)) r = ((algebra_map R A) r) ⊗ₜ[R] 1 := rfl

variables {C : Type v₃} [semiring C] [algebra R C]

@[ext]
theorem ext {g h : (A ⊗[R] B) →ₐ[R] C}
  (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
begin
  apply @alg_hom.to_linear_map_injective R (A ⊗[R] B) C _ _ _ _ _ _ _ _,
  ext,
  simp [H],
end

/-- The algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`. -/
def include_left : A →ₐ[R] A ⊗[R] B :=
{ to_fun := λ a, a ⊗ₜ 1,
  map_zero' := by simp,
  map_add' := by simp [add_tmul],
  map_one' := rfl,
  map_mul' := by simp,
  commutes' := by simp, }

@[simp]
lemma include_left_apply (a : A) : (include_left : A →ₐ[R] A ⊗[R] B) a = a ⊗ₜ 1 := rfl

/-- The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`. -/
def include_right : B →ₐ[R] A ⊗[R] B :=
{ to_fun := λ b, 1 ⊗ₜ b,
  map_zero' := by simp,
  map_add' := by simp [tmul_add],
  map_one' := rfl,
  map_mul' := by simp,
  commutes' := λ r,
  begin
    simp only [algebra_map_apply],
    transitivity r • ((1 : A) ⊗ₜ[R] (1 : B)),
    { rw [←tmul_smul, algebra.smul_def], simp, },
    { simp [algebra.smul_def], },
  end, }

@[simp]
lemma include_right_apply (b : B) : (include_right : B →ₐ[R] A ⊗[R] B) b = 1 ⊗ₜ b := rfl

end semiring

section ring

variables {R : Type u} [comm_ring R]
variables {A : Type v₁} [ring A] [algebra R A]
variables {B : Type v₂} [ring B] [algebra R B]

instance : ring (A ⊗[R] B) :=
{ .. (by apply_instance : add_comm_group (A ⊗[R] B)),
  .. (by apply_instance : semiring (A ⊗[R] B)) }.

end ring

section comm_ring

variables {R : Type u} [comm_ring R]
variables {A : Type v₁} [comm_ring A] [algebra R A]
variables {B : Type v₂} [comm_ring B] [algebra R B]

instance : comm_ring (A ⊗[R] B) :=
{ mul_comm := λ x y,
  begin
    apply tensor_product.induction_on x,
    { simp, },
    { intros a₁ b₁,
      apply tensor_product.induction_on y,
      { simp, },
      { intros a₂ b₂,
        simp [mul_comm], },
      { intros a₂ b₂ ha hb,
        simp [mul_add, add_mul, ha, hb], }, },
    { intros x₁ x₂ h₁ h₂,
      simp [mul_add, add_mul, h₁, h₂], },
  end
  .. (by apply_instance : ring (A ⊗[R] B)) }.

end comm_ring

/--
Verify that typeclass search finds the ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely rings, by treating both as `ℤ`-algebras.
-/
example {A : Type v₁} [ring A] {B : Type v₂} [ring B] : ring (A ⊗[ℤ] B) :=
by apply_instance

/--
Verify that typeclass search finds the comm_ring structure on `A ⊗[ℤ] B`
when `A` and `B` are merely comm_rings, by treating both as `ℤ`-algebras.
-/
example {A : Type v₁} [comm_ring A] {B : Type v₂} [comm_ring B] : comm_ring (A ⊗[ℤ] B) :=
by apply_instance

/-!
We now build the structure maps for the symmetric monoidal category of `R`-algebras.
-/
section monoidal

section
variables {R : Type u} [comm_semiring R]
variables {A : Type v₁} [semiring A] [algebra R A]
variables {B : Type v₂} [semiring B] [algebra R B]
variables {C : Type v₃} [semiring C] [algebra R C]
variables {D : Type v₄} [semiring D] [algebra R D]

/--
Build an algebra morphism from a linear map out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def alg_hom_of_linear_map_tensor_product
  (f : A ⊗[R] B →ₗ[R] C)
  (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
  (w₂ : ∀ r, f ((algebra_map R A) r ⊗ₜ[R] 1) = (algebra_map R C) r):
  A ⊗[R] B →ₐ[R] C :=
{ map_one' := by simpa using w₂ 1,
  map_zero' := by simp,
  map_mul' := λ x y,
  begin
    apply tensor_product.induction_on x,
    { simp, },
    { intros a₁ b₁,
      apply tensor_product.induction_on y,
      { simp, },
      { intros a₂ b₂,
        simp [w₁], },
      { intros x₁ x₂ h₁ h₂,
        simp at h₁, simp at h₂,
        simp [mul_add, add_mul, h₁, h₂], }, },
    { intros x₁ x₂ h₁ h₂,
      simp at h₁, simp at h₂,
      simp [mul_add, add_mul, h₁, h₂], }
  end,
  commutes' := λ r, by simp [w₂],
  .. f }

@[simp]
lemma alg_hom_of_linear_map_tensor_product_apply (f w₁ w₂ x) :
  (alg_hom_of_linear_map_tensor_product f w₁ w₂ : A ⊗[R] B →ₐ[R] C) x = f x := rfl

/--
Build an algebra equivalence from a linear equivalence out of a tensor product,
and evidence of multiplicativity on pure tensors.
-/
def alg_equiv_of_linear_equiv_tensor_product
  (f : A ⊗[R] B ≃ₗ[R] C)
  (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B), f ((a₁ * a₂) ⊗ₜ (b₁ * b₂)) = f (a₁ ⊗ₜ b₁) * f (a₂ ⊗ₜ b₂))
  (w₂ : ∀ r, f ((algebra_map R A) r ⊗ₜ[R] 1) = (algebra_map R C) r):
  A ⊗[R] B ≃ₐ[R] C :=
{ .. alg_hom_of_linear_map_tensor_product (f : A ⊗[R] B →ₗ[R] C) w₁ w₂,
  .. f }

@[simp]
lemma alg_equiv_of_linear_equiv_tensor_product_apply (f w₁ w₂ x) :
  (alg_equiv_of_linear_equiv_tensor_product f w₁ w₂ : A ⊗[R] B ≃ₐ[R] C) x = f x := rfl

/--
Build an algebra equivalence from a linear equivalence out of a triple tensor product,
and evidence of multiplicativity on pure tensors.
-/
def alg_equiv_of_linear_equiv_triple_tensor_product
  (f : ((A ⊗[R] B) ⊗[R] C) ≃ₗ[R] D)
  (w₁ : ∀ (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C),
    f ((a₁ * a₂) ⊗ₜ (b₁ * b₂) ⊗ₜ (c₁ * c₂)) = f (a₁ ⊗ₜ b₁ ⊗ₜ c₁) * f (a₂ ⊗ₜ b₂ ⊗ₜ c₂))
  (w₂ : ∀ r, f (((algebra_map R A) r ⊗ₜ[R] (1 : B)) ⊗ₜ[R] (1 : C)) = (algebra_map R D) r) :
  (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D :=
{ to_fun := f,
  map_mul' := λ x y,
  begin
    apply tensor_product.induction_on x,
    { simp, },
    { intros ab₁ c₁,
      apply tensor_product.induction_on y,
      { simp, },
      { intros ab₂ c₂,
        apply tensor_product.induction_on ab₁,
        { simp, },
        { intros a₁ b₁,
          apply tensor_product.induction_on ab₂,
          { simp, },
          { simp [w₁], },
          { intros x₁ x₂ h₁ h₂,
            simp at h₁ h₂,
            simp [mul_add, add_tmul, h₁, h₂], }, },
        { intros x₁ x₂ h₁ h₂,
          simp at h₁ h₂,
          simp [add_mul, add_tmul, h₁, h₂], }, },
      { intros x₁ x₂ h₁ h₂,
        simp [mul_add, add_mul, h₁, h₂], }, },
    { intros x₁ x₂ h₁ h₂,
      simp [mul_add, add_mul, h₁, h₂], }
  end,
  commutes' := λ r, by simp [w₂],
  .. f }

@[simp]
lemma alg_equiv_of_linear_equiv_triple_tensor_product_apply (f w₁ w₂ x) :
  (alg_equiv_of_linear_equiv_triple_tensor_product f w₁ w₂ : (A ⊗[R] B) ⊗[R] C ≃ₐ[R] D) x = f x :=
rfl

end

variables {R : Type u} [comm_semiring R]
variables {A : Type v₁} [semiring A] [algebra R A]
variables {B : Type v₂} [semiring B] [algebra R B]
variables {C : Type v₃} [semiring C] [algebra R C]
variables {D : Type v₄} [semiring D] [algebra R D]

section
variables (R A)
/--
The base ring is a left identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected def lid : R ⊗[R] A ≃ₐ[R] A :=
alg_equiv_of_linear_equiv_tensor_product (tensor_product.lid R A)
(by simp [mul_smul]) (by simp [algebra.smul_def])

@[simp] theorem lid_tmul (r : R) (a : A) :
  (tensor_product.lid R A : (R ⊗ A → A)) (r ⊗ₜ a) = r • a :=
by simp [tensor_product.lid]

/--
The base ring is a right identity for the tensor product of algebra, up to algebra isomorphism.
-/
protected def rid : A ⊗[R] R ≃ₐ[R] A :=
alg_equiv_of_linear_equiv_tensor_product (tensor_product.rid R A)
(by simp [mul_smul]) (by simp [algebra.smul_def])

@[simp] theorem rid_tmul (r : R) (a : A) :
  (tensor_product.rid R A : (A ⊗ R → A)) (a ⊗ₜ r) = r • a :=
by simp [tensor_product.rid]

section
variables (R A B)

/--
The tensor product of R-algebras is commutative, up to algebra isomorphism.
-/
protected def comm : A ⊗[R] B ≃ₐ[R] B ⊗[R] A :=
alg_equiv_of_linear_equiv_tensor_product (tensor_product.comm R A B)
(by simp)
(λ r, begin
  transitivity r • ((1 : B) ⊗ₜ[R] (1 : A)),
  { rw [←tmul_smul, algebra.smul_def], simp, },
  { simp [algebra.smul_def], },
end)

@[simp]
theorem comm_tmul (a : A) (b : B) :
  (tensor_product.comm R A B : (A ⊗[R] B → B ⊗[R] A)) (a ⊗ₜ b) = (b ⊗ₜ a) :=
by simp [tensor_product.comm]

end

section
variables {R A B C}

lemma assoc_aux_1 (a₁ a₂ : A) (b₁ b₂ : B) (c₁ c₂ : C) :
  (tensor_product.assoc R A B C) (((a₁ * a₂) ⊗ₜ[R] (b₁ * b₂)) ⊗ₜ[R] (c₁ * c₂)) =
    (tensor_product.assoc R A B C) ((a₁ ⊗ₜ[R] b₁) ⊗ₜ[R] c₁) *
      (tensor_product.assoc R A B C) ((a₂ ⊗ₜ[R] b₂) ⊗ₜ[R] c₂) :=
rfl

lemma assoc_aux_2 (r : R) :
  (tensor_product.assoc R A B C) (((algebra_map R A) r ⊗ₜ[R] 1) ⊗ₜ[R] 1) =
    (algebra_map R (A ⊗ (B ⊗ C))) r := rfl

-- variables (R A B C)

-- -- local attribute [elab_simple] alg_equiv_of_linear_equiv_triple_tensor_product

-- /-- The associator for tensor product of R-algebras, as an algebra isomorphism. -/
-- -- FIXME This is _really_ slow to compile. :-(
-- protected def assoc : ((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C)) :=
-- alg_equiv_of_linear_equiv_triple_tensor_product
--   (tensor_product.assoc R A B C)
--   assoc_aux_1 assoc_aux_2

-- variables {R A B C}

-- @[simp] theorem assoc_tmul (a : A) (b : B) (c : C) :
--   ((tensor_product.assoc R A B C) :
--   (A ⊗[R] B) ⊗[R] C → A ⊗[R] (B ⊗[R] C)) ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
-- rfl

end

variables {R A B C D}

/-- The tensor product of a pair of algebra morphisms. -/
def map (f : A →ₐ[R] B) (g : C →ₐ[R] D) : A ⊗[R] C →ₐ[R] B ⊗[R] D :=
alg_hom_of_linear_map_tensor_product
  (tensor_product.map f.to_linear_map g.to_linear_map)
  (by simp)
  (by simp [alg_hom.commutes])

@[simp] theorem map_tmul (f : A →ₐ[R] B) (g : C →ₐ[R] D) (a : A) (c : C) :
  map f g (a ⊗ₜ c) = f a ⊗ₜ g c :=
rfl

/--
Construct an isomorphism between tensor products of R-algebras
from isomorphisms between the tensor factors.
-/
def congr (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) : A ⊗[R] C ≃ₐ[R] B ⊗[R] D :=
alg_equiv.of_alg_hom (map f g) (map f.symm g.symm)
  (ext $ λ b d, by simp)
  (ext $ λ a c, by simp)

@[simp]
lemma congr_apply (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x) :
  congr f g x = (map (f : A →ₐ[R] B) (g : C →ₐ[R] D)) x := rfl

@[simp]
lemma congr_symm_apply (f : A ≃ₐ[R] B) (g : C ≃ₐ[R] D) (x) :
  (congr f g).symm x = (map (f.symm : B →ₐ[R] A) (g.symm : D →ₐ[R] C)) x := rfl

end

end monoidal

end tensor_product

end algebra
