/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/

import algebra.algebra.basic

universes u v₁ v₂ v₃ v₄


/-!
# The tensor product of R-algebras

We construct the R-algebra structure on `A ⊗[R] B`, when `A` and `B` are both `R`-algebras,
and provide the structure isomorphisms

* `R ⊗[R] A ≃ₐ[R] A`
* `A ⊗[R] R ≃ₐ[R] A`
* `A ⊗[R] B ≃ₐ[R] B ⊗[R] A`

The code for
* `((A ⊗[R] B) ⊗[R] C) ≃ₐ[R] (A ⊗[R] (B ⊗[R] C))`
is written and compiles, but takes longer than the `-T100000` time limit,
so is currently commented out.
-/

namespace algebra

open_locale tensor_product
open tensor_product

namespace tensor_product

section semiring

variables {R : Type u} [comm_semiring R]
variables {A : Type v₁} [semiring A] [algebra R A]
variables {B : Type v₂} [semiring B] [algebra R B]

/--
(Implementation detail)
The multiplication map on `A ⊗[R] B`,
for a fixed pure tensor in the first argument,
as an `R`-linear map.
-/
def mul_aux (a₁ : A) (b₁ : B) : (A ⊗[R] B) →ₗ[R] (A ⊗[R] B) :=
begin
  -- Why doesn't `apply tensor_product.lift` work?
  apply @tensor_product.lift R _ A B (A ⊗[R] B) _ _ _ _ _ _ _,
  fsplit,
  intro a₂,
  fsplit,
  intro b₂,
  exact (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂),
  { intros b₂ b₂',
    simp [mul_add, tmul_add], },
  { intros c b₂,
    simp [mul_smul, tmul_smul], },
  { intros a₂ a₂', ext b₂,
    simp [mul_add, add_tmul], },
  { intros c a₂, ext b₂,
    simp [mul_smul, smul_tmul], }
end

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
begin
  apply @tensor_product.lift R _ A B ((A ⊗[R] B) →ₗ[R] (A ⊗[R] B)) _ _ _ _ _ _ _,
  fsplit,
  intro a₁,
  fsplit,
  intro b₁,
  exact mul_aux a₁ b₁,
  { intros b₁ b₁',
    -- Why doesn't just `apply tensor_product.ext`, or indeed `ext` work?!
    apply @tensor_product.ext R _ A B (A ⊗[R] B) _ _ _ _ _ _,
    intros a₂ b₂,
    simp [add_mul, tmul_add], },
  { intros c b₁,
    apply @tensor_product.ext R _ A B (A ⊗[R] B) _ _ _ _ _ _,
    intros a₂ b₂,
    simp, },
  { intros a₁ a₁', ext1 b₁,
    apply @tensor_product.ext R _ A B (A ⊗[R] B) _ _ _ _ _ _,
    intros a₂ b₂,
    simp [add_mul, add_tmul], },
  { intros c a₁, ext1 b₁,
    apply @tensor_product.ext R _ A B (A ⊗[R] B) _ _ _ _ _ _,
    intros a₂ b₂,
    simp [smul_tmul], },
end

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
  .. (by apply_instance : semimodule R (A ⊗[R] B)) }.

@[simp]
lemma algebra_map_apply (r : R) :
  (algebra_map R (A ⊗[R] B)) r = ((algebra_map R A) r) ⊗ₜ[R] 1 := rfl

variables {C : Type v₃} [semiring C] [algebra R C]

@[ext]
theorem ext {g h : (A ⊗[R] B) →ₐ[R] C}
  (H : ∀ a b, g (a ⊗ₜ b) = h (a ⊗ₜ b)) : g = h :=
begin
  apply @alg_hom.to_linear_map_inj R (A ⊗[R] B) C _ _ _ _ _ _ _ _,
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
--   ((tensor_product.assoc R A B C) : (A ⊗[R] B) ⊗[R] C → A ⊗[R] (B ⊗[R] C)) ((a ⊗ₜ b) ⊗ₜ c) = a ⊗ₜ (b ⊗ₜ c) :=
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
