/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser.
-/

import linear_algebra.tensor_algebra
import linear_algebra.alternating

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

## Definitions

* `ι_multi` is the `alternating_map` corresponding to the wedge product of `ι R m` terms.

## Implementation details

The exterior algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `exterior_algebra.rel R M` on `tensor_algebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `0`.
2. The exterior algebra is the quotient of the tensor algebra by this relation.

-/

variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_monoid M] [semimodule R M]

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

variables {M}

-- typeclass resolution times out here, so we give it a hand
instance {S : Type*} [comm_ring S] [semimodule S M] : ring (exterior_algebra S M) :=
let i : ring (tensor_algebra S M) := infer_instance in
@ring_quot.ring (tensor_algebra S M) i (exterior_algebra.rel S M)

/--
The canonical linear map `M →ₗ[R] exterior_algebra R M`.
-/
def ι : M →ₗ[R] exterior_algebra R M :=
(ring_quot.mk_alg_hom R _).to_linear_map.comp (tensor_algebra.ι R)


variables {R}

/-- As well as being linear, `ι m` squares to zero -/
@[simp]
theorem ι_square_zero (m : M) : (ι R m) * (ι R m) = 0 :=
begin
  erw [←alg_hom.map_mul, ring_quot.mk_alg_hom_rel R (rel.of m), alg_hom.map_zero _],
end

variables {A : Type*} [semiring A] [algebra R A]

@[simp]
theorem comp_ι_square_zero (g : exterior_algebra R M →ₐ[R] A)
  (m : M) : g (ι R m) * g (ι R m) = 0 :=
by rw [←alg_hom.map_mul, ι_square_zero, alg_hom.map_zero]

variables (R)

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `exterior_algebra R M` to `A`.
-/
@[simps symm_apply]
def lift : {f : M →ₗ[R] A // ∀ m, f m * f m = 0} ≃ (exterior_algebra R M →ₐ[R] A) :=
{ to_fun := λ f,
  ring_quot.lift_alg_hom R ⟨tensor_algebra.lift R (f : M →ₗ[R] A),
    λ x y (h : rel R M x y), by {
      induction h,
      rw [alg_hom.map_zero, alg_hom.map_mul, tensor_algebra.lift_ι_apply, f.prop] }⟩,
  inv_fun := λ F, ⟨F.to_linear_map.comp (ι R), λ m, by rw [
    linear_map.comp_apply, alg_hom.to_linear_map_apply, comp_ι_square_zero]⟩,
  left_inv := λ f, by { ext, simp [ι] },
  right_inv := λ F, by { ext, simp [ι] } }

@[simp]
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) :
  (lift R ⟨f, cond⟩).to_linear_map.comp (ι R) = f :=
(subtype.mk_eq_mk.mp $ (lift R).symm_apply_apply ⟨f, cond⟩)

@[simp]
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (x) :
  lift R ⟨f, cond⟩ (ι R x) = f x :=
(linear_map.ext_iff.mp $ ι_comp_lift R f cond) x

@[simp]
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0)
  (g : exterior_algebra R M →ₐ[R] A) : g.to_linear_map.comp (ι R) = f ↔ g = lift R ⟨f, cond⟩ :=
begin
  convert (lift R).symm_apply_eq,
  rw lift_symm_apply,
  simp only,
end

attribute [irreducible] ι lift
-- Marking `exterior_algebra` irreducible makes our `ring` instances inaccessible.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.

variables {R M}

@[simp]
theorem lift_comp_ι (g : exterior_algebra R M →ₐ[R] A) :
  lift R ⟨g.to_linear_map.comp (ι R), comp_ι_square_zero _⟩ = g :=
begin
  convert (lift R).apply_symm_apply g,
  rw lift_symm_apply,
  refl,
end

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {f g : exterior_algebra R M →ₐ[R] A}
  (h : f.to_linear_map.comp (ι R) = g.to_linear_map.comp (ι R)) : f = g :=
begin
  apply (lift R).symm.injective,
  rw [lift_symm_apply, lift_symm_apply],
  simp only [h],
end

/-- The left-inverse of `algebra_map`. -/
def algebra_map_inv : exterior_algebra R M →ₐ[R] R :=
exterior_algebra.lift R ⟨(0 : M →ₗ[R] R), λ m, by simp⟩

lemma algebra_map_left_inverse :
  function.left_inverse algebra_map_inv (algebra_map R $ exterior_algebra R M) :=
λ x, by simp [algebra_map_inv]

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `triv_sq_zero_ext` which has a suitable
algebra structure. -/
def ι_inv : exterior_algebra R M →ₗ[R] M :=
(triv_sq_zero_ext.snd_hom R M).comp
  (lift R ⟨triv_sq_zero_ext.inr_hom R M, λ m, triv_sq_zero_ext.inr_mul_inr R _ m m⟩).to_linear_map

lemma ι_left_inverse : function.left_inverse ι_inv (ι R : M → exterior_algebra R M) :=
λ x, by simp [ι_inv]

@[simp]
lemma ι_add_mul_swap (x y : M) : ι R x * ι R y + ι R y * ι R x = 0 :=
calc _ = ι R (x + y) * ι R (x + y) : by simp [mul_add, add_mul]
   ... = _ : ι_square_zero _

lemma ι_mul_prod_list {n : ℕ} (f : fin n → M) (i : fin n) :
  (ι R $ f i) * (list.of_fn $ λ i, ι R $ f i).prod = 0 :=
begin
  induction n with n hn,
  { exact i.elim0, },
  { rw [list.of_fn_succ, list.prod_cons, ←mul_assoc],
    by_cases h : i = 0,
    { rw [h, ι_square_zero, zero_mul], },
    { replace hn := congr_arg ((*) $ ι R $ f 0) (hn (λ i, f $ fin.succ i) (i.pred h)),
      simp only at hn,
      rw [fin.succ_pred, ←mul_assoc, mul_zero] at hn,
      refine (eq_zero_iff_eq_zero_of_add_eq_zero _).mp hn,
      rw [← add_mul, ι_add_mul_swap, zero_mul], } }
end

variables (R)
/-- The product of `n` terms of the form `ι R m` is an alternating map.

This is a special case of `multilinear_map.mk_pi_algebra_fin` -/
def ι_multi (n : ℕ) :
  alternating_map R M (exterior_algebra R M) (fin n) :=
let F := (multilinear_map.mk_pi_algebra_fin R n (exterior_algebra R M)).comp_linear_map (λ i, ι R)
in
{ map_eq_zero_of_eq' := λ f x y hfxy hxy, begin
    rw [multilinear_map.comp_linear_map_apply, multilinear_map.mk_pi_algebra_fin_apply],
    wlog h : x < y := lt_or_gt_of_ne hxy using x y,
    clear hxy,
    induction n with n hn generalizing x y,
    { exact x.elim0, },
    { rw [list.of_fn_succ, list.prod_cons],
      by_cases hx : x = 0,
      -- one of the repeated terms is on the left
      { rw hx at hfxy h,
        rw [hfxy, ←fin.succ_pred y (ne_of_lt h).symm],
        exact ι_mul_prod_list (f ∘ fin.succ) _, },
      -- ignore the left-most term and induct on the remaining ones, decrementing indices
      { convert mul_zero _,
        refine hn (λ i, f $ fin.succ i)
          (x.pred hx) (y.pred (ne_of_lt $ lt_of_le_of_lt x.zero_le h).symm)
          (fin.pred_lt_pred_iff.mpr h) _,
        simp only [fin.succ_pred],
        exact hfxy, } }
  end,
  to_fun := F, ..F}
variables {R}

lemma ι_multi_apply {n : ℕ} (v : fin n → M) :
  ι_multi R n v = (list.of_fn $ λ i, ι R (v i)).prod := rfl

end exterior_algebra

namespace tensor_algebra

variables {R M}

/-- The canonical image of the `tensor_algebra` in the `exterior_algebra`, which maps
`tensor_algebra.ι R x` to `exterior_algebra.ι R x`. -/
def to_exterior : tensor_algebra R M →ₐ[R] exterior_algebra R M :=
tensor_algebra.lift R (exterior_algebra.ι R)

@[simp] lemma to_exterior_ι (m : M) : (tensor_algebra.ι R m).to_exterior = exterior_algebra.ι R m :=
by simp [to_exterior]

end tensor_algebra
