/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import linear_algebra.multilinear

/-!
# Tensor product of an indexed family of semimodules over commutative semirings

We define the tensor product of an indexed family `s : ι → Type*` of semimodules over commutative
semirings. We denote this space by `⨂[R] i, s i` and define it as `free_add_monoid (R × Π i, s i)`
quotiented by the appropriate equivalence relation. The treatment follows very closely that of the
binary tensor product in `linear_algebra/tensor_product.lean`.

## Main definitions

* `pi_tensor_product R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor product
  of all the `s i`'s. This is denoted by `⨂[R] i, s i`.
* `tprod R f` with `f : Π i, s i` is the tensor product of the vectors `f i` over all `i : ι`.
  This is bundled as a multilinear map from `Π i, s i` to `⨂[R] i, s i`.
* `lift_add_hom` constructs an `add_monoid_hom` from `(⨂[R] i, s i)` to some space `F` from a
  function `φ : (R × Π i, s i) → F` with the appropriate properties.
* `lift φ` with `φ : multilinear_map R s E` is the corresponding linear map
  `(⨂[R] i, s i) →ₗ[R] E`. This is bundled as a linear equivalence.

## Notations

* `⨂[R] i, s i` is defined as localized notation in locale `tensor_product`
* `⨂ₜ[R] i, f i` with `f : Π i, f i` is defined globally as the tensor product of all the `f i`'s.

## Implementation notes

* We define it via `free_add_monoid (R × Π i, s i)` with the `R` representing a "hidden" tensor
  factor, rather than `free_add_monoid (Π i, s i)` to ensure that, if `ι` is an empty type,
  the space is isomorphic to the base ring `R`.
* We have not restricted the index type `ι` to be a `fintype`, as nothing we do here strictly
  requires it. However, problems may arise in the case where `ι` is infinite; use at your own
  caution.

## TODO

* Define tensor powers, symmetric subspace, etc.
* API for the various ways `ι` can be split into subsets; connect this with the binary
  tensor product.
* Include connection with holors.
* Port more of the API from the binary tensor product over to this case.

## Tags

multilinear, tensor, tensor product
-/

noncomputable theory
open_locale classical
open function

section semiring

variables {ι : Type*} {R : Type*} [comm_semiring R]
variables {R' : Type*} [comm_semiring R'] [algebra R' R]
variables {s : ι → Type*} [∀ i, add_comm_monoid (s i)] [∀ i, semimodule R (s i)]
variables {E : Type*} [add_comm_monoid E] [semimodule R E]
variables {F : Type*} [add_comm_monoid F]

namespace pi_tensor_product
include R
variables (R) (s)

/-- The relation on `free_add_monoid (R × Π i, s i)` that generates a congruence whose quotient is
the tensor product. -/
inductive eqv : free_add_monoid (R × Π i, s i) → free_add_monoid (R × Π i, s i) → Prop
| of_zero : ∀ (r : R) (f : Π i, s i) (i : ι) (hf : f i = 0), eqv (free_add_monoid.of (r, f)) 0
| of_zero_scalar : ∀ (f : Π i, s i), eqv (free_add_monoid.of (0, f)) 0
| of_add : ∀ (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i), eqv
    (free_add_monoid.of (r, update f i m₁) + free_add_monoid.of (r, update f i m₂))
    (free_add_monoid.of (r, update f i (m₁ + m₂)))
| of_add_scalar : ∀ (r r' : R) (f : Π i, s i), eqv
    (free_add_monoid.of (r, f) + free_add_monoid.of (r', f))
    (free_add_monoid.of (r + r', f))
| of_smul : ∀ (r : R) (f : Π i, s i) (i : ι) (r' : R), eqv
    (free_add_monoid.of (r, update f i (r' • (f i))))
    (free_add_monoid.of (r' * r, f))
| add_comm : ∀ x y, eqv (x + y) (y + x)

end pi_tensor_product

variables (R) (s)

/-- `pi_tensor_product R s` with `R` a commutative semiring and `s : ι → Type*` is the tensor
  product of all the `s i`'s. This is denoted by `⨂[R] i, s i`. -/
def pi_tensor_product : Type* :=
(add_con_gen (pi_tensor_product.eqv R s)).quotient

variables {R}

/- This enables the notation `⨂[R] i : ι, s i` for the pi tensor product, given `s : ι → Type*`. -/
localized "notation `⨂[`:100 R `] ` binders `, ` r:(scoped:67 f, pi_tensor_product R f) := r"
  in tensor_product

open_locale tensor_product

namespace pi_tensor_product

section module

instance : add_comm_monoid (⨂[R] i, s i) :=
{ add_comm := λ x y, add_con.induction_on₂ x y $ λ x y, quotient.sound' $
    add_con_gen.rel.of _ _ $ eqv.add_comm _ _,
  .. (add_con_gen (pi_tensor_product.eqv R s)).add_monoid }

instance : inhabited (⨂[R] i, s i) := ⟨0⟩

variables (R) {s}

/-- `tprod_coeff R r f` with `r : R` and `f : Π i, s i` is the tensor product of the vectors `f i`
over all `i : ι`, multiplied by the coefficient `r`. Note that this is meant as an auxiliary
definition for this file alone, and that one should use `tprod` defined below for most purposes. -/
def tprod_coeff (r : R) (f : Π i, s i) : ⨂[R] i, s i := add_con.mk' _ $ free_add_monoid.of (r, f)

variables {R}

lemma zero_tprod_coeff (f : Π i, s i) : tprod_coeff R 0 f = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero_scalar _

lemma zero_tprod_coeff' (z : R) (f : Π i, s i) (i : ι) (hf: f i = 0) : tprod_coeff R z f = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero _ _ i hf

lemma add_tprod_coeff (z : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i) :
  tprod_coeff R z (update f i m₁) + tprod_coeff R z (update f i m₂) =
    tprod_coeff R z (update f i (m₁ + m₂)) :=
quotient.sound' $ add_con_gen.rel.of _ _ (eqv.of_add z f i m₁ m₂)

lemma add_tprod_coeff' (z₁ z₂ : R) (f : Π i, s i) :
  tprod_coeff R z₁ f + tprod_coeff R z₂ f = tprod_coeff R (z₁ + z₂) f :=
quotient.sound' $ add_con_gen.rel.of _ _ (eqv.of_add_scalar z₁ z₂ f)

lemma smul_tprod_coeff_aux (z : R) (f : Π i, s i) (i : ι) (r : R) :
  tprod_coeff R z (update f i (r • f i)) = tprod_coeff R (r * z) f :=
 quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_smul _ _ _ _

lemma smul_tprod_coeff (z : R) (f : Π i, s i) (i : ι) (r : R')
  [semimodule R' (s i)] [is_scalar_tower R' R (s i)] :
  tprod_coeff R z (update f i (r • f i)) = tprod_coeff R (r • z) f :=
begin
  have h₁ : r • z = (r • (1 : R)) * z := by simp,
  have h₂ : r • (f i) = (r • (1 : R)) • f i := by simp,
  rw [h₁, h₂],
  exact smul_tprod_coeff_aux z f i _,
end

/-- Construct an `add_monoid_hom` from `(⨂[R] i, s i)` to some space `F` from a function
`φ : (R × Π i, s i) → F` with the appropriate properties. -/
def lift_add_hom (φ : (R × Π i, s i) → F)
  (C0 : ∀ (r : R) (f : Π i, s i) (i : ι) (hf : f i = 0), φ (r, f) = 0)
  (C0' : ∀ (f : Π i, s i), φ (0, f) = 0)
  (C_add : ∀ (r : R) (f : Π i, s i) (i : ι) (m₁ m₂ : s i),
    φ (r, update f i m₁) + φ (r, update f i m₂) = φ (r, update f i (m₁ + m₂)))
  (C_add_scalar : ∀ (r r' : R) (f : Π i, s i),
    φ (r , f) + φ (r', f) = φ (r + r', f))
  (C_smul : ∀ (r : R) (f : Π i, s i) (i : ι) (r' : R),
    φ (r, update f i (r' • (f i))) = φ (r' * r, f))
: (⨂[R] i, s i) →+ F :=
(add_con_gen (pi_tensor_product.eqv R s)).lift (free_add_monoid.lift φ) $ add_con.add_con_gen_le $
λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero r' f i hf)        := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C0 r' f i hf]
| _, _, (eqv.of_zero_scalar f)        := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C0']
| _, _, (eqv.of_add z f i m₁ m₂)      := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C_add]
| _, _, (eqv.of_add_scalar z₁ z₂ f)      := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C_add_scalar]
| _, _, (eqv.of_smul z f i r')     := (add_con.ker_rel _).2 $
    by simp [free_add_monoid.lift_eval_of, C_smul]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
instance has_scalar' : has_scalar R' (⨂[R] i, s i) :=
⟨λ r, lift_add_hom (λ f : R × Π i, s i, tprod_coeff R (r • f.1) f.2)
  (λ r' f i hf, by simp_rw [zero_tprod_coeff' _ f i hf])
  (λ f, by simp [zero_tprod_coeff])
  (λ r' f i m₁ m₂, by simp [add_tprod_coeff])
  (λ r' r'' f, by simp [add_tprod_coeff', mul_add])
  (λ z f i r', by simp [smul_tprod_coeff])⟩

instance : has_scalar R (⨂[R] i, s i) := pi_tensor_product.has_scalar'

lemma smul_tprod_coeff' (r : R') (z : R) (f : Π i, s i) :
  r • (tprod_coeff R z f) = tprod_coeff R (r • z) f := rfl

protected theorem smul_add (r : R') (x y : ⨂[R] i, s i) :
  r • (x + y) = r • x + r • y :=
add_monoid_hom.map_add _ _ _

@[elab_as_eliminator]
protected theorem induction_on'
  {C : (⨂[R] i, s i) → Prop}
  (z : ⨂[R] i, s i)
  (C1 : ∀ {r : R} {f : Π i, s i}, C (tprod_coeff R r f))
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
begin
  have C0 : C 0,
  { have h₁ := @C1 0 0,
    rwa [zero_tprod_coeff] at h₁ },
  refine add_con.induction_on z (λ x, free_add_monoid.rec_on x C0 _),
  simp_rw add_con.coe_add,
  refine λ f y ih, Cp _ ih,
  convert @C1 f.1 f.2,
  simp only [prod.mk.eta],
end

-- Most of the time we want the instance below this one, which is easier for typeclass resolution
-- to find.
instance semimodule' : semimodule R' (⨂[R] i, s i) :=
{ smul := (•),
  smul_add := λ r x y, pi_tensor_product.smul_add r x y,
  mul_smul := λ r r' x,
    begin
      refine pi_tensor_product.induction_on' x _ _,
      { intros r'' f,
        simp [smul_tprod_coeff', smul_smul] },
      { intros x y ihx ihy,
        simp [pi_tensor_product.smul_add, ihx, ihy] }
    end,
  one_smul := λ x, pi_tensor_product.induction_on' x
    (λ f, by simp [smul_tprod_coeff' _ _])
    (λ z y ihz ihy, by simp_rw [pi_tensor_product.smul_add, ihz, ihy]),
  add_smul := λ r r' x,
    begin
      refine pi_tensor_product.induction_on' x _ _,
      { intros r f,
        simp [smul_tprod_coeff' _ _, add_smul, add_tprod_coeff'] },
      { intros x y ihx ihy,
        simp [pi_tensor_product.smul_add, ihx, ihy, add_add_add_comm] }
    end,
  smul_zero := λ r, add_monoid_hom.map_zero _,
  zero_smul := λ x,
    begin
      refine pi_tensor_product.induction_on' x _ _,
      { intros r f,
        simp_rw [smul_tprod_coeff' _ _, zero_smul],
        exact zero_tprod_coeff _ },
      { intros x y ihx ihy,
        rw [pi_tensor_product.smul_add, ihx, ihy, add_zero] },
    end }

instance : semimodule R' (⨂[R] i, s i) := pi_tensor_product.semimodule'

variables {R}

variables (R)
/-- The canonical `multilinear_map R s (⨂[R] i, s i)`. -/
def tprod : multilinear_map R s (⨂[R] i, s i) :=
{ to_fun := tprod_coeff R 1,
  map_add' := λ f i x y, (add_tprod_coeff (1 : R) f i x y).symm,
  map_smul' := λ f i r x,
    by simp_rw [smul_tprod_coeff', ←smul_tprod_coeff (1 : R) _ i, update_idem, update_same] }

variables {R}

notation `⨂ₜ[`:100 R`] ` binders `, ` r:(scoped:67 f, tprod R f) := r

@[simp]
lemma tprod_coeff_eq_smul_tprod (z : R) (f : Π i, s i) : tprod_coeff R z f = z • tprod R f :=
begin
  have : z = z • (1 : R) := by simp only [mul_one, algebra.id.smul_eq_mul],
  conv_lhs { rw this },
  rw ←smul_tprod_coeff',
  refl,
end

@[elab_as_eliminator]
protected theorem induction_on
  {C : (⨂[R] i, s i) → Prop}
  (z : ⨂[R] i, s i)
  (C1 : ∀ {r : R} {f : Π i, s i}, C (r • (tprod R f)))
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
begin
  simp_rw ←tprod_coeff_eq_smul_tprod at C1,
  exact pi_tensor_product.induction_on' z @C1 @Cp,
end

@[ext]
theorem ext {φ₁ φ₂ : (⨂[R] i, s i) →ₗ[R] E}
  (H : φ₁.comp_multilinear_map (tprod R) = φ₂.comp_multilinear_map (tprod R)) : φ₁ = φ₂ :=
begin
  refine linear_map.ext _,
  refine λ z,
    (pi_tensor_product.induction_on' z _ (λ x y hx hy, by rw [φ₁.map_add, φ₂.map_add, hx, hy])),
  { intros r f,
    rw [tprod_coeff_eq_smul_tprod, φ₁.map_smul, φ₂.map_smul],
    apply _root_.congr_arg,
    exact multilinear_map.congr_fun H f }
end

end module

section multilinear
open multilinear_map
variables {s}

/-- Auxiliary function to constructing a linear map `(⨂[R] i, s i) → E` given a
`multilinear map R s E` with the property that its composition with the canonical
`multilinear_map R s (⨂[R] i, s i)` is the given multilinear map. -/
def lift_aux (φ : multilinear_map R s E) : (⨂[R] i, s i) →+ E :=
  lift_add_hom (λ (p : R × Π i, s i), p.1 • (φ p.2))
    (λ z f i hf, by rw [map_coord_zero φ i hf, smul_zero])
    (λ f, by rw [zero_smul])
    (λ z f i m₁ m₂, by rw [←smul_add, φ.map_add])
    (λ z₁ z₂ f, by rw [←add_smul])
    (λ z f i r, by simp [φ.map_smul, smul_smul, mul_comm])

lemma lift_aux_tprod (φ : multilinear_map R s E) (f : Π i, s i) : lift_aux φ (tprod R f) = φ f :=
by simp only [lift_aux, lift_add_hom, tprod, multilinear_map.coe_mk, tprod_coeff,
              free_add_monoid.lift_eval_of, one_smul, add_con.lift_mk']

lemma lift_aux_tprod_coeff (φ : multilinear_map R s E) (z : R) (f : Π i, s i) :
  lift_aux φ (tprod_coeff R z f) = z • φ f :=
by simp [lift_aux, lift_add_hom, tprod_coeff, free_add_monoid.lift_eval_of]

lemma lift_aux.smul {φ : multilinear_map R s E} (r : R) (x : ⨂[R] i, s i) :
  lift_aux φ (r • x) = r • lift_aux φ x :=
begin
  refine pi_tensor_product.induction_on' x _ _,
  { intros z f,
    rw [smul_tprod_coeff' r z f, lift_aux_tprod_coeff, lift_aux_tprod_coeff, smul_assoc] },
  { intros z y ihz ihy,
    rw [smul_add, (lift_aux φ).map_add, ihz, ihy, (lift_aux φ).map_add, smul_add] }
end

/-- Constructing a linear map `(⨂[R] i, s i) → E` given a `multilinear_map R s E` with the
property that its composition with the canonical `multilinear_map R s E` is
the given multilinear map `φ`. -/
def lift : (multilinear_map R s E) ≃ₗ[R] ((⨂[R] i, s i) →ₗ[R] E) :=
{ to_fun := λ φ, { map_smul' := lift_aux.smul, .. lift_aux φ },
  inv_fun := λ φ', φ'.comp_multilinear_map (tprod R),
  left_inv := λ φ, by { ext, simp [lift_aux_tprod, linear_map.comp_multilinear_map] },
  right_inv := λ φ, by { ext, simp [lift_aux_tprod] },
  map_add' := λ φ₁ φ₂, by { ext, simp [lift_aux_tprod] },
  map_smul' := λ r φ₂, by { ext, simp [lift_aux_tprod] } }

variables {φ : multilinear_map R s E}

@[simp] lemma lift.tprod (f : Π i, s i) : lift φ (tprod R f) = φ f := lift_aux_tprod φ f
theorem lift.unique' {φ' : (⨂[R] i, s i) →ₗ[R] E} (H : φ'.comp_multilinear_map (tprod R) = φ) :
  φ' = lift φ :=
ext $ H.symm ▸ (lift.symm_apply_apply φ).symm

theorem lift.unique {φ' : (⨂[R] i, s i) →ₗ[R] E} (H : ∀ f, φ' (tprod R f) = φ f) :
  φ' = lift φ :=
lift.unique' (multilinear_map.ext H)

theorem lift_tprod : lift (tprod R : multilinear_map R s _) = linear_map.id :=
eq.symm $ lift.unique' rfl

end multilinear

end pi_tensor_product

end semiring

section ring
namespace pi_tensor_product

open pi_tensor_product
open_locale tensor_product

variables {ι : Type*} {R : Type*} [comm_ring R]
variables {s : ι → Type*} [∀ i, add_comm_group (s i)] [∀ i, module R (s i)]

/- Unlike for the binary tensor product, we require `R` to be a `comm_ring` here, otherwise
this is false in the case where `ι` is empty. -/
instance : add_comm_group (⨂[R] i, s i) := semimodule.add_comm_monoid_to_add_comm_group R

end pi_tensor_product
end ring
