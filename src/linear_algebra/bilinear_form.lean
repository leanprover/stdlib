/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/

import linear_algebra.matrix
import linear_algebra.tensor_product
import linear_algebra.nonsingular_inverse

/-!
# Bilinear form

This file defines a bilinear form over a module. Basic ideas
such as orthogonality are also introduced, as well as reflexivive,
symmetric, non-degenerate and alternating bilinear forms. Adjoints of
linear maps with respect to a bilinear form are also introduced.

A bilinear form on an R-(semi)module M, is a function from M x M to R,
that is linear in both arguments. Comments will typically abbreviate
"(semi)module" as just "module", but the definitions should be as general as
possible.

The result that there exists an orthogonal basis with respect to a symmetric,
nondegenerate bilinear form can be found in `quadratic_form.lean` with
`exists_orthogonal_basis`.

## Notations

Given any term B of type bilin_form, due to a coercion, can use
the notation B x y to refer to the function field, ie. B x y = B.bilin x y.

In this file we use the following type variables:
 - `M`, `M'`, ... are semimodules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are semimodules over the commutative semiring `R₂`,
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`,
 - `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

open_locale big_operators

universes u v w

/-- `bilin_form R M` is the type of `R`-bilinear functions `M → M → R`. -/
structure bilin_form (R : Type*) (M : Type*) [semiring R] [add_comm_monoid M] [semimodule R M] :=
(bilin : M → M → R)
(bilin_add_left : ∀ (x y z : M), bilin (x + y) z = bilin x z + bilin y z)
(bilin_smul_left : ∀ (a : R) (x y : M), bilin (a • x) y = a * (bilin x y))
(bilin_add_right : ∀ (x y z : M), bilin x (y + z) = bilin x y + bilin x z)
(bilin_smul_right : ∀ (a : R) (x y : M), bilin x (a • y) = a * (bilin x y))

variables {R : Type*} {M : Type*} [semiring R] [add_comm_monoid M] [semimodule R M]
variables {R₁ : Type*} {M₁ : Type*} [ring R₁] [add_comm_group M₁] [module R₁ M₁]
variables {R₂ : Type*} {M₂ : Type*} [comm_semiring R₂] [add_comm_monoid M₂] [semimodule R₂ M₂]
variables {R₃ : Type*} {M₃ : Type*} [comm_ring R₃] [add_comm_group M₃] [module R₃ M₃]
variables {V : Type*} {K : Type*} [field K] [add_comm_group V] [vector_space K V]
variables {B : bilin_form R M} {B₁ : bilin_form R₁ M₁} {B₂ : bilin_form R₂ M₂}

namespace bilin_form

instance : has_coe_to_fun (bilin_form R M) :=
⟨_, λ B, B.bilin⟩

initialize_simps_projections bilin_form (bilin -> apply)

@[simp] lemma coe_fn_mk (f : M → M → R) (h₁ h₂ h₃ h₄) :
  (bilin_form.mk f h₁ h₂ h₃ h₄ : M → M → R) = f :=
rfl

lemma coe_fn_congr : Π {x x' y y' : M}, x = x' → y = y' → B x y = B x' y'
| _ _ _ _ rfl rfl := rfl

@[simp]
lemma add_left (x y z : M) : B (x + y) z = B x z + B y z := bilin_add_left B x y z

@[simp]
lemma smul_left (a : R) (x y : M) : B (a • x) y = a * (B x y) := bilin_smul_left B a x y

@[simp]
lemma add_right (x y z : M) : B x (y + z) = B x y + B x z := bilin_add_right B x y z

@[simp]
lemma smul_right (a : R) (x y : M) : B x (a • y) = a * (B x y) := bilin_smul_right B a x y

@[simp]
lemma zero_left (x : M) : B 0 x = 0 :=
by { rw [←@zero_smul R _ _ _ _ (0 : M), smul_left, zero_mul] }

@[simp]
lemma zero_right (x : M) : B x 0 = 0 :=
by rw [←@zero_smul _ _ _ _ _ (0 : M), smul_right, zero_mul]

@[simp]
lemma neg_left (x y : M₁) : B₁ (-x) y = -(B₁ x y) :=
by rw [←@neg_one_smul R₁ _ _, smul_left, neg_one_mul]

@[simp]
lemma neg_right (x y : M₁) : B₁ x (-y) = -(B₁ x y) :=
by rw [←@neg_one_smul R₁ _ _, smul_right, neg_one_mul]

@[simp]
lemma sub_left (x y z : M₁) : B₁ (x - y) z = B₁ x z - B₁ y z :=
by rw [sub_eq_add_neg, sub_eq_add_neg, add_left, neg_left]

@[simp]
lemma sub_right (x y z : M₁) : B₁ x (y - z) = B₁ x y - B₁ x z :=
by rw [sub_eq_add_neg, sub_eq_add_neg, add_right, neg_right]

variable {D : bilin_form R M}
@[ext] lemma ext (H : ∀ (x y : M), B x y = D x y) : B = D :=
by { cases B, cases D, congr, funext, exact H _ _ }

instance : add_comm_monoid (bilin_form R M) :=
{ add := λ B D, { bilin := λ x y, B x y + D x y,
                  bilin_add_left := λ x y z, by { rw add_left, rw add_left, ac_refl },
                  bilin_smul_left := λ a x y, by { rw [smul_left, smul_left, mul_add] },
                  bilin_add_right := λ x y z, by { rw add_right, rw add_right, ac_refl },
                  bilin_smul_right := λ a x y, by { rw [smul_right, smul_right, mul_add] } },
  add_assoc := by { intros, ext, unfold bilin coe_fn has_coe_to_fun.coe bilin, rw add_assoc },
  zero := { bilin := λ x y, 0,
            bilin_add_left := λ x y z, (add_zero 0).symm,
            bilin_smul_left := λ a x y, (mul_zero a).symm,
            bilin_add_right := λ x y z, (zero_add 0).symm,
            bilin_smul_right := λ a x y, (mul_zero a).symm },
  zero_add := by { intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw zero_add },
  add_zero := by { intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw add_zero },
  add_comm := by { intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw add_comm } }

instance : add_comm_group (bilin_form R₁ M₁) :=
{ neg := λ B, { bilin := λ x y, - (B.1 x y),
                bilin_add_left := λ x y z, by rw [bilin_add_left, neg_add],
                bilin_smul_left := λ a x y, by rw [bilin_smul_left, mul_neg_eq_neg_mul_symm],
                bilin_add_right := λ x y z, by rw [bilin_add_right, neg_add],
                bilin_smul_right := λ a x y, by rw [bilin_smul_right, mul_neg_eq_neg_mul_symm] },
  add_left_neg := by { intros, ext, unfold coe_fn has_coe_to_fun.coe bilin, rw neg_add_self },
  .. bilin_form.add_comm_monoid }

@[simp]
lemma add_apply (x y : M) : (B + D) x y = B x y + D x y := rfl

@[simp]
lemma zero_apply (x y : M) : (0 : bilin_form R M) x y = 0 := rfl

@[simp]
lemma neg_apply (x y : M₁) : (-B₁) x y = -(B₁ x y) := rfl

instance : inhabited (bilin_form R M) := ⟨0⟩

section

/-- `bilin_form R M` inherits the scalar action from any commutative subalgebra `R₂` of `R`.

When `R` itself is commutative, this provides an `R`-action via `algebra.id`. -/
instance [algebra R₂ R] : semimodule R₂ (bilin_form R M) :=
{ smul := λ c B,
  { bilin := λ x y, c • B x y,
    bilin_add_left := λ x y z,
      by { unfold coe_fn has_coe_to_fun.coe bilin, rw [bilin_add_left, smul_add] },
    bilin_smul_left := λ a x y, by { unfold coe_fn has_coe_to_fun.coe bilin,
      rw [bilin_smul_left, ←algebra.mul_smul_comm] },
    bilin_add_right := λ x y z, by { unfold coe_fn has_coe_to_fun.coe bilin,
      rw [bilin_add_right, smul_add] },
    bilin_smul_right := λ a x y, by { unfold coe_fn has_coe_to_fun.coe bilin,
      rw [bilin_smul_right, ←algebra.mul_smul_comm] } },
  smul_add := λ c B D, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw smul_add },
  add_smul := λ c B D, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw add_smul },
  mul_smul := λ a c D, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw ←smul_assoc, refl },
  one_smul := λ B, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw one_smul },
  zero_smul := λ B, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw zero_smul },
  smul_zero := λ B, by { ext, unfold coe_fn has_coe_to_fun.coe bilin, rw smul_zero } }

@[simp] lemma smul_apply [algebra R₂ R] (B : bilin_form R M) (a : R₂) (x y : M) :
  (a • B) x y = a • (B x y) :=
rfl

end

section flip

variables (R₂)

/-- Auxiliary construction for the flip of a bilinear form, obtained by exchanging the left and
right arguments. This is a verison is an `add_monoid_hom`; it is later upgraded to an `add_equiv`
in `flip'`, and for a commutative ring to a `linear_equiv` in `flip`. -/
def flip_hom_aux [algebra R₂ R] : bilin_form R M →ₗ[R₂] bilin_form R M :=
{ to_fun := λ A,
  { bilin := λ i j, A j i,
    bilin_add_left := λ x y z, A.bilin_add_right z x y,
    bilin_smul_left := λ a x y, A.bilin_smul_right a y x,
    bilin_add_right := λ x y z, A.bilin_add_left y z x,
    bilin_smul_right := λ a x y, A.bilin_smul_left a y x },
  map_add' := λ A₁ A₂, by { ext, simp } ,
  map_smul' := λ c A, by { ext, simp } }

variables {R₂}

lemma flip_flip_aux [algebra R₂ R] (A : bilin_form R M) :
  (flip_hom_aux R₂) (flip_hom_aux R₂ A) = A :=
by { ext A x y, simp [flip_hom_aux] }

variables (R₂)

/-- The flip of a bilinear form, obtained by exchanging the left and right arguments. This is a
less structured version of the equiv which applies to general (noncommutative) rings `R` with a
distinguished commutative subring `R₂`; over a commutative ring use `flip`. -/
def flip_hom [algebra R₂ R] : bilin_form R M ≃ₗ[R₂] bilin_form R M :=
{ inv_fun := flip_hom_aux R₂,
  left_inv := flip_flip_aux,
  right_inv := flip_flip_aux,
  .. flip_hom_aux R₂ }

variables {R₂}

@[simp] lemma flip_apply [algebra R₂ R] (A : bilin_form R M) (x y : M) :
  flip_hom R₂ A x y = A y x :=
rfl

lemma flip_flip [algebra R₂ R] :
  (flip_hom R₂).trans (flip_hom R₂) = linear_equiv.refl R₂ (bilin_form R M) :=
by { ext A x y, simp }

/-- The flip of a bilinear form over a ring, obtained by exchanging the left and right arguments,
here considered as an `ℕ`-linear map, i.e. an additive homomorphism. -/
abbreviation flip' : bilin_form R M ≃ₗ[ℕ] bilin_form R M := flip_hom ℕ

/-- The `flip` of a bilinear form over a commutative ring, obtained by exchanging the left and
right arguments. -/
abbreviation flip : bilin_form R₂ M₂ ≃ₗ[R₂] bilin_form R₂ M₂ := flip_hom R₂

end flip

section to_lin'

variables (R₂) [algebra R₂ R] [semimodule R₂ M] [is_scalar_tower R₂ R M]

/-- The linear map obtained from a `bilin_form` by fixing the left co-ordinate and evaluating in
the right.
This is the most general version of the construction; it is `R₂`-linear for some distinguished
commutative subsemiring `R₂` of the scalar ring.  Over semiring with no particular distinguished
such subsemiring, use `to_lin'`, which is `ℕ`-linear.  Over a commutative semiring, use `to_lin`,
which is linear. -/
def to_lin_hom : bilin_form R M →ₗ[R₂] M →ₗ[R₂] M →ₗ[R] R :=
{ to_fun := λ A,
  { to_fun := λ x,
    { to_fun := λ y, A x y,
      map_add' := A.bilin_add_right x,
      map_smul' := λ c, A.bilin_smul_right c x },
    map_add' := λ x₁ x₂, by { ext, simp },
    map_smul' := λ c x, by { ext y, simpa using smul_left (c • (1 : R)) x y } },
  map_add' := λ A₁ A₂, by { ext, simp },
  map_smul' := λ c A, by { ext, simp } }

variables {R₂}

@[simp] lemma to_lin'_apply (A : bilin_form R M) (x : M) :
  ⇑(to_lin_hom R₂ A x) = A x :=
rfl

/-- The linear map obtained from a `bilin_form` by fixing the left co-ordinate and evaluating in
the right.
Over a commutative semiring, use `to_lin`, which is linear rather than `ℕ`-linear. -/
abbreviation to_lin' : bilin_form R M →ₗ[ℕ] M →ₗ[ℕ] M →ₗ[R] R := to_lin_hom ℕ

variables (R₂)

/-- The linear map obtained from a `bilin_form` by fixing the right co-ordinate and evaluating in
the left.
This is the most general version of the construction; it is `R₂`-linear for some distinguished
commutative subsemiring `R₂` of the scalar ring.  Over semiring with no particular distinguished
such subsemiring, use `to_lin'_flip`, which is `ℕ`-linear.  Over a commutative semiring, use
`to_lin_flip`, which is linear. -/
def to_lin_hom_flip : bilin_form R M →ₗ[R₂] M →ₗ[R₂] M →ₗ[R] R :=
(to_lin_hom R₂).comp (flip_hom R₂).to_linear_map

variables {R₂}

@[simp] lemma to_lin'_flip_apply (A : bilin_form R M) (x : M) :
  ⇑(to_lin_hom_flip R₂ A x) = λ y, A y x :=
rfl

/-- The linear map obtained from a `bilin_form` by fixing the right co-ordinate and evaluating in
the left.
Over a commutative semiring, use `to_lin_flip`, which is linear rather than `ℕ`-linear. -/
abbreviation to_lin'_flip : bilin_form R M →ₗ[ℕ] M →ₗ[ℕ] M →ₗ[R] R := to_lin_hom_flip ℕ

end to_lin'

end bilin_form

section equiv_lin

/-- A map with two arguments that is linear in both is a bilinear form.

This is an auxiliary definition for the full linear equivalence `linear_map.to_bilin`.
-/
def linear_map.to_bilin_aux (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) : bilin_form R₂ M₂ :=
{ bilin := λ x y, f x y,
  bilin_add_left := λ x y z, (linear_map.map_add f x y).symm ▸ linear_map.add_apply (f x) (f y) z,
  bilin_smul_left := λ a x y, by rw [linear_map.map_smul, linear_map.smul_apply, smul_eq_mul],
  bilin_add_right := λ x y z, linear_map.map_add (f x) y z,
  bilin_smul_right := λ a x y, linear_map.map_smul (f x) a y }

/-- Bilinear forms are linearly equivalent to maps with two arguments that are linear in both. -/
def bilin_form.to_lin : bilin_form R₂ M₂ ≃ₗ[R₂] (M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) :=
{ inv_fun := linear_map.to_bilin_aux,
  left_inv := λ B, by { ext, simp [linear_map.to_bilin_aux] },
  right_inv := λ B, by { ext, simp [linear_map.to_bilin_aux] },
  .. bilin_form.to_lin_hom R₂ }

/-- A map with two arguments that is linear in both is linearly equivalent to bilinear form. -/
def linear_map.to_bilin : (M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) ≃ₗ[R₂] bilin_form R₂ M₂ :=
bilin_form.to_lin.symm

@[simp] lemma linear_map.to_bilin_aux_eq (f : M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂) :
  linear_map.to_bilin_aux f = linear_map.to_bilin f :=
rfl

@[simp] lemma linear_map.to_bilin_symm :
  (linear_map.to_bilin.symm : bilin_form R₂ M₂ ≃ₗ _) = bilin_form.to_lin := rfl

@[simp] lemma bilin_form.to_lin_symm :
  (bilin_form.to_lin.symm : _ ≃ₗ bilin_form R₂ M₂) = linear_map.to_bilin :=
linear_map.to_bilin.symm_symm

@[simp, norm_cast]
lemma to_linear_map_apply (x : M₂) : ⇑(bilin_form.to_lin B₂ x) = B₂ x := rfl

@[simp]
lemma map_sum_left {α} (t : finset α) (g : α → M₂) (w : M₂) :
  B₂ (∑ i in t, g i) w = ∑ i in t, B₂ (g i) w :=
show bilin_form.to_lin B₂ (∑ i in t, g i) w = ∑ i in t, bilin_form.to_lin B₂ (g i) w,
by rw [linear_map.map_sum, linear_map.coe_fn_sum, finset.sum_apply]

@[simp]
lemma map_sum_right {α} (t : finset α) (w : M₂) (g : α → M₂) :
  B₂ w (∑ i in t, g i) = ∑ i in t, B₂ w (g i) :=
show bilin_form.to_lin B₂ w (∑ i in t, g i) = ∑ i in t, bilin_form.to_lin B₂ w (g i),
from linear_map.map_sum _

/-- Bilinear forms are linearly equivalent to maps with two arguments that are linear in both,
"arguments-reversed" version. -/
def bilin_form.to_lin_flip : bilin_form R₂ M₂ ≃ₗ[R₂] M₂ →ₗ[R₂] M₂ →ₗ[R₂] R₂ :=
bilin_form.flip.trans bilin_form.to_lin

@[simp] lemma bilin_form.to_lin_flip_eq_flip : B₂.to_lin_flip = B₂.to_lin.flip := rfl

end equiv_lin

namespace bilin_form

section comp

variables {M' : Type w} [add_comm_monoid M'] [semimodule R M']

/-- Apply a linear map on the left and right argument of a bilinear form. -/
def comp (B : bilin_form R M') (l r : M →ₗ[R] M') : bilin_form R M :=
{ bilin := λ x y, B (l x) (r y),
  bilin_add_left := λ x y z, by rw [linear_map.map_add, add_left],
  bilin_smul_left := λ x y z, by rw [linear_map.map_smul, smul_left],
  bilin_add_right := λ x y z, by rw [linear_map.map_add, add_right],
  bilin_smul_right := λ x y z, by rw [linear_map.map_smul, smul_right] }

/-- Apply a linear map to the left argument of a bilinear form. -/
def comp_left (B : bilin_form R M) (f : M →ₗ[R] M) : bilin_form R M :=
B.comp f linear_map.id

/-- Apply a linear map to the right argument of a bilinear form. -/
def comp_right (B : bilin_form R M) (f : M →ₗ[R] M) : bilin_form R M :=
B.comp linear_map.id f

lemma comp_comp {M'' : Type*} [add_comm_monoid M''] [semimodule R M'']
  (B : bilin_form R M'') (l r : M →ₗ[R] M') (l' r' : M' →ₗ[R] M'') :
  (B.comp l' r').comp l r = B.comp (l'.comp l) (r'.comp r) := rfl

@[simp] lemma comp_left_comp_right (B : bilin_form R M) (l r : M →ₗ[R] M) :
  (B.comp_left l).comp_right r = B.comp l r := rfl

@[simp] lemma comp_right_comp_left (B : bilin_form R M) (l r : M →ₗ[R] M) :
  (B.comp_right r).comp_left l = B.comp l r := rfl

@[simp] lemma comp_apply (B : bilin_form R M') (l r : M →ₗ[R] M') (v w) :
  B.comp l r v w = B (l v) (r w) := rfl

@[simp] lemma comp_left_apply (B : bilin_form R M) (f : M →ₗ[R] M) (v w) :
  B.comp_left f v w = B (f v) w := rfl

@[simp] lemma comp_right_apply (B : bilin_form R M) (f : M →ₗ[R] M) (v w) :
  B.comp_right f v w = B v (f w) := rfl

lemma comp_injective (B₁ B₂ : bilin_form R M') {l r : M →ₗ[R] M'}
  (hₗ : function.surjective l) (hᵣ : function.surjective r) :
  B₁.comp l r = B₂.comp l r ↔ B₁ = B₂ :=
begin
  split; intros h,
  { -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext,
    cases hₗ x with x' hx, subst hx,
    cases hᵣ y with y' hy, subst hy,
    rw [←comp_apply, ←comp_apply, h], },
  { -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    subst h, },
end

end comp

variables {M₂' : Type*} [add_comm_monoid M₂'] [semimodule R₂ M₂']

section congr

/-- Apply a linear equivalence on the arguments of a bilinear form. -/
def congr (e : M₂ ≃ₗ[R₂] M₂') : bilin_form R₂ M₂ ≃ₗ[R₂] bilin_form R₂ M₂' :=
{ to_fun := λ B, B.comp e.symm e.symm,
  inv_fun := λ B, B.comp e e,
  left_inv :=
    λ B, ext (λ x y, by simp only [comp_apply, linear_equiv.coe_coe, e.symm_apply_apply]),
  right_inv :=
    λ B, ext (λ x y, by simp only [comp_apply, linear_equiv.coe_coe, e.apply_symm_apply]),
  map_add' := λ B B', ext (λ x y, by simp only [comp_apply, add_apply]),
  map_smul' := λ B B', ext (λ x y, by simp only [comp_apply, smul_apply]) }

@[simp] lemma congr_apply (e : M₂ ≃ₗ[R₂] M₂') (B : bilin_form R₂ M₂) (x y : M₂') :
  congr e B x y = B (e.symm x) (e.symm y) := rfl

@[simp] lemma congr_symm (e : M₂ ≃ₗ[R₂] M₂') :
  (congr e).symm = congr e.symm :=
by { ext B x y, simp only [congr_apply, linear_equiv.symm_symm], refl }

lemma congr_comp {M₂'' : Type*} [add_comm_monoid M₂''] [semimodule R₂ M₂'']
  (e : M₂ ≃ₗ[R₂] M₂') (B : bilin_form R₂ M₂) (l r : M₂'' →ₗ[R₂] M₂') :
  (congr e B).comp l r = B.comp
    (linear_map.comp (e.symm : M₂' →ₗ[R₂] M₂) l)
    (linear_map.comp (e.symm : M₂' →ₗ[R₂] M₂) r) :=
rfl

lemma comp_congr {M₂'' : Type*} [add_comm_monoid M₂''] [semimodule R₂ M₂'']
  (e : M₂' ≃ₗ[R₂] M₂'') (B : bilin_form R₂ M₂) (l r : M₂' →ₗ[R₂] M₂) :
  congr e (B.comp l r) = B.comp
    (l.comp (e.symm : M₂'' →ₗ[R₂] M₂'))
    (r.comp (e.symm : M₂'' →ₗ[R₂] M₂')) :=
rfl

end congr

section lin_mul_lin

/-- `lin_mul_lin f g` is the bilinear form mapping `x` and `y` to `f x * g y` -/
def lin_mul_lin (f g : M₂ →ₗ[R₂] R₂) : bilin_form R₂ M₂ :=
{ bilin := λ x y, f x * g y,
  bilin_add_left := λ x y z, by rw [linear_map.map_add, add_mul],
  bilin_smul_left := λ x y z, by rw [linear_map.map_smul, smul_eq_mul, mul_assoc],
  bilin_add_right := λ x y z, by rw [linear_map.map_add, mul_add],
  bilin_smul_right := λ x y z, by rw [linear_map.map_smul, smul_eq_mul, mul_left_comm] }

variables {f g : M₂ →ₗ[R₂] R₂}

@[simp] lemma lin_mul_lin_apply (x y) : lin_mul_lin f g x y = f x * g y := rfl

@[simp] lemma lin_mul_lin_comp (l r : M₂' →ₗ[R₂] M₂) :
  (lin_mul_lin f g).comp l r = lin_mul_lin (f.comp l) (g.comp r) :=
rfl

@[simp] lemma lin_mul_lin_comp_left (l : M₂ →ₗ[R₂] M₂) :
  (lin_mul_lin f g).comp_left l = lin_mul_lin (f.comp l) g :=
rfl

@[simp] lemma lin_mul_lin_comp_right (r : M₂ →ₗ[R₂] M₂) :
  (lin_mul_lin f g).comp_right r = lin_mul_lin f (g.comp r) :=
rfl

end lin_mul_lin

/-- The proposition that two elements of a bilinear form space are orthogonal. For orthogonality
of an indexed set of elements, use `bilin_form.is_Ortho`. -/
def is_ortho (B : bilin_form R M) (x y : M) : Prop :=
B x y = 0

lemma is_ortho_def {B : bilin_form R M} {x y : M} :
  B.is_ortho x y ↔ B x y = 0 := iff.rfl

lemma is_ortho_zero_left (x : M) : is_ortho B (0 : M) x :=
zero_left x

lemma is_ortho_zero_right (x : M) : is_ortho B x (0 : M) :=
zero_right x

lemma ne_zero_of_not_is_ortho_self {B : bilin_form K V}
  (x : V) (hx₁ : ¬ B.is_ortho x x) : x ≠ 0 :=
λ hx₂, hx₁ (hx₂.symm ▸ is_ortho_zero_left _)

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. For orthogonality between two elements, use
`bilin_form.is_ortho` -/
def is_Ortho {n : Type w} (B : bilin_form R M) (v : n → M) : Prop :=
∀ i j : n, i ≠ j → B.is_ortho (v j) (v i)

lemma is_Ortho_def {n : Type w} {B : bilin_form R M} {v : n → M} :
  B.is_Ortho v ↔ ∀ i j : n, i ≠ j → B (v j) (v i) = 0 := iff.rfl

section

variables {R₄ M₄ : Type*} [domain R₄] [add_comm_group M₄] [module R₄ M₄] {G : bilin_form R₄ M₄}

@[simp]
theorem is_ortho_smul_left {x y : M₄} {a : R₄} (ha : a ≠ 0) :
  is_ortho G (a • x) y ↔ is_ortho G x y :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_left, mul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }},
  { rw [smul_left, H, mul_zero] },
end

@[simp]
theorem is_ortho_smul_right {x y : M₄} {a : R₄} (ha : a ≠ 0) :
  is_ortho G x (a • y) ↔ is_ortho G x y :=
begin
  dunfold is_ortho,
  split; intro H,
  { rw [smul_right, mul_eq_zero] at H,
    cases H,
    { trivial },
    { exact H }},
  { rw [smul_right, H, mul_zero] },
end

/-- A set of orthogonal vectors `v` with respect to some bilinear form `B` is linearly independent
  if for all `i`, `B (v i) (v i) ≠ 0`. -/
lemma linear_independent_of_is_Ortho
  {n : Type w} {B : bilin_form K V} {v : n → V}
  (hv₁ : B.is_Ortho v) (hv₂ : ∀ i, ¬ B.is_ortho (v i) (v i)) :
  linear_independent K v :=
begin
  classical,
  rw linear_independent_iff',
  intros s w hs i hi,
  have : B (s.sum $ λ (i : n), w i • v i) (v i) = 0,
  { rw [hs, zero_left] },
  have hsum : s.sum (λ (j : n), w j * B (v j) (v i)) =
    s.sum (λ (j : n), if i = j then w j * B (v j) (v i) else 0),
  { refine finset.sum_congr rfl (λ j hj, _),
    by_cases (i = j),
    { rw [if_pos h] },
    { rw [if_neg h, is_Ortho_def.1 hv₁ _ _ h, mul_zero] } },
  simp_rw [map_sum_left, smul_left, hsum, finset.sum_ite_eq] at this,
  rw [if_pos, mul_eq_zero] at this,
  cases this,
  { assumption },
  { exact false.elim (hv₂ i $ this) },
  { assumption }
end

end

section is_basis

variables {B₃ F₃ : bilin_form R₃ M₃}
variables {ι : Type*} {b : ι → M₃} (hb : is_basis R₃ b)

/-- Two bilinear forms are equal when they are equal on all basis vectors. -/
lemma ext_basis (h : ∀ i j, B₃ (b i) (b j) = F₃ (b i) (b j)) : B₃ = F₃ :=
to_lin.injective $ hb.ext $ λ i, hb.ext $ λ j, h i j

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis. -/
lemma sum_repr_mul_repr_mul (x y : M₃) :
  (hb.repr x).sum (λ i xi, (hb.repr y).sum (λ j yj, xi • yj • B₃ (b i) (b j))) = B₃ x y :=
begin
  conv_rhs { rw [← hb.total_repr x, ← hb.total_repr y] },
  simp_rw [finsupp.total_apply, finsupp.sum, map_sum_left, map_sum_right,
    smul_left, smul_right, smul_eq_mul]
end

end is_basis

end bilin_form

section matrix
variables {n o : Type*} [fintype n] [fintype o]

open bilin_form finset linear_map matrix
open_locale matrix

/-- The map from `matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `matrix.to_bilin_form'`. -/
def matrix.to_bilin'_aux (M : matrix n n R₂) : bilin_form R₂ (n → R₂) :=
{ bilin := λ v w, ∑ i j, v i * M i j * w j,
  bilin_add_left := λ x y z, by simp only [pi.add_apply, add_mul, sum_add_distrib],
  bilin_smul_left := λ a x y, by simp only [pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum],
  bilin_add_right := λ x y z, by simp only [pi.add_apply, mul_add, sum_add_distrib],
  bilin_smul_right := λ a x y,
    by simp only [pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_sum] }

lemma matrix.to_bilin'_aux_std_basis [decidable_eq n] (M : matrix n n R₂) (i j : n) :
  M.to_bilin'_aux (std_basis R₂ (λ _, R₂) i 1) (std_basis R₂ (λ _, R₂) j 1) =
    M i j :=
begin
  rw [matrix.to_bilin'_aux, coe_fn_mk, sum_eq_single i, sum_eq_single j],
  { simp only [std_basis_same, std_basis_same, one_mul, mul_one] },
  { rintros j' - hj',
    apply mul_eq_zero_of_right,
    exact std_basis_ne R₂ (λ _, R₂) _ _ hj' 1 },
  { intros,
    have := finset.mem_univ j,
    contradiction },
  { rintros i' - hi',
    refine finset.sum_eq_zero (λ j _, _),
    apply mul_eq_zero_of_left,
    apply mul_eq_zero_of_left,
    exact std_basis_ne R₂ (λ _, R₂) _ _ hi' 1 },
  { intros,
    have := finset.mem_univ i,
    contradiction }
end

/-- The linear map from bilinear forms to `matrix n n R` given an `n`-indexed basis.

This is an auxiliary definition for the equivalence `matrix.to_bilin_form'`. -/
def bilin_form.to_matrix_aux (b : n → M₂) : bilin_form R₂ M₂ →ₗ[R₂] matrix n n R₂ :=
{ to_fun := λ B i j, B (b i) (b j),
  map_add' := λ f g, rfl,
  map_smul' := λ f g, rfl }

lemma to_bilin'_aux_to_matrix_aux [decidable_eq n] (B₃ : bilin_form R₃ (n → R₃)) :
  matrix.to_bilin'_aux (bilin_form.to_matrix_aux (λ j, std_basis R₃ (λ _, R₃) j 1) B₃) =
    B₃ :=
begin
  refine ext_basis (pi.is_basis_fun R₃ n) (λ i j, _),
  rw [bilin_form.to_matrix_aux, linear_map.coe_mk, matrix.to_bilin'_aux_std_basis]
end

section to_matrix'

/-! ### `to_matrix'` section

This section deals with the conversion between matrices and bilinear forms on `n → R₃`.
-/

variables [decidable_eq n] [decidable_eq o]

/-- The linear equivalence between bilinear forms on `n → R` and `n × n` matrices -/
def bilin_form.to_matrix' : bilin_form R₃ (n → R₃) ≃ₗ[R₃] matrix n n R₃ :=
{ inv_fun := matrix.to_bilin'_aux,
  left_inv := by convert to_bilin'_aux_to_matrix_aux,
  right_inv := λ M,
    by { ext i j, simp only [bilin_form.to_matrix_aux, matrix.to_bilin'_aux_std_basis] },
  ..bilin_form.to_matrix_aux (λ j, std_basis R₃ (λ _, R₃) j 1) }

@[simp] lemma bilin_form.to_matrix_aux_std_basis (B : bilin_form R₃ (n → R₃)) :
  bilin_form.to_matrix_aux (λ j, std_basis R₃ (λ _, R₃) j 1) B =
    bilin_form.to_matrix' B :=
rfl

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
def matrix.to_bilin' : matrix n n R₃ ≃ₗ[R₃] bilin_form R₃ (n → R₃) :=
bilin_form.to_matrix'.symm

@[simp] lemma matrix.to_bilin'_aux_eq (M : matrix n n R₃) :
  matrix.to_bilin'_aux M = matrix.to_bilin' M :=
rfl

lemma matrix.to_bilin'_apply (M : matrix n n R₃) (x y : n → R₃) :
  matrix.to_bilin' M x y = ∑ i j, x i * M i j * y j := rfl

lemma matrix.to_bilin'_apply' (M : matrix n n R₃) (v w : n → R₃) :
  matrix.to_bilin' M v w = matrix.dot_product v (M.mul_vec w) :=
begin
  simp_rw [matrix.to_bilin'_apply, matrix.dot_product,
           matrix.mul_vec, matrix.dot_product],
  refine finset.sum_congr rfl (λ _ _, _),
  rw finset.mul_sum,
  refine finset.sum_congr rfl (λ _ _, _),
  rw ← mul_assoc,
end

@[simp] lemma matrix.to_bilin'_std_basis (M : matrix n n R₃) (i j : n) :
  matrix.to_bilin' M (std_basis R₃ (λ _, R₃) i 1) (std_basis R₃ (λ _, R₃) j 1) =
    M i j :=
matrix.to_bilin'_aux_std_basis M i j

@[simp] lemma bilin_form.to_matrix'_symm :
  (bilin_form.to_matrix'.symm : matrix n n R₃ ≃ₗ _) = matrix.to_bilin' :=
rfl

@[simp] lemma matrix.to_bilin'_symm :
  (matrix.to_bilin'.symm : _ ≃ₗ matrix n n R₃) = bilin_form.to_matrix' :=
bilin_form.to_matrix'.symm_symm

@[simp] lemma matrix.to_bilin'_to_matrix' (B : bilin_form R₃ (n → R₃)) :
  matrix.to_bilin' (bilin_form.to_matrix' B) = B :=
matrix.to_bilin'.apply_symm_apply B

@[simp] lemma bilin_form.to_matrix'_to_bilin' (M : matrix n n R₃) :
  bilin_form.to_matrix' (matrix.to_bilin' M) = M :=
bilin_form.to_matrix'.apply_symm_apply M

@[simp] lemma bilin_form.to_matrix'_apply (B : bilin_form R₃ (n → R₃)) (i j : n) :
  bilin_form.to_matrix' B i j =
    B (std_basis R₃ (λ _, R₃) i 1) (std_basis R₃ (λ _, R₃) j 1) :=
rfl

@[simp] lemma bilin_form.to_matrix'_comp (B : bilin_form R₃ (n → R₃))
  (l r : (o → R₃) →ₗ[R₃] (n → R₃)) :
  (B.comp l r).to_matrix' = l.to_matrix'ᵀ ⬝ B.to_matrix' ⬝ r.to_matrix' :=
begin
  ext i j,
  simp only [bilin_form.to_matrix'_apply, bilin_form.comp_apply, transpose_apply, matrix.mul_apply,
    linear_map.to_matrix', linear_equiv.coe_mk, sum_mul],
  rw sum_comm,
  conv_lhs { rw ← sum_repr_mul_repr_mul (pi.is_basis_fun R₃ n) (l _) (r _) },
  rw finsupp.sum_fintype,
  { apply sum_congr rfl,
    rintros i' -,
    rw finsupp.sum_fintype,
    { apply sum_congr rfl,
      rintros j' -,
      simp only [smul_eq_mul, pi.is_basis_fun_repr, mul_assoc, mul_comm, mul_left_comm] },
    { intros, simp only [zero_smul, smul_zero] } },
  { intros, simp only [zero_smul, finsupp.sum_zero] }
end

lemma bilin_form.to_matrix'_comp_left (B : bilin_form R₃ (n → R₃)) (f : (n → R₃) →ₗ[R₃] (n → R₃)) :
  (B.comp_left f).to_matrix' = f.to_matrix'ᵀ ⬝ B.to_matrix' :=
by simp only [comp_left, bilin_form.to_matrix'_comp, to_matrix'_id, matrix.mul_one]

lemma bilin_form.to_matrix'_comp_right (B : bilin_form R₃ (n → R₃)) (f : (n → R₃) →ₗ[R₃] (n → R₃)) :
  (B.comp_right f).to_matrix' = B.to_matrix' ⬝ f.to_matrix' :=
by simp only [bilin_form.comp_right, bilin_form.to_matrix'_comp, to_matrix'_id,
              transpose_one, matrix.one_mul]

lemma bilin_form.mul_to_matrix'_mul (B : bilin_form R₃ (n → R₃))
  (M : matrix o n R₃) (N : matrix n o R₃) :
  M ⬝ B.to_matrix' ⬝ N = (B.comp Mᵀ.to_lin' N.to_lin').to_matrix' :=
by simp only [B.to_matrix'_comp, transpose_transpose, to_matrix'_to_lin']

lemma bilin_form.mul_to_matrix' (B : bilin_form R₃ (n → R₃)) (M : matrix n n R₃) :
  M ⬝ B.to_matrix' = (B.comp_left Mᵀ.to_lin').to_matrix' :=
by simp only [B.to_matrix'_comp_left, transpose_transpose, to_matrix'_to_lin']

lemma bilin_form.to_matrix'_mul (B : bilin_form R₃ (n → R₃)) (M : matrix n n R₃) :
  B.to_matrix' ⬝ M = (B.comp_right M.to_lin').to_matrix' :=
by simp only [B.to_matrix'_comp_right, to_matrix'_to_lin']

lemma matrix.to_bilin'_comp (M : matrix n n R₃) (P Q : matrix n o R₃) :
  M.to_bilin'.comp P.to_lin' Q.to_lin' = (Pᵀ ⬝ M ⬝ Q).to_bilin' :=
bilin_form.to_matrix'.injective
  (by simp only [bilin_form.to_matrix'_comp, bilin_form.to_matrix'_to_bilin', to_matrix'_to_lin'])

end to_matrix'

section to_matrix

/-! ### `to_matrix` section

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/

variables [decidable_eq n] {b : n → M₃} (hb : is_basis R₃ b)

/-- `bilin_form.to_matrix hb` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `hb` is an `R`-basis for `M`. -/
noncomputable def bilin_form.to_matrix : bilin_form R₃ M₃ ≃ₗ[R₃] matrix n n R₃ :=
(bilin_form.congr hb.equiv_fun).trans bilin_form.to_matrix'

/-- `bilin_form.to_matrix hb` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `hb` is an `R`-basis for `M`. -/
noncomputable def matrix.to_bilin : matrix n n R₃ ≃ₗ[R₃] bilin_form R₃ M₃ :=
(bilin_form.to_matrix hb).symm

@[simp] lemma is_basis.equiv_fun_symm_std_basis (i : n) :
  hb.equiv_fun.symm (std_basis R₃ (λ _, R₃) i 1) = b i :=
begin
  rw [hb.equiv_fun_symm_apply, finset.sum_eq_single i],
  { rw [std_basis_same, one_smul] },
  { rintros j - hj,
    rw [std_basis_ne _ _ _ _ hj, zero_smul] },
  { intro,
    have := mem_univ i,
    contradiction }
end

@[simp] lemma bilin_form.to_matrix_apply (B : bilin_form R₃ M₃) (i j : n) :
  bilin_form.to_matrix hb B i j = B (b i) (b j) :=
by rw [bilin_form.to_matrix, linear_equiv.trans_apply, bilin_form.to_matrix'_apply, congr_apply,
       hb.equiv_fun_symm_std_basis, hb.equiv_fun_symm_std_basis]

@[simp] lemma matrix.to_bilin_apply (M : matrix n n R₃) (x y : M₃) :
  matrix.to_bilin hb M x y = ∑ i j, hb.repr x i * M i j * hb.repr y j :=
show ((congr hb.equiv_fun).symm (matrix.to_bilin' M)) x y =
    ∑ (i j : n), hb.repr x i * M i j * hb.repr y j,
by simp only [congr_symm, congr_apply, linear_equiv.symm_symm, matrix.to_bilin'_apply,
  is_basis.equiv_fun_apply]

-- Not a `simp` lemma since `bilin_form.to_matrix` needs an extra argument
lemma bilinear_form.to_matrix_aux_eq (B : bilin_form R₃ M₃) :
  bilin_form.to_matrix_aux b B = bilin_form.to_matrix hb B :=
ext (λ i j, by rw [bilin_form.to_matrix_apply, bilin_form.to_matrix_aux, linear_map.coe_mk])

@[simp] lemma bilin_form.to_matrix_symm :
  (bilin_form.to_matrix hb).symm = matrix.to_bilin hb :=
rfl

@[simp] lemma matrix.to_bilin_symm :
  (matrix.to_bilin hb).symm = bilin_form.to_matrix hb :=
(bilin_form.to_matrix hb).symm_symm

lemma matrix.to_bilin_is_basis_fun :
  matrix.to_bilin (pi.is_basis_fun R₃ n) = matrix.to_bilin' :=
by { ext M, simp only [matrix.to_bilin_apply, matrix.to_bilin'_apply, pi.is_basis_fun_repr] }

lemma bilin_form.to_matrix_is_basis_fun :
  bilin_form.to_matrix (pi.is_basis_fun R₃ n) = bilin_form.to_matrix' :=
by { ext B, rw [bilin_form.to_matrix_apply, bilin_form.to_matrix'_apply] }

@[simp] lemma matrix.to_bilin_to_matrix (B : bilin_form R₃ M₃) :
  matrix.to_bilin hb (bilin_form.to_matrix hb B) = B :=
(matrix.to_bilin hb).apply_symm_apply B

@[simp] lemma bilin_form.to_matrix_to_bilin (M : matrix n n R₃) :
  bilin_form.to_matrix hb (matrix.to_bilin hb M) = M :=
(bilin_form.to_matrix hb).apply_symm_apply M

variables {M₃' : Type*} [add_comm_group M₃'] [module R₃ M₃']
variables {c : o → M₃'} (hc : is_basis R₃ c)
variables [decidable_eq o]

-- Cannot be a `simp` lemma because `hb` must be inferred.
lemma bilin_form.to_matrix_comp
  (B : bilin_form R₃ M₃) (l r : M₃' →ₗ[R₃] M₃) :
  bilin_form.to_matrix hc (B.comp l r) =
    (to_matrix hc hb l)ᵀ ⬝ bilin_form.to_matrix hb B ⬝ to_matrix hc hb r :=
begin
  ext i j,
  simp only [bilin_form.to_matrix_apply, bilin_form.comp_apply, transpose_apply, matrix.mul_apply,
    linear_map.to_matrix', linear_equiv.coe_mk, sum_mul],
  rw sum_comm,
  conv_lhs { rw ← sum_repr_mul_repr_mul hb },
  rw finsupp.sum_fintype,
  { apply sum_congr rfl,
    rintros i' -,
    rw finsupp.sum_fintype,
    { apply sum_congr rfl,
      rintros j' -,
      simp only [smul_eq_mul, linear_map.to_matrix_apply,
        is_basis.equiv_fun_apply, mul_assoc, mul_comm, mul_left_comm] },
    { intros, simp only [zero_smul, smul_zero] } },
  { intros, simp only [zero_smul, finsupp.sum_zero] }
end

lemma bilin_form.to_matrix_comp_left (B : bilin_form R₃ M₃) (f : M₃ →ₗ[R₃] M₃) :
  bilin_form.to_matrix hb (B.comp_left f) = (to_matrix hb hb f)ᵀ ⬝ bilin_form.to_matrix hb B :=
by simp only [comp_left, bilin_form.to_matrix_comp hb hb, to_matrix_id, matrix.mul_one]

lemma bilin_form.to_matrix_comp_right (B : bilin_form R₃ M₃) (f : M₃ →ₗ[R₃] M₃) :
  bilin_form.to_matrix hb (B.comp_right f) = bilin_form.to_matrix hb B ⬝ (to_matrix hb hb f) :=
by simp only [bilin_form.comp_right, bilin_form.to_matrix_comp hb hb, to_matrix_id,
              transpose_one, matrix.one_mul]

lemma bilin_form.mul_to_matrix_mul (B : bilin_form R₃ M₃)
  (M : matrix o n R₃) (N : matrix n o R₃) :
  M ⬝ bilin_form.to_matrix hb B ⬝ N =
    bilin_form.to_matrix hc (B.comp (to_lin hc hb Mᵀ) (to_lin hc hb N)) :=
by simp only [B.to_matrix_comp hb hc, to_matrix_to_lin, transpose_transpose]

lemma bilin_form.mul_to_matrix (B : bilin_form R₃ M₃) (M : matrix n n R₃) :
  M ⬝ bilin_form.to_matrix hb B =
    bilin_form.to_matrix hb (B.comp_left (to_lin hb hb Mᵀ)) :=
by rw [B.to_matrix_comp_left hb, to_matrix_to_lin, transpose_transpose]

lemma bilin_form.to_matrix_mul (B : bilin_form R₃ M₃) (M : matrix n n R₃) :
  bilin_form.to_matrix hb B ⬝ M =
    bilin_form.to_matrix hb (B.comp_right (to_lin hb hb M)) :=
by rw [B.to_matrix_comp_right hb, to_matrix_to_lin]

lemma matrix.to_bilin_comp (M : matrix n n R₃) (P Q : matrix n o R₃) :
  (matrix.to_bilin hb M).comp (to_lin hc hb P) (to_lin hc hb Q) = matrix.to_bilin hc (Pᵀ ⬝ M ⬝ Q) :=
(bilin_form.to_matrix hc).injective
  (by simp only [bilin_form.to_matrix_comp hb hc, bilin_form.to_matrix_to_bilin, to_matrix_to_lin])

end to_matrix

end matrix

namespace finsupp

variables {α β : Type*}
variables {M' : Type*} [add_comm_monoid M']
variables {N : Type*} [has_zero N]

lemma bilin_add_left' (A : α → β → N → (M' →+ R)) (p q : α →₀ M') (r : β →₀ N) :
  (p + q).sum (λ i x, r.sum (λ j y, A i j y x))
  = p.sum (λ i x, r.sum (λ j y, A i j y x)) + q.sum (λ i x, r.sum (λ j y, A i j y x)) :=
begin
  rw finsupp.sum_add_index,
  { simp },
  { simp }
end

lemma bilin_add_right' (A : α → β → N → (M' →+ R)) (p : α →₀ N) (q r : β →₀ M') :
  p.sum (λ i x, (q + r).sum (λ j y, A i j x y))
  = p.sum (λ i x, q.sum (λ j y, A i j x y)) + p.sum (λ i x, r.sum (λ j y, A i j x y)) :=
begin
  rw ← finsupp.sum_add,
  congr,
  ext i x,
  rw finsupp.sum_add_index,
  { simp },
  { simp [mul_add] }
end

lemma bilin_smul_left' (A : α → β → N → (M →ₗ[R] R)) (a : R)
  (p : α →₀ M) (q : β →₀ N) :
  (a • p).sum (λ i x, q.sum (λ j y, A i j y x))
  = a • p.sum (λ i x, q.sum (λ j y, A i j y x)) :=
begin
  let h : α → M →ₗ[R] R := λ i, q.sum (λ j y, A i j y),
  have := @finsupp.sum_smul_index_linear_map' _ _ _ _ _ _ _ _ _ _ _ h,
  convert this;
  { ext i x,
    simp [h] },
end

lemma bilin_smul_right' (A : α → β → N → (M →ₗ[R] R)) (a : R)
  (p : α →₀ N) (q : β →₀ M) :
  p.sum (λ i x, (a • q).sum (λ j y, A i j x y))
  = a • p.sum (λ i x, q.sum (λ j y, A i j x y)) :=
begin
  rw finsupp.smul_sum,
  congr,
  ext i x,
  exact finsupp.sum_smul_index_linear_map'
end

open bilin_form

/-- A collection of `bilin_form R M`, parametrized by two indices in `α`, induces a bilinear form
on `α →₀ M`.  This can be thought of as an infinite-dimensional version of `matrix.to_bilin_form`.
-/
noncomputable def to_bilin_form (A : α → α → (bilin_form R M)) :
  bilin_form R (α →₀ M) :=
{ bilin := λ p q, p.sum (λ i x, q.sum (λ j y, A i j x y)),
  bilin_add_left := bilin_add_left' (λ i j x, (to_lin'_flip (A i j) x).to_add_monoid_hom),
  bilin_smul_left := bilin_smul_left' (λ i j, to_lin'_flip (A i j)),
  bilin_add_right := bilin_add_right' (λ i j x, (to_lin' (A i j) x).to_add_monoid_hom),
  bilin_smul_right := bilin_smul_right' (λ i j, to_lin' (A i j)) }

@[simp] lemma to_bilin_form_apply (A : α → α → (bilin_form R M)) (p q : α →₀ M) :
  finsupp.to_bilin_form A p q = p.sum (λ i x, q.sum (λ j y, A i j x y)) :=
rfl

end finsupp

namespace refl_bilin_form

open refl_bilin_form bilin_form

/-- The proposition that a bilinear form is reflexive -/
def is_refl (B : bilin_form R M) : Prop := ∀ (x y : M), B x y = 0 → B y x = 0

variable (H : is_refl B)

lemma eq_zero : ∀ {x y : M}, B x y = 0 → B y x = 0 := λ x y, H x y

lemma ortho_sym {x y : M} :
  is_ortho B x y ↔ is_ortho B y x := ⟨eq_zero H, eq_zero H⟩

end refl_bilin_form

namespace sym_bilin_form

open sym_bilin_form bilin_form

/-- The proposition that a bilinear form is symmetric -/
def is_sym (B : bilin_form R M) : Prop := ∀ (x y : M), B x y = B y x

variable (H : is_sym B)

lemma sym (x y : M) : B x y = B y x := H x y

lemma is_refl : refl_bilin_form.is_refl B := λ x y H1, H x y ▸ H1

lemma ortho_sym {x y : M} :
  is_ortho B x y ↔ is_ortho B y x := refl_bilin_form.ortho_sym (is_refl H)

lemma is_sym_iff_flip' [algebra R₂ R] : is_sym B ↔ flip_hom R₂ B = B :=
begin
  split,
  { intros h,
    ext x y,
    exact h y x },
  { intros h x y,
    conv_lhs { rw ← h },
    simp }
end

end sym_bilin_form

/-- A bilinear form on `finsupp` from an "infinite matrix" is symmetric, if the coefficients
satisfy a symmetry condition. -/
-- TODO the same for matrices
lemma finsupp.is_sym_to_bilinear_form {α : Type*} (A : α → α → (bilin_form R M))
  (hA : ∀ i j x y, A i j x y = A j i y x) :
  sym_bilin_form.is_sym (finsupp.to_bilin_form A) :=
begin
  intros p q,
  simp only [finsupp.to_bilin_form_apply, p.sum_comm q],
  congr,
  ext i x,
  congr,
  ext j y,
  exact (hA i j x y).symm
end

namespace alt_bilin_form

open alt_bilin_form bilin_form

/-- The proposition that a bilinear form is alternating -/
def is_alt (B : bilin_form R M) : Prop := ∀ (x : M), B x x = 0

variable (H : is_alt B)
include H

lemma self_eq_zero (x : M) : B x x = 0 := H x

lemma neg (H : is_alt B₁) (x y : M₁) :
  - B₁ x y = B₁ y x :=
begin
  have H1 : B₁ (x + y) (x + y) = 0,
  { exact self_eq_zero H (x + y) },
  rw [add_left, add_right, add_right,
    self_eq_zero H, self_eq_zero H, ring.zero_add,
    ring.add_zero, add_eq_zero_iff_neg_eq] at H1,
  exact H1,
end

end alt_bilin_form

namespace bilin_form

section linear_adjoints

variables (B) (F : bilin_form R M)
variables {M' : Type*} [add_comm_monoid M'] [semimodule R M']
variables (B' : bilin_form R M') (f f' : M →ₗ[R] M') (g g' : M' →ₗ[R] M)

/-- Given a pair of modules equipped with bilinear forms, this is the condition for a pair of
maps between them to be mutually adjoint. -/
def is_adjoint_pair := ∀ ⦃x y⦄, B' (f x) y = B x (g y)

variables {B B' B₂ f f' g g'}

lemma is_adjoint_pair.eq (h : is_adjoint_pair B B' f g) :
  ∀ {x y}, B' (f x) y = B x (g y) := h

lemma is_adjoint_pair_iff_comp_left_eq_comp_right (f g : module.End R M) :
  is_adjoint_pair B F f g ↔ F.comp_left f = B.comp_right g :=
begin
  split; intros h,
  { ext x y, rw [comp_left_apply, comp_right_apply], apply h, },
  { intros x y, rw [←comp_left_apply, ←comp_right_apply], rw h, },
end

lemma is_adjoint_pair_zero : is_adjoint_pair B B' 0 0 :=
λ x y, by simp only [bilin_form.zero_left, bilin_form.zero_right, linear_map.zero_apply]

lemma is_adjoint_pair_id : is_adjoint_pair B B 1 1 := λ x y, rfl

lemma is_adjoint_pair.add (h : is_adjoint_pair B B' f g) (h' : is_adjoint_pair B B' f' g') :
  is_adjoint_pair B B' (f + f') (g + g') :=
λ x y, by rw [linear_map.add_apply, linear_map.add_apply, add_left, add_right, h, h']

variables {M₁' : Type*} [add_comm_group M₁'] [module R₁ M₁']
variables {B₁' : bilin_form R₁ M₁'} {f₁ f₁' : M₁ →ₗ[R₁] M₁'} {g₁ g₁' : M₁' →ₗ[R₁] M₁}

lemma is_adjoint_pair.sub (h : is_adjoint_pair B₁ B₁' f₁ g₁) (h' : is_adjoint_pair B₁ B₁' f₁' g₁') :
  is_adjoint_pair B₁ B₁' (f₁ - f₁') (g₁ - g₁') :=
λ x y, by rw [linear_map.sub_apply, linear_map.sub_apply, sub_left, sub_right, h, h']

variables {M₂' : Type*} [add_comm_monoid M₂'] [semimodule R₂ M₂']
variables {B₂' : bilin_form R₂ M₂'} {f₂ f₂' : M₂ →ₗ[R₂] M₂'} {g₂ g₂' : M₂' →ₗ[R₂] M₂}

lemma is_adjoint_pair.smul (c : R₂) (h : is_adjoint_pair B₂ B₂' f₂ g₂) :
  is_adjoint_pair B₂ B₂' (c • f₂) (c • g₂) :=
λ x y, by rw [linear_map.smul_apply, linear_map.smul_apply, smul_left, smul_right, h]

variables {M'' : Type*} [add_comm_monoid M''] [semimodule R M'']
variables (B'' : bilin_form R M'')

lemma is_adjoint_pair.comp {f' : M' →ₗ[R] M''} {g' : M'' →ₗ[R] M'}
  (h : is_adjoint_pair B B' f g) (h' : is_adjoint_pair B' B'' f' g') :
  is_adjoint_pair B B'' (f'.comp f) (g.comp g') :=
λ x y, by rw [linear_map.comp_apply, linear_map.comp_apply, h', h]

lemma is_adjoint_pair.mul
  {f g f' g' : module.End R M} (h : is_adjoint_pair B B f g) (h' : is_adjoint_pair B B f' g') :
  is_adjoint_pair B B (f * f') (g' * g) :=
λ x y, by rw [linear_map.mul_apply, linear_map.mul_apply, h, h']

variables (B B' B₁ B₂) (F₂ : bilin_form R₂ M₂)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear forms
on the underlying module. In the case that these two forms are identical, this is the usual concept
of self adjointness. In the case that one of the forms is the negation of the other, this is the
usual concept of skew adjointness. -/
def is_pair_self_adjoint (f : module.End R M) := is_adjoint_pair B F f f

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
def is_pair_self_adjoint_submodule : submodule R₂ (module.End R₂ M₂) :=
{ carrier   := { f | is_pair_self_adjoint B₂ F₂ f },
  zero_mem' := is_adjoint_pair_zero,
  add_mem'  := λ f g hf hg, hf.add hg,
  smul_mem' := λ c f h, h.smul c, }

@[simp] lemma mem_is_pair_self_adjoint_submodule (f : module.End R₂ M₂) :
  f ∈ is_pair_self_adjoint_submodule B₂ F₂ ↔ is_pair_self_adjoint B₂ F₂ f :=
by refl

variables {M₃' : Type*} [add_comm_group M₃'] [module R₃ M₃']
variables (B₃ F₃ : bilin_form R₃ M₃)

lemma is_pair_self_adjoint_equiv (e : M₃' ≃ₗ[R₃] M₃) (f : module.End R₃ M₃) :
  is_pair_self_adjoint B₃ F₃ f ↔
    is_pair_self_adjoint (B₃.comp ↑e ↑e) (F₃.comp ↑e ↑e) (e.symm.conj f) :=
begin
  have hₗ : (F₃.comp ↑e ↑e).comp_left (e.symm.conj f) = (F₃.comp_left f).comp ↑e ↑e :=
    by { ext, simp [linear_equiv.symm_conj_apply], },
  have hᵣ : (B₃.comp ↑e ↑e).comp_right (e.symm.conj f) = (B₃.comp_right f).comp ↑e ↑e :=
    by { ext, simp [linear_equiv.conj_apply], },
  have he : function.surjective (⇑(↑e : M₃' →ₗ[R₃] M₃) : M₃' → M₃) := e.surjective,
  show bilin_form.is_adjoint_pair _ _ _ _  ↔ bilin_form.is_adjoint_pair _ _ _ _,
  rw [is_adjoint_pair_iff_comp_left_eq_comp_right, is_adjoint_pair_iff_comp_left_eq_comp_right,
      hᵣ, hₗ, comp_injective _ _ he he],
end

/-- An endomorphism of a module is self-adjoint with respect to a bilinear form if it serves as an
adjoint for itself. -/
def is_self_adjoint (f : module.End R M) := is_adjoint_pair B B f f

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear form if its negation
serves as an adjoint. -/
def is_skew_adjoint (f : module.End R₁ M₁) := is_adjoint_pair B₁ B₁ f (-f)

lemma is_skew_adjoint_iff_neg_self_adjoint (f : module.End R₁ M₁) :
  B₁.is_skew_adjoint f ↔ is_adjoint_pair (-B₁) B₁ f f :=
show (∀ x y, B₁ (f x) y = B₁ x ((-f) y)) ↔ ∀ x y, B₁ (f x) y = (-B₁) x (f y),
by simp only [linear_map.neg_apply, bilin_form.neg_apply, bilin_form.neg_right]

/-- The set of self-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Jordan subalgebra.) -/
def self_adjoint_submodule := is_pair_self_adjoint_submodule B₂ B₂

@[simp] lemma mem_self_adjoint_submodule (f : module.End R₂ M₂) :
  f ∈ B₂.self_adjoint_submodule ↔ B₂.is_self_adjoint f := iff.rfl

/-- The set of skew-adjoint endomorphisms of a module with bilinear form is a submodule. (In fact
it is a Lie subalgebra.) -/
def skew_adjoint_submodule := is_pair_self_adjoint_submodule (-B₃) B₃

@[simp] lemma mem_skew_adjoint_submodule (f : module.End R₃ M₃) :
  f ∈ B₃.skew_adjoint_submodule ↔ B₃.is_skew_adjoint f :=
by { rw is_skew_adjoint_iff_neg_self_adjoint, exact iff.rfl, }

end linear_adjoints

end bilin_form

section matrix_adjoints
open_locale matrix

variables {n : Type w} [fintype n]
variables {b : n → M₃} (hb : is_basis R₃ b)
variables (J J₃ A A' : matrix n n R₃)

/-- The condition for the square matrices `A`, `A'` to be an adjoint pair with respect to the square
matrices `J`, `J₃`. -/
def matrix.is_adjoint_pair := Aᵀ ⬝ J₃ = J ⬝ A'

/-- The condition for a square matrix `A` to be self-adjoint with respect to the square matrix
`J`. -/
def matrix.is_self_adjoint := matrix.is_adjoint_pair J J A A

/-- The condition for a square matrix `A` to be skew-adjoint with respect to the square matrix
`J`. -/
def matrix.is_skew_adjoint := matrix.is_adjoint_pair J J A (-A)

@[simp] lemma is_adjoint_pair_to_bilin' [decidable_eq n] :
  bilin_form.is_adjoint_pair (matrix.to_bilin' J) (matrix.to_bilin' J₃)
      (matrix.to_lin' A) (matrix.to_lin' A') ↔
    matrix.is_adjoint_pair J J₃ A A' :=
begin
  rw bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right,
  have h : ∀ (B B' : bilin_form R₃ (n → R₃)), B = B' ↔
    (bilin_form.to_matrix' B) = (bilin_form.to_matrix' B'),
  { intros B B',
    split; intros h,
    { rw h },
    { exact bilin_form.to_matrix'.injective h } },
  rw [h, bilin_form.to_matrix'_comp_left, bilin_form.to_matrix'_comp_right,
      linear_map.to_matrix'_to_lin', linear_map.to_matrix'_to_lin',
      bilin_form.to_matrix'_to_bilin', bilin_form.to_matrix'_to_bilin'],
  refl,
end

@[simp] lemma is_adjoint_pair_to_bilin [decidable_eq n] :
  bilin_form.is_adjoint_pair (matrix.to_bilin hb J) (matrix.to_bilin hb J₃)
      (matrix.to_lin hb hb A) (matrix.to_lin hb hb A') ↔
    matrix.is_adjoint_pair J J₃ A A' :=
begin
  rw bilin_form.is_adjoint_pair_iff_comp_left_eq_comp_right,
  have h : ∀ (B B' : bilin_form R₃ M₃), B = B' ↔
    (bilin_form.to_matrix hb B) = (bilin_form.to_matrix hb B'),
  { intros B B',
    split; intros h,
    { rw h },
    { exact (bilin_form.to_matrix hb).injective h } },
  rw [h, bilin_form.to_matrix_comp_left, bilin_form.to_matrix_comp_right,
      linear_map.to_matrix_to_lin, linear_map.to_matrix_to_lin,
      bilin_form.to_matrix_to_bilin, bilin_form.to_matrix_to_bilin],
  refl,
end

lemma matrix.is_adjoint_pair_equiv [decidable_eq n] (P : matrix n n R₃) (h : is_unit P) :
  (Pᵀ ⬝ J ⬝ P).is_adjoint_pair (Pᵀ ⬝ J ⬝ P) A A' ↔
    J.is_adjoint_pair J (P ⬝ A ⬝ P⁻¹) (P ⬝ A' ⬝ P⁻¹) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
begin
  let u := P.nonsing_inv_unit h',
  let v := Pᵀ.nonsing_inv_unit (P.is_unit_det_transpose h'),
  let x := Aᵀ * Pᵀ * J,
  let y := J * P * A',
  suffices : x * ↑u = ↑v * y ↔ ↑v⁻¹ * x = y * ↑u⁻¹,
  { dunfold matrix.is_adjoint_pair,
    repeat { rw matrix.transpose_mul, },
    simp only [←matrix.mul_eq_mul, ←mul_assoc, P.transpose_nonsing_inv h'],
    conv_lhs { to_rhs, rw [mul_assoc, mul_assoc], congr, skip, rw ←mul_assoc, },
    conv_rhs { rw [mul_assoc, mul_assoc], conv { to_lhs, congr, skip, rw ←mul_assoc }, },
    exact this, },
  rw units.eq_mul_inv_iff_mul_eq, conv_rhs { rw mul_assoc, }, rw v.inv_mul_eq_iff_eq_mul,
end

variables [decidable_eq n]

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pair_self_adjoint_matrices_submodule : submodule R₃ (matrix n n R₃) :=
(bilin_form.is_pair_self_adjoint_submodule (matrix.to_bilin' J) (matrix.to_bilin' J₃)).map
  (linear_map.to_matrix' : ((n → R₃) →ₗ[R₃] (n → R₃)) ≃ₗ[R₃] matrix n n R₃)

@[simp] lemma mem_pair_self_adjoint_matrices_submodule :
  A ∈ (pair_self_adjoint_matrices_submodule J J₃) ↔ matrix.is_adjoint_pair J J₃ A A :=
begin
  simp only [pair_self_adjoint_matrices_submodule, linear_equiv.coe_coe,
    linear_map.to_matrix'_apply, submodule.mem_map, bilin_form.mem_is_pair_self_adjoint_submodule],
  split,
  { rintros ⟨f, hf, hA⟩,
    have hf' : f = A.to_lin' := by rw [←hA, matrix.to_lin'_to_matrix'], rw hf' at hf,
    rw ← is_adjoint_pair_to_bilin',
    exact hf, },
  { intros h, refine ⟨A.to_lin', _, linear_map.to_matrix'_to_lin' _⟩,
    exact (is_adjoint_pair_to_bilin' _ _ _ _).mpr h, },
end

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def self_adjoint_matrices_submodule : submodule R₃ (matrix n n R₃) :=
  pair_self_adjoint_matrices_submodule J J

@[simp] lemma mem_self_adjoint_matrices_submodule :
  A ∈ self_adjoint_matrices_submodule J ↔ J.is_self_adjoint A :=
by { erw mem_pair_self_adjoint_matrices_submodule, refl, }

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skew_adjoint_matrices_submodule : submodule R₃ (matrix n n R₃) :=
  pair_self_adjoint_matrices_submodule (-J) J

@[simp] lemma mem_skew_adjoint_matrices_submodule :
  A ∈ skew_adjoint_matrices_submodule J ↔ J.is_skew_adjoint A :=
begin
  erw mem_pair_self_adjoint_matrices_submodule,
  simp [matrix.is_skew_adjoint, matrix.is_adjoint_pair],
end

end matrix_adjoints

namespace bilin_form

section orthogonal

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
def orthogonal (B : bilin_form R M) (N : submodule R M) : submodule R M :=
{ carrier := { m | ∀ n ∈ N, is_ortho B n m },
  zero_mem' := λ x _, is_ortho_zero_right x,
  add_mem' := λ x y hx hy n hn,
    by rw [is_ortho, add_right, show B n x = 0, by exact hx n hn,
        show B n y = 0, by exact hy n hn, zero_add],
  smul_mem' := λ c x hx n hn,
    by rw [is_ortho, smul_right, show B n x = 0, by exact hx n hn, mul_zero] }

variables {N L : submodule R M}

@[simp] lemma mem_orthogonal_iff {N : submodule R M} {m : M} :
  m ∈ B.orthogonal N ↔ ∀ n ∈ N, is_ortho B n m := iff.rfl

lemma orthogonal_le (h : N ≤ L) : B.orthogonal L ≤ B.orthogonal N :=
λ _ hn l hl, hn l (h hl)

lemma le_orthogonal_orthogonal (hB : refl_bilin_form.is_refl B) :
  N ≤ B.orthogonal (B.orthogonal N) :=
λ n hn m hm, hB _ _ (hm n hn)

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
lemma span_singleton_inf_orthogonal_eq_bot
  {B : bilin_form K V} {x : V} (hx : ¬ B.is_ortho x x) :
  (K ∙ x) ⊓ B.orthogonal (K ∙ x) = ⊥ :=
begin
  rw ← finset.coe_singleton,
  refine eq_bot_iff.2 (λ y h, _),
  rcases mem_span_finset.1 h.1 with ⟨μ, rfl⟩,
  have := h.2 x _,
  { rw finset.sum_singleton at this ⊢,
    suffices hμzero : μ x = 0,
    { rw [hμzero, zero_smul, submodule.mem_bot] },
    change B x (μ x • x) = 0 at this, rw [smul_right] at this,
    exact or.elim (zero_eq_mul.mp this.symm) id (λ hfalse, false.elim $ hx hfalse) },
  { rw submodule.mem_span; exact λ _ hp, hp $ finset.mem_singleton_self _ }
end

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
lemma orthogonal_span_singleton_eq_to_lin_ker {B : bilin_form K V} (x : V) :
  B.orthogonal (K ∙ x) = (bilin_form.to_lin B x).ker :=
begin
  ext y,
  simp_rw [mem_orthogonal_iff, linear_map.mem_ker,
           submodule.mem_span_singleton ],
  split,
  { exact λ h, h x ⟨1, one_smul _ _⟩ },
  { rintro h _ ⟨z, rfl⟩,
    rw [is_ortho, smul_left, mul_eq_zero],
    exact or.intro_right _ h }
end

lemma span_singleton_sup_orthogonal_eq_top {B : bilin_form K V}
  {x : V} (hx : ¬ B.is_ortho x x) :
  (K ∙ x) ⊔ B.orthogonal (K ∙ x) = ⊤ :=
begin
  rw orthogonal_span_singleton_eq_to_lin_ker,
  exact linear_map.span_singleton_sup_ker_eq_top _ hx,
end

/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
lemma is_compl_span_singleton_orthogonal {B : bilin_form K V}
  {x : V} (hx : ¬ B.is_ortho x x) : is_compl (K ∙ x) (B.orthogonal $ K ∙ x) :=
{ inf_le_bot := eq_bot_iff.1 $ span_singleton_inf_orthogonal_eq_bot hx,
  top_le_sup := eq_top_iff.1 $ span_singleton_sup_orthogonal_eq_top hx }

end orthogonal

/-- The restriction of a bilinear form on a submodule. -/
@[simps apply]
def restrict (B : bilin_form R M) (W : submodule R M) : bilin_form R W :=
{ bilin := λ a b, B a b,
  bilin_add_left := λ _ _ _, add_left _ _ _,
  bilin_smul_left := λ _ _ _, smul_left _ _ _,
  bilin_add_right := λ _ _ _, add_right _ _ _,
  bilin_smul_right := λ _ _ _, smul_right _ _ _}

/-- The restriction of a symmetric bilinear form on a submodule is also symmetric. -/
lemma restrict_sym (B : bilin_form R M) (hB : sym_bilin_form.is_sym B)
  (W : submodule R M) : sym_bilin_form.is_sym $ B.restrict W :=
λ x y, hB x y

/-- A nondegenerate bilinear form is a bilinear form such that the only element that is orthogonal
to every other element is `0`; i.e., for all nonzero `m` in `M`, there exists `n` in `M` with
`B m n ≠ 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "left" nondegeneracy condition one could define a "right"
nondegeneracy condition that in the situation described, `B n m ≠ 0`.  This variant definition is
not currently provided in mathlib. In finite dimension either definition implies the other. -/
def nondegenerate (B : bilin_form R M) : Prop :=
∀ m : M, (∀ n : M, B m n = 0) → m = 0

/-- A bilinear form is nondegenerate if and only if it has a trivial kernel. -/
theorem nondegenerate_iff_ker_eq_bot {B : bilin_form R₂ M₂} :
  B.nondegenerate ↔ B.to_lin.ker = ⊥ :=
begin
  rw linear_map.ker_eq_bot',
  split; intro h,
  { refine λ m hm, h _ (λ x, _),
    rw [← to_linear_map_apply, hm], refl },
  { intros m hm, apply h,
    ext, exact hm x }
end

section

variable [finite_dimensional K V]

/-- Given a nondegenerate bilinear form `B` on a finite-dimensional vector space, `B.to_dual` is
the linear equivalence between a vector space and its dual with the underlying linear map
`B.to_lin`. -/
noncomputable def to_dual (B : bilin_form K V) (hB : B.nondegenerate) :
  V ≃ₗ[K] module.dual K V :=
B.to_lin.linear_equiv_of_ker_eq_bot
  (nondegenerate_iff_ker_eq_bot.mp hB) subspace.dual_findim_eq.symm

lemma to_dual_def {B : bilin_form K V} (hB : B.nondegenerate) {m n : V} :
  B.to_dual hB m n = B m n := rfl

end

/-- The restriction of a symmetric, non-degenerate bilinear form on the orthogonal complement of
the span of a singleton is also non-degenerate. -/
lemma restrict_orthogonal_span_singleton_nondegenerate (B : bilin_form K V)
  (hB₁ : nondegenerate B) (hB₂ : sym_bilin_form.is_sym B) {x : V} (hx : ¬ B.is_ortho x x) :
  nondegenerate $ B.restrict $ B.orthogonal (K ∙ x) :=
begin
  refine λ m hm, submodule.coe_eq_zero.1 (hB₁ m.1 (λ n, _)),
  have : n ∈ (K ∙ x) ⊔ B.orthogonal (K ∙ x) :=
    (span_singleton_sup_orthogonal_eq_top hx).symm ▸ submodule.mem_top,
  rcases submodule.mem_sup.1 this with ⟨y, hy, z, hz, rfl⟩,
  specialize hm ⟨z, hz⟩,
  rw restrict at hm,
  erw [add_right, show B m.1 y = 0, by rw hB₂; exact m.2 y hy, hm, add_zero]
end

end bilin_form
