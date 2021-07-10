/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying
-/

import algebra.invertible
import linear_algebra.bilinear_form
import linear_algebra.matrix.determinant
import linear_algebra.special_linear_group
import analysis.special_functions.pow
import data.real.sign

/-!
# Quadratic forms

This file defines quadratic forms over a `R`-module `M`.
A quadratic form is a map `Q : M → R` such that
  (`to_fun_smul`) `Q (a • x) = a * a * Q x`
  (`polar_...`) The map `polar Q := λ x y, Q (x + y) - Q x - Q y` is bilinear.
They come with a scalar multiplication, `(a • Q) x = Q (a • x) = a * a * Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

 * `quadratic_form.associated`: associated bilinear form
 * `quadratic_form.pos_def`: positive definite quadratic forms
 * `quadratic_form.anisotropic`: anisotropic quadratic forms
 * `quadratic_form.discr`: discriminant of a quadratic form

## Main statements

 * `quadratic_form.associated_left_inverse`,
 * `quadratic_form.associated_right_inverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic forms and symmetric
  bilinear forms
 * `bilin_form.exists_orthogonal_basis`: There exists an orthogonal basis with
  respect to any nondegenerate, symmetric bilinear form `B`.

## Notation

In this file, the variable `R` is used when a `ring` structure is sufficient and
`R₁` is used when specifically a `comm_ring` is required. This allows us to keep
`[module R M]` and `[module R₁ M]` assumptions in the variables without
confusion between `*` from `ring` and `*` from `comm_ring`.

The variable `S` is used when `R` itself has a `•` action.

## References

 * https://en.wikipedia.org/wiki/Quadratic_form
 * https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic form, homogeneous polynomial, quadratic polynomial
-/

universes u v w
variables {S : Type*}
variables {R : Type*} {M : Type*} [add_comm_group M] [ring R]
variables {R₁ : Type*} [comm_ring R₁]

namespace quadratic_form
/-- Up to a factor 2, `Q.polar` is the associated bilinear form for a quadratic form `Q`.d

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def polar (f : M → R) (x y : M) :=
f (x + y) - f x - f y

lemma polar_add (f g : M → R) (x y : M) :
  polar (f + g) x y = polar f x y + polar g x y :=
by { simp only [polar, pi.add_apply], abel }

lemma polar_neg (f : M → R) (x y : M) :
  polar (-f) x y = - polar f x y :=
by { simp only [polar, pi.neg_apply, sub_eq_add_neg, neg_add] }

lemma polar_smul [monoid S] [distrib_mul_action S R] (f : M → R) (s : S) (x y : M) :
  polar (s • f) x y = s • polar f x y :=
by { simp only [polar, pi.smul_apply, smul_sub] }

lemma polar_comm (f : M → R) (x y : M) : polar f x y = polar f y x :=
by rw [polar, polar, add_comm, sub_sub, sub_sub, add_comm (f x) (f y)]

end quadratic_form

variables [module R M] [module R₁ M]

open quadratic_form
/-- A quadratic form over a module. -/
structure quadratic_form (R : Type u) (M : Type v) [ring R] [add_comm_group M] [module R M] :=
(to_fun : M → R)
(to_fun_smul : ∀ (a : R) (x : M), to_fun (a • x) = a * a * to_fun x)
(polar_add_left' : ∀ (x x' y : M), polar to_fun (x + x') y = polar to_fun x y + polar to_fun x' y)
(polar_smul_left' : ∀ (a : R) (x y : M), polar to_fun (a • x) y = a • polar to_fun x y)
(polar_add_right' : ∀ (x y y' : M), polar to_fun x (y + y') = polar to_fun x y + polar to_fun x y')
(polar_smul_right' : ∀ (a : R) (x y : M), polar to_fun x (a • y) = a • polar to_fun x y)

namespace quadratic_form

variables {Q : quadratic_form R M}

instance : has_coe_to_fun (quadratic_form R M) :=
⟨_, to_fun⟩

/-- The `simp` normal form for a quadratic form is `coe_fn`, not `to_fun`. -/
@[simp] lemma to_fun_eq_apply : Q.to_fun = ⇑ Q := rfl

lemma map_smul (a : R) (x : M) : Q (a • x) = a * a * Q x := Q.to_fun_smul a x

lemma map_add_self (x : M) : Q (x + x) = 4 * Q x :=
by { rw [←one_smul R x, ←add_smul, map_smul], norm_num }

@[simp] lemma map_zero : Q 0 = 0 :=
by rw [←@zero_smul R _ _ _ _ (0 : M), map_smul, zero_mul, zero_mul]

@[simp] lemma map_neg (x : M) : Q (-x) = Q x :=
by rw [←@neg_one_smul R _ _ _ _ x, map_smul, neg_one_mul, neg_neg, one_mul]

lemma map_sub (x y : M) : Q (x - y) = Q (y - x) :=
by rw [←neg_sub, map_neg]

@[simp]
lemma polar_zero_left (y : M) : polar Q 0 y = 0 :=
by simp [polar]

@[simp]
lemma polar_add_left (x x' y : M) :
  polar Q (x + x') y = polar Q x y + polar Q x' y :=
Q.polar_add_left' x x' y

@[simp]
lemma polar_smul_left (a : R) (x y : M) :
  polar Q (a • x) y = a * polar Q x y :=
Q.polar_smul_left' a x y

@[simp]
lemma polar_neg_left (x y : M) :
  polar Q (-x) y = -polar Q x y :=
by rw [←neg_one_smul R x, polar_smul_left, neg_one_mul]

@[simp]
lemma polar_sub_left (x x' y : M) :
  polar Q (x - x') y = polar Q x y - polar Q x' y :=
by rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_left, polar_neg_left]

@[simp]
lemma polar_zero_right (y : M) : polar Q y 0 = 0 :=
by simp [polar]

@[simp]
lemma polar_add_right (x y y' : M) :
  polar Q x (y + y') = polar Q x y + polar Q x y' :=
Q.polar_add_right' x y y'

@[simp]
lemma polar_smul_right (a : R) (x y : M) :
  polar Q x (a • y) = a * polar Q x y :=
Q.polar_smul_right' a x y

@[simp]
lemma polar_neg_right (x y : M) :
  polar Q x (-y) = -polar Q x y :=
by rw [←neg_one_smul R y, polar_smul_right, neg_one_mul]

@[simp]
lemma polar_sub_right (x y y' : M) :
  polar Q x (y - y') = polar Q x y - polar Q x y' :=
by rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_right, polar_neg_right]

@[simp]
lemma polar_self (x : M) : polar Q x x = 2 * Q x :=
begin
  rw [polar, map_add_self, sub_sub, sub_eq_iff_eq_add, ←two_mul, ←two_mul, ←mul_assoc],
  norm_num
end

section of_tower

variables [comm_semiring S] [algebra S R] [module S M] [is_scalar_tower S R M]

@[simp]
lemma polar_smul_left_of_tower (a : S) (x y : M) :
  polar Q (a • x) y = a • polar Q x y :=
by rw [←is_scalar_tower.algebra_map_smul R a x, polar_smul_left, algebra.smul_def]

@[simp]
lemma polar_smul_right_of_tower (a : S) (x y : M) :
  polar Q x (a • y) = a • polar Q x y :=
by rw [←is_scalar_tower.algebra_map_smul R a y, polar_smul_right, algebra.smul_def]

end of_tower

variable {Q' : quadratic_form R M}
@[ext] lemma ext (H : ∀ (x : M), Q x = Q' x) : Q = Q' :=
by { cases Q, cases Q', congr, funext, apply H }

instance : has_zero (quadratic_form R M) :=
⟨ { to_fun := λ x, 0,
    to_fun_smul := λ a x, by simp,
    polar_add_left' := λ x x' y, by simp [polar],
    polar_smul_left' := λ a x y, by simp [polar],
    polar_add_right' := λ x y y', by simp [polar],
    polar_smul_right' := λ a x y, by simp [polar] } ⟩

@[simp] lemma coe_fn_zero : ⇑(0 : quadratic_form R M) = 0 := rfl

@[simp] lemma zero_apply (x : M) : (0 : quadratic_form R M) x = 0 := rfl

instance : inhabited (quadratic_form R M) := ⟨0⟩

instance : has_add (quadratic_form R M) :=
⟨ λ Q Q',
  { to_fun := Q + Q',
    to_fun_smul := λ a x,
      by simp only [pi.add_apply, map_smul, mul_add],
    polar_add_left' := λ x x' y,
      by simp only [polar_add, polar_add_left, add_assoc, add_left_comm],
    polar_smul_left' := λ a x y,
      by simp only [polar_add, smul_eq_mul, mul_add, polar_smul_left],
    polar_add_right' := λ x y y',
      by simp only [polar_add, polar_add_right, add_assoc, add_left_comm],
    polar_smul_right' := λ a x y,
      by simp only [polar_add, smul_eq_mul, mul_add, polar_smul_right] } ⟩

@[simp] lemma coe_fn_add (Q Q' : quadratic_form R M) : ⇑(Q + Q') = Q + Q' := rfl

@[simp] lemma add_apply (Q Q' : quadratic_form R M) (x : M) : (Q + Q') x = Q x + Q' x := rfl

instance : has_neg (quadratic_form R M) :=
⟨ λ Q,
  { to_fun := -Q,
  to_fun_smul := λ a x,
    by simp only [pi.neg_apply, map_smul, mul_neg_eq_neg_mul_symm],
  polar_add_left' := λ x x' y,
    by simp only [polar_neg, polar_add_left, neg_add],
  polar_smul_left' := λ a x y,
    by simp only [polar_neg, polar_smul_left, mul_neg_eq_neg_mul_symm, smul_eq_mul],
  polar_add_right' := λ x y y',
    by simp only [polar_neg, polar_add_right, neg_add],
  polar_smul_right' := λ a x y,
    by simp only [polar_neg, polar_smul_right, mul_neg_eq_neg_mul_symm, smul_eq_mul] } ⟩

@[simp] lemma coe_fn_neg (Q : quadratic_form R M) : ⇑(-Q) = -Q := rfl

@[simp] lemma neg_apply (Q : quadratic_form R M) (x : M) : (-Q) x = -Q x := rfl

instance : add_comm_group (quadratic_form R M) :=
{ add := (+),
  zero := 0,
  neg := has_neg.neg,
  add_comm := λ Q Q', by { ext, simp only [add_apply, add_comm] },
  add_assoc := λ Q Q' Q'', by { ext, simp only [add_apply, add_assoc] },
  add_left_neg := λ Q, by { ext, simp only [add_apply, neg_apply, zero_apply, add_left_neg] },
  add_zero := λ Q, by { ext, simp only [zero_apply, add_apply, add_zero] },
  zero_add := λ Q, by { ext, simp only [zero_apply, add_apply, zero_add] } }

@[simp] lemma coe_fn_sub (Q Q' : quadratic_form R M) : ⇑(Q - Q') = Q - Q' :=
by simp [sub_eq_add_neg]

@[simp] lemma sub_apply (Q Q' : quadratic_form R M) (x : M) : (Q - Q') x = Q x - Q' x :=
by simp [sub_eq_add_neg]

/-- `@coe_fn (quadratic_form R M)` as an `add_monoid_hom`.

This API mirrors `add_monoid_hom.coe_fn`. -/
@[simps apply]
def coe_fn_add_monoid_hom : quadratic_form R M →+ (M → R) :=
{ to_fun := coe_fn, map_zero' := coe_fn_zero, map_add' := coe_fn_add }

/-- Evaluation on a particular element of the module `M` is an additive map over quadratic forms. -/
@[simps apply]
def eval_add_monoid_hom (m : M) : quadratic_form R M →+ R :=
(pi.eval_add_monoid_hom _ m).comp coe_fn_add_monoid_hom

section sum

open_locale big_operators

@[simp] lemma coe_fn_sum {ι : Type*} (Q : ι → quadratic_form R M) (s : finset ι) :
  ⇑(∑ i in s, Q i) = ∑ i in s, Q i :=
(coe_fn_add_monoid_hom : _ →+ (M → R)).map_sum Q s

@[simp] lemma sum_apply {ι : Type*} (Q : ι → quadratic_form R M) (s : finset ι) (x : M) :
  (∑ i in s, Q i) x = ∑ i in s, Q i x :=
(eval_add_monoid_hom x : _ →+ R).map_sum Q s

end sum

section has_scalar

variables [monoid S] [distrib_mul_action S R] [smul_comm_class S R R]

/-- `quadratic_form R M` inherits the scalar action from any algebra over `R`.

When `R` is commutative, this provides an `R`-action via `algebra.id`. -/
instance : has_scalar S (quadratic_form R M) :=
⟨ λ a Q,
  { to_fun := a • Q,
    to_fun_smul := λ b x, by rw [pi.smul_apply, map_smul, pi.smul_apply, mul_smul_comm],
    polar_add_left' := λ x x' y, by simp only [polar_smul, polar_add_left, smul_add],
    polar_smul_left' := λ b x y, begin
      simp only [polar_smul, polar_smul_left, ←mul_smul_comm, smul_eq_mul],
    end,
    polar_add_right' := λ x y y', by simp only [polar_smul, polar_add_right, smul_add],
    polar_smul_right' := λ b x y, begin
      simp only [polar_smul, polar_smul_right, ←mul_smul_comm, smul_eq_mul],
    end } ⟩

@[simp] lemma coe_fn_smul (a : S) (Q : quadratic_form R M) : ⇑(a • Q) = a • Q := rfl

@[simp] lemma smul_apply (a : S) (Q : quadratic_form R M) (x : M) :
  (a • Q) x = a • Q x := rfl

instance : distrib_mul_action S (quadratic_form R M) :=
{ mul_smul := λ a b Q, ext (λ x, by simp only [smul_apply, mul_smul]),
  one_smul := λ Q, ext (λ x, by simp),
  smul_add := λ a Q Q', by { ext, simp only [add_apply, smul_apply, smul_add] },
  smul_zero := λ a, by { ext, simp only [zero_apply, smul_apply, smul_zero] }, }

end has_scalar

section module

instance [semiring S] [module S R] [smul_comm_class S R R] : module S (quadratic_form R M) :=
{ zero_smul := λ Q, by { ext, simp only [zero_apply, smul_apply, zero_smul] },
  add_smul := λ a b Q, by { ext, simp only [add_apply, smul_apply, add_smul] } }

end module

section comp

variables {N : Type v} [add_comm_group N] [module R N]

/-- Compose the quadratic form with a linear function. -/
def comp (Q : quadratic_form R N) (f : M →ₗ[R] N) :
  quadratic_form R M :=
{ to_fun := λ x, Q (f x),
  to_fun_smul := λ a x, by simp only [map_smul, f.map_smul],
  polar_add_left' := λ x x' y,
    by convert polar_add_left (f x) (f x') (f y) using 1;
      simp only [polar, f.map_add],
  polar_smul_left' := λ a x y,
    by convert polar_smul_left a (f x) (f y) using 1;
      simp only [polar, f.map_smul, f.map_add, smul_eq_mul],
  polar_add_right' := λ x y y',
    by convert polar_add_right (f x) (f y) (f y') using 1;
      simp only [polar, f.map_add],
  polar_smul_right' := λ a x y,
    by convert polar_smul_right a (f x) (f y) using 1;
      simp only [polar, f.map_smul, f.map_add, smul_eq_mul] }

@[simp] lemma comp_apply (Q : quadratic_form R N) (f : M →ₗ[R] N) (x : M) :
  (Q.comp f) x = Q (f x) := rfl

end comp

section comm_ring

/-- Create a quadratic form in a commutative ring by proving only one side of the bilinearity. -/
def mk_left (f : M → R₁)
  (to_fun_smul : ∀ a x, f (a • x) = a * a * f x)
  (polar_add_left : ∀ x x' y, polar f (x + x') y = polar f x y + polar f x' y)
  (polar_smul_left : ∀ a x y, polar f (a • x) y = a * polar f x y) :
  quadratic_form R₁ M :=
{ to_fun := f,
  to_fun_smul := to_fun_smul,
  polar_add_left' := polar_add_left,
  polar_smul_left' := polar_smul_left,
  polar_add_right' :=
    λ x y y', by rw [polar_comm, polar_add_left, polar_comm f y x, polar_comm f y' x],
  polar_smul_right' :=
    λ a x y, by rw [polar_comm, polar_smul_left, polar_comm f y x, smul_eq_mul] }

/-- The product of linear forms is a quadratic form. -/
def lin_mul_lin (f g : M →ₗ[R₁] R₁) : quadratic_form R₁ M :=
mk_left (f * g)
  (λ a x, by { simp, ring })
  (λ x x' y, by { simp [polar], ring })
  (λ a x y, by { simp [polar], ring })

@[simp]
lemma lin_mul_lin_apply (f g : M →ₗ[R₁] R₁) (x) : lin_mul_lin f g x = f x * g x := rfl

@[simp]
lemma add_lin_mul_lin (f g h : M →ₗ[R₁] R₁) :
  lin_mul_lin (f + g) h = lin_mul_lin f h + lin_mul_lin g h :=
ext (λ x, add_mul _ _ _)

@[simp]
lemma lin_mul_lin_add (f g h : M →ₗ[R₁] R₁) :
  lin_mul_lin f (g + h) = lin_mul_lin f g + lin_mul_lin f h :=
ext (λ x, mul_add _ _ _)

variables {N : Type v} [add_comm_group N] [module R₁ N]

@[simp]
lemma lin_mul_lin_comp (f g : M →ₗ[R₁] R₁) (h : N →ₗ[R₁] M) :
  (lin_mul_lin f g).comp h = lin_mul_lin (f.comp h) (g.comp h) :=
rfl

variables {n : Type*}

/-- `proj i j` is the quadratic form mapping the vector `x : n → R₁` to `x i * x j` -/
def proj (i j : n) : quadratic_form R₁ (n → R₁) :=
lin_mul_lin (@linear_map.proj _ _ _ (λ _, R₁) _ _ i) (@linear_map.proj _ _ _ (λ _, R₁) _ _ j)

@[simp]
lemma proj_apply (i j : n) (x : n → R₁) : proj i j x = x i * x j := rfl

end comm_ring

end quadratic_form

/-!
### Associated bilinear forms

Over a commutative ring with an inverse of 2, the theory of quadratic forms is
basically identical to that of symmetric bilinear forms. The map from quadratic
forms to bilinear forms giving this identification is called the `associated`
quadratic form.
-/

variables {B : bilin_form R M}

namespace bilin_form
open quadratic_form

lemma polar_to_quadratic_form (x y : M) : polar (λ x, B x x) x y = B x y + B y x :=
by simp [polar, add_left, add_right, sub_eq_add_neg _ (B y y), add_comm (B y x) _, add_assoc]

/-- A bilinear form gives a quadratic form by applying the argument twice. -/
def to_quadratic_form (B : bilin_form R M) : quadratic_form R M :=
⟨ λ x, B x x,
  λ a x, by simp [smul_left, smul_right, mul_assoc],
  λ x x' y, by simp [polar_to_quadratic_form, add_left, add_right, add_left_comm, add_assoc],
  λ a x y, by simp [polar_to_quadratic_form, smul_left, smul_right, mul_add],
  λ x y y', by simp [polar_to_quadratic_form, add_left, add_right, add_left_comm, add_assoc],
  λ a x y, by simp [polar_to_quadratic_form, smul_left, smul_right, mul_add] ⟩

@[simp] lemma to_quadratic_form_apply (B : bilin_form R M) (x : M) :
  B.to_quadratic_form x = B x x :=
rfl

end bilin_form

namespace quadratic_form
open bilin_form sym_bilin_form

section associated_hom
variables (S) [comm_semiring S] [algebra S R]
variables [invertible (2 : R)] {B₁ : bilin_form R M}

/-- `associated_hom` is the map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form.  As provided here, this has the structure of an `S`-linear map
where `S` is a commutative subring of `R`.

Over a commutative ring, use `associated`, which gives an `R`-linear map.  Over a general ring with
no nontrivial distinguished commutative subring, use `associated'`, which gives an additive
homomorphism (or more precisely a `ℤ`-linear map.) -/
def associated_hom : quadratic_form R M →ₗ[S] bilin_form R M :=
{ to_fun := λ Q,
  { bilin := λ x y, ⅟2 * polar Q x y,
    bilin_add_left := λ x y z, by rw [← mul_add, polar_add_left],
    bilin_smul_left := λ x y z, begin
      have htwo : x * ⅟2 = ⅟2 * x := (commute.one_right x).bit0_right.inv_of_right,
      simp [polar_smul_left, ← mul_assoc, htwo]
    end,
    bilin_add_right := λ x y z, by rw [← mul_add, polar_add_right],
    bilin_smul_right := λ x y z, begin
      have htwo : x * ⅟2 = ⅟2 * x := (commute.one_right x).bit0_right.inv_of_right,
      simp [polar_smul_left, ← mul_assoc, htwo]
    end },
  map_add' := λ Q Q', by { ext, simp [bilin_form.add_apply, polar_add, mul_add] },
  map_smul' := λ s Q, by { ext, simp [polar_smul, algebra.mul_smul_comm] } }

variables {Q : quadratic_form R M} {S}

@[simp] lemma associated_apply (x y : M) :
  associated_hom S Q x y = ⅟2 * (Q (x + y) - Q x - Q y) := rfl

lemma associated_is_sym : is_sym (associated_hom S Q) :=
λ x y, by simp only [associated_apply, add_comm, add_left_comm, sub_eq_add_neg]

@[simp] lemma associated_comp {N : Type v} [add_comm_group N] [module R N] (f : N →ₗ[R] M) :
  associated_hom S (Q.comp f) = (associated_hom S Q).comp f f :=
by { ext, simp }

lemma associated_to_quadratic_form (B : bilin_form R M) (x y : M) :
  associated_hom S B.to_quadratic_form x y = ⅟2 * (B x y + B y x) :=
by simp [associated_apply, ←polar_to_quadratic_form, polar]

lemma associated_left_inverse (h : is_sym B₁) :
  associated_hom S (B₁.to_quadratic_form) = B₁ :=
bilin_form.ext $ λ x y,
by rw [associated_to_quadratic_form, sym h x y, ←two_mul, ←mul_assoc, inv_of_mul_self, one_mul]

lemma associated_right_inverse : (associated_hom S Q).to_quadratic_form = Q :=
quadratic_form.ext $ λ x,
  calc (associated_hom S Q).to_quadratic_form x
      = ⅟2 * (Q x + Q x) : by simp [map_add_self, bit0, add_mul, add_assoc]
  ... = Q x : by rw [← two_mul (Q x), ←mul_assoc, inv_of_mul_self, one_mul]

lemma associated_eq_self_apply (x : M) : associated_hom S Q x x = Q x :=
begin
  rw [associated_apply, map_add_self],
  suffices : (⅟2) * (2 * Q x) = Q x,
  { convert this,
    simp only [bit0, add_mul, one_mul],
    abel },
  simp [← mul_assoc],
end

/-- `associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form. -/
abbreviation associated' : quadratic_form R M →ₗ[ℤ] bilin_form R M :=
associated_hom ℤ

/-- There exists a non-null vector with respect to any quadratic form `Q` whose associated
bilinear form is non-degenerate, i.e. there exists `x` such that `Q x ≠ 0`. -/
lemma exists_quadratic_form_neq_zero [nontrivial M]
  {Q : quadratic_form R M} (hB₁ : Q.associated'.nondegenerate) :
  ∃ x, Q x ≠ 0 :=
begin
  rw nondegenerate at hB₁,
  contrapose! hB₁,
  obtain ⟨x, hx⟩ := exists_ne (0 : M),
  refine ⟨x, λ y, _, hx⟩,
  have : Q = 0 := quadratic_form.ext hB₁,
  simp [this]
end

end associated_hom

section associated
variables [invertible (2 : R₁)]

-- Note:  When possible, rather than writing lemmas about `associated`, write a lemma applying to
-- the more general `associated_hom` and place it in the previous section.

/-- `associated` is the linear map that sends a quadratic form over a commutative ring to its
associated symmetric bilinear form. -/
abbreviation associated : quadratic_form R₁ M →ₗ[R₁] bilin_form R₁ M :=
associated_hom R₁

@[simp] lemma associated_lin_mul_lin (f g : M →ₗ[R₁] R₁) :
  (lin_mul_lin f g).associated =
    ⅟(2 : R₁) • (bilin_form.lin_mul_lin f g + bilin_form.lin_mul_lin g f) :=
by { ext, simp [bilin_form.add_apply, bilin_form.smul_apply], ring }

end associated

section anisotropic

/-- An anisotropic quadratic form is zero only on zero vectors. -/
def anisotropic (Q : quadratic_form R M) : Prop := ∀ x, Q x = 0 → x = 0

lemma not_anisotropic_iff_exists (Q : quadratic_form R M) :
  ¬anisotropic Q ↔ ∃ x ≠ 0, Q x = 0 :=
by simp only [anisotropic, not_forall, exists_prop, and_comm]

/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
lemma nondegenerate_of_anisotropic [invertible (2 : R)] (Q : quadratic_form R M)
  (hB : Q.anisotropic) : Q.associated'.nondegenerate :=
begin
  intros x hx,
  refine hB _ _,
  rw ← hx x,
  exact (associated_eq_self_apply x).symm,
end

end anisotropic

section pos_def

variables {R₂ : Type u} [ordered_ring R₂] [module R₂ M] {Q₂ : quadratic_form R₂ M}

/-- A positive definite quadratic form is positive on nonzero vectors. -/
def pos_def (Q₂ : quadratic_form R₂ M) : Prop := ∀ x ≠ 0, 0 < Q₂ x

lemma pos_def.smul {R} [linear_ordered_comm_ring R] [module R M]
  {Q : quadratic_form R M} (h : pos_def Q) {a : R} (a_pos : 0 < a) : pos_def (a • Q) :=
λ x hx, mul_pos a_pos (h x hx)

variables {n : Type*}

lemma pos_def.add (Q Q' : quadratic_form R₂ M) (hQ : pos_def Q) (hQ' : pos_def Q') :
  pos_def (Q + Q') :=
λ x hx, add_pos (hQ x hx) (hQ' x hx)

lemma lin_mul_lin_self_pos_def {R} [linear_ordered_comm_ring R] [module R M]
  (f : M →ₗ[R] R) (hf : linear_map.ker f = ⊥) :
  pos_def (lin_mul_lin f f) :=
λ x hx, mul_self_pos (λ h, hx (linear_map.ker_eq_bot.mp hf (by rw [h, linear_map.map_zero])))

end pos_def
end quadratic_form

section
/-!
### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/

variables {n : Type w} [fintype n] [decidable_eq n]

/-- `M.to_quadratic_form` is the map `λ x, col x ⬝ M ⬝ row x` as a quadratic form. -/
def matrix.to_quadratic_form' (M : matrix n n R₁) :
  quadratic_form R₁ (n → R₁) :=
M.to_bilin'.to_quadratic_form

variables [invertible (2 : R₁)]

/-- A matrix representation of the quadratic form. -/
def quadratic_form.to_matrix' (Q : quadratic_form R₁ (n → R₁)) : matrix n n R₁ :=
Q.associated.to_matrix'

open quadratic_form
lemma quadratic_form.to_matrix'_smul (a : R₁) (Q : quadratic_form R₁ (n → R₁)) :
  (a • Q).to_matrix' = a • Q.to_matrix' :=
by simp only [to_matrix', linear_equiv.map_smul, linear_map.map_smul]

end

namespace quadratic_form

variables {n : Type w} [fintype n]
variables [decidable_eq n] [invertible (2 : R₁)]
variables {m : Type w} [decidable_eq m] [fintype m]
open_locale matrix

@[simp]
lemma to_matrix'_comp (Q : quadratic_form R₁ (m → R₁)) (f : (n → R₁) →ₗ[R₁] (m → R₁)) :
  (Q.comp f).to_matrix' = f.to_matrix'ᵀ ⬝ Q.to_matrix' ⬝ f.to_matrix' :=
by { ext, simp [to_matrix', bilin_form.to_matrix'_comp] }

section discriminant
variables {Q : quadratic_form R₁ (n → R₁)}

/-- The discriminant of a quadratic form generalizes the discriminant of a quadratic polynomial. -/
def discr (Q : quadratic_form R₁ (n → R₁)) : R₁ := Q.to_matrix'.det

lemma discr_smul (a : R₁) : (a • Q).discr = a ^ fintype.card n * Q.discr :=
by simp only [discr, to_matrix'_smul, matrix.det_smul]

lemma discr_comp (f : (n → R₁) →ₗ[R₁] (n → R₁)) :
  (Q.comp f).discr = f.to_matrix'.det * f.to_matrix'.det * Q.discr :=
by simp [discr, mul_left_comm, mul_comm]

end discriminant

end quadratic_form

namespace quadratic_form

variables {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variables [add_comm_group M₁] [add_comm_group M₂] [add_comm_group M₃]
variables [module R M₁] [module R M₂] [module R M₃]

/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear equivalence between `M₁` and `M₂` that commutes with the quadratic forms. -/
@[nolint has_inhabited_instance] structure isometry
  (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) extends M₁ ≃ₗ[R] M₂ :=
(map_app' : ∀ m, Q₂ (to_fun m) = Q₁ m)

/-- Two quadratic forms over a ring `R` are equivalent
if there exists an isometry between them:
a linear equivalence that transforms one quadratic form into the other. -/
def equivalent (Q₁ : quadratic_form R M₁) (Q₂ : quadratic_form R M₂) := nonempty (Q₁.isometry Q₂)

namespace isometry

variables {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} {Q₃ : quadratic_form R M₃}

instance : has_coe (Q₁.isometry Q₂) (M₁ ≃ₗ[R] M₂) := ⟨isometry.to_linear_equiv⟩

instance : has_coe_to_fun (Q₁.isometry Q₂) :=
{ F := λ _, M₁ → M₂, coe := λ f, ⇑(f : M₁ ≃ₗ[R] M₂) }

@[simp] lemma map_app (f : Q₁.isometry Q₂) (m : M₁) : Q₂ (f m) = Q₁ m := f.map_app' m

/-- The identity isometry from a quadratic form to itself. -/
@[refl]
def refl (Q : quadratic_form R M) : Q.isometry Q :=
{ map_app' := λ m, rfl,
  .. linear_equiv.refl R M }

/-- The inverse isometry of an isometry between two quadratic forms. -/
@[symm]
def symm (f : Q₁.isometry Q₂) : Q₂.isometry Q₁ :=
{ map_app' := by { intro m, rw ← f.map_app, congr, exact f.to_linear_equiv.apply_symm_apply m },
  .. (f : M₁ ≃ₗ[R] M₂).symm }

/-- The composition of two isometries between quadratic forms. -/
@[trans]
def trans (f : Q₁.isometry Q₂) (g : Q₂.isometry Q₃) : Q₁.isometry Q₃ :=
{ map_app' := by { intro m, rw [← f.map_app, ← g.map_app], refl },
  .. (f : M₁ ≃ₗ[R] M₂).trans (g : M₂ ≃ₗ[R] M₃) }

end isometry

namespace equivalent

variables {Q₁ : quadratic_form R M₁} {Q₂ : quadratic_form R M₂} {Q₃ : quadratic_form R M₃}

@[refl]
lemma refl (Q : quadratic_form R M) : Q.equivalent Q := ⟨isometry.refl Q⟩

@[symm]
lemma symm (h : Q₁.equivalent Q₂) : Q₂.equivalent Q₁ := h.elim $ λ f, ⟨f.symm⟩

@[trans]
lemma trans (h : Q₁.equivalent Q₂) (h' : Q₂.equivalent Q₃) : Q₁.equivalent Q₃ :=
h'.elim $ h.elim $ λ f g, ⟨f.trans g⟩

end equivalent

end quadratic_form

namespace bilin_form

/-- A bilinear form is nondegenerate if the quadratic form it is associated with is anisotropic. -/
lemma nondegenerate_of_anisotropic
  {B : bilin_form R M} (hB : B.to_quadratic_form.anisotropic) : B.nondegenerate :=
λ x hx, hB _ (hx x)

/-- There exists a non-null vector with respect to any symmetric, nondegenerate bilinear form `B`
on a nontrivial module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`. -/
lemma exists_bilin_form_self_neq_zero [htwo : invertible (2 : R)] [nontrivial M]
  {B : bilin_form R M} (hB₁ : B.nondegenerate) (hB₂ : sym_bilin_form.is_sym B) :
  ∃ x, ¬ B.is_ortho x x :=
begin
  have : B.to_quadratic_form.associated'.nondegenerate,
  { simpa [quadratic_form.associated_left_inverse hB₂] using hB₁ },
  obtain ⟨x, hx⟩ := quadratic_form.exists_quadratic_form_neq_zero this,
  refine ⟨x, λ h, hx (B.to_quadratic_form_apply x ▸ h)⟩,
end

open finite_dimensional

variables {V : Type u} {K : Type v} [field K] [add_comm_group V] [module K V]
variable [finite_dimensional K V]

-- We start proving that symmetric nondegenerate bilinear forms are diagonalisable, or equivalently
-- there exists a orthogonal basis with respect to any symmetric nondegenerate bilinear form.

lemma exists_orthogonal_basis' [hK : invertible (2 : K)]
  {B : bilin_form K V} (hB₁ : B.nondegenerate) (hB₂ : sym_bilin_form.is_sym B) :
  ∃ (v : basis (fin (finrank K V)) K V),
    B.is_Ortho v ∧ ∀ i, B (v i) (v i) ≠ 0 :=
begin
  tactic.unfreeze_local_instances,
  induction hd : finrank K V with d ih generalizing V,
  { exact ⟨basis_of_finrank_zero hd, λ _ _ _, zero_left _, fin.elim0⟩ },
  haveI := finrank_pos_iff.1 (hd.symm ▸ nat.succ_pos d : 0 < finrank K V),
  cases exists_bilin_form_self_neq_zero hB₁ hB₂ with x hx,
  have hd' := hd,
  rw [← submodule.finrank_add_eq_of_is_compl
        (is_compl_span_singleton_orthogonal hx).symm,
      finrank_span_singleton (ne_zero_of_not_is_ortho_self x hx)] at hd,
  rcases @ih (B.orthogonal $ K ∙ x) _ _ _
    (B.restrict _) (B.restrict_orthogonal_span_singleton_nondegenerate hB₁ hB₂ hx)
    (B.restrict_sym hB₂ _) (nat.succ.inj hd) with ⟨v', hv₁, hv₃⟩,

  set v := (λ (i : fin _), if h : i = 0 then x else coe (v' (i.pred h))) with v_def,
  have : ∀ i j (hij : i ≠ j), B.is_ortho (v i) (v j),
  { intros i j hij,
    simp only [v_def],
    split_ifs with hi hj hj,
    { have : i = j := hi.trans hj.symm, contradiction },
    { exact (v' (j.pred hj)).2 _ (submodule.mem_span_singleton_self x) },
    { rw [is_ortho, hB₂],
      exact (v' (i.pred hi)).2 _ (submodule.mem_span_singleton_self x) },
    { exact hv₁ (j.pred hj) (i.pred hi) (by simpa using hij.symm) } },

  refine ⟨@basis_of_linear_independent_of_card_eq_finrank _ _ _ _ _ _ _ _
      v
      (@linear_independent_of_is_Ortho _ _ _ _ _ _ B v (λ i j hij, this j i hij.symm) _)
      (by rw [hd', fintype.card_fin]), _, _⟩,
  { intro i,
    simp only [v_def],
    split_ifs with hi,
    { exact hx },
    { exact hv₃ (i.pred hi) } },
  { intros i j hij,
    simp only [v_def, basis_of_linear_independent_of_card_eq_finrank, basis.mk_apply],
    exact this j i hij.symm },
  { intro i,
    simp only [v_def, basis_of_linear_independent_of_card_eq_finrank, basis.mk_apply],
    split_ifs with hi,
    { exact hx },
    { exact hv₃ (i.pred hi) } }
end .

/-- Given a nondegenerate symmetric bilinear form `B` on some vector space `V` over the
  field `K` with invertible `2`, there exists an orthogonal basis with respect to `B`. -/
theorem exists_orthogonal_basis [hK : invertible (2 : K)]
  {B : bilin_form K V} (hB₁ : B.nondegenerate) (hB₂ : sym_bilin_form.is_sym B) :
  ∃ v : basis (fin (finrank K V)) K V, B.is_Ortho v :=
let ⟨v, hv₁, _⟩ := exists_orthogonal_basis' hB₁ hB₂ in ⟨v, hv₁⟩

end bilin_form

namespace quadratic_form

open_locale big_operators

open finset bilin_form

variables {M₁ : Type*} [add_comm_group M₁] [module R M₁]
variables {ι : Type*} [fintype ι] {v : basis ι R M}

/-- A quadratic form composed with a `linear_equiv` is isometric to itself. -/
def isometry_of_comp_linear_equiv (Q : quadratic_form R M) (f : M₁ ≃ₗ[R] M) :
  Q.isometry (Q.comp (f : M₁ →ₗ[R] M)) :=
{ map_app' :=
  begin
    intro,
    simp only [comp_apply, linear_equiv.coe_coe, linear_equiv.to_fun_eq_coe,
               linear_equiv.apply_symm_apply, f.apply_symm_apply],
  end,
  .. f.symm }

/-- Given a quadratic form `Q` and a basis, `basis_repr` is the basis representation of `Q`. -/
noncomputable def basis_repr (Q : quadratic_form R M) (v : basis ι R M) :
  quadratic_form R (ι → R) :=
Q.comp v.equiv_fun.symm

@[simp]
lemma basis_repr_apply (Q : quadratic_form R M) (w : ι → R) :
  Q.basis_repr v w = Q (∑ i : ι, w i • v i) :=
by { rw ← v.equiv_fun_symm_apply, refl }

/-- A quadratic form is isometric to its bases representations. -/
noncomputable def isometry_basis_repr (Q : quadratic_form R M) (v : basis ι R M):
  isometry Q (Q.basis_repr v) :=
isometry_of_comp_linear_equiv Q v.equiv_fun.symm

lemma isometry_of_is_Ortho_apply [invertible (2 : R₁)]
  (Q : quadratic_form R₁ M) (v : basis ι R₁ M)
  (hv₂ : (associated Q).is_Ortho v) (w : ι → R₁) :
  Q.basis_repr v w = ∑ i : ι, associated Q (v i) (v i) * (w i * w i) :=
begin
  rw [basis_repr_apply, ← @associated_eq_self_apply R₁, sum_left],
  refine sum_congr rfl (λ j hj, _),
  rw [sum_right, sum_eq_single j],
  { rw [smul_left, smul_right], ring },
  { intros i _ hij,
    rw [smul_left, smul_right,
        show (associated_hom R₁) Q (v j) (v i) = 0, by exact hv₂ i j hij,
        mul_zero, mul_zero] },
  { contradiction }
end

section

variable (R₁)

/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R₁` or
`[algebra S R₁]`, although this is stated more generally. -/
def weighted_sum_squares [monoid S] [distrib_mul_action S R₁] [smul_comm_class S R₁ R₁]
  (w : ι → S) : quadratic_form R₁ (ι → R₁) :=
∑ i : ι, w i • proj i i

end

@[simp]
lemma weighted_sum_squares_apply [monoid S] [distrib_mul_action S R₁] [smul_comm_class S R₁ R₁]
  (w : ι → S) (v : ι → R₁) :
  weighted_sum_squares R₁ w v = ∑ i : ι, w i • (v i * v i) :=
quadratic_form.sum_apply _ _ _

variables {V : Type*} {K : Type*} [field K] [invertible (2 : K)]
variables [add_comm_group V] [module K V] [finite_dimensional K V]

lemma equivalent_weighted_sum_squares_of_nondegenerate'
  (Q : quadratic_form K V) (hQ : (associated Q).nondegenerate) :
  ∃ w : fin (finite_dimensional.finrank K V) → units K,
    equivalent Q (weighted_sum_squares K w) :=
begin
  obtain ⟨v, hv₁, hv₂⟩ := exists_orthogonal_basis' hQ associated_is_sym,
  refine ⟨λ i, units.mk0 _ (hv₂ i), nonempty.intro _⟩,
  convert Q.isometry_basis_repr v,
  ext w,
  rw [isometry_of_is_Ortho_apply Q v hv₁, weighted_sum_squares_apply],
  refl
end

section complex

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
noncomputable def isometry_sum_squares [decidable_eq ι] (w : ι → units ℂ) :
  isometry (weighted_sum_squares ℂ w) (weighted_sum_squares ℂ (1 : ι → ℂ)) :=
begin
  have hw' : ∀ i : ι, (w i : ℂ) ^ - (1 / 2 : ℂ) ≠ 0,
  { intros i hi,
    exact (w i).ne_zero ((complex.cpow_eq_zero_iff _ _).1 hi).1 },
  convert (weighted_sum_squares ℂ w).isometry_basis_repr
    ((pi.basis_fun ℂ ι).units_smul (λ i, (is_unit_iff_ne_zero.2 $ hw' i).unit)),
  ext1 v,
  erw [basis_repr_apply, weighted_sum_squares_apply, weighted_sum_squares_apply],
  refine sum_congr rfl (λ j hj, _),
  have hsum : (∑ (i : ι), v i • ((is_unit_iff_ne_zero.2 $ hw' i).unit : ℂ) •
    (pi.basis_fun ℂ ι) i) j = v j • w j ^ - (1 / 2 : ℂ),
  { rw [finset.sum_apply, sum_eq_single j, pi.basis_fun_apply, is_unit.unit_spec,
        linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, function.update_same,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one],
    intros i _ hij,
    rw [pi.basis_fun_apply, linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply,
        function.update_noteq hij.symm, pi.zero_apply, smul_eq_mul, smul_eq_mul,
        mul_zero, mul_zero],
    intro hj', exact false.elim (hj' hj) },
  simp_rw basis.units_smul_apply,
  erw [hsum, smul_eq_mul],
  suffices : 1 * v j * v j =  w j ^ - (1 / 2 : ℂ) * w j ^ - (1 / 2 : ℂ) * w j * v j * v j,
  { erw [pi.one_apply, ← mul_assoc, this, smul_eq_mul, smul_eq_mul], ring },
  rw [← complex.cpow_add _ _ (w j).ne_zero, show - (1 / 2 : ℂ) + - (1 / 2) = -1, by ring,
      complex.cpow_neg_one, inv_mul_cancel (w j).ne_zero],
end

/-- A nondegenerate quadratic form on the complex numbers is equivalent to
the sum of squares, i.e. `weighted_sum_squares` with weight `λ i : ι, 1`. -/
theorem equivalent_sum_squares {M : Type*} [add_comm_group M] [module ℂ M]
  [finite_dimensional ℂ M] (Q : quadratic_form ℂ M) (hQ : (associated Q).nondegenerate) :
  equivalent Q (weighted_sum_squares ℂ (1 : fin (finite_dimensional.finrank ℂ M) → ℂ)) :=
let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_of_nondegenerate' hQ in
  ⟨hw₁.trans (isometry_sum_squares w)⟩

end complex

section real

open real

/-- The isometry between a weighted sum of squares with weights `u` on the
(non-zero) real numbers and the weighted sum of squares with weights `sign ∘ u`. -/
noncomputable def isometry_sign_weighted_sum_squares
  [decidable_eq ι] (u : ι → units ℝ) :
  isometry (weighted_sum_squares ℝ u) (weighted_sum_squares ℝ (sign ∘ coe ∘ u)) :=
begin
  have hu' : ∀ i : ι, (sign (u i) * u i) ^ - (1 / 2 : ℝ) ≠ 0,
  { intro i, refine (ne_of_lt (real.rpow_pos_of_pos
      (sign_mul_pos_of_ne_zero _ $ units.ne_zero _) _)).symm},
  convert ((weighted_sum_squares ℝ u).isometry_basis_repr
    ((pi.basis_fun ℝ ι).units_smul (λ i, (is_unit_iff_ne_zero.2 $ hu' i).unit))),
  ext1 v,
  rw [basis_repr_apply, weighted_sum_squares_apply, weighted_sum_squares_apply],
  refine sum_congr rfl (λ j hj, _),
  have hsum : (∑ (i : ι), v i • ((is_unit_iff_ne_zero.2 $ hu' i).unit : ℝ) •
    (pi.basis_fun ℝ ι) i) j = v j • (sign (u j) * u j) ^ - (1 / 2 : ℝ),
  { rw [finset.sum_apply, sum_eq_single j, pi.basis_fun_apply, is_unit.unit_spec,
        linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply, function.update_same,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one],
    intros i _ hij,
    rw [pi.basis_fun_apply, linear_map.std_basis_apply, pi.smul_apply, pi.smul_apply,
        function.update_noteq hij.symm, pi.zero_apply, smul_eq_mul, smul_eq_mul,
        mul_zero, mul_zero],
    intro hj', exact false.elim (hj' hj) },
  simp_rw basis.units_smul_apply,
  erw [hsum, smul_eq_mul],
  suffices : (sign ∘ coe ∘ u) j * v j * v j = (sign (u j) * u j) ^ - (1 / 2 : ℝ) *
    (sign (u j) * u j) ^ - (1 / 2 : ℝ) * u j * v j * v j,
  { erw [← mul_assoc, this, smul_eq_mul, smul_eq_mul], ring },
  rw [← real.rpow_add (sign_mul_pos_of_ne_zero _ $ units.ne_zero _),
      show - (1 / 2 : ℝ) + - (1 / 2) = -1, by ring, real.rpow_neg_one, _root_.mul_inv',
      inv_sign, mul_assoc (sign (u j)) (u j)⁻¹,
      inv_mul_cancel (units.ne_zero _), mul_one],
  apply_instance
end

/-- Sylvester's law of inertia: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1. -/
theorem equivalent_one_neg_one_weighted_sum_squared
  {M : Type*} [add_comm_group M] [module ℝ M] [finite_dimensional ℝ M]
  (Q : quadratic_form ℝ M) (hQ : (associated Q).nondegenerate) :
  ∃ w : fin (finite_dimensional.finrank ℝ M) → ℝ,
  (∀ i, w i = -1 ∨ w i = 1) ∧ equivalent Q (weighted_sum_squares ℝ w) :=
let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weighted_sum_squares_of_nondegenerate' hQ in
  ⟨sign ∘ coe ∘ w,
   λ i, sign_apply_eq_of_ne_zero (w i) (w i).ne_zero,
   ⟨hw₁.trans (isometry_sign_weighted_sum_squares w)⟩⟩

end real

end quadratic_form
