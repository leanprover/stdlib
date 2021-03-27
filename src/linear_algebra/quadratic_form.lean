/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import algebra.invertible
import linear_algebra.bilinear_form
import linear_algebra.determinant
import linear_algebra.special_linear_group

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
⟨_, λ B, B.to_fun⟩

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

variables [comm_semiring S] [algebra S R] [semimodule S M] [is_scalar_tower S R M]

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

section has_scalar

variables [comm_semiring S] [algebra S R]

/-- `quadratic_form R M` inherits the scalar action from any algebra over `R`.

When `R` is commutative, this provides an `R`-action via `algebra.id`. -/
instance : has_scalar S (quadratic_form R M) :=
⟨ λ a Q,
  { to_fun := a • Q,
    to_fun_smul := λ b x, by rw [pi.smul_apply, map_smul, pi.smul_apply, algebra.mul_smul_comm],
    polar_add_left' := λ x x' y, by simp only [polar_smul, polar_add_left, smul_add],
    polar_smul_left' := λ b x y, begin
      simp only [polar_smul, polar_smul_left, ←algebra.mul_smul_comm, smul_eq_mul],
    end,
    polar_add_right' := λ x y y', by simp only [polar_smul, polar_add_right, smul_add],
    polar_smul_right' := λ b x y, begin
      simp only [polar_smul, polar_smul_right, ←algebra.mul_smul_comm, smul_eq_mul],
    end } ⟩

@[simp] lemma coe_fn_smul (a : S) (Q : quadratic_form R M) : ⇑(a • Q) = a • Q := rfl

@[simp] lemma smul_apply (a : S) (Q : quadratic_form R M) (x : M) :
  (a • Q) x = a • Q x := rfl

instance : semimodule S (quadratic_form R M) :=
{ mul_smul := λ a b Q, ext (λ x, by
    simp only [smul_apply, mul_left_comm, ←smul_eq_mul, smul_assoc]),
  one_smul := λ Q, ext (λ x, by simp),
  smul_add := λ a Q Q', by { ext, simp only [add_apply, smul_apply, smul_add] },
  smul_zero := λ a, by { ext, simp only [zero_apply, smul_apply, smul_zero] },
  zero_smul := λ Q, by { ext, simp only [zero_apply, smul_apply, zero_smul] },
  add_smul := λ a b Q, by { ext, simp only [add_apply, smul_apply, add_smul] } }

end has_scalar

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

namespace finsupp
variables {α : Type*}

/-- A collection of `bilin_form R M`, parametrized by two indices in `α` induces a quadratic form
on `α →₀ M`.  This can be thought of as an infinite-dimensional version of
`matrix.to_quadratic_form`.  For this construction to be well-behaved, we usually require an
additional symmetry hypothesis on the coefficients `A`. -/
noncomputable def to_quadratic_form (A : α → α → (bilin_form R M)) :
  quadratic_form R (α →₀ M) :=
(finsupp.to_bilin_form A).to_quadratic_form

@[simp] lemma to_quadratic_form_apply (A : α → α → (bilin_form R M)) (p : α →₀ M) :
  (finsupp.to_quadratic_form A) p = p.sum (λ i x, p.sum (λ j y, A i j x y)) :=
rfl

@[simp] lemma to_quadratic_form_polar (A : α → α → (bilin_form R M))
  (hA : ∀ i j x y, A i j x y = A j i y x) :
  (finsupp.to_quadratic_form A).polar = 2 • (finsupp.to_bilin_form A) :=
begin
  ext x y,
  convert bilin_form.polar_to_quadratic_form x y,
  simp only [pi.smul_apply],
  rw finsupp.is_sym_to_bilinear_form A hA,
  simp [bit0, add_smul]
end

@[simp] lemma to_quadratic_form_polar_apply (A : α → α → (bilin_form R M))
  (hA : ∀ i j x y, A i j x y = A j i y x) (p q : α →₀ M) :
  polar (finsupp.to_quadratic_form A) p q = 2 * (finsupp.to_bilin_form A) p q :=
by { rw [to_quadratic_form_polar A hA, bit0], simp [add_smul, two_mul] }

/-- The "Euclidean" quadratic form on `α →₀ R₁`:  the sum of the squares of the elements. -/
noncomputable def norm_sq [decidable_eq α] : quadratic_form R₁ (α →₀ R₁) :=
finsupp.to_quadratic_form
  (λ i j, if i = j then bilin_form.lin_mul_lin linear_map.id linear_map.id else 0)

@[simp] lemma norm_sq_apply [decidable_eq α] (p : α →₀ R₁) : norm_sq p = p.sum (λ i x, x ^ 2) :=
begin
  simp only [norm_sq, to_quadratic_form_apply],
  transitivity p.sum (λ i x, p.sum (λ j y, ite (i = j) (x * y) 0)),
  { congr,
    ext i x,
    congr,
    ext j y,
    split_ifs; simp },
  { apply finset.sum_congr rfl,
    intros i hi,
    simp only [mem_support_iff, ne.def, sum_ite_eq],
    rw if_pos,
    { rw pow_two },
    { simpa using hi } },
end

end finsupp

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

variables {V : Type u} {K : Type v} [field K] [add_comm_group V] [vector_space K V]
variable [finite_dimensional K V]

-- We start proving that symmetric nondegenerate bilinear forms are diagonalisable, or equivalently
-- there exists a orthogonal basis with respect to any symmetric nondegenerate bilinear form.

lemma exists_orthogonal_basis' [hK : invertible (2 : K)]
  {B : bilin_form K V} (hB₁ : B.nondegenerate) (hB₂ : sym_bilin_form.is_sym B) :
  ∃ v : fin (findim K V) → V,
    B.is_Ortho v ∧ is_basis K v ∧ ∀ i, B (v i) (v i) ≠ 0 :=
begin
  tactic.unfreeze_local_instances,
  induction hd : findim K V with d ih generalizing V,
  { exact ⟨λ _, 0, λ _ _ _, zero_left _, is_basis_of_findim_zero' hd, fin.elim0⟩ },
  { haveI := findim_pos_iff.1 (hd.symm ▸ nat.succ_pos d : 0 < findim K V),
    cases exists_bilin_form_self_neq_zero hB₁ hB₂ with x hx,
    { have hd' := hd,
      rw [← submodule.findim_add_eq_of_is_compl
            (is_compl_span_singleton_orthogonal hx).symm,
          findim_span_singleton (ne_zero_of_not_is_ortho_self x hx)] at hd,
      rcases @ih (B.orthogonal $ K ∙ x) _ _ _
        (B.restrict _) (B.restrict_orthogonal_span_singleton_nondegenerate hB₁ hB₂ hx)
        (B.restrict_sym hB₂ _) (nat.succ.inj hd) with ⟨v', hv₁, hv₂, hv₃⟩,
      refine ⟨λ i, if h : i ≠ 0 then coe (v' (i.pred h)) else x, λ i j hij, _, _, _⟩,
      { by_cases hi : i = 0,
        { subst i,
          simp only [eq_self_iff_true, not_true, ne.def, dif_neg,
            not_false_iff, dite_not],
          rw [dif_neg hij.symm, is_ortho, hB₂],
          exact (v' (j.pred hij.symm)).2 _ (submodule.mem_span_singleton_self x) },
        by_cases hj : j = 0,
        { subst j,
          simp only [eq_self_iff_true, not_true, ne.def, dif_neg,
            not_false_iff, dite_not],
          rw dif_neg hi,
          exact (v' (i.pred hi)).2 _ (submodule.mem_span_singleton_self x) },
        { simp_rw [dif_pos hi, dif_pos hj],
          rw [is_ortho, hB₂],
          exact hv₁ (j.pred hj) (i.pred hi) (by simpa using hij.symm) } },
      { refine is_basis_of_linear_independent_of_card_eq_findim
          (@linear_independent_of_is_Ortho _ _ _ _ _ _ B _ _ _)
          (by rw [hd', fintype.card_fin]),
        { intros i j hij,
          by_cases hi : i = 0,
          { subst hi,
            simp only [eq_self_iff_true, not_true, ne.def, dif_neg,
              not_false_iff, dite_not],
            rw [dif_neg hij.symm, is_ortho, hB₂],
            exact (v' (j.pred hij.symm)).2 _ (submodule.mem_span_singleton_self x) },
          by_cases hj : j = 0,
          { subst j,
            simp only [eq_self_iff_true, not_true, ne.def, dif_neg,
              not_false_iff, dite_not],
            rw dif_neg hi,
            exact (v' (i.pred hi)).2 _ (submodule.mem_span_singleton_self x) },
          { simp_rw [dif_pos hi, dif_pos hj],
            rw [is_ortho, hB₂],
            exact hv₁ (j.pred hj) (i.pred hi) (by simpa using hij.symm) } },
        { intro i,
          by_cases hi : i ≠ 0,
          { rw dif_pos hi,
            exact hv₃ (i.pred hi) },
          { rw dif_neg hi, exact hx } } },
      { intro i,
          by_cases hi : i ≠ 0,
          { rw dif_pos hi,
            exact hv₃ (i.pred hi) },
          { rw dif_neg hi, exact hx } } } }
end .

/-- Given a nondegenerate symmetric bilinear form `B` on some vector space `V` over the
  field `K` with invertible `2`, there exists an orthogonal basis with respect to `B`. -/
theorem exists_orthogonal_basis [hK : invertible (2 : K)]
  {B : bilin_form K V} (hB₁ : B.nondegenerate) (hB₂ : sym_bilin_form.is_sym B) :
  ∃ v : fin (findim K V) → V, B.is_Ortho v ∧ is_basis K v :=
let ⟨v, hv₁, hv₂, _⟩ := exists_orthogonal_basis' hB₁ hB₂ in ⟨v, hv₁, hv₂⟩

end bilin_form
