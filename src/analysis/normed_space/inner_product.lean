/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/

import linear_algebra.bilinear_form
import linear_algebra.sesquilinear_form
import analysis.special_functions.pow
import topology.metric_space.pi_Lp
import data.complex.is_R_or_C

/-!
# Inner Product Space

This file defines inner product spaces and proves its basic properties.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `is_R_or_C` typeclass.


## Main results

- We define the class `inner_product_space 𝕜 E` extending `normed_space 𝕜 E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `𝕜` is understood to be either `ℝ`
  or `ℂ`, through the `is_R_or_C` typeclass.
- We show that if `f i` is an inner product space for each `i`, then so is `Π i, f i`
- We define `euclidean_space 𝕜 n` to be `n → 𝕜` for any `fintype n`, and show that
  this an inner product space.
- Existence of orthogonal projection onto nonempty complete subspace:
  Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
  Then there exists a unique `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
  The point `v` is usually called the orthogonal projection of `u` onto `K`.

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `real_inner_product_space`, `complex_inner_product_space`,
which respectively introduce the plain notation `⟪·, ·⟫` for the the real and complex inner product.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## TODO

- Fix the section on the existence of minimizers and orthogonal projections to make sure that it
  also applies in the complex case.

## Tags

inner product space, norm

## References
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

noncomputable theory

open is_R_or_C real
open_locale big_operators classical

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]

/-- Syntactic typeclass for types endowed with an inner product -/
class has_inner (𝕜 E : Type*) := (inner : E → E → 𝕜)

export has_inner (inner)

notation `⟪`x`, `y`⟫_ℝ` := @inner ℝ _ _ x y
notation `⟪`x`, `y`⟫_ℂ` := @inner ℂ _ _ x y

section notations

localized "notation `⟪`x`, `y`⟫` := @inner ℝ _ _ x y" in real_inner_product_space
localized "notation `⟪`x`, `y`⟫` := @inner ℂ _ _ x y" in complex_inner_product_space

end notations

/--
An inner product space is a vector space with an additional operation called inner product.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that `∥x∥^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class inner_product_space (𝕜 : Type*) (E : Type*) [is_R_or_C 𝕜]
  extends normed_group E, normed_space 𝕜 E, has_inner 𝕜 E :=
(norm_sq_eq_inner : ∀ (x : E), ∥x∥^2 = re (inner x x))
(conj_sym  : ∀ x y, conj (inner y x) = inner x y)
(nonneg_im : ∀ x, im (inner x x) = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

/- This instance generates the type-class problem `inner_product_space ?m E` when looking for
   `normed_group E`. However, since `?m` can only ever be `ℝ` or `ℂ`, this should not cause
   problems. -/
attribute [nolint dangerous_instance] inner_product_space.to_normed_group

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`inner_product_space.core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `inner_product_space`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/

/-- A structure requiring that a scalar product is positive definite and symmetric, from which one
can construct an `inner_product_space` instance in `inner_product_space.of_core`. -/
@[nolint has_inhabited_instance]
structure inner_product_space.core
  (𝕜 : Type*) (F : Type*)
  [is_R_or_C 𝕜] [add_comm_group F] [semimodule 𝕜 F] :=
(inner     : F → F → 𝕜)
(conj_sym  : ∀ x y, conj (inner y x) = inner x y)
(nonneg_im : ∀ x, im (inner x x) = 0)
(nonneg_re : ∀ x, 0 ≤ re (inner x x))
(definite  : ∀ x, inner x x = 0 → x = 0)
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

/- We set `inner_product_space.core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] inner_product_space.core

namespace inner_product_space.of_core

variables [add_comm_group F] [semimodule 𝕜 F] [c : inner_product_space.core 𝕜 F]
include c

local notation `⟪`x`, `y`⟫` := @inner 𝕜 F _ x y
local notation `norm_sqK` := @is_R_or_C.norm_sq 𝕜 _
local notation `reK` := @is_R_or_C.re 𝕜 _
local notation `absK` := @is_R_or_C.abs 𝕜 _
local notation `ext_iff` := @is_R_or_C.ext_iff 𝕜 _
local postfix `†`:90 := @is_R_or_C.conj 𝕜 _

/-- Inner product defined by the `inner_product_space.core` structure. -/
def to_has_inner : has_inner 𝕜 F := { inner := c.inner }
local attribute [instance] to_has_inner

/-- The norm squared function for `inner_product_space.core` structure. -/
def norm_sq (x : F) := reK ⟪x, x⟫

local notation `norm_sqF` := @norm_sq 𝕜 F _ _ _ _

lemma inner_conj_sym (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ := c.conj_sym x y

lemma inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ := c.nonneg_re _

lemma inner_self_nonneg_im {x : F} : im ⟪x, x⟫ = 0 := c.nonneg_im _

lemma inner_self_im_zero {x : F} : im ⟪x, x⟫ = 0 := c.nonneg_im _

lemma inner_add_left {x y z : F} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
c.add_left _ _ _

lemma inner_add_right {x y z : F} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
by rw [←inner_conj_sym, inner_add_left, ring_hom.map_add]; simp only [inner_conj_sym]

lemma inner_norm_sq_eq_inner_self (x : F) : (norm_sqF x : 𝕜) = ⟪x, x⟫ :=
begin
  rw ext_iff,
  exact ⟨by simp only [of_real_re]; refl, by simp only [inner_self_nonneg_im, of_real_im]⟩
end

lemma inner_re_symm {x y : F} : re ⟪x, y⟫ = re ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_re]

lemma inner_im_symm {x y : F} : im ⟪x, y⟫ = -im ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_im]

lemma inner_smul_left {x y : F} {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
c.smul_left _ _ _

lemma inner_smul_right {x y : F} {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_smul_left]; simp only [conj_conj, inner_conj_sym, ring_hom.map_mul]

lemma inner_zero_left {x : F} : ⟪0, x⟫ = 0 :=
by rw [←zero_smul 𝕜 (0 : F), inner_smul_left]; simp only [zero_mul, ring_hom.map_zero]

lemma inner_zero_right {x : F} : ⟪x, 0⟫ = 0 :=
by rw [←inner_conj_sym, inner_zero_left]; simp only [ring_hom.map_zero]

lemma inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
iff.intro (c.definite _) (by { rintro rfl, exact inner_zero_left })

lemma inner_self_re_to_K {x : F} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
by norm_num [ext_iff, inner_self_nonneg_im]

lemma inner_abs_conj_sym {x y : F} : abs ⟪x, y⟫ = abs ⟪y, x⟫ :=
  by rw [←inner_conj_sym, abs_conj]

lemma inner_neg_left {x y : F} : ⟪-x, y⟫ = -⟪x, y⟫ :=
by { rw [← neg_one_smul 𝕜 x, inner_smul_left], simp }

lemma inner_neg_right {x y : F} : ⟪x, -y⟫ = -⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_neg_left]; simp only [ring_hom.map_neg, inner_conj_sym]

lemma inner_sub_left {x y z : F} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_left, inner_neg_left] }

lemma inner_sub_right {x y z : F} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_right, inner_neg_right] }

lemma inner_mul_conj_re_abs {x y : F} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
by { rw[←inner_conj_sym, mul_comm], exact re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `inner (x + y) (x + y)` -/
lemma inner_add_add_self {x y : F} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_add_left, inner_add_right]; ring

/- Expand `inner (x - y) (x - y)` -/
lemma inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_sub_left, inner_sub_right]; ring

/--
Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia.
We need this for the `core` structure to prove the triangle inequality below when
showing the core is a normed group.
-/
lemma inner_mul_inner_self_le (x y : F) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
begin
  by_cases hy : y = 0,
  { rw [hy], simp only [is_R_or_C.abs_zero, inner_zero_left, mul_zero, add_monoid_hom.map_zero] },
  { change y ≠ 0 at hy,
    have hy' : ⟪y, y⟫ ≠ 0 := λ h, by rw [inner_self_eq_zero] at h; exact hy h,
    set T := ⟪y, x⟫ / ⟪y, y⟫ with hT,
    have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_re_symm,
    have h₂ : im ⟪y, x⟫ = -im ⟪x, y⟫ := inner_im_symm,
    have h₃ : ⟪y, x⟫ * ⟪x, y⟫ * ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = ⟪y, x⟫ * ⟪x, y⟫ / ⟪y, y⟫,
    { rw [mul_div_assoc],
      have : ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = 1 / ⟪y, y⟫ :=
        by rw [div_mul_eq_div_mul_one_div, div_self hy', one_mul],
      rw [this, div_eq_mul_inv, one_mul, ←div_eq_mul_inv] },
    have h₄ : ⟪y, y⟫ = re ⟪y, y⟫ := by simp only [inner_self_re_to_K],
    have h₅ : re ⟪y, y⟫ > 0,
    { refine lt_of_le_of_ne inner_self_nonneg _,
      intro H,
      apply hy',
      rw ext_iff,
      exact ⟨by simp [H],by simp [inner_self_nonneg_im]⟩ },
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gt h₅,
    have hmain := calc
      0   ≤ re ⟪x - T • y, x - T • y⟫
                  : inner_self_nonneg
      ... = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫
                  : by simp [inner_sub_sub_self, inner_smul_left, inner_smul_right, h₁, h₂]
      ... = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫)
                  : by simp [inner_smul_left, inner_smul_right, mul_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫)
                  : by field_simp [-mul_re, inner_conj_sym, hT, conj_div, h₁, h₃]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫)
                  : by rw [div_mul_eq_mul_div_comm, ←mul_div_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / re ⟪y, y⟫)
                  : by conv_lhs { rw [h₄] }
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [div_re_of_real]
      ... = re ⟪x, x⟫ - abs (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [inner_mul_conj_re_abs]
      ... = re ⟪x, x⟫ - abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫
                  : by rw is_R_or_C.abs_mul,
    have hmain' : abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ ≤ re ⟪x, x⟫ := by linarith,
    have := (mul_le_mul_right h₅).mpr hmain',
    rwa [div_mul_cancel (abs ⟪x, y⟫ * abs ⟪y, x⟫) h₆] at this }
end

/-- Norm constructed from a `inner_product_space.core` structure, defined to be the square root
of the scalar product. -/
def to_has_norm : has_norm F :=
{ norm := λ x, sqrt (re ⟪x, x⟫) }

local attribute [instance] to_has_norm

lemma norm_eq_sqrt_inner (x : F) : ∥x∥ = sqrt (re ⟪x, x⟫) := rfl

lemma inner_self_eq_norm_square (x : F) : re ⟪x, x⟫ = ∥x∥ * ∥x∥ :=
by rw[norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
  sqrt_mul_self inner_self_nonneg]

lemma sqrt_norm_sq_eq_norm {x : F} : sqrt (norm_sqF x) = ∥x∥ := rfl

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : F) : abs ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ :=
nonneg_le_nonneg_of_squares_le (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
begin
  have H : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = re ⟪y, y⟫ * re ⟪x, x⟫,
  { simp only [inner_self_eq_norm_square], ring, },
  rw H,
  conv
  begin
    to_lhs, congr, rw[inner_abs_conj_sym],
  end,
  exact inner_mul_inner_self_le y x,
end

/-- Normed group structure constructed from an `inner_product_space.core` structure -/
def to_normed_group : normed_group F :=
normed_group.of_core F
{ norm_eq_zero_iff := assume x,
  begin
    split,
    { intro H,
      change sqrt (re ⟪x, x⟫) = 0 at H,
      rw [sqrt_eq_zero inner_self_nonneg] at H,
      apply (inner_self_eq_zero : ⟪x, x⟫ = 0 ↔ x = 0).mp,
      rw ext_iff,
      exact ⟨by simp [H], by simp [inner_self_im_zero]⟩ },
    { rintro rfl,
      change sqrt (re ⟪0, 0⟫) = 0,
      simp only [sqrt_zero, inner_zero_right, add_monoid_hom.map_zero] }
  end,
  triangle := assume x y,
  begin
    have h₁ : abs ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ := abs_inner_le_norm _ _,
    have h₂ : re ⟪x, y⟫ ≤ abs ⟪x, y⟫ := re_le_abs _,
    have h₃ : re ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ := by linarith,
    have h₄ : re ⟪y, x⟫ ≤ ∥x∥ * ∥y∥ := by rwa [←inner_conj_sym, conj_re],
    have : ∥x + y∥ * ∥x + y∥ ≤ (∥x∥ + ∥y∥) * (∥x∥ + ∥y∥),
    { simp [←inner_self_eq_norm_square, inner_add_add_self, add_mul, mul_add, mul_comm],
      linarith },
    exact nonneg_le_nonneg_of_squares_le (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
  end,
  norm_neg := λ x, by simp only [norm, inner_neg_left, neg_neg, inner_neg_right] }

local attribute [instance] to_normed_group

/-- Normed space structure constructed from a `inner_product_space.core` structure -/
def to_normed_space : normed_space 𝕜 F :=
{ norm_smul_le := assume r x,
  begin
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ←mul_assoc],
    rw [conj_mul_eq_norm_sq_left, of_real_mul_re, sqrt_mul, ←inner_norm_sq_eq_inner_self, of_real_re],
    { simp [sqrt_norm_sq_eq_norm, is_R_or_C.sqrt_norm_sq_eq_norm] },
    { exact norm_sq_nonneg r }
  end }

end inner_product_space.of_core

/-- Given a `inner_product_space.core` structure on a space, one can use it to turn
the space into an inner product space, constructing the norm out of the inner product -/
def inner_product_space.of_core [add_comm_group F] [semimodule 𝕜 F]
  (c : inner_product_space.core 𝕜 F) : inner_product_space 𝕜 F :=
begin
  letI : normed_group F := @inner_product_space.of_core.to_normed_group 𝕜 F _ _ _ c,
  letI : normed_space 𝕜 F := @inner_product_space.of_core.to_normed_space 𝕜 F _ _ _ c,
  exact { norm_sq_eq_inner := λ x,
    begin
      have h₁ : ∥x∥^2 = (sqrt (re (c.inner x x))) ^ 2 := rfl,
      have h₂ : 0 ≤ re (c.inner x x) := inner_product_space.of_core.inner_self_nonneg,
      simp [h₁, sqr_sqrt, h₂],
    end,
    ..c }
end

/-! ### Properties of inner product spaces -/

variables [inner_product_space 𝕜 E] [inner_product_space ℝ F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
local notation `IK` := @is_R_or_C.I 𝕜 _
local notation `absR` := _root_.abs
local notation `absK` := @is_R_or_C.abs 𝕜 _
local postfix `†`:90 := @is_R_or_C.conj 𝕜 _
local postfix `⋆`:90 := complex.conj

export inner_product_space (norm_sq_eq_inner)

section basic_properties

lemma inner_conj_sym (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ := inner_product_space.conj_sym _ _
lemma real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := inner_conj_sym x y

lemma inner_eq_zero_sym {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 :=
⟨λ h, by simp [←inner_conj_sym, h], λ h, by simp [←inner_conj_sym, h]⟩

lemma inner_self_nonneg_im {x : E} : im ⟪x, x⟫ = 0 := inner_product_space.nonneg_im _

lemma inner_self_im_zero {x : E} : im ⟪x, x⟫ = 0 := inner_product_space.nonneg_im _

lemma inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
inner_product_space.add_left _ _ _

lemma inner_add_right {x y z : E} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
begin
  rw [←inner_conj_sym, inner_add_left, ring_hom.map_add],
  conv_rhs { rw ←inner_conj_sym, conv { congr, skip, rw ←inner_conj_sym } }
end

lemma inner_re_symm {x y : E} : re ⟪x, y⟫ = re ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_re]

lemma inner_im_symm {x y : E} : im ⟪x, y⟫ = -im ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_im]

lemma inner_smul_left {x y : E} {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
inner_product_space.smul_left _ _ _
lemma real_inner_smul_left {x y : F} {r : ℝ} : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ := inner_smul_left

lemma inner_smul_right {x y : E} {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_smul_left, ring_hom.map_mul, conj_conj, inner_conj_sym]
lemma real_inner_smul_right {x y : F} {r : ℝ} : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ := inner_smul_right

/-- The inner product as a sesquilinear form. -/
def sesq_form_of_inner : sesq_form 𝕜 E conj_to_ring_equiv :=
{ sesq := λ x y, ⟪y, x⟫,    -- Note that sesquilinear forms are linear in the first argument
  sesq_add_left := λ x y z, inner_add_right,
  sesq_add_right := λ x y z, inner_add_left,
  sesq_smul_left := λ r x y, inner_smul_right,
  sesq_smul_right := λ r x y, inner_smul_left }

/-- The real inner product as a bilinear form. -/
def bilin_form_of_real_inner : bilin_form ℝ F :=
{ bilin := inner,
  bilin_add_left := λ x y z, inner_add_left,
  bilin_smul_left := λ a x y, inner_smul_left,
  bilin_add_right := λ x y z, inner_add_right,
  bilin_smul_right := λ a x y, inner_smul_right }

/-- An inner product with a sum on the left. -/
lemma sum_inner {ι : Type*} (s : finset ι) (f : ι → E) (x : E) :
  ⟪∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫ :=
sesq_form.map_sum_right (sesq_form_of_inner) _ _ _

/-- An inner product with a sum on the right. -/
lemma inner_sum {ι : Type*} (s : finset ι) (f : ι → E) (x : E) :
  ⟪x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫ :=
sesq_form.map_sum_left (sesq_form_of_inner) _ _ _

@[simp] lemma inner_zero_left {x : E} : ⟪0, x⟫ = 0 :=
by rw [← zero_smul 𝕜 (0:E), inner_smul_left, ring_hom.map_zero, zero_mul]

lemma inner_re_zero_left {x : E} : re ⟪0, x⟫ = 0 :=
by simp only [inner_zero_left, add_monoid_hom.map_zero]

@[simp] lemma inner_zero_right {x : E} : ⟪x, 0⟫ = 0 :=
by rw [←inner_conj_sym, inner_zero_left, ring_hom.map_zero]

lemma inner_re_zero_right {x : E} : re ⟪x, 0⟫ = 0 :=
by simp only [inner_zero_right, add_monoid_hom.map_zero]

lemma inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ :=
by rw [←norm_sq_eq_inner]; exact pow_nonneg (norm_nonneg x) 2
lemma real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ := @inner_self_nonneg ℝ F _ _ x

@[simp] lemma inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    have h₁ : re ⟪x, x⟫ = 0 := by rw is_R_or_C.ext_iff at h; simp [h.1],
    rw [←norm_sq_eq_inner x] at h₁,
    rw [←norm_eq_zero],
    exact pow_eq_zero h₁ },
  { rintro rfl,
    exact inner_zero_left }
end

@[simp] lemma inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 :=
begin
  split,
  { intro h,
    rw ←inner_self_eq_zero,
    have H₁ : re ⟪x, x⟫ ≥ 0, exact inner_self_nonneg,
    have H₂ : re ⟪x, x⟫ = 0, exact le_antisymm h H₁,
    rw is_R_or_C.ext_iff,
    exact ⟨by simp [H₂], by simp [inner_self_nonneg_im]⟩ },
  { rintro rfl,
    simp only [inner_zero_left, add_monoid_hom.map_zero] }
end

lemma real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 :=
by { have h := @inner_self_nonpos ℝ F _ _ x, simpa using h }

@[simp] lemma inner_self_re_to_K {x : E} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
by rw is_R_or_C.ext_iff; exact ⟨by simp, by simp [inner_self_nonneg_im]⟩

lemma inner_self_re_abs {x : E} : re ⟪x, x⟫ = abs ⟪x, x⟫ :=
begin
  have H : ⟪x, x⟫ = (re ⟪x, x⟫ : 𝕜) + im ⟪x, x⟫ * I,
  { rw re_add_im, },
  rw [H, is_add_hom.map_add re ((re ⟪x, x⟫) : 𝕜) (((im ⟪x, x⟫) : 𝕜) * I)],
  rw [mul_re, I_re, mul_zero, I_im, zero_sub, tactic.ring.add_neg_eq_sub],
  rw [of_real_re, of_real_im, sub_zero, inner_self_nonneg_im],
  simp only [abs_of_real, add_zero, of_real_zero, zero_mul],
  exact (_root_.abs_of_nonneg inner_self_nonneg).symm,
end

lemma inner_self_abs_to_K {x : E} : (absK ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
by { rw[←inner_self_re_abs], exact inner_self_re_to_K }

lemma real_inner_self_abs {x : F} : absR ⟪x, x⟫_ℝ = ⟪x, x⟫_ℝ :=
by { have h := @inner_self_abs_to_K ℝ F _ _ x, simpa using h }

lemma inner_abs_conj_sym {x y : E} : abs ⟪x, y⟫ = abs ⟪y, x⟫ :=
by rw [←inner_conj_sym, abs_conj]

@[simp] lemma inner_neg_left {x y : E} : ⟪-x, y⟫ = -⟪x, y⟫ :=
by { rw [← neg_one_smul 𝕜 x, inner_smul_left], simp }

@[simp] lemma inner_neg_right {x y : E} : ⟪x, -y⟫ = -⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_neg_left]; simp only [ring_hom.map_neg, inner_conj_sym]

lemma inner_neg_neg {x y : E} : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp

@[simp] lemma inner_self_conj {x : E} : ⟪x, x⟫† = ⟪x, x⟫ :=
by rw [is_R_or_C.ext_iff]; exact ⟨by rw [conj_re], by rw [conj_im, inner_self_im_zero, neg_zero]⟩

lemma inner_sub_left {x y z : E} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_left] }

lemma inner_sub_right {x y z : E} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
by { simp [sub_eq_add_neg, inner_add_right] }

lemma inner_mul_conj_re_abs {x y : E} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
by { rw[←inner_conj_sym, mul_comm], exact re_eq_abs_of_mul_conj (inner y x), }

/-- Expand `⟪x + y, x + y⟫` -/
lemma inner_add_add_self {x y : E} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_add_left, inner_add_right]; ring

/-- Expand `⟪x + y, x + y⟫_ℝ` -/
lemma real_inner_add_add_self {x y : F} : ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
begin
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [←inner_conj_sym]; refl,
  simp [inner_add_add_self, this],
  ring,
end

/- Expand `⟪x - y, x - y⟫` -/
lemma inner_sub_sub_self {x y : E} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ :=
by simp only [inner_sub_left, inner_sub_right]; ring

/-- Expand `⟪x - y, x - y⟫_ℝ` -/
lemma real_inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
begin
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [←inner_conj_sym]; refl,
  simp [inner_sub_sub_self, this],
  ring,
end

/-- Parallelogram law -/
lemma parallelogram_law {x y : E} :
  ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) :=
by simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]

/-- Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia. -/
lemma inner_mul_inner_self_le (x y : E) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
begin
  by_cases hy : y = 0,
  { rw [hy], simp only [is_R_or_C.abs_zero, inner_zero_left, mul_zero, add_monoid_hom.map_zero] },
  { change y ≠ 0 at hy,
    have hy' : ⟪y, y⟫ ≠ 0 := λ h, by rw [inner_self_eq_zero] at h; exact hy h,
    set T := ⟪y, x⟫ / ⟪y, y⟫ with hT,
    have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_re_symm,
    have h₂ : im ⟪y, x⟫ = -im ⟪x, y⟫ := inner_im_symm,
    have h₃ : ⟪y, x⟫ * ⟪x, y⟫ * ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = ⟪y, x⟫ * ⟪x, y⟫ / ⟪y, y⟫,
    { rw [mul_div_assoc],
      have : ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = 1 / ⟪y, y⟫ :=
        by rw [div_mul_eq_div_mul_one_div, div_self hy', one_mul],
      rw [this, div_eq_mul_inv, one_mul, ←div_eq_mul_inv] },
    have h₄ : ⟪y, y⟫ = re ⟪y, y⟫ := by simp,
    have h₅ : re ⟪y, y⟫ > 0,
    { refine lt_of_le_of_ne inner_self_nonneg _,
      intro H,
      apply hy',
      rw is_R_or_C.ext_iff,
      exact ⟨by simp [H],by simp [inner_self_nonneg_im]⟩ },
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gt h₅,
    have hmain := calc
      0   ≤ re ⟪x - T • y, x - T • y⟫
                  : inner_self_nonneg
      ... = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫
                  : by simp [inner_sub_sub_self, inner_smul_left, inner_smul_right, h₁, h₂]
      ... = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫)
                  : by simp [inner_smul_left, inner_smul_right, mul_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫)
                  : by field_simp [-mul_re, hT, conj_div, h₁, h₃, inner_conj_sym]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫)
                  : by rw [div_mul_eq_mul_div_comm, ←mul_div_assoc]
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / re ⟪y, y⟫)
                  : by conv_lhs { rw [h₄] }
      ... = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [div_re_of_real]
      ... = re ⟪x, x⟫ - abs (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫
                  : by rw [inner_mul_conj_re_abs]
      ... = re ⟪x, x⟫ - abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫
                  : by rw is_R_or_C.abs_mul,
    have hmain' : abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ ≤ re ⟪x, x⟫ := by linarith,
    have := (mul_le_mul_right h₅).mpr hmain',
    rwa [div_mul_cancel (abs ⟪x, y⟫ * abs ⟪y, x⟫) h₆] at this }
end

/-- Cauchy–Schwarz inequality for real inner products. -/
lemma real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ :=
begin
  have h₁ : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [←inner_conj_sym]; refl,
  have h₂ := @inner_mul_inner_self_le ℝ F _ _ x y,
  dsimp at h₂,
  have h₃ := abs_mul_abs_self ⟪x, y⟫_ℝ,
  rw [h₁] at h₂,
  simpa [h₃] using h₂,
end

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
lemma linear_independent_of_ne_zero_of_inner_eq_zero {ι : Type*} {v : ι → E}
  (hz : ∀ i, v i ≠ 0) (ho : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) : linear_independent 𝕜 v :=
begin
  rw linear_independent_iff',
  intros s g hg i hi,
  have h' : g i * inner (v i) (v i) = inner (v i) (∑ j in s, g j • v j),
  { rw inner_sum,
    symmetry,
    convert finset.sum_eq_single i _ _,
    { rw inner_smul_right },
    { intros j hj hji,
      rw [inner_smul_right, ho i j hji.symm, mul_zero] },
    { exact λ h, false.elim (h hi) } },
  simpa [hg, hz] using h'
end

end basic_properties

section norm

lemma norm_eq_sqrt_inner (x : E) : ∥x∥ = sqrt (re ⟪x, x⟫) :=
begin
  have h₁ : ∥x∥^2 = re ⟪x, x⟫ := norm_sq_eq_inner x,
  have h₂ := congr_arg sqrt h₁,
  simpa using h₂,
end

lemma norm_eq_sqrt_real_inner (x : F) : ∥x∥ = sqrt ⟪x, x⟫_ℝ :=
by { have h := @norm_eq_sqrt_inner ℝ F _ _ x, simpa using h }

lemma inner_self_eq_norm_square (x : E) : re ⟪x, x⟫ = ∥x∥ * ∥x∥ :=
by rw[norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
  sqrt_mul_self inner_self_nonneg]

lemma real_inner_self_eq_norm_square (x : F) : ⟪x, x⟫_ℝ = ∥x∥ * ∥x∥ :=
by { have h := @inner_self_eq_norm_square ℝ F _ _ x, simpa using h }


/-- Expand the square -/
lemma norm_add_pow_two {x y : E} : ∥x + y∥^2 = ∥x∥^2 + 2 * (re ⟪x, y⟫) + ∥y∥^2 :=
begin
  repeat {rw [pow_two, ←inner_self_eq_norm_square]},
  rw[inner_add_add_self, two_mul],
  simp only [add_assoc, add_left_inj, add_right_inj, add_monoid_hom.map_add],
  rw [←inner_conj_sym, conj_re],
end

/-- Expand the square -/
lemma norm_add_pow_two_real {x y : F} : ∥x + y∥^2 = ∥x∥^2 + 2 * ⟪x, y⟫_ℝ + ∥y∥^2 :=
by { have h := @norm_add_pow_two ℝ F _ _, simpa using h }

/-- Expand the square -/
lemma norm_add_mul_self {x y : E} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * (re ⟪x, y⟫) + ∥y∥ * ∥y∥ :=
by { repeat {rw [← pow_two]}, exact norm_add_pow_two }

/-- Expand the square -/
lemma norm_add_mul_self_real {x y : F} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * ⟪x, y⟫_ℝ + ∥y∥ * ∥y∥ :=
by { have h := @norm_add_mul_self ℝ F _ _, simpa using h }

/-- Expand the square -/
lemma norm_sub_pow_two {x y : E} : ∥x - y∥^2 = ∥x∥^2 - 2 * (re ⟪x, y⟫) + ∥y∥^2 :=
begin
  repeat {rw [pow_two, ←inner_self_eq_norm_square]},
  rw[inner_sub_sub_self],
  calc
    re (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫)
        = re ⟪x, x⟫ - re ⟪x, y⟫ - re ⟪y, x⟫ + re ⟪y, y⟫  : by simp
    ... = -re ⟪y, x⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫  : by ring
    ... = -re (⟪x, y⟫†) - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ : by rw[inner_conj_sym]
    ... = -re ⟪x, y⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ : by rw[conj_re]
    ... = re ⟪x, x⟫ - 2*re ⟪x, y⟫ + re ⟪y, y⟫ : by ring
end

/-- Expand the square -/
lemma norm_sub_pow_two_real {x y : F} : ∥x - y∥^2 = ∥x∥^2 - 2 * ⟪x, y⟫_ℝ + ∥y∥^2 :=
by { have h := @norm_sub_pow_two ℝ F _ _, simpa using h }

/-- Expand the square -/
lemma norm_sub_mul_self {x y : E} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * re ⟪x, y⟫ + ∥y∥ * ∥y∥ :=
by { repeat {rw [← pow_two]}, exact norm_sub_pow_two }

/-- Expand the square -/
lemma norm_sub_mul_self_real {x y : F} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * ⟪x, y⟫_ℝ + ∥y∥ * ∥y∥ :=
by { have h := @norm_sub_mul_self ℝ F _ _, simpa using h }

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_inner_le_norm (x y : E) : abs ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ :=
nonneg_le_nonneg_of_squares_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
begin
  have : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = (re ⟪x, x⟫) * (re ⟪y, y⟫),
    simp only [inner_self_eq_norm_square], ring,
  rw this,
  conv_lhs { congr, skip, rw [inner_abs_conj_sym] },
  exact inner_mul_inner_self_le _ _
end

/-- Cauchy–Schwarz inequality with norm -/
lemma abs_real_inner_le_norm (x y : F) : absR ⟪x, y⟫_ℝ ≤ ∥x∥ * ∥y∥ :=
by { have h := @abs_inner_le_norm ℝ F _ _ x y, simpa using h }

include 𝕜
lemma parallelogram_law_with_norm {x y : E} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
begin
  simp only [(inner_self_eq_norm_square _).symm],
  rw[←add_monoid_hom.map_add, parallelogram_law, two_mul, two_mul],
  simp only [add_monoid_hom.map_add],
end
omit 𝕜

lemma parallelogram_law_with_norm_real {x y : F} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
by { have h := @parallelogram_law_with_norm ℝ F _ _ x y, simpa using h }

/-- Polarization identity: The real inner product, in terms of the norm. -/
lemma real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
  ⟪x, y⟫_ℝ = (∥x + y∥ * ∥x + y∥ - ∥x∥ * ∥x∥ - ∥y∥ * ∥y∥) / 2 :=
by rw norm_add_mul_self; ring

/-- Polarization identity: The real inner product, in terms of the norm. -/
lemma real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
  ⟪x, y⟫_ℝ = (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - ∥x - y∥ * ∥x - y∥) / 2 :=
by rw norm_sub_mul_self; ring

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
lemma norm_add_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero (x y : F) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ ⟪x, y⟫_ℝ = 0 :=
begin
  rw [norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, vector inner product form. -/
lemma norm_add_square_eq_norm_square_add_norm_square_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
begin
  rw [norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero],
  apply or.inr,
  simp only [h, zero_re'],
end

/-- Pythagorean theorem, vector inner product form. -/
lemma norm_add_square_eq_norm_square_add_norm_square_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
  ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(norm_add_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero (x y : F) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ ⟪x, y⟫_ℝ = 0 :=
begin
  rw [norm_sub_mul_self, add_right_cancel_iff, sub_eq_add_neg, add_right_eq_self, neg_eq_zero,
      mul_eq_zero],
  norm_num
end

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
lemma norm_sub_square_eq_norm_square_add_norm_square_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
  ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
(norm_sub_square_eq_norm_square_add_norm_square_iff_real_inner_eq_zero x y).2 h

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
lemma real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_ℝ = 0 ↔ ∥x∥ = ∥y∥ :=
begin
  conv_rhs { rw ←mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _) },
  simp only [←inner_self_eq_norm_square, inner_add_left, inner_sub_right,
            real_inner_comm y x, sub_eq_zero, re_to_real],
  split,
  { intro h,
    rw [add_comm] at h,
    linarith },
  { intro h,
    linarith }
end

/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
lemma abs_real_inner_div_norm_mul_norm_le_one (x y : F) : absR (⟪x, y⟫_ℝ / (∥x∥ * ∥y∥)) ≤ 1 :=
begin
  rw _root_.abs_div,
  by_cases h : 0 = absR (∥x∥ * ∥y∥),
  { rw [←h, div_zero],
    norm_num },
  { change 0 ≠ absR (∥x∥ * ∥y∥) at h,
    rw div_le_iff' (lt_of_le_of_ne (ge_iff_le.mp (_root_.abs_nonneg (∥x∥ * ∥y∥))) h),
    convert abs_real_inner_le_norm x y using 1,
    rw [_root_.abs_mul, _root_.abs_of_nonneg (norm_nonneg x), _root_.abs_of_nonneg (norm_nonneg y), mul_one] }
end

/-- The inner product of a vector with a multiple of itself. -/
lemma real_inner_smul_self_left (x : F) (r : ℝ) : ⟪r • x, x⟫_ℝ = r * (∥x∥ * ∥x∥) :=
by rw [real_inner_smul_left, ←real_inner_self_eq_norm_square]

/-- The inner product of a vector with a multiple of itself. -/
lemma real_inner_smul_self_right (x : F) (r : ℝ) : ⟪x, r • x⟫_ℝ = r * (∥x∥ * ∥x∥) :=
by rw [inner_smul_right, ←real_inner_self_eq_norm_square]

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
lemma abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  {x : E} {r : 𝕜} (hx : x ≠ 0) (hr : r ≠ 0) : abs ⟪x, r • x⟫ / (∥x∥ * ∥r • x∥) = 1 :=
begin
  have hx' : ∥x∥ ≠ 0 := by simp [norm_eq_zero, hx],
  have hr' : abs r ≠ 0 := by simp [is_R_or_C.abs_eq_zero, hr],
  rw [inner_smul_right, is_R_or_C.abs_mul, ←inner_self_re_abs, inner_self_eq_norm_square, norm_smul],
  rw [is_R_or_C.norm_eq_abs, ←mul_assoc, ←div_div_eq_div_mul, mul_div_cancel _ hx',
     ←div_div_eq_div_mul, mul_comm, mul_div_cancel _ hr', div_self hx'],
end

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
lemma abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
  {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r ≠ 0) : absR ⟪x, r • x⟫_ℝ / (∥x∥ * ∥r • x∥) = 1 :=
begin
  rw ← abs_to_real,
  exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr
end

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
lemma real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul
  {x : F} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) : ⟪x, r • x⟫_ℝ / (∥x∥ * ∥r • x∥) = 1 :=
begin
  rw [real_inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ∥x∥, mul_comm _ (absR r),
      mul_assoc, _root_.abs_of_nonneg (le_of_lt hr), div_self],
  exact mul_ne_zero (ne_of_gt hr)
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h)))
end

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
lemma real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul
  {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r < 0) : ⟪x, r • x⟫_ℝ / (∥x∥ * ∥r • x∥) = -1 :=
begin
  rw [real_inner_smul_self_right, norm_smul, real.norm_eq_abs, ←mul_assoc ∥x∥, mul_comm _ (absR r),
      mul_assoc, abs_of_neg hr, ←neg_mul_eq_neg_mul, div_neg_eq_neg_div, div_self],
  exact mul_ne_zero (ne_of_lt hr)
    (λ h, hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h)))
end

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
lemma abs_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
  abs (⟪x, y⟫ / (∥x∥ * ∥y∥)) = 1 ↔ (x ≠ 0 ∧ ∃ (r : 𝕜), r ≠ 0 ∧ y = r • x) :=
begin
  split,
  { intro h,
    have hx0 : x ≠ 0,
    { intro hx0,
      rw [hx0, inner_zero_left, zero_div] at h,
      norm_num at h,
      exact h },
    refine and.intro hx0 _,
    set r := ⟪x, y⟫ / (∥x∥ * ∥x∥) with hr,
    use r,
    set t := y - r • x with ht,
    have ht0 : ⟪x, t⟫ = 0,
    { rw [ht, inner_sub_right, inner_smul_right, hr],
      norm_cast,
      rw [←inner_self_eq_norm_square, inner_self_re_to_K,
          div_mul_cancel _ (λ h, hx0 (inner_self_eq_zero.1 h)), sub_self] },
    replace h : ∥r • x∥ / ∥t + r • x∥ = 1,
    { rw [←sub_add_cancel y (r • x), ←ht, inner_add_right, ht0, zero_add, inner_smul_right,
        is_R_or_C.abs_div, is_R_or_C.abs_mul, ←inner_self_re_abs,
        inner_self_eq_norm_square] at h,
      norm_cast at h,
      rwa [_root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm, ←mul_assoc, mul_comm,
        mul_div_mul_left _ _ (λ h, hx0 (norm_eq_zero.1 h)), ←is_R_or_C.norm_eq_abs,
        ←norm_smul] at h },
    have hr0 : r ≠ 0,
    { intro hr0,
      rw [hr0, zero_smul, norm_zero, zero_div] at h,
      norm_num at h },
    refine and.intro hr0 _,
    have h2 : ∥r • x∥ ^ 2 = ∥t + r • x∥ ^ 2,
    { rw [eq_of_div_eq_one h] },
    replace h2 : ⟪r • x, r • x⟫ = ⟪t, t⟫ + ⟪t, r • x⟫ + ⟪r • x, t⟫ + ⟪r • x, r • x⟫,
    { rw [pow_two, pow_two, ←inner_self_eq_norm_square, ←inner_self_eq_norm_square ] at h2,
      have h2' := congr_arg (λ z : ℝ, (z : 𝕜)) h2,
      simp_rw [inner_self_re_to_K, inner_add_add_self] at h2',
      exact h2' },
    conv at h2 in ⟪r • x, t⟫ { rw [inner_smul_left, ht0, mul_zero] },
    symmetry' at h2,
    have h₁ : ⟪t, r • x⟫ = 0 := by { rw [inner_smul_right, ←inner_conj_sym, ht0], simp },
    rw [add_zero, h₁, add_left_eq_self, add_zero, inner_self_eq_zero] at h2,
    rw h2 at ht,
    exact eq_of_sub_eq_zero ht.symm },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw [hy, is_R_or_C.abs_div],
    norm_cast,
    rw [_root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm],
    exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr }
end

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
lemma abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
  absR (⟪x, y⟫_ℝ / (∥x∥ * ∥y∥)) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r ≠ 0 ∧ y = r • x) :=
begin
  have := @abs_inner_div_norm_mul_norm_eq_one_iff ℝ F _ _ x y,
  simpa [coe_real_eq_id] using this,
end

/--
If the inner product of two vectors is equal to the product of their norms, then the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
-/
lemma abs_inner_eq_norm_iff (x y : E) (hx0 : x ≠ 0) (hy0 : y ≠ 0):
  abs ⟪x, y⟫ = ∥x∥ * ∥y∥ ↔ ∃ (r : 𝕜), r ≠ 0 ∧ y = r • x :=
begin
  have hx0' : ∥x∥ ≠ 0 := by simp [norm_eq_zero, hx0],
  have hy0' : ∥y∥ ≠ 0 := by simp [norm_eq_zero, hy0],
  have hxy0 : ∥x∥ * ∥y∥ ≠ 0 := by simp [hx0', hy0'],
  have h₁ : abs ⟪x, y⟫ = ∥x∥ * ∥y∥ ↔ abs (⟪x, y⟫ / (∥x∥ * ∥y∥)) = 1,
  { refine ⟨_ ,_⟩,
    { intro h,
      norm_cast,
      rw [is_R_or_C.abs_div, h, abs_of_real, _root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm],
      exact div_self hxy0 },
    { intro h,
      norm_cast at h,
      rwa [is_R_or_C.abs_div, abs_of_real, _root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm,
          div_eq_one_iff_eq hxy0] at h } },
  rw [h₁, abs_inner_div_norm_mul_norm_eq_one_iff x y],
  have : x ≠ 0 := λ h, (hx0' $ norm_eq_zero.mpr h),
  simp [this]
end

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
lemma real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
  ⟪x, y⟫_ℝ / (∥x∥ * ∥y∥) = 1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), 0 < r ∧ y = r • x) :=
begin
  split,
  { intro h,
    have ha := h,
    apply_fun absR at ha,
    norm_num at ha,
    rcases (abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    use [hx, r],
    refine and.intro _ hy,
    by_contradiction hrneg,
    rw hy at h,
    rw real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx
      (lt_of_le_of_ne (le_of_not_lt hrneg) hr) at h,
    norm_num at h },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr }
end

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
lemma real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) :
  ⟪x, y⟫_ℝ / (∥x∥ * ∥y∥) = -1 ↔ (x ≠ 0 ∧ ∃ (r : ℝ), r < 0 ∧ y = r • x) :=
begin
  split,
  { intro h,
    have ha := h,
    apply_fun absR at ha,
    norm_num at ha,
    rcases (abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    use [hx, r],
    refine and.intro _ hy,
    by_contradiction hrpos,
    rw hy at h,
    rw real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx
      (lt_of_le_of_ne (le_of_not_lt hrpos) hr.symm) at h,
    norm_num at h },
  { intro h,
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩,
    rw hy,
    exact real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx hr }
end

/-- The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences. -/
lemma inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type*} {s₁ : finset ι₁} {w₁ : ι₁ → ℝ}
    (v₁ : ι₁ → F) (h₁ : ∑ i in s₁, w₁ i = 0) {ι₂ : Type*} {s₂ : finset ι₂} {w₂ : ι₂ → ℝ}
    (v₂ : ι₂ → F) (h₂ : ∑ i in s₂, w₂ i = 0) :
  ⟪(∑ i₁ in s₁, w₁ i₁ • v₁ i₁), (∑ i₂ in s₂, w₂ i₂ • v₂ i₂)⟫_ℝ =
    (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (∥v₁ i₁ - v₂ i₂∥ * ∥v₁ i₁ - v₂ i₂∥)) / 2 :=
by simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
            real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two,
            ←div_sub_div_same, ←div_add_div_same, mul_sub_left_distrib, left_distrib,
            finset.sum_sub_distrib, finset.sum_add_distrib, ←finset.mul_sum, ←finset.sum_mul,
            h₁, h₂, zero_mul, mul_zero, finset.sum_const_zero, zero_add, zero_sub, finset.mul_sum,
            neg_div, finset.sum_div, mul_div_assoc, mul_assoc]

end norm

section of_norm

variables {E' : Type*} [normed_group E'] [normed_space 𝕜 E']

lemma a_plus_I_b (a b : E') (h : (I : 𝕜) ≠ 0) :
  a + (I : 𝕜) • b = (I : 𝕜) • (b - (I : 𝕜) • a) :=
begin
  have h' := I_mul_I_of_nonzero h,
  rw [smul_sub I, ←smul_assoc, smul_eq_mul, h', neg_smul, sub_neg_eq_add, one_smul, add_comm]
end

-- TODO, some useful references:
-- http://www.mathematik.uni-muenchen.de/~michel/jordan-von_neumann_-_parallelogram_identity.pdf
-- https://math.stackexchange.com/questions/21792/norms-induced-by-inner-products-and-the-parallelogram-law
-- https://math.dartmouth.edu/archive/m113w10/public_html/jordan-vneumann-thm.pdf

/-- Fréchet–von Neumann–Jordan theorm. A normed space `E'` whose norm satisfies the parallelogram
identity can be given a compatible inner product. -/
def inner_product_space.of_norm
  (h : ∀ x y : E', ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥)) :
  inner_product_space 𝕜 E' :=
{ inner := λ x y, 4⁻¹ * ((𝓚 ∥x + y∥) * (𝓚 ∥x + y∥) - (𝓚 ∥x - y∥) * (𝓚 ∥x - y∥)
            + (I:𝕜) * (𝓚 ∥x + (I:𝕜) • y∥) * (𝓚 ∥x + (I:𝕜) • y∥)
            - (I:𝕜) * (𝓚 ∥x - (I:𝕜) • y∥) * (𝓚 ∥x - (I:𝕜) • y∥)),
  norm_sq_eq_inner := assume x,
  begin
    have h₁ : norm_sq (4:𝕜) = 16,
    { have : (of_real 4 : 𝕜) = (4 : 𝕜),
      { simp only [of_real_one, of_real_bit0] },
      rw [←this, norm_sq_eq_def', is_R_or_C.norm_eq_abs, is_R_or_C.abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)],
      norm_num },
    have h₂ : ∥x + x∥ = 2 * ∥x∥,
    { have : ∥(2 : 𝕜)∥ = 2,
      { rw [is_R_or_C.norm_eq_abs, is_R_or_C.abs_two] },
      rw [←this, ←norm_smul, two_smul] },
    simp only [inner, h₁, h₂, one_im, bit0_zero, add_zero, norm_zero, I_re, of_real_im,
      add_monoid_hom.map_add, bit0_im, zero_div, zero_mul, add_monoid_hom.map_neg, of_real_re,
      add_monoid_hom.map_sub, sub_zero, inv_re, one_re, inv_im, bit0_re, mul_re, mul_zero, sub_self,
      neg_zero],
    ring
  end,
  conj_sym := λ x y, begin
    simp [inner],
    congr' 1,
    { have : (of_real 4⁻¹ : 𝕜) = (4⁻¹ : 𝕜),
      { simp only [of_real_one, of_real_bit0, of_real_inv]},
      rw [←this, conj_of_real] },
    have : y + x = x + y := by abel,
    rw this,
    have : y - x = - (x - y) := by abel,
    rw this,
    rw norm_neg,
    by_cases h : (I : 𝕜) = 0,
    { rw h, simp only [add_zero, zero_mul, sub_zero, neg_zero]},
    have := abs_I_of_nonzero h,
    rw ← is_R_or_C.norm_eq_abs at this,
    rw [a_plus_I_b x y h, a_plus_I_b y x h, norm_smul, norm_smul, this],
    ring, ring -- huh?
  end,
  nonneg_im := λ x, begin
    simp [inner],
    right,
    by_cases h : (I : 𝕜) = 0,
    { rw h, simp only [zero_mul, sub_zero, add_monoid_hom.map_zero]},
    have := abs_I_of_nonzero h,
    rw ← is_R_or_C.norm_eq_abs at this,
    rw [a_plus_I_b x x h, norm_smul, this, one_mul, sub_self]
  end,
  add_left := assume x y z,
  begin
    simp [inner],
    rw ←mul_add,
    congr,
    apply is_R_or_C.ext,
    { simp only [add_zero, I_re, of_real_im, add_monoid_hom.map_add, zero_mul, of_real_re,
        add_monoid_hom.map_sub, sub_zero, mul_im, mul_re, mul_zero],
      have : ∥x + y + z∥ * ∥x + y + z∥ = (∥2 • x + y∥ * ∥2 • x + y∥ + ∥2 • z + y∥ * ∥2 • z + y∥) / 2 - ∥x - z∥ * ∥x - z∥,
      { apply eq_sub_of_add_eq,
        rw eq_div_iff (by norm_num : (2 : ℝ) ≠ 0),
        rw mul_comm _ (2 : ℝ),
        symmetry,
        have h₀ := h (x + y + z) (x - z),
        convert h₀ using 4; { rw two_smul, abel } },
      rw this,
      have : ∥x + y - z∥ * ∥x + y - z∥ = (∥2 • x + y∥ * ∥2 • x + y∥ + ∥y - 2 • z∥ * ∥y - 2 • z∥) / 2 - ∥x + z∥ * ∥x + z∥,
      { apply eq_sub_of_add_eq,
        rw eq_div_iff (by norm_num : (2 : ℝ) ≠ 0),
        rw mul_comm _ (2 : ℝ),
        symmetry,
        have h₀ := h (x + y - z) (x + z),
        convert h₀ using 4; { rw two_smul, abel } },
      rw this,
      have : ∥2 • z + y∥ * ∥2 • z + y∥ = 2 * (∥y + z∥ * ∥y + z∥ + ∥z∥ * ∥z∥) - ∥y∥ * ∥y∥,
      { apply eq_sub_of_add_eq,
        have h₀ := h (y + z) z,
        convert h₀ using 4; { try { rw two_smul }, abel } },
      rw this,
      have : ∥y - 2 • z∥ * ∥y - 2 • z∥ = 2 * (∥y - z∥ * ∥y - z∥ + ∥z∥ * ∥z∥) - ∥y∥ * ∥y∥,
      { apply eq_sub_of_add_eq,
        have h₀ := h (y - z) z,
        conv_lhs at h₀ { rw add_comm },
        convert h₀ using 4; { try { rw two_smul }, abel }, },
      rw this,
      ring },
    { simp only [of_real_im, add_monoid_hom.map_add, zero_mul, of_real_re, add_monoid_hom.map_sub,
        sub_zero, mul_im, zero_add, mul_zero],
      simp_rw [mul_assoc, ←mul_sub, ←mul_add],
      congr,
      have : ∥x + y + (I : 𝕜) • z∥ * ∥x + y + (I : 𝕜) • z∥ =
        (∥2 • x + y∥ * ∥2 • x + y∥ + ∥2 • (I : 𝕜) • z + y∥ * ∥2 • (I : 𝕜) • z + y∥) / 2 -
        ∥x - (I : 𝕜) • z∥ * ∥x - (I : 𝕜) • z∥,
      { apply eq_sub_of_add_eq,
        rw eq_div_iff (by norm_num : (2 : ℝ) ≠ 0),
        rw mul_comm _ (2 : ℝ),
        symmetry,
        have h₀ := h (x + y + (I : 𝕜) • z) (x - (I : 𝕜) • z),
        convert h₀ using 4; { try { rw two_smul }, abel } },
      rw this,
      have : ∥x + y - (I : 𝕜) • z∥ * ∥x + y - (I : 𝕜) • z∥ =
        (∥2 • x + y∥ * ∥2 • x + y∥ + ∥y - 2 • (I : 𝕜) • z∥ * ∥y - 2 • (I : 𝕜) • z∥) / 2 -
        ∥x + (I : 𝕜) • z∥ * ∥x + (I : 𝕜) • z∥,
      { apply eq_sub_of_add_eq,
        rw eq_div_iff (by norm_num : (2 : ℝ) ≠ 0),
        rw mul_comm _ (2 : ℝ),
        symmetry,
        have h₀ := h (x + y - (I : 𝕜) • z) (x + (I : 𝕜) • z),
        convert h₀ using 4; { try { rw two_smul }, abel } },
      rw this,
      have : ∥2 • (I : 𝕜) • z + y∥ * ∥2 • (I : 𝕜) • z + y∥ = 2 * (∥y + (I : 𝕜) • z∥ * ∥y + (I : 𝕜) • z∥ + ∥(I : 𝕜) • z∥ * ∥(I : 𝕜) • z∥) - ∥y∥ * ∥y∥,
      { apply eq_sub_of_add_eq,
        have h₀ := h (y + (I : 𝕜) • z) ((I : 𝕜) • z),
        convert h₀ using 4; { try { rw two_smul }, abel } },
      rw this,
      have : ∥y - 2 • (I : 𝕜) • z∥ * ∥y - 2 • (I : 𝕜) • z∥ = 2 * (∥y - (I : 𝕜) • z∥ * ∥y - (I : 𝕜) • z∥ + ∥(I : 𝕜) • z∥ * ∥(I : 𝕜) • z∥) - ∥y∥ * ∥y∥,
      { apply eq_sub_of_add_eq,
        have h₀ := h (y - (I : 𝕜) • z) ((I : 𝕜) • z),
        conv_lhs at h₀ { rw add_comm },
        convert h₀ using 4; { try { rw two_smul }, abel }, },
      rw this,
      ring },
  end,
  smul_left := assume x y r,
  begin
    simp [inner],
    sorry,
  end }

end of_norm

/-! ### Inner product space structure on product spaces -/

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `pi_Lp 2 one_le_two f` for the product space, which is endowed with the `L^2` norm.
-/
instance pi_Lp.inner_product_space {ι : Type*} [fintype ι] (f : ι → Type*)
  [Π i, inner_product_space 𝕜 (f i)] : inner_product_space 𝕜 (pi_Lp 2 one_le_two f) :=
{ inner := λ x y, ∑ i, inner (x i) (y i),
  norm_sq_eq_inner :=
  begin
    intro x,
    have h₁ : ∑ (i : ι), ∥x i∥ ^ (2 : ℕ) = ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { apply finset.sum_congr rfl,
      intros j hj,
      simp [←rpow_nat_cast] },
    have h₂ : 0 ≤ ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { rw [←h₁],
      exact finset.sum_nonneg (λ (j : ι) (hj : j ∈ finset.univ), pow_nonneg (norm_nonneg (x j)) 2) },
    simp [norm, add_monoid_hom.map_sum, ←norm_sq_eq_inner],
    rw [←rpow_nat_cast ((∑ (i : ι), ∥x i∥ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) 2],
    rw [←rpow_mul h₂],
    norm_num [h₁],
  end,
  conj_sym :=
  begin
    intros x y,
    unfold inner,
    rw [←finset.sum_hom finset.univ conj],
    apply finset.sum_congr rfl,
    rintros z -,
    apply inner_conj_sym,
    apply_instance
  end,
  nonneg_im :=
  begin
    intro x,
    unfold inner,
    rw[←finset.sum_hom finset.univ im],
    apply finset.sum_eq_zero,
    rintros z -,
    exact inner_self_nonneg_im,
    apply_instance
  end,
  add_left := λ x y z,
    show ∑ i, inner (x i + y i) (z i) = ∑ i, inner (x i) (z i) + ∑ i, inner (y i) (z i),
    by simp only [inner_add_left, finset.sum_add_distrib],
  smul_left := λ x y r,
    show ∑ (i : ι), inner (r • x i) (y i) = (conj r) * ∑ i, inner (x i) (y i),
    by simp only [finset.mul_sum, inner_smul_left]
}

/-- A field `𝕜` satisfying `is_R_or_C` is itself a `𝕜`-inner product space. -/
instance is_R_or_C.inner_product_space : inner_product_space 𝕜 𝕜 :=
{ inner := (λ x y, (conj x) * y),
  norm_sq_eq_inner := λ x, by unfold inner; rw [mul_comm, mul_conj, of_real_re, norm_sq, norm_sq_eq_def],
  conj_sym := λ x y, by simp [mul_comm],
  nonneg_im := λ x, by rw[mul_im, conj_re, conj_im]; ring,
  add_left := λ x y z, by simp [inner, add_mul],
  smul_left := λ x y z, by simp [inner, mul_assoc] }

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional space
use `euclidean_space 𝕜 (fin n)`.  -/
@[reducible, nolint unused_arguments]
def euclidean_space (𝕜 : Type*) [is_R_or_C 𝕜]
  (n : Type*) [fintype n] : Type* := pi_Lp 2 one_le_two (λ (i : n), 𝕜)

section is_R_or_C_to_real

variables {G : Type*}

variables (𝕜)
include 𝕜

/-- A general inner product implies a real inner product. This is not registered as an instance
since it creates problems with the case `𝕜 = ℝ`. -/
def has_inner.is_R_or_C_to_real : has_inner ℝ E :=
{ inner := λ x y, re ⟪x, y⟫ }

lemma real_inner_eq_re_inner (x y : E) :
  @has_inner.inner ℝ E (has_inner.is_R_or_C_to_real 𝕜) x y = re ⟪x, y⟫ := rfl

/-- A general inner product space structure implies a real inner product structure. This is not
registered as an instance since it creates problems with the case `𝕜 = ℝ`, but in can be used in a
proof to obtain a real inner product space structure from a given `𝕜`-inner product space
structure. -/
def inner_product_space.is_R_or_C_to_real : inner_product_space ℝ E :=
{ norm_sq_eq_inner := norm_sq_eq_inner,
  conj_sym := λ x y, inner_re_symm,
  nonneg_im := λ x, rfl,
  add_left := λ x y z, by {
    change re ⟪x + y, z⟫ = re ⟪x, z⟫ + re ⟪y, z⟫,
    simp [inner_add_left] },
  smul_left := λ x y r, by {
    change re ⟪(r : 𝕜) • x, y⟫ = r * re ⟪x, y⟫,
    simp [inner_smul_left] },
  ..has_inner.is_R_or_C_to_real 𝕜,
  ..normed_space.restrict_scalars ℝ 𝕜 E }

omit 𝕜

/-- A complex inner product implies a real inner product -/
instance inner_product_space.complex_to_real [inner_product_space ℂ G] : inner_product_space ℝ G :=
inner_product_space.is_R_or_C_to_real ℂ

end is_R_or_C_to_real

section pi_Lp
local attribute [reducible] pi_Lp
variables {ι : Type*} [fintype ι]

instance : finite_dimensional 𝕜 (euclidean_space 𝕜 ι) := by apply_instance

@[simp] lemma findim_euclidean_space :
  finite_dimensional.findim 𝕜 (euclidean_space 𝕜 ι) = fintype.card ι := by simp

lemma findim_euclidean_space_fin {n : ℕ} :
  finite_dimensional.findim 𝕜 (euclidean_space 𝕜 (fin n)) = n := by simp

end pi_Lp


/-! ### Orthogonal projection in inner product spaces -/

section orthogonal

open filter

/--
Existence of minimizers
Let `u` be a point in a real inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
 -/
-- FIXME this monolithic proof causes a deterministic timeout with `-T50000`
-- It should be broken in a sequence of more manageable pieces,
-- perhaps with individual statements for the three steps below.
theorem exists_norm_eq_infi_of_complete_convex {K : set F} (ne : K.nonempty) (h₁ : is_complete K)
  (h₂ : convex K) : ∀ u : F, ∃ v ∈ K, ∥u - v∥ = ⨅ w : K, ∥u - w∥ := assume u,
begin
  let δ := ⨅ w : K, ∥u - w∥,
  letI : nonempty K := ne.to_subtype,
  have zero_le_δ : 0 ≤ δ := le_cinfi (λ _, norm_nonneg _),
  have δ_le : ∀ w : K, δ ≤ ∥u - w∥,
    from cinfi_le ⟨0, set.forall_range_iff.2 $ λ _, norm_nonneg _⟩,
  have δ_le' : ∀ w ∈ K, δ ≤ ∥u - w∥ := assume w hw, δ_le ⟨w, hw⟩,
  -- Step 1: since `δ` is the infimum, can find a sequence `w : ℕ → K` in `K`
  -- such that `∥u - w n∥ < δ + 1 / (n + 1)` (which implies `∥u - w n∥ --> δ`);
  -- maybe this should be a separate lemma
  have exists_seq : ∃ w : ℕ → K, ∀ n, ∥u - w n∥ < δ + 1 / (n + 1),
  { have hδ : ∀n:ℕ, δ < δ + 1 / (n + 1), from
      λ n, lt_add_of_le_of_pos (le_refl _) nat.one_div_pos_of_nat,
    have h := λ n, exists_lt_of_cinfi_lt (hδ n),
    let w : ℕ → K := λ n, classical.some (h n),
    exact ⟨w, λ n, classical.some_spec (h n)⟩ },
  rcases exists_seq with ⟨w, hw⟩,
  have norm_tendsto : tendsto (λ n, ∥u - w n∥) at_top (nhds δ),
  { have h : tendsto (λ n:ℕ, δ) at_top (nhds δ) := tendsto_const_nhds,
    have h' : tendsto (λ n:ℕ, δ + 1 / (n + 1)) at_top (nhds δ),
    { convert h.add tendsto_one_div_add_at_top_nhds_0_nat, simp only [add_zero] },
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h'
      (λ x, δ_le _) (λ x, le_of_lt (hw _)) },
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : cauchy_seq (λ n, ((w n):F)),
  { rw cauchy_seq_iff_le_tendsto_0, -- splits into three goals
    let b := λ n:ℕ, (8 * δ * (1/(n+1)) + 4 * (1/(n+1)) * (1/(n+1))),
    use (λn, sqrt (b n)),
    split,
    -- first goal :  `∀ (n : ℕ), 0 ≤ sqrt (b n)`
    assume n, exact sqrt_nonneg _,
    split,
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ sqrt (b N)`
    assume p q N hp hq,
    let wp := ((w p):F), let wq := ((w q):F),
    let a := u - wq, let b := u - wp,
    let half := 1 / (2:ℝ), let div := 1 / ((N:ℝ) + 1),
    have : 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥ =
      2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) :=
    calc
      4 * ∥u - half•(wq + wp)∥ * ∥u - half•(wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥
          = (2*∥u - half•(wq + wp)∥) * (2 * ∥u - half•(wq + wp)∥) + ∥wp-wq∥*∥wp-wq∥ : by ring
      ... = (absR ((2:ℝ)) * ∥u - half•(wq + wp)∥) * (absR ((2:ℝ)) * ∥u - half•(wq+wp)∥) + ∥wp-wq∥*∥wp-wq∥ :
      by { rw _root_.abs_of_nonneg, exact add_nonneg zero_le_one zero_le_one }
      ... = ∥(2:ℝ) • (u - half • (wq + wp))∥ * ∥(2:ℝ) • (u - half • (wq + wp))∥ + ∥wp-wq∥ * ∥wp-wq∥ :
      by simp [norm_smul]
      ... = ∥a + b∥ * ∥a + b∥ + ∥a - b∥ * ∥a - b∥ :
      begin
        rw [smul_sub, smul_smul, mul_one_div_cancel (_root_.two_ne_zero : (2 : ℝ) ≠ 0),
            ← one_add_one_eq_two, add_smul],
        simp only [one_smul],
        have eq₁ : wp - wq = a - b := calc
            wp - wq = (u - wq) - (u - wp)    : by rw [sub_sub_assoc_swap, add_sub_assoc, sub_add_sub_cancel']
                ... = a - b                  : rfl,
        have eq₂ : u + u - (wq + wp) = a + b, show u + u - (wq + wp) = (u - wq) + (u - wp), abel,
        rw [eq₁, eq₂],
      end
      ... = 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) : parallelogram_law_with_norm,
    have eq : δ ≤ ∥u - half • (wq + wp)∥,
    { rw smul_add,
      apply δ_le', apply h₂,
        repeat {exact subtype.mem _},
        repeat {exact le_of_lt one_half_pos},
        exact add_halves 1 },
    have eq₁ : 4 * δ * δ ≤ 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥,
    {  mono, mono, norm_num, apply mul_nonneg, norm_num, exact norm_nonneg _ },
    have eq₂ : ∥a∥ * ∥a∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw q) (add_le_add_left (nat.one_div_le_one_div hq) _)),
    have eq₂' : ∥b∥ * ∥b∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw p) (add_le_add_left (nat.one_div_le_one_div hp) _)),
    rw dist_eq_norm,
    apply nonneg_le_nonneg_of_squares_le, { exact sqrt_nonneg _ },
    rw mul_self_sqrt,
    exact calc
      ∥wp - wq∥ * ∥wp - wq∥ = 2 * (∥a∥*∥a∥ + ∥b∥*∥b∥) - 4 * ∥u - half • (wq+wp)∥ * ∥u - half • (wq+wp)∥ :
        by { rw ← this, simp }
      ... ≤ 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) - 4 * δ * δ : sub_le_sub_left eq₁ _
      ... ≤ 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ :
        sub_le_sub_right (mul_le_mul_of_nonneg_left (add_le_add eq₂ eq₂') (by norm_num)) _
      ... = 8 * δ * div + 4 * div * div : by ring,
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) zero_le_δ) (le_of_lt nat.one_div_pos_of_nat))
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt nat.one_div_pos_of_nat)) (le_of_lt nat.one_div_pos_of_nat)),
    -- third goal : `tendsto (λ (n : ℕ), sqrt (b n)) at_top (𝓝 0)`
    apply tendsto.comp,
    { convert continuous_sqrt.continuous_at, exact sqrt_zero.symm },
    have eq₁ : tendsto (λ (n : ℕ), 8 * δ * (1 / (n + 1))) at_top (nhds (0:ℝ)),
    { convert (@tendsto_const_nhds _ _ _ (8 * δ) _).mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    have : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1))) at_top (nhds (0:ℝ)),
    { convert (@tendsto_const_nhds _ _ _ (4:ℝ) _).mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    have eq₂ : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1)) * (1 / (n + 1))) at_top (nhds (0:ℝ)),
    { convert this.mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    convert eq₁.add eq₂, simp only [add_zero] },
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchy_seq_tendsto_of_is_complete h₁ (λ n, _) seq_is_cauchy with ⟨v, hv, w_tendsto⟩,
  use v, use hv,
  have h_cont : continuous (λ v, ∥u - v∥) :=
    continuous.comp continuous_norm (continuous.sub continuous_const continuous_id),
  have : tendsto (λ n, ∥u - w n∥) at_top (nhds ∥u - v∥),
    convert (tendsto.comp h_cont.continuous_at w_tendsto),
  exact tendsto_nhds_unique this norm_tendsto,
  exact subtype.mem _
end

/-- Characterization of minimizers for the projection on a convex set in a real inner product
space. -/
theorem norm_eq_infi_iff_real_inner_le_zero {K : set F} (h : convex K) {u : F} {v : F}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : K, ∥u - w∥) ↔ ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 :=
iff.intro
begin
  assume eq w hw,
  let δ := ⨅ w : K, ∥u - w∥, let p := ⟪u - v, w - v⟫_ℝ, let q := ∥w - v∥^2,
  letI : nonempty K := ⟨⟨v, hv⟩⟩,
  have zero_le_δ : 0 ≤ δ,
    apply le_cinfi, intro, exact norm_nonneg _,
  have δ_le : ∀ w : K, δ ≤ ∥u - w∥,
    assume w, apply cinfi_le, use (0:ℝ), rintros _ ⟨_, rfl⟩, exact norm_nonneg _,
  have δ_le' : ∀ w ∈ K, δ ≤ ∥u - w∥ := assume w hw, δ_le ⟨w, hw⟩,
  have : ∀θ:ℝ, 0 < θ → θ ≤ 1 → 2 * p ≤ θ * q,
    assume θ hθ₁ hθ₂,
    have : ∥u - v∥^2 ≤ ∥u - v∥^2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ*θ*∥w - v∥^2 :=
    calc
      ∥u - v∥^2 ≤ ∥u - (θ•w + (1-θ)•v)∥^2 :
      begin
        simp only [pow_two], apply mul_self_le_mul_self (norm_nonneg _),
        rw [eq], apply δ_le',
        apply h hw hv,
        exacts [le_of_lt hθ₁, sub_nonneg.2 hθ₂, add_sub_cancel'_right _ _],
      end
      ... = ∥(u - v) - θ • (w - v)∥^2 :
      begin
        have : u - (θ•w + (1-θ)•v) = (u - v) - θ • (w - v),
        { rw [smul_sub, sub_smul, one_smul],
          simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add_rev] },
        rw this
      end
      ... = ∥u - v∥^2 - 2 * θ * inner (u - v) (w - v) + θ*θ*∥w - v∥^2 :
      begin
        rw [norm_sub_pow_two, inner_smul_right, norm_smul],
        simp only [pow_two],
        show ∥u-v∥*∥u-v∥-2*(θ*inner(u-v)(w-v))+absR (θ)*∥w-v∥*(absR (θ)*∥w-v∥)=
                ∥u-v∥*∥u-v∥-2*θ*inner(u-v)(w-v)+θ*θ*(∥w-v∥*∥w-v∥),
        rw abs_of_pos hθ₁, ring
      end,
    have eq₁ : ∥u-v∥^2-2*θ*inner(u-v)(w-v)+θ*θ*∥w-v∥^2=∥u-v∥^2+(θ*θ*∥w-v∥^2-2*θ*inner(u-v)(w-v)), abel,
    rw [eq₁, le_add_iff_nonneg_right] at this,
    have eq₂ : θ*θ*∥w-v∥^2-2*θ*inner(u-v)(w-v)=θ*(θ*∥w-v∥^2-2*inner(u-v)(w-v)), ring,
    rw eq₂ at this,
    have := le_of_sub_nonneg (nonneg_of_mul_nonneg_left this hθ₁),
    exact this,
  by_cases hq : q = 0,
  { rw hq at this,
    have : p ≤ 0,
      have := this (1:ℝ) (by norm_num) (by norm_num),
      linarith,
    exact this },
  { have q_pos : 0 < q,
      apply lt_of_le_of_ne, exact pow_two_nonneg _, intro h, exact hq h.symm,
    by_contradiction hp, rw not_le at hp,
    let θ := min (1:ℝ) (p / q),
    have eq₁ : θ*q ≤ p := calc
      θ*q ≤ (p/q) * q : mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_two_nonneg _)
      ... = p : div_mul_cancel _ hq,
    have : 2 * p ≤ p := calc
      2 * p ≤ θ*q : by { refine this θ (lt_min (by norm_num) (div_pos hp q_pos)) (by norm_num) }
      ... ≤ p : eq₁,
    linarith }
end
begin
  assume h,
  letI : nonempty K := ⟨⟨v, hv⟩⟩,
  apply le_antisymm,
  { apply le_cinfi, assume w,
    apply nonneg_le_nonneg_of_squares_le (norm_nonneg _),
    have := h w w.2,
    exact calc
      ∥u - v∥ * ∥u - v∥ ≤ ∥u - v∥ * ∥u - v∥ - 2 * inner (u - v) ((w:F) - v) : by linarith
      ... ≤ ∥u - v∥^2 - 2 * inner (u - v) ((w:F) - v) + ∥(w:F) - v∥^2 :
        by { rw pow_two, refine le_add_of_nonneg_right _, exact pow_two_nonneg _ }
      ... = ∥(u - v) - (w - v)∥^2 : norm_sub_pow_two.symm
      ... = ∥u - w∥ * ∥u - w∥ :
        by { have : (u - v) - (w - v) = u - w, abel, rw [this, pow_two] } },
  { show (⨅ (w : K), ∥u - w∥) ≤ (λw:K, ∥u - w∥) ⟨v, hv⟩,
      apply cinfi_le, use 0, rintros y ⟨z, rfl⟩, exact norm_nonneg _ }
end

/--
Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_infi_of_complete_subspace (K : subspace 𝕜 E)
  (h : is_complete (↑K : set E)) : ∀ u : E, ∃ v ∈ K, ∥u - v∥ = ⨅ w : (K : set E), ∥u - w∥ :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜,
  letI : module ℝ E := restrict_scalars.semimodule ℝ 𝕜 E,
  letI : is_scalar_tower ℝ 𝕜 E := restrict_scalars.is_scalar_tower _ _ _,
  let K' : subspace ℝ E := submodule.restrict_scalars ℝ K,
  exact exists_norm_eq_infi_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex
end

/--
Characterization of minimizers in the projection on a subspace, in the real case.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`).
This is superceded by `norm_eq_infi_iff_inner_eq_zero` that gives the same conclusion over
any `is_R_or_C` field.
-/
theorem norm_eq_infi_iff_real_inner_eq_zero (K : subspace ℝ F) {u : F} {v : F}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : (↑K : set F), ∥u - w∥) ↔ ∀ w ∈ K, ⟪u - v, w⟫_ℝ = 0 :=
iff.intro
begin
  assume h,
  have h : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0,
  { rwa [norm_eq_infi_iff_real_inner_le_zero] at h, exacts [K.convex, hv] },
  assume w hw,
  have le : ⟪u - v, w⟫_ℝ ≤ 0,
    let w' := w + v,
    have : w' ∈ K := submodule.add_mem _ hw hv,
    have h₁ := h w' this,
    have h₂ : w' - v = w, simp only [add_neg_cancel_right, sub_eq_add_neg],
    rw h₂ at h₁, exact h₁,
  have ge : ⟪u - v, w⟫_ℝ ≥ 0,
    let w'' := -w + v,
    have : w'' ∈ K := submodule.add_mem _ (submodule.neg_mem _ hw) hv,
    have h₁ := h w'' this,
    have h₂ : w'' - v = -w, simp only [neg_inj, add_neg_cancel_right, sub_eq_add_neg],
    rw [h₂, inner_neg_right] at h₁,
    linarith,
    exact le_antisymm le ge
end
begin
  assume h,
  have : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0,
    assume w hw,
    let w' := w - v,
    have : w' ∈ K := submodule.sub_mem _ hw hv,
    have h₁ := h w' this,
    exact le_of_eq h₁,
  rwa norm_eq_infi_iff_real_inner_le_zero,
  exacts [submodule.convex _, hv]
end

/--
Characterization of minimizers in the projection on a subspace.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_infi_iff_inner_eq_zero (K : subspace 𝕜 E) {u : E} {v : E}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : (↑K : set E), ∥u - w∥) ↔ ∀ w ∈ K, ⟪u - v, w⟫ = 0 :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜,
  letI : module ℝ E := restrict_scalars.semimodule ℝ 𝕜 E,
  letI : is_scalar_tower ℝ 𝕜 E := restrict_scalars.is_scalar_tower _ _ _,
  let K' : subspace ℝ E := K.restrict_scalars ℝ,
  split,
  { assume H,
    have A : ∀ w ∈ K, re ⟪u - v, w⟫ = 0 := (norm_eq_infi_iff_real_inner_eq_zero K' hv).1 H,
    assume w hw,
    apply ext,
    { simp [A w hw] },
    { symmetry, calc
      im (0 : 𝕜) = 0 : im.map_zero
      ... = re ⟪u - v, (-I) • w⟫ : (A _ (K.smul_mem (-I) hw)).symm
      ... = re ((-I) * ⟪u - v, w⟫) : by rw inner_smul_right
      ... = im ⟪u - v, w⟫ : by simp } },
  { assume H,
    have : ∀ w ∈ K', ⟪u - v, w⟫_ℝ = 0,
    { assume w hw,
      rw [real_inner_eq_re_inner, H w hw],
      exact zero_re' },
    exact (norm_eq_infi_iff_real_inner_eq_zero K' hv).2 this }
end

/-- The orthogonal projection onto a complete subspace, as an
unbundled function.  This definition is only intended for use in
setting up the bundled version `orthogonal_projection` and should not
be used once that is defined. -/
def orthogonal_projection_fn {K : subspace 𝕜 E} (h : is_complete (K : set E)) (v : E) :=
(exists_norm_eq_infi_of_complete_subspace K h v).some

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
lemma orthogonal_projection_fn_mem {K : submodule 𝕜 E} (h : is_complete (K : set E)) (v : E) :
  orthogonal_projection_fn h v ∈ K :=
(exists_norm_eq_infi_of_complete_subspace K h v).some_spec.some

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
lemma orthogonal_projection_fn_inner_eq_zero {K : submodule 𝕜 E} (h : is_complete (K : set E))
  (v : E) : ∀ w ∈ K, ⟪v - orthogonal_projection_fn h v, w⟫ = 0 :=
begin
  rw ←norm_eq_infi_iff_inner_eq_zero K (orthogonal_projection_fn_mem h v),
  exact (exists_norm_eq_infi_of_complete_subspace K h v).some_spec.some_spec
end

/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property.  This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
lemma eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero {K : submodule 𝕜 E}
  (h : is_complete (K : set E)) {u v : E} (hvm : v ∈ K) (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) :
  v = orthogonal_projection_fn h u :=
begin
  rw [←sub_eq_zero, ←inner_self_eq_zero],
  have hvs : v - orthogonal_projection_fn h u ∈ K :=
    submodule.sub_mem K hvm (orthogonal_projection_fn_mem h u),
  have huo : ⟪u - orthogonal_projection_fn h u, v - orthogonal_projection_fn h u⟫ = 0 :=
    orthogonal_projection_fn_inner_eq_zero h u _ hvs,
  have huv : ⟪u - v, v - orthogonal_projection_fn h u⟫ = 0 := hvo _ hvs,
  have houv : ⟪(u - orthogonal_projection_fn h u) - (u - v), v - orthogonal_projection_fn h u⟫ = 0,
  { rw [inner_sub_left, huo, huv, sub_zero] },
  rwa sub_sub_sub_cancel_left at houv
end

/-- The orthogonal projection onto a complete subspace.  For most
purposes, `orthogonal_projection`, which removes the `is_complete`
hypothesis and is the identity map when the subspace is not complete,
should be used instead. -/
def orthogonal_projection_of_complete {K : submodule 𝕜 E} (h : is_complete (K : set E)) :
  linear_map 𝕜 E E :=
{ to_fun := orthogonal_projection_fn h,
  map_add' := λ x y, begin
    have hm : orthogonal_projection_fn h x + orthogonal_projection_fn h y ∈ K :=
      submodule.add_mem K (orthogonal_projection_fn_mem h x) (orthogonal_projection_fn_mem h y),
    have ho :
      ∀ w ∈ K, ⟪x + y - (orthogonal_projection_fn h x + orthogonal_projection_fn h y), w⟫ = 0,
    { intros w hw,
      rw [add_sub_comm, inner_add_left, orthogonal_projection_fn_inner_eq_zero h _ w hw,
          orthogonal_projection_fn_inner_eq_zero h _ w hw, add_zero] },
    rw eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero h hm ho
  end,
  map_smul' := λ c x, begin
    have hm : c • orthogonal_projection_fn h x ∈ K :=
      submodule.smul_mem K _ (orthogonal_projection_fn_mem h x),
    have ho : ∀ w ∈ K, ⟪c • x - c • orthogonal_projection_fn h x, w⟫ = 0,
    { intros w hw,
      rw [←smul_sub, inner_smul_left, orthogonal_projection_fn_inner_eq_zero h _ w hw, mul_zero] },
    rw eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero h hm ho
  end }

/-- The orthogonal projection onto a subspace, which is expected to be
complete.  If the subspace is not complete, this uses the identity map
instead. -/
def orthogonal_projection (K : submodule 𝕜 E) : linear_map 𝕜 E E :=
if h : is_complete (K : set E) then orthogonal_projection_of_complete h else linear_map.id

/-- The definition of `orthogonal_projection` using `if`. -/
lemma orthogonal_projection_def (K : submodule 𝕜 E) :
  orthogonal_projection K =
    if h : is_complete (K : set E) then orthogonal_projection_of_complete h else linear_map.id :=
rfl

@[simp]
lemma orthogonal_projection_fn_eq {K : submodule 𝕜 E} (h : is_complete (K : set E)) (v : E) :
  orthogonal_projection_fn h v = orthogonal_projection K v :=
by { rw [orthogonal_projection_def, dif_pos h], refl }

/-- The orthogonal projection is in the given subspace. -/
lemma orthogonal_projection_mem {K : submodule 𝕜 E} (h : is_complete (K : set E)) (v : E) :
  orthogonal_projection K v ∈ K :=
begin
  rw ←orthogonal_projection_fn_eq h,
  exact orthogonal_projection_fn_mem h v
end

/-- The characterization of the orthogonal projection.  -/
@[simp]
lemma orthogonal_projection_inner_eq_zero (K : submodule 𝕜 E) (v : E) :
  ∀ w ∈ K, ⟪v - orthogonal_projection K v, w⟫ = 0 :=
begin
  simp_rw orthogonal_projection_def,
  split_ifs,
  { exact orthogonal_projection_fn_inner_eq_zero h v },
  { simp },
end

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
lemma eq_orthogonal_projection_of_mem_of_inner_eq_zero {K : submodule 𝕜 E}
  (h : is_complete (K : set E)) {u v : E} (hvm : v ∈ K) (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) :
  v = orthogonal_projection K u :=
begin
  rw ←orthogonal_projection_fn_eq h,
  exact eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero h hvm hvo
end

/-- The subspace of vectors orthogonal to a given subspace. -/
def submodule.orthogonal (K : submodule 𝕜 E) : submodule 𝕜 E :=
{ carrier := {v | ∀ u ∈ K, ⟪u, v⟫ = 0},
  zero_mem' := λ _ _, inner_zero_right,
  add_mem' := λ x y hx hy u hu, by rw [inner_add_right, hx u hu, hy u hu, add_zero],
  smul_mem' := λ c x hx u hu, by rw [inner_smul_right, hx u hu, mul_zero] }

/-- When a vector is in `K.orthogonal`. -/
lemma submodule.mem_orthogonal (K : submodule 𝕜 E) (v : E) :
  v ∈ K.orthogonal ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 :=
iff.rfl

/-- When a vector is in `K.orthogonal`, with the inner product the
other way round. -/
lemma submodule.mem_orthogonal' (K : submodule 𝕜 E) (v : E) :
  v ∈ K.orthogonal ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 :=
by simp_rw [submodule.mem_orthogonal, inner_eq_zero_sym]

/-- A vector in `K` is orthogonal to one in `K.orthogonal`. -/
lemma submodule.inner_right_of_mem_orthogonal {u v : E} {K : submodule 𝕜 E} (hu : u ∈ K)
    (hv : v ∈ K.orthogonal) : ⟪u, v⟫ = 0 :=
(K.mem_orthogonal v).1 hv u hu

/-- A vector in `K.orthogonal` is orthogonal to one in `K`. -/
lemma submodule.inner_left_of_mem_orthogonal {u v : E} {K : submodule 𝕜 E} (hu : u ∈ K)
    (hv : v ∈ K.orthogonal) : ⟪v, u⟫ = 0 :=
by rw [inner_eq_zero_sym]; exact submodule.inner_right_of_mem_orthogonal hu hv

/-- `K` and `K.orthogonal` have trivial intersection. -/
lemma submodule.orthogonal_disjoint (K : submodule 𝕜 E) : disjoint K K.orthogonal :=
begin
  simp_rw [submodule.disjoint_def, submodule.mem_orthogonal],
  exact λ x hx ho, inner_self_eq_zero.1 (ho x hx)
end

variables (𝕜 E)

/-- `submodule.orthogonal` gives a `galois_connection` between
`submodule 𝕜 E` and its `order_dual`. -/
lemma submodule.orthogonal_gc :
  @galois_connection (submodule 𝕜 E) (order_dual $ submodule 𝕜 E) _ _
    submodule.orthogonal submodule.orthogonal :=
λ K₁ K₂, ⟨λ h v hv u hu, submodule.inner_left_of_mem_orthogonal hv (h hu),
          λ h v hv u hu, submodule.inner_left_of_mem_orthogonal hv (h hu)⟩

variables {𝕜 E}

/-- `submodule.orthogonal` reverses the `≤` ordering of two
subspaces. -/
lemma submodule.orthogonal_le {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) :
  K₂.orthogonal ≤ K₁.orthogonal :=
(submodule.orthogonal_gc 𝕜 E).monotone_l h


/-- `K` is contained in `K.orthogonal.orthogonal`. -/
lemma submodule.le_orthogonal_orthogonal (K : submodule 𝕜 E) : K ≤ K.orthogonal.orthogonal :=
(submodule.orthogonal_gc 𝕜 E).le_u_l _

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
lemma submodule.inf_orthogonal (K₁ K₂ : submodule 𝕜 E) :
  K₁.orthogonal ⊓ K₂.orthogonal = (K₁ ⊔ K₂).orthogonal :=
(submodule.orthogonal_gc 𝕜 E).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
lemma submodule.infi_orthogonal {ι : Type*} (K : ι → submodule 𝕜 E) :
  (⨅ i, (K i).orthogonal) = (supr K).orthogonal :=
(submodule.orthogonal_gc 𝕜 E).l_supr.symm

/-- The inf of a set of orthogonal subspaces equals the subspace
orthogonal to the sup. -/
lemma submodule.Inf_orthogonal (s : set $ submodule 𝕜 E) :
  (⨅ K ∈ s, submodule.orthogonal K) = (Sup s).orthogonal :=
(submodule.orthogonal_gc 𝕜 E).l_Sup.symm

/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁.orthogonal ⊓ K₂` span `K₂`. -/
lemma submodule.sup_orthogonal_inf_of_is_complete {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂)
  (hc : is_complete (K₁ : set E)) : K₁ ⊔ (K₁.orthogonal ⊓ K₂) = K₂ :=
begin
  ext x,
  rw submodule.mem_sup,
  rcases exists_norm_eq_infi_of_complete_subspace K₁ hc x with ⟨v, hv, hvm⟩,
  rw norm_eq_infi_iff_inner_eq_zero K₁ hv at hvm,
  split,
  { rintro ⟨y, hy, z, hz, rfl⟩,
    exact K₂.add_mem (h hy) hz.2 },
  { exact λ hx, ⟨v, hv, x - v, ⟨(K₁.mem_orthogonal' _).2 hvm, K₂.sub_mem hx (h hv)⟩,
                 add_sub_cancel'_right _ _⟩ }
end

/-- If `K` is complete, `K` and `K.orthogonal` span the whole
space. -/
lemma submodule.sup_orthogonal_of_is_complete {K : submodule 𝕜 E} (h : is_complete (K : set E)) :
  K ⊔ K.orthogonal = ⊤ :=
begin
  convert submodule.sup_orthogonal_inf_of_is_complete (le_top : K ≤ ⊤) h,
  simp
end

/-- If `K` is complete, `K` and `K.orthogonal` are complements of each
other. -/
lemma submodule.is_compl_orthogonal_of_is_complete {K : submodule 𝕜 E}
    (h : is_complete (K : set E)) : is_compl K K.orthogonal :=
⟨K.orthogonal_disjoint, le_of_eq (submodule.sup_orthogonal_of_is_complete h).symm⟩

@[simp] lemma submodule.top_orthogonal_eq_bot : (⊤ : submodule 𝕜 E).orthogonal = ⊥ :=
begin
  ext,
  rw [submodule.mem_bot, submodule.mem_orthogonal],
  exact ⟨λ h, inner_self_eq_zero.mp (h x submodule.mem_top), by { rintro rfl, simp }⟩
end

@[simp] lemma submodule.bot_orthogonal_eq_top : (⊥ : submodule 𝕜 E).orthogonal = ⊤ :=
begin
  rw [← submodule.top_orthogonal_eq_bot, eq_top_iff],
  exact submodule.le_orthogonal_orthogonal ⊤
end

lemma submodule.eq_top_iff_orthogonal_eq_bot {K : submodule 𝕜 E} (hK : is_complete (K : set E)) :
  K = ⊤ ↔ K.orthogonal = ⊥ :=
begin
  refine ⟨by { rintro rfl, exact submodule.top_orthogonal_eq_bot }, _⟩,
  intro h,
  have : K ⊔ K.orthogonal = ⊤ := submodule.sup_orthogonal_of_is_complete hK,
  rwa [h, sup_comm, bot_sup_eq] at this,
end

open finite_dimensional

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
lemma submodule.findim_add_inf_findim_orthogonal {K₁ K₂ : submodule 𝕜 E}
  [finite_dimensional 𝕜 K₂] (h : K₁ ≤ K₂) :
  findim 𝕜 K₁ + findim 𝕜 (K₁.orthogonal ⊓ K₂ : submodule 𝕜 E) = findim 𝕜 K₂ :=
begin
  haveI := submodule.finite_dimensional_of_le h,
  have hd := submodule.dim_sup_add_dim_inf_eq K₁ (K₁.orthogonal ⊓ K₂),
  rw [←inf_assoc, (submodule.orthogonal_disjoint K₁).eq_bot, bot_inf_eq, findim_bot,
      submodule.sup_orthogonal_inf_of_is_complete h
        (submodule.complete_of_finite_dimensional _)] at hd,
  rw add_zero at hd,
  exact hd.symm
end
end orthogonal
