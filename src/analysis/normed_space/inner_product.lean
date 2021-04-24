/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis, Heather Macbeth
-/

import linear_algebra.bilinear_form
import linear_algebra.sesquilinear_form
import topology.metric_space.pi_Lp
import data.complex.is_R_or_C
import analysis.special_functions.sqrt

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
- We define `orthonormal`, a predicate on a function `v : ι → E`.  We prove the existence of a
  maximal orthonormal set, `exists_maximal_orthonormal`, and also prove that a maximal orthonormal
  set is a basis (`maximal_orthonormal_iff_is_basis_of_finite_dimensional`), if `E` is finite-
  dimensional, or in general (`maximal_orthonormal_iff_dense_span`) a set whose span is dense
  (i.e., a Hilbert basis, although we do not make that definition).

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `real_inner_product_space`, `complex_inner_product_space`,
which respectively introduce the plain notation `⟪·, ·⟫` for the the real and complex inner product.

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

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

open is_R_or_C real filter
open_locale big_operators classical topological_space

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
(add_left  : ∀ x y z, inner (x + y) z = inner x z + inner y z)
(smul_left : ∀ x y r, inner (r • x) y = (conj r) * inner x y)

attribute [nolint dangerous_instance] inner_product_space.to_normed_group
-- note [is_R_or_C instance]

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

lemma inner_self_nonneg_im {x : F} : im ⟪x, x⟫ = 0 :=
by rw [← @of_real_inj 𝕜, im_eq_conj_sub]; simp [inner_conj_sym]

lemma inner_self_im_zero {x : F} : im ⟪x, x⟫ = 0 :=
inner_self_nonneg_im

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
    rw [conj_mul_eq_norm_sq_left, of_real_mul_re, sqrt_mul, ←inner_norm_sq_eq_inner_self,
        of_real_re],
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

@[simp] lemma inner_conj_sym (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ := inner_product_space.conj_sym _ _
lemma real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := inner_conj_sym x y

lemma inner_eq_zero_sym {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 :=
⟨λ h, by simp [←inner_conj_sym, h], λ h, by simp [←inner_conj_sym, h]⟩

@[simp] lemma inner_self_nonneg_im {x : E} : im ⟪x, x⟫ = 0 :=
by rw [← @of_real_inj 𝕜, im_eq_conj_sub]; simp

lemma inner_self_im_zero {x : E} : im ⟪x, x⟫ = 0 := inner_self_nonneg_im

lemma inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
inner_product_space.add_left _ _ _

lemma inner_add_right {x y z : E} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
by { rw [←inner_conj_sym, inner_add_left, ring_hom.map_add], simp only [inner_conj_sym] }

lemma inner_re_symm {x y : E} : re ⟪x, y⟫ = re ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_re]

lemma inner_im_symm {x y : E} : im ⟪x, y⟫ = -im ⟪y, x⟫ :=
by rw [←inner_conj_sym, conj_im]

lemma inner_smul_left {x y : E} {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
inner_product_space.smul_left _ _ _
lemma real_inner_smul_left {x y : F} {r : ℝ} : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ := inner_smul_left

lemma inner_smul_real_left {x y : E} {r : ℝ} : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ :=
by { rw [inner_smul_left, conj_of_real, algebra.smul_def], refl }

lemma inner_smul_right {x y : E} {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ :=
by rw [←inner_conj_sym, inner_smul_left, ring_hom.map_mul, conj_conj, inner_conj_sym]
lemma real_inner_smul_right {x y : F} {r : ℝ} : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ := inner_smul_right

lemma inner_smul_real_right {x y : E} {r : ℝ} : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ :=
by { rw [inner_smul_right, algebra.smul_def], refl }

/-- The inner product as a sesquilinear form. -/
@[simps]
def sesq_form_of_inner : sesq_form 𝕜 E (conj_to_ring_equiv 𝕜) :=
{ sesq := λ x y, ⟪y, x⟫,    -- Note that sesquilinear forms are linear in the first argument
  sesq_add_left := λ x y z, inner_add_right,
  sesq_add_right := λ x y z, inner_add_left,
  sesq_smul_left := λ r x y, inner_smul_right,
  sesq_smul_right := λ r x y, inner_smul_left }

/-- The real inner product as a bilinear form. -/
@[simps]
def bilin_form_of_real_inner : bilin_form ℝ F :=
{ bilin := inner,
  bilin_add_left := λ x y z, inner_add_left,
  bilin_smul_left := λ a x y, inner_smul_left,
  bilin_add_right := λ x y z, inner_add_right,
  bilin_smul_right := λ a x y, inner_smul_right }

/-- An inner product with a sum on the left. -/
lemma sum_inner {ι : Type*} (s : finset ι) (f : ι → E) (x : E) :
  ⟪∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫ :=
sesq_form.sum_right (sesq_form_of_inner) _ _ _

/-- An inner product with a sum on the right. -/
lemma inner_sum {ι : Type*} (s : finset ι) (f : ι → E) (x : E) :
  ⟪x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫ :=
sesq_form.sum_left (sesq_form_of_inner) _ _ _

/-- An inner product with a sum on the left, `finsupp` version. -/
lemma finsupp.sum_inner {ι : Type*} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
  ⟪l.sum (λ (i : ι) (a : 𝕜), a • v i), x⟫
  = l.sum (λ (i : ι) (a : 𝕜), (is_R_or_C.conj a) • ⟪v i, x⟫) :=
by { convert sum_inner l.support (λ a, l a • v a) x, simp [inner_smul_left, finsupp.sum] }

/-- An inner product with a sum on the right, `finsupp` version. -/
lemma finsupp.inner_sum {ι : Type*} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
  ⟪x, l.sum (λ (i : ι) (a : 𝕜), a • v i)⟫ = l.sum (λ (i : ι) (a : 𝕜), a • ⟪x, v i⟫) :=
by { convert inner_sum l.support (λ a, l a • v a) x, simp [inner_smul_right, finsupp.sum] }

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

lemma inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (∥x∥ ^ 2 : 𝕜) :=
begin
  suffices : (is_R_or_C.re ⟪x, x⟫ : 𝕜) = ∥x∥ ^ 2,
  { simpa [inner_self_re_to_K] using this },
  exact_mod_cast (norm_sq_eq_inner x).symm
end

lemma inner_self_re_abs {x : E} : re ⟪x, x⟫ = abs ⟪x, x⟫ :=
begin
  conv_rhs { rw [←inner_self_re_to_K] },
  symmetry,
  exact is_R_or_C.abs_of_nonneg inner_self_nonneg,
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

section orthonormal_sets
variables {ι : Type*} (𝕜)

include 𝕜

/-- An orthonormal set of vectors in an `inner_product_space` -/
def orthonormal (v : ι → E) : Prop :=
(∀ i, ∥v i∥ = 1) ∧ (∀ {i j}, i ≠ j → ⟪v i, v j⟫ = 0)

omit 𝕜

variables {𝕜}

/-- `if ... then ... else` characterization of an indexed set of vectors being orthonormal.  (Inner
product equals Kronecker delta.) -/
lemma orthonormal_iff_ite {v : ι → E} :
  orthonormal 𝕜 v ↔ ∀ i j, ⟪v i, v j⟫ = if i = j then (1:𝕜) else (0:𝕜) :=
begin
  split,
  { intros hv i j,
    split_ifs,
    { simp [h, inner_self_eq_norm_sq_to_K, hv.1] },
    { exact hv.2 h } },
  { intros h,
    split,
    { intros i,
      have h' : ∥v i∥ ^ 2 = 1 ^ 2 := by simp [norm_sq_eq_inner, h i i],
      have h₁ : 0 ≤ ∥v i∥ := norm_nonneg _,
      have h₂ : (0:ℝ) ≤ 1 := by norm_num,
      rwa eq_of_pow_two_eq_pow_two h₁ h₂ at h' },
    { intros i j hij,
      simpa [hij] using h i j } }
end

/-- `if ... then ... else` characterization of a set of vectors being orthonormal.  (Inner product
equals Kronecker delta.) -/
theorem orthonormal_subtype_iff_ite {s : set E} :
  orthonormal 𝕜 (coe : s → E) ↔
  (∀ v ∈ s, ∀ w ∈ s, ⟪v, w⟫ = if v = w then 1 else 0) :=
begin
  rw orthonormal_iff_ite,
  split,
  { intros h v hv w hw,
    convert h ⟨v, hv⟩ ⟨w, hw⟩ using 1,
    simp },
  { rintros h ⟨v, hv⟩ ⟨w, hw⟩,
    convert h v hv w hw using 1,
    simp }
end

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_right_finsupp {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
  ⟪v i, finsupp.total ι E 𝕜 v l⟫ = l i :=
by simp [finsupp.total_apply, finsupp.inner_sum, orthonormal_iff_ite.mp hv]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_right_fintype [fintype ι]
  {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι → 𝕜) (i : ι) :
  ⟪v i, ∑ i : ι, (l i) • (v i)⟫ = l i :=
by simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_left_finsupp {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
  ⟪finsupp.total ι E 𝕜 v l, v i⟫ = conj (l i) :=
by rw [← inner_conj_sym, hv.inner_right_finsupp]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
lemma orthonormal.inner_left_fintype [fintype ι]
  {v : ι → E} (hv : orthonormal 𝕜 v) (l : ι → 𝕜) (i : ι) :
  ⟪∑ i : ι, (l i) • (v i), v i⟫ = conj (l i) :=
by simp [sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv]

/-- An orthonormal set is linearly independent. -/
lemma orthonormal.linear_independent {v : ι → E} (hv : orthonormal 𝕜 v) :
  linear_independent 𝕜 v :=
begin
  rw linear_independent_iff,
  intros l hl,
  ext i,
  have key : ⟪v i, finsupp.total ι E 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw hl,
  simpa [hv.inner_right_finsupp] using key
end

/-- A subfamily of an orthonormal family (i.e., a composition with an injective map) is an
orthonormal family. -/
lemma orthonormal.comp
  {ι' : Type*} {v : ι → E} (hv : orthonormal 𝕜 v) (f : ι' → ι) (hf : function.injective f) :
  orthonormal 𝕜 (v ∘ f) :=
begin
  rw orthonormal_iff_ite at ⊢ hv,
  intros i j,
  convert hv (f i) (f j) using 1,
  simp [hf.eq_iff]
end

/-- A linear combination of some subset of an orthonormal set is orthogonal to other members of the
set. -/
lemma orthonormal.inner_finsupp_eq_zero
  {v : ι → E} (hv : orthonormal 𝕜 v) {s : set ι} {i : ι} (hi : i ∉ s) {l : ι →₀ 𝕜}
  (hl : l ∈ finsupp.supported 𝕜 𝕜 s) :
  ⟪finsupp.total ι E 𝕜 v l, v i⟫ = 0 :=
begin
  rw finsupp.mem_supported' at hl,
  simp [hv.inner_left_finsupp, hl i hi],
end

/- The material that follows, culminating in the existence of a maximal orthonormal subset, is
adapted from the corresponding development of the theory of linearly independents sets.  See
`exists_linear_independent` in particular. -/

variables (𝕜 E)
lemma orthonormal_empty : orthonormal 𝕜 (λ x, x : (∅ : set E) → E) :=
by simp [orthonormal_subtype_iff_ite]
variables {𝕜 E}

lemma orthonormal_Union_of_directed
  {η : Type*} {s : η → set E} (hs : directed (⊆) s) (h : ∀ i, orthonormal 𝕜 (λ x, x : s i → E)) :
  orthonormal 𝕜 (λ x, x : (⋃ i, s i) → E) :=
begin
  rw orthonormal_subtype_iff_ite,
  rintros x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩,
  obtain ⟨k, hik, hjk⟩ := hs i j,
  have h_orth : orthonormal 𝕜 (λ x, x : (s k) → E) := h k,
  rw orthonormal_subtype_iff_ite at h_orth,
  exact h_orth x (hik hxi) y (hjk hyj)
end

lemma orthonormal_sUnion_of_directed
  {s : set (set E)} (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, orthonormal 𝕜 (λ x, x : (a : set E) → E)) :
  orthonormal 𝕜 (λ x, x : (⋃₀ s) → E) :=
by rw set.sUnion_eq_Union; exact orthonormal_Union_of_directed hs.directed_coe (by simpa using h)

/-- Given an orthonormal set `v` of vectors in `E`, there exists a maximal orthonormal set
containing it. -/
lemma exists_maximal_orthonormal {s : set E} (hs : orthonormal 𝕜 (coe : s → E)) :
  ∃ w ⊇ s, orthonormal 𝕜 (coe : w → E) ∧ ∀ u ⊇ w, orthonormal 𝕜 (coe : u → E) → u = w :=
begin
  rcases zorn.zorn_subset₀ {b | orthonormal 𝕜 (coe : b → E)} _ _ hs  with ⟨b, bi, sb, h⟩,
  { refine ⟨b, sb, bi, _⟩,
    exact λ u hus hu, h u hu hus },
  { refine λ c hc cc c0, ⟨⋃₀ c, _, _⟩,
    { exact orthonormal_sUnion_of_directed cc.directed_on (λ x xc, hc xc) },
    { exact λ _, set.subset_sUnion_of_mem } }
end

lemma orthonormal.ne_zero {v : ι → E} (hv : orthonormal 𝕜 v) (i : ι) : v i ≠ 0 :=
begin
  have : ∥v i∥ ≠ 0,
  { rw hv.1 i,
    norm_num },
  simpa using this
end

open finite_dimensional

lemma is_basis_of_orthonormal_of_card_eq_findim [fintype ι] [nonempty ι] {v : ι → E}
  (hv : orthonormal 𝕜 v) (card_eq : fintype.card ι = findim 𝕜 E) :
  is_basis 𝕜 v :=
is_basis_of_linear_independent_of_card_eq_findim hv.linear_independent card_eq

end orthonormal_sets

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
norm_sub_pow_two

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

/-- Cauchy–Schwarz inequality with norm -/
lemma real_inner_le_norm (x y : F) : ⟪x, y⟫_ℝ ≤ ∥x∥ * ∥y∥ :=
le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)

include 𝕜
lemma parallelogram_law_with_norm {x y : E} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
begin
  simp only [← inner_self_eq_norm_square],
  rw[← re.map_add, parallelogram_law, two_mul, two_mul],
  simp only [re.map_add],
end
omit 𝕜

lemma parallelogram_law_with_norm_real {x y : F} :
  ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
by { have h := @parallelogram_law_with_norm ℝ F _ _ x y, simpa using h }

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
lemma re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
  re ⟪x, y⟫ = (∥x + y∥ * ∥x + y∥ - ∥x∥ * ∥x∥ - ∥y∥ * ∥y∥) / 2 :=
by { rw norm_add_mul_self, ring }

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
lemma re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
  re ⟪x, y⟫ = (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - ∥x - y∥ * ∥x - y∥) / 2 :=
by { rw [norm_sub_mul_self], ring }

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
lemma re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
  re ⟪x, y⟫ = (∥x + y∥ * ∥x + y∥ - ∥x - y∥ * ∥x - y∥) / 4 :=
by { rw [norm_add_mul_self, norm_sub_mul_self], ring }

/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
lemma im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four (x y : E) :
  im ⟪x, y⟫ = (∥x - IK • y∥ * ∥x - IK • y∥ - ∥x + IK • y∥ * ∥x + IK • y∥) / 4 :=
by { simp only [norm_add_mul_self, norm_sub_mul_self, inner_smul_right, I_mul_re], ring }

/-- Polarization identity: The inner product, in terms of the norm. -/
lemma inner_eq_sum_norm_sq_div_four (x y : E) :
  ⟪x, y⟫ = (∥x + y∥ ^ 2 - ∥x - y∥ ^ 2 + (∥x - IK • y∥ ^ 2 - ∥x + IK • y∥ ^ 2) * IK) / 4 :=
begin
  rw [← re_add_im ⟪x, y⟫, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four],
  push_cast,
  simp only [pow_two, ← mul_div_right_comm, ← add_div]
end

section

variables {E' : Type*} [inner_product_space 𝕜 E']

/-- A linear isometry preserves the inner product. -/
@[simp] lemma linear_isometry.inner_map_map (f : E →ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
by simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]

/-- A linear isometric equivalence preserves the inner product. -/
@[simp] lemma linear_isometry_equiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) :
  ⟪f x, f y⟫ = ⟪x, y⟫ :=
f.to_linear_isometry.inner_map_map x y

/-- A linear map that preserves the inner product is a linear isometry. -/
def linear_map.isometry_of_inner (f : E →ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[𝕜] E' :=
⟨f, λ x, by simp only [norm_eq_sqrt_inner, h]⟩

@[simp] lemma linear_map.coe_isometry_of_inner (f : E →ₗ[𝕜] E') (h) :
  ⇑(f.isometry_of_inner h) = f := rfl

@[simp] lemma linear_map.isometry_of_inner_to_linear_map (f : E →ₗ[𝕜] E') (h) :
  (f.isometry_of_inner h).to_linear_map = f := rfl

/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
def linear_equiv.isometry_of_inner (f : E ≃ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) :
  E ≃ₗᵢ[𝕜] E' :=
⟨f, ((f : E →ₗ[𝕜] E').isometry_of_inner h).norm_map⟩

@[simp] lemma linear_equiv.coe_isometry_of_inner (f : E ≃ₗ[𝕜] E') (h) :
  ⇑(f.isometry_of_inner h) = f := rfl

@[simp] lemma linear_equiv.isometry_of_inner_to_linear_equiv (f : E ≃ₗ[𝕜] E') (h) :
  (f.isometry_of_inner h).to_linear_equiv = f := rfl

end

/-- Polarization identity: The real inner product, in terms of the norm. -/
lemma real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
  ⟪x, y⟫_ℝ = (∥x + y∥ * ∥x + y∥ - ∥x∥ * ∥x∥ - ∥y∥ * ∥y∥) / 2 :=
re_to_real.symm.trans $
  re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

/-- Polarization identity: The real inner product, in terms of the norm. -/
lemma real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
  ⟪x, y⟫_ℝ = (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - ∥x - y∥ * ∥x - y∥) / 2 :=
re_to_real.symm.trans $
  re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

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
    rw [_root_.abs_mul, _root_.abs_of_nonneg (norm_nonneg x), _root_.abs_of_nonneg (norm_nonneg y),
        mul_one] }
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
  rw [inner_smul_right, is_R_or_C.abs_mul, ←inner_self_re_abs, inner_self_eq_norm_square,
      norm_smul],
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
      norm_num at h, },
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
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
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

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ∥x∥ * ∥y∥`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
lemma inner_eq_norm_mul_iff {x y : E} :
  ⟪x, y⟫ = (∥x∥ : 𝕜) * ∥y∥ ↔ (∥y∥ : 𝕜) • x = (∥x∥ : 𝕜) • y :=
begin
  by_cases h : (x = 0 ∨ y = 0), -- WLOG `x` and `y` are nonzero
  { cases h; simp [h] },
  calc ⟪x, y⟫ = (∥x∥ : 𝕜) * ∥y∥ ↔ ∥x∥ * ∥y∥ = re ⟪x, y⟫ :
  begin
    norm_cast,
    split,
    { intros h',
      simp [h'] },
    { have cauchy_schwarz := abs_inner_le_norm x y,
      intros h',
      rw h' at ⊢ cauchy_schwarz,
      rwa re_eq_self_of_le }
  end
  ... ↔ 2 * ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥ - re ⟪x, y⟫) = 0 :
    by simp [h, show (2:ℝ) ≠ 0, by norm_num, sub_eq_zero]
  ... ↔ ∥(∥y∥:𝕜) • x - (∥x∥:𝕜) • y∥ * ∥(∥y∥:𝕜) • x - (∥x∥:𝕜) • y∥ = 0 :
  begin
    simp only [norm_sub_mul_self, inner_smul_left, inner_smul_right, norm_smul, conj_of_real,
      is_R_or_C.norm_eq_abs, abs_of_real, of_real_im, of_real_re, mul_re, abs_norm_eq_norm],
    refine eq.congr _ rfl,
    ring
  end
  ... ↔ (∥y∥ : 𝕜) • x = (∥x∥ : 𝕜) • y : by simp [norm_sub_eq_zero_iff]
end

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ∥x∥ * ∥y∥`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
lemma inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ = ∥x∥ * ∥y∥ ↔ ∥y∥ • x = ∥x∥ • y :=
inner_eq_norm_mul_iff

/-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
the equality case for Cauchy-Schwarz. -/
lemma inner_eq_norm_mul_iff_of_norm_one {x y : E} (hx : ∥x∥ = 1) (hy : ∥y∥ = 1) :
  ⟪x, y⟫ = 1 ↔ x = y :=
by { convert inner_eq_norm_mul_iff using 2; simp [hx, hy] }

lemma inner_lt_norm_mul_iff_real {x y : F} :
  ⟪x, y⟫_ℝ < ∥x∥ * ∥y∥ ↔ ∥y∥ • x ≠ ∥x∥ • y :=
calc ⟪x, y⟫_ℝ < ∥x∥ * ∥y∥
    ↔ ⟪x, y⟫_ℝ ≠ ∥x∥ * ∥y∥ : ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
... ↔ ∥y∥ • x ≠ ∥x∥ • y : not_congr inner_eq_norm_mul_iff_real

/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
lemma inner_lt_one_iff_real_of_norm_one {x y : F} (hx : ∥x∥ = 1) (hy : ∥y∥ = 1) :
  ⟪x, y⟫_ℝ < 1 ↔ x ≠ y :=
by { convert inner_lt_norm_mul_iff_real; simp [hx, hy] }

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

/-- The inner product with a fixed left element, as a continuous linear map.  This can be upgraded
to a continuous map which is jointly conjugate-linear in the left argument and linear in the right
argument, once (TODO) conjugate-linear maps have been defined. -/
def inner_right (v : E) : E →L[𝕜] 𝕜 :=
linear_map.mk_continuous
  { to_fun := λ w, ⟪v, w⟫,
    map_add' := λ x y, inner_add_right,
    map_smul' := λ c x, inner_smul_right }
  ∥v∥
  (by simpa [is_R_or_C.norm_eq_abs] using abs_inner_le_norm v)

@[simp] lemma inner_right_coe (v : E) : (inner_right v : E → 𝕜) = λ w, ⟪v, w⟫ := rfl

@[simp] lemma inner_right_apply (v w : E) : inner_right v w = ⟪v, w⟫ := rfl

end norm

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
      exact finset.sum_nonneg (λ j (hj : j ∈ finset.univ), pow_nonneg (norm_nonneg (x j)) 2) },
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
  add_left := λ x y z,
    show ∑ i, inner (x i + y i) (z i) = ∑ i, inner (x i) (z i) + ∑ i, inner (y i) (z i),
    by simp only [inner_add_left, finset.sum_add_distrib],
  smul_left := λ x y r,
    show ∑ (i : ι), inner (r • x i) (y i) = (conj r) * ∑ i, inner (x i) (y i),
    by simp only [finset.mul_sum, inner_smul_left]
}

@[simp] lemma pi_Lp.inner_apply {ι : Type*} [fintype ι] {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x y : pi_Lp 2 one_le_two f) :
  ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
rfl

lemma pi_Lp.norm_eq_of_L2 {ι : Type*} [fintype ι] {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x : pi_Lp 2 one_le_two f) :
  ∥x∥ = sqrt (∑ (i : ι), ∥x i∥ ^ 2) :=
by { rw [pi_Lp.norm_eq_of_nat 2]; simp [sqrt_eq_rpow] }

/-- A field `𝕜` satisfying `is_R_or_C` is itself a `𝕜`-inner product space. -/
instance is_R_or_C.inner_product_space : inner_product_space 𝕜 𝕜 :=
{ inner := (λ x y, (conj x) * y),
  norm_sq_eq_inner := λ x,
    by { unfold inner, rw [mul_comm, mul_conj, of_real_re, norm_sq_eq_def'] },
  conj_sym := λ x y, by simp [mul_comm],
  add_left := λ x y z, by simp [inner, add_mul],
  smul_left := λ x y z, by simp [inner, mul_assoc] }

@[simp] lemma is_R_or_C.inner_apply (x y : 𝕜) : ⟪x, y⟫ = (conj x) * y := rfl

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `euclidean_space 𝕜 (fin n)`. -/
@[reducible, nolint unused_arguments]
def euclidean_space (𝕜 : Type*) [is_R_or_C 𝕜]
  (n : Type*) [fintype n] : Type* := pi_Lp 2 one_le_two (λ (i : n), 𝕜)

lemma euclidean_space.norm_eq {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]
  (x : euclidean_space 𝕜 n) : ∥x∥ = real.sqrt (∑ (i : n), ∥x i∥ ^ 2) :=
pi_Lp.norm_eq_of_L2 x

/-! ### Inner product space structure on subspaces -/

/-- Induced inner product on a submodule. -/
instance submodule.inner_product_space (W : submodule 𝕜 E) : inner_product_space 𝕜 W :=
{ inner             := λ x y, ⟪(x:E), (y:E)⟫,
  conj_sym          := λ _ _, inner_conj_sym _ _ ,
  norm_sq_eq_inner  := λ _, norm_sq_eq_inner _,
  add_left          := λ _ _ _ , inner_add_left,
  smul_left         := λ _ _ _, inner_smul_left,
  ..submodule.normed_space W }

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp] lemma submodule.coe_inner (W : submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x:E), ↑y⟫ := rfl

section is_R_or_C_to_real

variables {G : Type*}

variables (𝕜 E)
include 𝕜

/-- A general inner product implies a real inner product. This is not registered as an instance
since it creates problems with the case `𝕜 = ℝ`. -/
def has_inner.is_R_or_C_to_real : has_inner ℝ E :=
{ inner := λ x y, re ⟪x, y⟫ }

/-- A general inner product space structure implies a real inner product structure. This is not
registered as an instance since it creates problems with the case `𝕜 = ℝ`, but in can be used in a
proof to obtain a real inner product space structure from a given `𝕜`-inner product space
structure. -/
def inner_product_space.is_R_or_C_to_real : inner_product_space ℝ E :=
{ norm_sq_eq_inner := norm_sq_eq_inner,
  conj_sym := λ x y, inner_re_symm,
  add_left := λ x y z, by {
    change re ⟪x + y, z⟫ = re ⟪x, z⟫ + re ⟪y, z⟫,
    simp [inner_add_left] },
  smul_left := λ x y r, by {
    change re ⟪(r : 𝕜) • x, y⟫ = r * re ⟪x, y⟫,
    simp [inner_smul_left] },
  ..has_inner.is_R_or_C_to_real 𝕜 E,
  ..normed_space.restrict_scalars ℝ 𝕜 E }

instance pi_Lp.inner_product_space_real {ι : Type*} [fintype ι] (f : ι → Type*)
  [Π i, inner_product_space 𝕜 (f i)] : inner_product_space ℝ (pi_Lp 2 one_le_two f) :=
inner_product_space.is_R_or_C_to_real 𝕜 _

instance pi_Lp.is_scalar_tower {ι : Type*} [fintype ι] (f : ι → Type*)
  [Π i, inner_product_space 𝕜 (f i)] : is_scalar_tower ℝ 𝕜 (pi_Lp 2 one_le_two f) :=
restrict_scalars.is_scalar_tower _ _ _

variable {E}

lemma real_inner_eq_re_inner (x y : E) :
  @has_inner.inner ℝ E (has_inner.is_R_or_C_to_real 𝕜 E) x y = re ⟪x, y⟫ := rfl

omit 𝕜

/-- A complex inner product implies a real inner product -/
instance inner_product_space.complex_to_real [inner_product_space ℂ G] : inner_product_space ℝ G :=
inner_product_space.is_R_or_C_to_real ℂ G

end is_R_or_C_to_real

section deriv

/-!
### Derivative of the inner product

In this section we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `normed_space ℝ E`
instance. Though we can deduce this structure from `inner_product_space 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[normed_space ℝ E]` and
`[is_scalar_tower ℝ 𝕜 E]`. In both interesting cases `𝕜 = ℝ` and `𝕜 = ℂ` we have these instances.

-/

variables [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E]

lemma is_bounded_bilinear_map_inner : is_bounded_bilinear_map ℝ (λ p : E × E, ⟪p.1, p.2⟫) :=
{ add_left := λ _ _ _, inner_add_left,
  smul_left := λ r x y,
    by simp only [← algebra_map_smul 𝕜 r x, algebra_map_eq_of_real, inner_smul_real_left],
  add_right := λ _ _ _, inner_add_right,
  smul_right := λ r x y,
    by simp only [← algebra_map_smul 𝕜 r y, algebra_map_eq_of_real, inner_smul_real_right],
  bound := ⟨1, zero_lt_one, λ x y,
    by { rw [one_mul, is_R_or_C.norm_eq_abs], exact abs_inner_le_norm x y, }⟩ }

/-- Derivative of the inner product. -/
def fderiv_inner_clm (p : E × E) : E × E →L[ℝ] 𝕜 := is_bounded_bilinear_map_inner.deriv p

@[simp] lemma fderiv_inner_clm_apply (p x : E × E) :
  fderiv_inner_clm  p x = ⟪p.1, x.2⟫ + ⟪x.1, p.2⟫ := rfl

lemma times_cont_diff_inner {n} : times_cont_diff ℝ n (λ p : E × E, ⟪p.1, p.2⟫) :=
is_bounded_bilinear_map_inner.times_cont_diff

lemma times_cont_diff_at_inner {p : E × E} {n} :
  times_cont_diff_at ℝ n (λ p : E × E, ⟪p.1, p.2⟫) p :=
times_cont_diff_inner.times_cont_diff_at

lemma differentiable_inner : differentiable ℝ (λ p : E × E, ⟪p.1, p.2⟫) :=
is_bounded_bilinear_map_inner.differentiable_at

variables {G : Type*} [normed_group G] [normed_space ℝ G]
  {f g : G → E} {f' g' : G →L[ℝ] E} {s : set G} {x : G} {n : with_top ℕ}

include 𝕜

lemma times_cont_diff_within_at.inner (hf : times_cont_diff_within_at ℝ n f s x)
  (hg : times_cont_diff_within_at ℝ n g s x) :
  times_cont_diff_within_at ℝ n (λ x, ⟪f x, g x⟫) s x :=
times_cont_diff_at_inner.comp_times_cont_diff_within_at x (hf.prod hg)

lemma times_cont_diff_at.inner (hf : times_cont_diff_at ℝ n f x)
  (hg : times_cont_diff_at ℝ n g x) :
  times_cont_diff_at ℝ n (λ x, ⟪f x, g x⟫) x :=
hf.inner hg

lemma times_cont_diff_on.inner (hf : times_cont_diff_on ℝ n f s) (hg : times_cont_diff_on ℝ n g s) :
  times_cont_diff_on ℝ n (λ x, ⟪f x, g x⟫) s :=
λ x hx, (hf x hx).inner (hg x hx)

lemma times_cont_diff.inner (hf : times_cont_diff ℝ n f) (hg : times_cont_diff ℝ n g) :
  times_cont_diff ℝ n (λ x, ⟪f x, g x⟫) :=
times_cont_diff_inner.comp (hf.prod hg)

lemma has_fderiv_within_at.inner (hf : has_fderiv_within_at f f' s x)
  (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ t, ⟪f t, g t⟫) ((fderiv_inner_clm (f x, g x)).comp $ f'.prod g') s x :=
(is_bounded_bilinear_map_inner.has_fderiv_at (f x, g x)).comp_has_fderiv_within_at x (hf.prod hg)

lemma has_fderiv_at.inner (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ t, ⟪f t, g t⟫) ((fderiv_inner_clm (f x, g x)).comp $ f'.prod g') x :=
(is_bounded_bilinear_map_inner.has_fderiv_at (f x, g x)).comp x (hf.prod hg)

lemma has_deriv_within_at.inner {f g : ℝ → E} {f' g' : E} {s : set ℝ} {x : ℝ}
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ t, ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) s x :=
by simpa using (hf.has_fderiv_within_at.inner hg.has_fderiv_within_at).has_deriv_within_at

lemma has_deriv_at.inner {f g : ℝ → E} {f' g' : E} {x : ℝ} :
  has_deriv_at f f' x →  has_deriv_at g g' x →
  has_deriv_at (λ t, ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x :=
by simpa only [← has_deriv_within_at_univ] using has_deriv_within_at.inner

lemma differentiable_within_at.inner (hf : differentiable_within_at ℝ f s x)
  (hg : differentiable_within_at ℝ g s x) :
  differentiable_within_at ℝ (λ x, ⟪f x, g x⟫) s x :=
((differentiable_inner _).has_fderiv_at.comp_has_fderiv_within_at x
  (hf.prod hg).has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.inner (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) :
  differentiable_at ℝ (λ x, ⟪f x, g x⟫) x :=
(differentiable_inner _).comp x (hf.prod hg)

lemma differentiable_on.inner (hf : differentiable_on ℝ f s) (hg : differentiable_on ℝ g s) :
  differentiable_on ℝ (λ x, ⟪f x, g x⟫) s :=
λ x hx, (hf x hx).inner (hg x hx)

lemma differentiable.inner (hf : differentiable ℝ f) (hg : differentiable ℝ g) :
  differentiable ℝ (λ x, ⟪f x, g x⟫) :=
λ x, (hf x).inner (hg x)

lemma fderiv_inner_apply (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) (y : G) :
  fderiv ℝ (λ t, ⟪f t, g t⟫) x y = ⟪f x, fderiv ℝ g x y⟫ + ⟪fderiv ℝ f x y, g x⟫ :=
by { rw [(hf.has_fderiv_at.inner hg.has_fderiv_at).fderiv], refl }

lemma deriv_inner_apply {f g : ℝ → E} {x : ℝ} (hf : differentiable_at ℝ f x)
  (hg : differentiable_at ℝ g x) :
  deriv (λ t, ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫ + ⟪deriv f x, g x⟫ :=
(hf.has_deriv_at.inner hg.has_deriv_at).deriv

lemma times_cont_diff_norm_square : times_cont_diff ℝ n (λ x : E, ∥x∥ ^ 2) :=
begin
  simp only [pow_two, ← inner_self_eq_norm_square],
  exact (re_clm : 𝕜 →L[ℝ] ℝ).times_cont_diff.comp (times_cont_diff_id.inner times_cont_diff_id)
end

lemma times_cont_diff.norm_square (hf : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, ∥f x∥ ^ 2) :=
times_cont_diff_norm_square.comp hf

lemma times_cont_diff_within_at.norm_square (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ y, ∥f y∥ ^ 2) s x :=
times_cont_diff_norm_square.times_cont_diff_at.comp_times_cont_diff_within_at x hf

lemma times_cont_diff_at.norm_square (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ y, ∥f y∥ ^ 2) x :=
hf.norm_square

lemma times_cont_diff_at_norm {x : E} (hx : x ≠ 0) : times_cont_diff_at ℝ n norm x :=
have ∥id x∥ ^ 2 ≠ 0, from pow_ne_zero _ (norm_pos_iff.2 hx).ne',
by simpa only [id, sqrt_sqr, norm_nonneg] using times_cont_diff_at_id.norm_square.sqrt this

lemma times_cont_diff_at.norm (hf : times_cont_diff_at ℝ n f x) (h0 : f x ≠ 0) :
  times_cont_diff_at ℝ n (λ y, ∥f y∥) x :=
(times_cont_diff_at_norm h0).comp x hf

lemma times_cont_diff_at.dist (hf : times_cont_diff_at ℝ n f x) (hg : times_cont_diff_at ℝ n g x)
  (hne : f x ≠ g x) :
  times_cont_diff_at ℝ n (λ y, dist (f y) (g y)) x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm (sub_ne_zero.2 hne) }

lemma times_cont_diff_within_at.norm (hf : times_cont_diff_within_at ℝ n f s x) (h0 : f x ≠ 0) :
  times_cont_diff_within_at ℝ n (λ y, ∥f y∥) s x :=
(times_cont_diff_at_norm h0).comp_times_cont_diff_within_at x hf

lemma times_cont_diff_within_at.dist (hf : times_cont_diff_within_at ℝ n f s x)
  (hg : times_cont_diff_within_at ℝ n g s x) (hne : f x ≠ g x) :
  times_cont_diff_within_at ℝ n (λ y, dist (f y) (g y)) s x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm (sub_ne_zero.2 hne) }

lemma times_cont_diff_on.norm_square (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ y, ∥f y∥ ^ 2) s :=
(λ x hx, (hf x hx).norm_square)

lemma times_cont_diff_on.norm (hf : times_cont_diff_on ℝ n f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
  times_cont_diff_on ℝ n (λ y, ∥f y∥) s :=
λ x hx, (hf x hx).norm (h0 x hx)

lemma times_cont_diff_on.dist (hf : times_cont_diff_on ℝ n f s)
  (hg : times_cont_diff_on ℝ n g s) (hne : ∀ x ∈ s, f x ≠ g x) :
  times_cont_diff_on ℝ n (λ y, dist (f y) (g y)) s :=
λ x hx, (hf x hx).dist (hg x hx) (hne x hx)

lemma times_cont_diff.norm (hf : times_cont_diff ℝ n f) (h0 : ∀ x, f x ≠ 0) :
  times_cont_diff ℝ n (λ y, ∥f y∥) :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x, hf.times_cont_diff_at.norm (h0 x)

lemma times_cont_diff.dist (hf : times_cont_diff ℝ n f) (hg : times_cont_diff ℝ n g)
  (hne : ∀ x, f x ≠ g x) :
  times_cont_diff ℝ n (λ y, dist (f y) (g y)) :=
times_cont_diff_iff_times_cont_diff_at.2 $
  λ x, hf.times_cont_diff_at.dist hg.times_cont_diff_at (hne x)

lemma differentiable_at.norm_square (hf : differentiable_at ℝ f x) :
  differentiable_at ℝ (λ y, ∥f y∥ ^ 2) x :=
(times_cont_diff_at_id.norm_square.differentiable_at le_rfl).comp x hf

lemma differentiable_at.norm (hf : differentiable_at ℝ f x) (h0 : f x ≠ 0) :
  differentiable_at ℝ (λ y, ∥f y∥) x :=
((times_cont_diff_at_norm h0).differentiable_at le_rfl).comp x hf

lemma differentiable_at.dist (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x)
  (hne : f x ≠ g x) :
  differentiable_at ℝ (λ y, dist (f y) (g y)) x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm (sub_ne_zero.2 hne) }

lemma differentiable.norm_square (hf : differentiable ℝ f) : differentiable ℝ (λ y, ∥f y∥ ^ 2) :=
λ x, (hf x).norm_square

lemma differentiable.norm (hf : differentiable ℝ f) (h0 : ∀ x, f x ≠ 0) :
  differentiable ℝ (λ y, ∥f y∥) :=
λ x, (hf x).norm (h0 x)

lemma differentiable.dist (hf : differentiable ℝ f) (hg : differentiable ℝ g)
  (hne : ∀ x, f x ≠ g x) :
  differentiable ℝ (λ y, dist (f y) (g y)) :=
λ x, (hf x).dist (hg x) (hne x)

lemma differentiable_within_at.norm_square (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ y, ∥f y∥ ^ 2) s x :=
(times_cont_diff_at_id.norm_square.differentiable_at le_rfl).comp_differentiable_within_at x hf

lemma differentiable_within_at.norm (hf : differentiable_within_at ℝ f s x) (h0 : f x ≠ 0) :
  differentiable_within_at ℝ (λ y, ∥f y∥) s x :=
((times_cont_diff_at_id.norm h0).differentiable_at le_rfl).comp_differentiable_within_at x hf

lemma differentiable_within_at.dist (hf : differentiable_within_at ℝ f s x)
  (hg : differentiable_within_at ℝ g s x) (hne : f x ≠ g x) :
  differentiable_within_at ℝ (λ y, dist (f y) (g y)) s x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm (sub_ne_zero.2 hne) }

lemma differentiable_on.norm_square (hf : differentiable_on ℝ f s) :
  differentiable_on ℝ (λ y, ∥f y∥ ^ 2) s :=
λ x hx, (hf x hx).norm_square

lemma differentiable_on.norm (hf : differentiable_on ℝ f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λ y, ∥f y∥) s :=
λ x hx, (hf x hx).norm (h0 x hx)

lemma differentiable_on.dist (hf : differentiable_on ℝ f s) (hg : differentiable_on ℝ g s)
  (hne : ∀ x ∈ s, f x ≠ g x) :
  differentiable_on ℝ (λ y, dist (f y) (g y)) s :=
λ x hx, (hf x hx).dist (hg x hx) (hne x hx)

end deriv

section continuous

/-!
### Continuity and measurability of the inner product

Since the inner product is `ℝ`-smooth, it is continuous. We do not need a `[normed_space ℝ E]`
structure to *state* this fact and its corollaries, so we introduce them in the proof instead.
-/

lemma continuous_inner : continuous (λ p : E × E, ⟪p.1, p.2⟫) :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E,
  letI : is_scalar_tower ℝ 𝕜 E := restrict_scalars.is_scalar_tower _ _ _,
  exact differentiable_inner.continuous
end

variables {α : Type*}

lemma filter.tendsto.inner {f g : α → E} {l : filter α} {x y : E} (hf : tendsto f l (𝓝 x))
  (hg : tendsto g l (𝓝 y)) :
  tendsto (λ t, ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
(continuous_inner.tendsto _).comp (hf.prod_mk_nhds hg)

lemma measurable.inner [measurable_space α] [measurable_space E] [opens_measurable_space E]
  [topological_space.second_countable_topology E] [measurable_space 𝕜] [borel_space 𝕜]
  {f g : α → E} (hf : measurable f) (hg : measurable g) :
  measurable (λ t, ⟪f t, g t⟫) :=
continuous.measurable2 continuous_inner hf hg

lemma ae_measurable.inner [measurable_space α] [measurable_space E] [opens_measurable_space E]
  [topological_space.second_countable_topology E] [measurable_space 𝕜] [borel_space 𝕜]
  {μ : measure_theory.measure α} {f g : α → E} (hf : ae_measurable f μ) (hg : ae_measurable g μ) :
  ae_measurable (λ x, ⟪f x, g x⟫) μ :=
begin
  refine ⟨λ x, ⟪hf.mk f x, hg.mk g x⟫, hf.measurable_mk.inner hg.measurable_mk, _⟩,
  refine hf.ae_eq_mk.mp (hg.ae_eq_mk.mono (λ x hxg hxf, _)),
  dsimp only,
  congr,
  { exact hxf, },
  { exact hxg, },
end

variables [topological_space α] {f g : α → E} {x : α} {s : set α}

include 𝕜

lemma continuous_within_at.inner (hf : continuous_within_at f s x)
  (hg : continuous_within_at g s x) :
  continuous_within_at (λ t, ⟪f t, g t⟫) s x :=
hf.inner hg

lemma continuous_at.inner (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (λ t, ⟪f t, g t⟫) x :=
hf.inner hg

lemma continuous_on.inner (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λ t, ⟪f t, g t⟫) s :=
λ x hx, (hf x hx).inner (hg x hx)

lemma continuous.inner (hf : continuous f) (hg : continuous g) : continuous (λ t, ⟪f t, g t⟫) :=
continuous_iff_continuous_at.2 $ λ x, hf.continuous_at.inner hg.continuous_at

end continuous

section pi_Lp
local attribute [reducible] pi_Lp
variables {ι : Type*} [fintype ι]

instance : finite_dimensional 𝕜 (euclidean_space 𝕜 ι) := by apply_instance
instance : inner_product_space 𝕜 (euclidean_space 𝕜 ι) := by apply_instance

instance euclidean_space.inner_product_space_real {ι : Type*} [fintype ι] :
  inner_product_space ℝ (euclidean_space 𝕜 ι) :=
pi_Lp.inner_product_space_real 𝕜 _

instance euclidean_space.is_scalar_tower {ι : Type*} [fintype ι] :
  is_scalar_tower ℝ 𝕜 (euclidean_space 𝕜 ι) :=
by apply_instance

@[simp] lemma findim_euclidean_space :
  finite_dimensional.findim 𝕜 (euclidean_space 𝕜 ι) = fintype.card ι := by simp

lemma findim_euclidean_space_fin {n : ℕ} :
  finite_dimensional.findim 𝕜 (euclidean_space 𝕜 (fin n)) = n := by simp

/-- An orthonormal basis on a fintype `ι` for an inner product space induces an isometry with
`euclidean_space 𝕜 ι`. -/
def is_basis.isometry_euclidean_of_orthonormal
  {v : ι → E} (h : is_basis 𝕜 v) (hv : orthonormal 𝕜 v) :
  E ≃ₗᵢ[𝕜] (euclidean_space 𝕜 ι) :=
h.equiv_fun.isometry_of_inner
begin
  intros x y,
  let p : euclidean_space 𝕜 ι := h.equiv_fun x,
  let q : euclidean_space 𝕜 ι := h.equiv_fun y,
  have key : ⟪p, q⟫ = ⟪∑ i, p i • v i, ∑ i, q i • v i⟫,
  { simp [sum_inner, inner_smul_left, hv.inner_right_fintype] },
  convert key,
  { rw [← h.equiv_fun.symm_apply_apply x, h.equiv_fun_symm_apply] },
  { rw [← h.equiv_fun.symm_apply_apply y, h.equiv_fun_symm_apply] }
end

/-- `ℂ` is isometric to ℝ² with the Euclidean inner product. -/
def complex.isometry_euclidean : ℂ ≃ₗᵢ[ℝ] (euclidean_space ℝ (fin 2)) :=
complex.is_basis_one_I.isometry_euclidean_of_orthonormal
begin
  rw orthonormal_iff_ite,
  intros i, fin_cases i;
  intros j; fin_cases j;
  simp [real_inner_eq_re_inner]
end

@[simp] lemma complex.isometry_euclidean_symm_apply (x : euclidean_space ℝ (fin 2)) :
  complex.isometry_euclidean.symm x = (x 0) + (x 1) * I :=
begin
  convert complex.is_basis_one_I.equiv_fun_symm_apply x,
  { simpa },
  { simp },
end

lemma complex.isometry_euclidean_proj_eq_self (z : ℂ) :
  ↑(complex.isometry_euclidean z 0) + ↑(complex.isometry_euclidean z 1) * (I : ℂ) = z :=
by rw [← complex.isometry_euclidean_symm_apply (complex.isometry_euclidean z),
  complex.isometry_euclidean.symm_apply_apply z]

@[simp] lemma complex.isometry_euclidean_apply_zero (z : ℂ) :
  complex.isometry_euclidean z 0 = z.re :=
by { conv_rhs { rw ← complex.isometry_euclidean_proj_eq_self z }, simp }

@[simp] lemma complex.isometry_euclidean_apply_one (z : ℂ) :
  complex.isometry_euclidean z 1 = z.im :=
by { conv_rhs { rw ← complex.isometry_euclidean_proj_eq_self z }, simp }

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
      ... = (absR ((2:ℝ)) * ∥u - half•(wq + wp)∥) * (absR ((2:ℝ)) * ∥u - half•(wq+wp)∥) +
            ∥wp-wq∥*∥wp-wq∥ :
      by { rw _root_.abs_of_nonneg, exact zero_le_two }
      ... = ∥(2:ℝ) • (u - half • (wq + wp))∥ * ∥(2:ℝ) • (u - half • (wq + wp))∥ +
            ∥wp-wq∥ * ∥wp-wq∥ :
      by simp [norm_smul]
      ... = ∥a + b∥ * ∥a + b∥ + ∥a - b∥ * ∥a - b∥ :
      begin
        rw [smul_sub, smul_smul, mul_one_div_cancel (_root_.two_ne_zero : (2 : ℝ) ≠ 0),
            ← one_add_one_eq_two, add_smul],
        simp only [one_smul],
        have eq₁ : wp - wq = a - b, from (sub_sub_sub_cancel_left _ _ _).symm,
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
      ∥wp - wq∥ * ∥wp - wq∥ = 2 * (∥a∥*∥a∥ + ∥b∥*∥b∥) -
        4 * ∥u - half • (wq+wp)∥ * ∥u - half • (wq+wp)∥ : by { rw ← this, simp }
      ... ≤ 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) - 4 * δ * δ : sub_le_sub_left eq₁ _
      ... ≤ 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ :
        sub_le_sub_right (mul_le_mul_of_nonneg_left (add_le_add eq₂ eq₂') (by norm_num)) _
      ... = 8 * δ * div + 4 * div * div : by ring,
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) zero_le_δ) (le_of_lt nat.one_div_pos_of_nat))
      (mul_nonneg (mul_nonneg (by norm_num) nat.one_div_pos_of_nat.le) nat.one_div_pos_of_nat.le),
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
    have eq₁ : ∥u-v∥^2-2*θ*inner(u-v)(w-v)+θ*θ*∥w-v∥^2=∥u-v∥^2+(θ*θ*∥w-v∥^2-2*θ*inner(u-v)(w-v)),
      by abel,
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

variables (K : submodule 𝕜 E)

/--
Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_infi_of_complete_subspace
  (h : is_complete (↑K : set E)) : ∀ u : E, ∃ v ∈ K, ∥u - v∥ = ⨅ w : (K : set E), ∥u - w∥ :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E,
  letI : module ℝ E := restrict_scalars.semimodule ℝ 𝕜 E,
  letI : is_scalar_tower ℝ 𝕜 E := restrict_scalars.is_scalar_tower _ _ _,
  let K' : submodule ℝ E := submodule.restrict_scalars ℝ K,
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
theorem norm_eq_infi_iff_real_inner_eq_zero (K : submodule ℝ F) {u : F} {v : F}
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
theorem norm_eq_infi_iff_inner_eq_zero {u : E} {v : E}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : (↑K : set E), ∥u - w∥) ↔ ∀ w ∈ K, ⟪u - v, w⟫ = 0 :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E,
  letI : module ℝ E := restrict_scalars.semimodule ℝ 𝕜 E,
  letI : is_scalar_tower ℝ 𝕜 E := restrict_scalars.is_scalar_tower _ _ _,
  let K' : submodule ℝ E := K.restrict_scalars ℝ,
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

section orthogonal_projection
variables [complete_space K]

/-- The orthogonal projection onto a complete subspace, as an
unbundled function.  This definition is only intended for use in
setting up the bundled version `orthogonal_projection` and should not
be used once that is defined. -/
def orthogonal_projection_fn (v : E) :=
(exists_norm_eq_infi_of_complete_subspace K (complete_space_coe_iff_is_complete.mp ‹_›) v).some

variables {K}

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
lemma orthogonal_projection_fn_mem (v : E) : orthogonal_projection_fn K v ∈ K :=
(exists_norm_eq_infi_of_complete_subspace K
  (complete_space_coe_iff_is_complete.mp ‹_›) v).some_spec.some

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
lemma orthogonal_projection_fn_inner_eq_zero (v : E) :
  ∀ w ∈ K, ⟪v - orthogonal_projection_fn K v, w⟫ = 0 :=
begin
  rw ←norm_eq_infi_iff_inner_eq_zero K (orthogonal_projection_fn_mem v),
  exact (exists_norm_eq_infi_of_complete_subspace K
    (complete_space_coe_iff_is_complete.mp ‹_›) v).some_spec.some_spec
end

/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property.  This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
lemma eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
  {u v : E} (hvm : v ∈ K) (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) :
  orthogonal_projection_fn K u = v :=
begin
  rw [←sub_eq_zero, ←inner_self_eq_zero],
  have hvs : orthogonal_projection_fn K u - v ∈ K :=
    submodule.sub_mem K (orthogonal_projection_fn_mem u) hvm,
  have huo : ⟪u - orthogonal_projection_fn K u, orthogonal_projection_fn K u - v⟫ = 0 :=
    orthogonal_projection_fn_inner_eq_zero u _ hvs,
  have huv : ⟪u - v, orthogonal_projection_fn K u - v⟫ = 0 := hvo _ hvs,
  have houv : ⟪(u - v) - (u - orthogonal_projection_fn K u), orthogonal_projection_fn K u - v⟫ = 0,
  { rw [inner_sub_left, huo, huv, sub_zero] },
  rwa sub_sub_sub_cancel_left at houv
end

variables (K)

lemma orthogonal_projection_fn_norm_sq (v : E) :
  ∥v∥ * ∥v∥ = ∥v - (orthogonal_projection_fn K v)∥ * ∥v - (orthogonal_projection_fn K v)∥
            + ∥orthogonal_projection_fn K v∥ * ∥orthogonal_projection_fn K v∥ :=
begin
  set p := orthogonal_projection_fn K v,
  have h' : ⟪v - p, p⟫ = 0,
  { exact orthogonal_projection_fn_inner_eq_zero _ _ (orthogonal_projection_fn_mem v) },
  convert norm_add_square_eq_norm_square_add_norm_square_of_inner_eq_zero (v - p) p h' using 2;
  simp,
end

/-- The orthogonal projection onto a complete subspace. -/
def orthogonal_projection : E →L[𝕜] K :=
linear_map.mk_continuous
  { to_fun := λ v, ⟨orthogonal_projection_fn K v, orthogonal_projection_fn_mem v⟩,
    map_add' := λ x y, begin
      have hm : orthogonal_projection_fn K x + orthogonal_projection_fn K y ∈ K :=
        submodule.add_mem K (orthogonal_projection_fn_mem x) (orthogonal_projection_fn_mem y),
      have ho :
        ∀ w ∈ K, ⟪x + y - (orthogonal_projection_fn K x + orthogonal_projection_fn K y), w⟫ = 0,
      { intros w hw,
        rw [add_sub_comm, inner_add_left, orthogonal_projection_fn_inner_eq_zero _ w hw,
            orthogonal_projection_fn_inner_eq_zero _ w hw, add_zero] },
      ext,
      simp [eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hm ho]
    end,
    map_smul' := λ c x, begin
      have hm : c • orthogonal_projection_fn K x ∈ K :=
        submodule.smul_mem K _ (orthogonal_projection_fn_mem x),
      have ho : ∀ w ∈ K, ⟪c • x - c • orthogonal_projection_fn K x, w⟫ = 0,
      { intros w hw,
        rw [←smul_sub, inner_smul_left, orthogonal_projection_fn_inner_eq_zero _ w hw, mul_zero] },
      ext,
      simp [eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hm ho]
    end }
  1
  (λ x, begin
    simp only [one_mul, linear_map.coe_mk],
    refine le_of_pow_le_pow 2 (norm_nonneg _) (by norm_num) _,
    change ∥orthogonal_projection_fn K x∥ ^ 2 ≤ ∥x∥ ^ 2,
    nlinarith [orthogonal_projection_fn_norm_sq K x]
  end)

variables {K}

@[simp]
lemma orthogonal_projection_fn_eq (v : E) :
  orthogonal_projection_fn K v = (orthogonal_projection K v : E) :=
rfl

/-- The characterization of the orthogonal projection.  -/
@[simp]
lemma orthogonal_projection_inner_eq_zero (v : E) :
  ∀ w ∈ K, ⟪v - orthogonal_projection K v, w⟫ = 0 :=
orthogonal_projection_fn_inner_eq_zero v

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
lemma eq_orthogonal_projection_of_mem_of_inner_eq_zero
  {u v : E} (hvm : v ∈ K) (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) :
  (orthogonal_projection K u : E) = v :=
eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hvm hvo

/-- The orthogonal projections onto equal subspaces are coerced back to the same point in `E`. -/
lemma eq_orthogonal_projection_of_eq_submodule
  {K' : submodule 𝕜 E} [complete_space K'] (h : K = K') (u : E) :
  (orthogonal_projection K u : E) = (orthogonal_projection K' u : E) :=
begin
  change orthogonal_projection_fn K u = orthogonal_projection_fn K' u,
  congr,
  exact h
end

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp] lemma orthogonal_projection_mem_subspace_eq_self (v : K) : orthogonal_projection K v = v :=
by { ext, apply eq_orthogonal_projection_of_mem_of_inner_eq_zero; simp }

local attribute [instance] finite_dimensional_bot

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp] lemma orthogonal_projection_bot : orthogonal_projection (⊥ : submodule 𝕜 E) = 0 :=
begin
  ext u,
  apply eq_orthogonal_projection_of_mem_of_inner_eq_zero,
  { simp },
  { intros w hw,
    simp [(submodule.mem_bot 𝕜).mp hw] }
end

variables (K)

/-- The orthogonal projection has norm `≤ 1`. -/
lemma orthogonal_projection_norm_le : ∥orthogonal_projection K∥ ≤ 1 :=
linear_map.mk_continuous_norm_le _ (by norm_num) _

variables (𝕜)

lemma smul_orthogonal_projection_singleton {v : E} (w : E) :
  (∥v∥ ^ 2 : 𝕜) • (orthogonal_projection (𝕜 ∙ v) w : E) = ⟪v, w⟫ • v :=
begin
  suffices : ↑(orthogonal_projection (𝕜 ∙ v) ((∥v∥ ^ 2 : 𝕜) • w)) = ⟪v, w⟫ • v,
  { simpa using this },
  apply eq_orthogonal_projection_of_mem_of_inner_eq_zero,
  { rw submodule.mem_span_singleton,
    use ⟪v, w⟫ },
  { intros x hx,
    obtain ⟨c, rfl⟩ := submodule.mem_span_singleton.mp hx,
    have hv : ↑∥v∥ ^ 2 = ⟪v, v⟫ := by { norm_cast, simp [norm_sq_eq_inner] },
    simp [inner_sub_left, inner_smul_left, inner_smul_right, is_R_or_C.conj_div, mul_comm, hv,
      inner_product_space.conj_sym, hv] }
end

/-- Formula for orthogonal projection onto a single vector. -/
lemma orthogonal_projection_singleton {v : E} (w : E) :
  (orthogonal_projection (𝕜 ∙ v) w : E) = (⟪v, w⟫ / ∥v∥ ^ 2) • v :=
begin
  by_cases hv : v = 0,
  { rw [hv, eq_orthogonal_projection_of_eq_submodule submodule.span_zero_singleton],
    { simp },
    { apply_instance } },
  have hv' : ∥v∥ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv),
  have key : ((∥v∥ ^ 2 : 𝕜)⁻¹ * ∥v∥ ^ 2) • ↑(orthogonal_projection (𝕜 ∙ v) w)
              = ((∥v∥ ^ 2 : 𝕜)⁻¹ * ⟪v, w⟫) • v,
  { simp [mul_smul, smul_orthogonal_projection_singleton 𝕜 w] },
  convert key;
  field_simp [hv']
end

/-- Formula for orthogonal projection onto a single unit vector. -/
lemma orthogonal_projection_unit_singleton {v : E} (hv : ∥v∥ = 1) (w : E) :
  (orthogonal_projection (𝕜 ∙ v) w : E) = ⟪v, w⟫ • v :=
by { rw ← smul_orthogonal_projection_singleton 𝕜 w, simp [hv] }

end orthogonal_projection

/-- The subspace of vectors orthogonal to a given subspace. -/
def submodule.orthogonal : submodule 𝕜 E :=
{ carrier := {v | ∀ u ∈ K, ⟪u, v⟫ = 0},
  zero_mem' := λ _ _, inner_zero_right,
  add_mem' := λ x y hx hy u hu, by rw [inner_add_right, hx u hu, hy u hu, add_zero],
  smul_mem' := λ c x hx u hu, by rw [inner_smul_right, hx u hu, mul_zero] }

notation K`ᗮ`:1200 := submodule.orthogonal K

/-- When a vector is in `Kᗮ`. -/
lemma submodule.mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 := iff.rfl

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
lemma submodule.mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 :=
by simp_rw [submodule.mem_orthogonal, inner_eq_zero_sym]

variables {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
lemma submodule.inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
(K.mem_orthogonal v).1 hv u hu

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
lemma submodule.inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 :=
by rw [inner_eq_zero_sym]; exact submodule.inner_right_of_mem_orthogonal hu hv

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
lemma inner_right_of_mem_orthogonal_singleton (u : E) {v : E} (hv : v ∈ (𝕜 ∙ u)ᗮ) : ⟪u, v⟫ = 0 :=
submodule.inner_right_of_mem_orthogonal (submodule.mem_span_singleton_self u) hv

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
lemma inner_left_of_mem_orthogonal_singleton (u : E) {v : E} (hv : v ∈ (𝕜 ∙ u)ᗮ) : ⟪v, u⟫ = 0 :=
submodule.inner_left_of_mem_orthogonal (submodule.mem_span_singleton_self u) hv

variables (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
lemma submodule.inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x,
  rw submodule.mem_inf,
  exact λ ⟨hx, ho⟩, inner_self_eq_zero.1 (ho x hx)
end

/-- `K` and `Kᗮ` have trivial intersection. -/
lemma submodule.orthogonal_disjoint : disjoint K Kᗮ :=
by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
lemma orthogonal_eq_inter : Kᗮ = ⨅ v : K, (inner_right (v:E)).ker :=
begin
  apply le_antisymm,
  { rw le_infi_iff,
    rintros ⟨v, hv⟩ w hw,
    simpa using hw _ hv },
  { intros v hv w hw,
    simp only [submodule.mem_infi] at hv,
    exact hv ⟨w, hw⟩ }
end

/-- The orthogonal complement of any submodule `K` is closed. -/
lemma submodule.is_closed_orthogonal : is_closed (Kᗮ : set E) :=
begin
  rw orthogonal_eq_inter K,
  convert is_closed_Inter (λ v : K, (inner_right (v:E)).is_closed_ker),
  simp
end

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
instance [complete_space E] : complete_space Kᗮ := K.is_closed_orthogonal.complete_space_coe

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
lemma submodule.orthogonal_le {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
(submodule.orthogonal_gc 𝕜 E).monotone_l h

/-- `submodule.orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
lemma submodule.orthogonal_orthogonal_monotone {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) :
  K₁ᗮᗮ ≤ K₂ᗮᗮ :=
submodule.orthogonal_le (submodule.orthogonal_le h)

/-- `K` is contained in `Kᗮᗮ`. -/
lemma submodule.le_orthogonal_orthogonal : K ≤ Kᗮᗮ := (submodule.orthogonal_gc 𝕜 E).le_u_l _

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
lemma submodule.inf_orthogonal (K₁ K₂ : submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
(submodule.orthogonal_gc 𝕜 E).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
lemma submodule.infi_orthogonal {ι : Type*} (K : ι → submodule 𝕜 E) : (⨅ i, (K i)ᗮ) = (supr K)ᗮ :=
(submodule.orthogonal_gc 𝕜 E).l_supr.symm

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
lemma submodule.Inf_orthogonal (s : set $ submodule 𝕜 E) : (⨅ K ∈ s, Kᗮ) = (Sup s)ᗮ :=
(submodule.orthogonal_gc 𝕜 E).l_Sup.symm

/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
lemma submodule.sup_orthogonal_inf_of_is_complete {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂)
  (hc : is_complete (K₁ : set E)) : K₁ ⊔ (K₁ᗮ ⊓ K₂) = K₂ :=
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

variables {K}

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. -/
lemma submodule.sup_orthogonal_of_is_complete (h : is_complete (K : set E)) : K ⊔ Kᗮ = ⊤ :=
begin
  convert submodule.sup_orthogonal_inf_of_is_complete (le_top : K ≤ ⊤) h,
  simp
end

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. Version using `complete_space`. -/
lemma submodule.sup_orthogonal_of_complete_space [complete_space K] : K ⊔ Kᗮ = ⊤ :=
submodule.sup_orthogonal_of_is_complete (complete_space_coe_iff_is_complete.mp ‹_›)

variables (K)

/-- If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` and `Kᗮ`. -/
lemma submodule.exists_sum_mem_mem_orthogonal [complete_space K] (v : E) :
  ∃ (y ∈ K) (z ∈ Kᗮ), v = y + z :=
begin
  have h_mem : v ∈ K ⊔ Kᗮ := by simp [submodule.sup_orthogonal_of_complete_space],
  obtain ⟨y, hy, z, hz, hyz⟩ := submodule.mem_sup.mp h_mem,
  exact ⟨y, hy, z, hz, hyz.symm⟩
end

/-- If `K` is complete, then the orthogonal complement of its orthogonal complement is itself. -/
@[simp] lemma submodule.orthogonal_orthogonal [complete_space K] : Kᗮᗮ = K :=
begin
  ext v,
  split,
  { obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_sum_mem_mem_orthogonal v,
    intros hv,
    have hz' : z = 0,
    { have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_sym],
      simpa [inner_add_right, hyz] using hv z hz },
    simp [hy, hz'] },
  { intros hv w hw,
    rw inner_eq_zero_sym,
    exact hw v hv }
end

lemma submodule.orthogonal_orthogonal_eq_closure [complete_space E] :
  Kᗮᗮ = K.topological_closure :=
begin
  refine le_antisymm _ _,
  { convert submodule.orthogonal_orthogonal_monotone K.submodule_topological_closure,
    haveI : complete_space K.topological_closure :=
      K.is_closed_topological_closure.complete_space_coe,
    rw K.topological_closure.orthogonal_orthogonal },
  { exact K.topological_closure_minimal K.le_orthogonal_orthogonal Kᗮ.is_closed_orthogonal }
end

variables {K}

/-- If `K` is complete, `K` and `Kᗮ` are complements of each other. -/
lemma submodule.is_compl_orthogonal_of_is_complete (h : is_complete (K : set E)) : is_compl K Kᗮ :=
⟨K.orthogonal_disjoint, le_of_eq (submodule.sup_orthogonal_of_is_complete h).symm⟩

@[simp] lemma submodule.top_orthogonal_eq_bot : (⊤ : submodule 𝕜 E)ᗮ = ⊥ :=
begin
  ext,
  rw [submodule.mem_bot, submodule.mem_orthogonal],
  exact ⟨λ h, inner_self_eq_zero.mp (h x submodule.mem_top), by { rintro rfl, simp }⟩
end

@[simp] lemma submodule.bot_orthogonal_eq_top : (⊥ : submodule 𝕜 E)ᗮ = ⊤ :=
begin
  rw [← submodule.top_orthogonal_eq_bot, eq_top_iff],
  exact submodule.le_orthogonal_orthogonal ⊤
end

@[simp] lemma submodule.orthogonal_eq_bot_iff (hK : is_complete (K : set E)) :
  Kᗮ = ⊥ ↔ K = ⊤ :=
begin
  refine ⟨_, by { rintro rfl, exact submodule.top_orthogonal_eq_bot }⟩,
  intro h,
  have : K ⊔ Kᗮ = ⊤ := submodule.sup_orthogonal_of_is_complete hK,
  rwa [h, sup_comm, bot_sup_eq] at this,
end

@[simp] lemma submodule.orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ :=
begin
  refine ⟨_, by { rintro rfl, exact submodule.bot_orthogonal_eq_top }⟩,
  intro h,
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot,
  rwa [h, inf_comm, top_inf_eq] at this
end

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
lemma eq_orthogonal_projection_of_mem_orthogonal
  [complete_space K] {u v : E} (hv : v ∈ K) (hvo : u - v ∈ Kᗮ) :
  (orthogonal_projection K u : E) = v :=
eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hv (λ w, inner_eq_zero_sym.mp ∘ (hvo w))

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
lemma eq_orthogonal_projection_of_mem_orthogonal'
  [complete_space K] {u v z : E} (hv : v ∈ K) (hz : z ∈ Kᗮ) (hu : u = v + z) :
  (orthogonal_projection K u : E) = v :=
eq_orthogonal_projection_of_mem_orthogonal hv (by simpa [hu])

/-- The orthogonal projection onto `K` of an element of `Kᗮ` is zero. -/
lemma orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero
  [complete_space K] {v : E} (hv : v ∈ Kᗮ) :
  orthogonal_projection K v = 0 :=
by { ext, convert eq_orthogonal_projection_of_mem_orthogonal _ _; simp [hv] }

/-- The orthogonal projection onto `Kᗮ` of an element of `K` is zero. -/
lemma orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero
  [complete_space E] {v : E} (hv : v ∈ K) :
  orthogonal_projection Kᗮ v = 0 :=
orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero (K.le_orthogonal_orthogonal hv)

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero. -/
lemma orthogonal_projection_orthogonal_complement_singleton_eq_zero [complete_space E] (v : E) :
  orthogonal_projection (𝕜 ∙ v)ᗮ v = 0 :=
orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero
  (submodule.mem_span_singleton_self v)

variables (K)

/-- In a complete space `E`, a vector splits as the sum of its orthogonal projections onto a
complete submodule `K` and onto the orthogonal complement of `K`.-/
lemma eq_sum_orthogonal_projection_self_orthogonal_complement
  [complete_space E] [complete_space K] (w : E) :
  w = (orthogonal_projection K w : E) + (orthogonal_projection Kᗮ w : E) :=
begin
  obtain ⟨y, hy, z, hz, hwyz⟩ := K.exists_sum_mem_mem_orthogonal w,
  convert hwyz,
  { exact eq_orthogonal_projection_of_mem_orthogonal' hy hz hwyz },
  { rw add_comm at hwyz,
    refine eq_orthogonal_projection_of_mem_orthogonal' hz _ hwyz,
    simp [hy] }
end

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
lemma id_eq_sum_orthogonal_projection_self_orthogonal_complement
  [complete_space E] [complete_space K] :
  continuous_linear_map.id 𝕜 E
  = K.subtypeL.comp (orthogonal_projection K)
  + Kᗮ.subtypeL.comp (orthogonal_projection Kᗮ) :=
by { ext w, exact eq_sum_orthogonal_projection_self_orthogonal_complement K w }

open finite_dimensional

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
lemma submodule.findim_add_inf_findim_orthogonal {K₁ K₂ : submodule 𝕜 E}
  [finite_dimensional 𝕜 K₂] (h : K₁ ≤ K₂) :
  findim 𝕜 K₁ + findim 𝕜 (K₁ᗮ ⊓ K₂ : submodule 𝕜 E) = findim 𝕜 K₂ :=
begin
  haveI := submodule.finite_dimensional_of_le h,
  have hd := submodule.dim_sup_add_dim_inf_eq K₁ (K₁ᗮ ⊓ K₂),
  rw [←inf_assoc, (submodule.orthogonal_disjoint K₁).eq_bot, bot_inf_eq, findim_bot,
      submodule.sup_orthogonal_inf_of_is_complete h
        (submodule.complete_of_finite_dimensional _)] at hd,
  rw add_zero at hd,
  exact hd.symm
end

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
lemma submodule.findim_add_inf_findim_orthogonal' {K₁ K₂ : submodule 𝕜 E}
  [finite_dimensional 𝕜 K₂] (h : K₁ ≤ K₂) {n : ℕ} (h_dim : findim 𝕜 K₁ + n = findim 𝕜 K₂) :
  findim 𝕜 (K₁ᗮ ⊓ K₂ : submodule 𝕜 E) = n :=
by { rw ← add_right_inj (findim 𝕜 K₁), simp [submodule.findim_add_inf_findim_orthogonal h, h_dim] }

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
lemma submodule.findim_add_findim_orthogonal [finite_dimensional 𝕜 E] {K : submodule 𝕜 E} :
  findim 𝕜 K + findim 𝕜 Kᗮ = findim 𝕜 E :=
begin
  convert submodule.findim_add_inf_findim_orthogonal (le_top : K ≤ ⊤) using 1,
  { rw inf_top_eq },
  { simp }
end

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
lemma submodule.findim_add_findim_orthogonal' [finite_dimensional 𝕜 E] {K : submodule 𝕜 E} {n : ℕ}
  (h_dim : findim 𝕜 K + n = findim 𝕜 E) :
  findim 𝕜 Kᗮ = n :=
by { rw ← add_right_inj (findim 𝕜 K), simp [submodule.findim_add_findim_orthogonal, h_dim] }

local attribute [instance] finite_dimensional_of_findim_eq_succ

/-- In a finite-dimensional inner product space, the dimension of the orthogonal complement of the
span of a nonzero vector is one less than the dimension of the space. -/
lemma findim_orthogonal_span_singleton {n : ℕ} [_i : fact (findim 𝕜 E = n + 1)]
  {v : E} (hv : v ≠ 0) :
  findim 𝕜 (𝕜 ∙ v)ᗮ = n :=
submodule.findim_add_findim_orthogonal' $ by simp [findim_span_singleton hv, _i.elim, add_comm]

end orthogonal

section orthonormal_basis

/-! ### Existence of Hilbert basis, orthonormal basis, etc. -/

variables {𝕜 E} {v : set E}

open finite_dimensional submodule set

/-- An orthonormal set in an `inner_product_space` is maximal, if and only if the orthogonal
complement of its span is empty. -/
lemma maximal_orthonormal_iff_orthogonal_complement_eq_bot (hv : orthonormal 𝕜 (coe : v → E)) :
  (∀ u ⊇ v, orthonormal 𝕜 (coe : u → E) → u = v) ↔ (span 𝕜 v)ᗮ = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  split,
  { contrapose!,
    -- ** direction 1: nonempty orthogonal complement implies nonmaximal
    rintros ⟨x, hx', hx⟩,
    -- take a nonzero vector and normalize it
    let e := (∥x∥⁻¹ : 𝕜) • x,
    have he : ∥e∥ = 1 := by simp [e, norm_smul_inv_norm hx],
    have he' : e ∈ (span 𝕜 v)ᗮ := smul_mem' _ _ hx',
    have he'' : e ∉ v,
    { intros hev,
      have : e = 0,
      { have : e ∈ (span 𝕜 v) ⊓ (span 𝕜 v)ᗮ := ⟨subset_span hev, he'⟩,
        simpa [(span 𝕜 v).inf_orthogonal_eq_bot] using this },
      have : e ≠ 0 := hv.ne_zero ⟨e, hev⟩,
      contradiction },
    -- put this together with `v` to provide a candidate orthonormal basis for the whole space
    refine ⟨v.insert e, v.subset_insert e, ⟨_, _⟩, (v.ne_insert_of_not_mem he'').symm⟩,
    { -- show that the elements of `v.insert e` have unit length
      rintros ⟨a, ha'⟩,
      cases eq_or_mem_of_mem_insert ha' with ha ha,
      { simp [ha, he] },
      { exact hv.1 ⟨a, ha⟩ } },
    { -- show that the elements of `v.insert e` are orthogonal
      have h_end : ∀ a ∈ v, ⟪a, e⟫ = 0,
      { intros a ha,
        exact he' a (submodule.subset_span ha) },
      rintros ⟨a, ha'⟩,
      cases eq_or_mem_of_mem_insert ha' with ha ha,
      { rintros ⟨b, hb'⟩ hab',
        have hb : b ∈ v,
        { refine mem_of_mem_insert_of_ne hb' _,
          intros hbe',
          apply hab',
          simp [ha, hbe'] },
        rw inner_eq_zero_sym,
        simpa [ha] using h_end b hb },
      rintros ⟨b, hb'⟩ hab',
      cases eq_or_mem_of_mem_insert hb' with hb hb,
      { simpa [hb] using h_end a ha },
      have : (⟨a, ha⟩ : v) ≠ ⟨b, hb⟩,
      { intros hab'',
        apply hab',
        simpa using hab'' },
      exact hv.2 this } },
    { -- ** direction 2: empty orthogonal complement implies maximal
      simp only [subset.antisymm_iff],
      rintros h u (huv : v ⊆ u) hu,
      refine ⟨_, huv⟩,
      intros x hxu,
      refine ((mt (h x)) (hu.ne_zero ⟨x, hxu⟩)).imp_symm _,
      intros hxv y hy,
      have hxv' : (⟨x, hxu⟩ : u) ∉ (coe ⁻¹' v : set u) := by simp [huv, hxv],
      obtain ⟨l, hl, rfl⟩ :
        ∃ l ∈ finsupp.supported 𝕜 𝕜 (coe ⁻¹' v : set u), (finsupp.total ↥u E 𝕜 coe) l = y,
      { rw ← finsupp.mem_span_iff_total,
        simp [huv, inter_eq_self_of_subset_left, hy] },
      exact hu.inner_finsupp_eq_zero hxv' hl }
end

/-- An orthonormal set in an `inner_product_space` is maximal, if and only if the closure of its
span is the whole space. -/
lemma maximal_orthonormal_iff_dense_span [complete_space E] (hv : orthonormal 𝕜 (coe : v → E)) :
  (∀ u ⊇ v, orthonormal 𝕜 (coe : u → E) → u = v) ↔ (span 𝕜 v).topological_closure = ⊤ :=
by rw [maximal_orthonormal_iff_orthogonal_complement_eq_bot hv, ← submodule.orthogonal_eq_top_iff,
  (span 𝕜 v).orthogonal_orthogonal_eq_closure]

/-- Any orthonormal subset can be extended to an orthonormal set whose span is dense. -/
lemma exists_subset_is_orthonormal_dense_span
  [complete_space E] (hv : orthonormal 𝕜 (coe : v → E)) :
  ∃ u ⊇ v, orthonormal 𝕜 (coe : u → E) ∧ (span 𝕜 u).topological_closure = ⊤ :=
begin
  obtain ⟨u, hus, hu, hu_max⟩ := exists_maximal_orthonormal hv,
  rw maximal_orthonormal_iff_dense_span hu at hu_max,
  exact ⟨u, hus, hu, hu_max⟩
end

variables (𝕜 E)
/-- An inner product space admits an orthonormal set whose span is dense. -/
lemma exists_is_orthonormal_dense_span [complete_space E] :
  ∃ u : set E, orthonormal 𝕜 (coe : u → E) ∧ (span 𝕜 u).topological_closure = ⊤ :=
let ⟨u, hus, hu, hu_max⟩ := exists_subset_is_orthonormal_dense_span (orthonormal_empty 𝕜 E) in
⟨u, hu, hu_max⟩
variables {𝕜 E}

/-- An orthonormal set in a finite-dimensional `inner_product_space` is maximal, if and only if it
is a basis. -/
lemma maximal_orthonormal_iff_is_basis_of_finite_dimensional
  [finite_dimensional 𝕜 E] (hv : orthonormal 𝕜 (coe : v → E)) :
  (∀ u ⊇ v, orthonormal 𝕜 (coe : u → E) → u = v) ↔ is_basis 𝕜 (coe : v → E) :=
begin
  rw maximal_orthonormal_iff_orthogonal_complement_eq_bot hv,
  have hv_compl : is_complete (span 𝕜 v : set E) := (span 𝕜 v).complete_of_finite_dimensional,
  rw submodule.orthogonal_eq_bot_iff hv_compl,
  have hv_coe : range (coe : v → E) = v := by simp,
  split,
  { refine λ h, ⟨hv.linear_independent, _⟩,
    convert h },
  { intros h,
    convert ← h.2 }
end

/-- In a finite-dimensional `inner_product_space`, any orthonormal subset can be extended to an
orthonormal basis. -/
lemma exists_subset_is_orthonormal_basis
  [finite_dimensional 𝕜 E] (hv : orthonormal 𝕜 (coe : v → E)) :
  ∃ u ⊇ v, orthonormal 𝕜 (coe : u → E) ∧ is_basis 𝕜 (coe : u → E) :=
begin
  obtain ⟨u, hus, hu, hu_max⟩ := exists_maximal_orthonormal hv,
  rw maximal_orthonormal_iff_is_basis_of_finite_dimensional hu at hu_max,
  exact ⟨u, hus, hu, hu_max⟩
end

variables (𝕜 E)
/-- A finite-dimensional `inner_product_space` has an orthonormal basis. -/
lemma exists_is_orthonormal_basis [finite_dimensional 𝕜 E] :
  ∃ u : set E, orthonormal 𝕜 (coe : u → E) ∧ is_basis 𝕜 (coe : u → E) :=
let ⟨u, hus, hu, hu_max⟩ := exists_subset_is_orthonormal_basis (orthonormal_empty 𝕜 E) in
⟨u, hu, hu_max⟩
variables {𝕜 E}

/-- Given a natural number `n` equal to the `findim` of a finite-dimensional inner product space,
there exists an orthonormal basis for the space indexed by `fin n`. -/
lemma exists_is_orthonormal_basis' [finite_dimensional 𝕜 E] {n : ℕ} (hn : findim 𝕜 E = n) :
  ∃ v : fin n → E, orthonormal 𝕜 v ∧ is_basis 𝕜 v :=
begin
  obtain ⟨u, hu, hu_basis⟩ := exists_is_orthonormal_basis 𝕜 E,
  obtain ⟨g, hg⟩ := finite_dimensional.equiv_fin_of_dim_eq hn hu_basis,
  exact ⟨coe ∘ g, hu.comp _ g.injective, hg⟩
end

/-- Given a natural number `n` equal to the `findim` of a finite-dimensional inner product space,
there exists an isometry from the space to `euclidean_space 𝕜 (fin n)`. -/
def linear_isometry_equiv.of_inner_product_space
  [finite_dimensional 𝕜 E] {n : ℕ} (hn : findim 𝕜 E = n) :
  E ≃ₗᵢ[𝕜] (euclidean_space 𝕜 (fin n)) :=
let hv := classical.some_spec (exists_is_orthonormal_basis' hn) in
hv.2.isometry_euclidean_of_orthonormal hv.1

local attribute [instance] finite_dimensional_of_findim_eq_succ

/-- Given a natural number `n` one less than the `findim` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`euclidean_space 𝕜 (fin n)`. -/
def linear_isometry_equiv.from_orthogonal_span_singleton
  (n : ℕ) [fact (findim 𝕜 E = n + 1)] {v : E} (hv : v ≠ 0) :
  (𝕜 ∙ v)ᗮ ≃ₗᵢ[𝕜] (euclidean_space 𝕜 (fin n)) :=
linear_isometry_equiv.of_inner_product_space (findim_orthogonal_span_singleton hv)

end orthonormal_basis
