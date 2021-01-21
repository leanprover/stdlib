/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/

import analysis.normed_space.basic

/-!
# Seminorms and Local Convexity

This file introduces the following notions, defined for a vector space
over a normed field:

- the subset properties of being `absorbent` and `balanced`,

- a `seminorm`, a function to the reals that is positive-semidefinite,
  absolutely homogeneous, and subadditive.

We prove related properties.

## TODO

Define and show equivalence of two notions of local convexity for a
topological vector space over ℝ or ℂ: that it has a local base of
balanced convex absorbent sets, and that it carries the initial
topology induced by a family of seminorms.

## References
* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]
-/

/-!
### Subset Properties

Absorbent and balanced sets in a vector space over a
nondiscrete normed field.
-/

section

variables
(𝕜 : Type*) [nondiscrete_normed_field 𝕜]
{E : Type*} [add_comm_group E] [vector_space 𝕜 E]

open set normed_field
open_locale topological_space

/-- A set `A` absorbs another set `B` if `B` is contained in scaling
`A` by elements of sufficiently large norms. -/
def absorbs (A B : set E) := ∃ r > 0, ∀ a : 𝕜, r ≤ ∥a∥ → B ⊆ a • A

/-- A set is absorbent if it absorbs every singleton. -/
def absorbent (A : set E) := ∀ x, ∃ r > 0, ∀ a : 𝕜, r ≤ ∥a∥ → x ∈ a • A

/-- A set `A` is balanced if `a • A` is contained in `A` whenever `a`
has norm no greater than one. -/
def balanced (A : set E) := ∀ a : 𝕜, ∥a∥ ≤ 1 → a • A ⊆ A

variables {𝕜} (a : 𝕜) {A : set E}

/-- A balanced set absorbs itself. -/
lemma balanced.absorbs_self (hA : balanced 𝕜 A) : absorbs 𝕜 A A :=
begin
  use [1, zero_lt_one],
  intros a ha x hx,
  rw mem_smul_set_iff_inv_smul_mem,
  { apply hA a⁻¹,
    { rw norm_inv, exact inv_le_one ha },
    { rw mem_smul_set, use [x, hx] }},
  { rw ←norm_pos_iff, calc 0 < 1 : zero_lt_one ... ≤ ∥a∥ : ha, }
end

/-!
Properties of balanced and absorbing sets in a topological vector space:
-/
variables [topological_space E] [topological_vector_space 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
lemma absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : absorbent 𝕜 A :=
begin
  intro x,
  rcases mem_nhds_sets_iff.mp hA with ⟨w, hw₁, hw₂, hw₃⟩,
  have hc : continuous (λ t : 𝕜, t • x), from continuous_id.smul continuous_const,
  rcases metric.is_open_iff.mp (hw₂.preimage hc) 0 (by rwa [mem_preimage, zero_smul])
    with ⟨r, hr₁, hr₂⟩,
  have hr₃, from inv_pos.mpr (half_pos hr₁),
  use [(r/2)⁻¹, hr₃],
  intros a ha₁,
  have ha₂ : 0 < ∥a∥, from calc 0 < _ : hr₃ ... ≤ _ : ha₁,
  have ha₃ : a ⁻¹ • x ∈ w, begin
    apply hr₂,
    rw [metric.mem_ball, dist_eq_norm, sub_zero, norm_inv],
    calc ∥a∥⁻¹ ≤ r/2 : (inv_le (half_pos hr₁) ha₂).mp ha₁
    ...       < r : half_lt_self hr₁,
  end,
  rw [mem_smul_set_iff_inv_smul_mem (norm_pos_iff.mp ha₂)],
  exact hw₁ ha₃,
end

/-- The union of `{0}` with the interior of a balanced set
    is balanced. -/
lemma balanced_zero_union_interior (hA : balanced 𝕜 A) :
  balanced 𝕜 ({(0 : E)} ∪ interior A) :=
begin
  intros a ha, by_cases a = 0,
  { rw [h, zero_smul_set],
    apply subset_union_left _,
    exact union_nonempty.mpr (or.intro_left _ $ singleton_nonempty _) },
  { rw [←image_smul, image_union, union_subset_iff], split,
    { rw [image_singleton, smul_zero], exact subset_union_left _ _ },
    { apply subset_union_of_subset_right,
      apply interior_maximal,
      rw image_subset_iff,
      calc _ ⊆ A : interior_subset
      ...    ⊆ _ : by { rw ←image_subset_iff, exact hA _ ha},
      exact is_open_map_smul_of_ne_zero h _ is_open_interior }},
end

/-- The interior of a balanced set is balanced if it contains the origin. -/
lemma balanced.interior (hA : balanced 𝕜 A) (h : (0 : E) ∈ interior A) :
  balanced 𝕜 (interior A) :=
begin
  rw ←singleton_subset_iff at h,
  rw [←union_eq_self_of_subset_left h],
  exact balanced_zero_union_interior hA,
end

/-- The closure of a balanced set is balanced. -/
lemma balanced.closure (hA : balanced 𝕜 A) : balanced 𝕜 (closure A) :=
begin
  intros a ha,
  calc _ ⊆ closure (a • A) :
  by { simp_rw ←image_smul,
       exact image_closure_subset_closure_image
               (continuous_const.smul continuous_id) }
  ...    ⊆ _ : closure_mono (hA _ ha),
end

end

/-!
### Seminorms
-/

/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/
structure seminorm (𝕜 : Type*) (E : Type*)
  [normed_field 𝕜] [add_comm_group E] [vector_space 𝕜 E] :=
(to_fun    : E → ℝ)
(smul'     : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)
(triangle' : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)

variables
{𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [add_comm_group E] [vector_space 𝕜 E]

instance : inhabited (seminorm 𝕜 E) :=
⟨{ to_fun     := λ _, 0,
   smul'     := λ _ _, (mul_zero _).symm,
   triangle' := λ x y, by rw add_zero }⟩

instance : has_coe_to_fun (seminorm 𝕜 E) := ⟨_, λ p, p.to_fun⟩

namespace seminorm

variables (p : seminorm 𝕜 E) (c : 𝕜) (x y : E) (r : ℝ)

protected lemma smul : p (c • x) = ∥c∥ * p x := p.smul' _ _
protected lemma triangle : p (x + y) ≤ p x + p y := p.triangle' _ _

@[simp]
protected lemma zero : p 0 = 0 :=
calc p 0 = p ((0 : 𝕜) • 0) : by rw zero_smul
...      = 0 : by rw [p.smul, norm_zero, zero_mul]

@[simp]
protected lemma neg : p (-x) = p x :=
calc p (-x) = p ((-1 : 𝕜) • x) : by rw neg_one_smul
...         = p x : by rw [p.smul, norm_neg, norm_one, one_mul]

lemma nonneg : 0 ≤ p x :=
have h: 0 ≤ 2 * p x, from
calc 0 = p (x + (- x)) : by rw [add_neg_self, p.zero]
...    ≤ p x + p (-x)  : p.triangle _ _
...    = 2 * p x : by rw [p.neg, two_mul],
nonneg_of_mul_nonneg_left h zero_lt_two

lemma sub_rev : p (x - y) = p (y - x) :=
by rw [←neg_sub, p.neg]

/-- The ball of radius `r` at `x` with respect to seminorm `p`
    is the set of elements `y` with `p (y - x) < `r`. -/
def ball (p : seminorm 𝕜 E) (x : E) (r : ℝ) := { y : E | p (y - x) < r }

lemma mem_ball : y ∈ ball p x r ↔ p (y - x) < r :=
iff.rfl

lemma mem_ball_zero : y ∈ ball p 0 r ↔ p y < r :=
by rw [mem_ball, sub_zero]

lemma ball_zero_eq : ball p 0 r = { y : E | p y < r } :=
set.ext $ λ x,by { rw mem_ball_zero, exact iff.rfl }

/-- Seminorm-balls at the origin are balanced. -/
lemma balanced_ball_zero : balanced 𝕜 (ball p 0 r) :=
begin
  rintro a ha x ⟨y, hy, hx⟩,
  rw [mem_ball_zero, ←hx, p.smul],
  calc _ ≤ p y : mul_le_of_le_one_left (p.nonneg _) ha
  ...    < r   : by rwa mem_ball_zero at hy,
end

-- TODO: convexity and absorbent/balanced sets in vector spaces over ℝ

end seminorm

-- TODO: the minkowski functional, topology induced by family of
-- seminorms, local convexity.
