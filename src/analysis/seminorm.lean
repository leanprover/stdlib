/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/

import algebra.pointwise
import analysis.normed_space.basic
import analysis.convex.basic
import data.set.intervals

/-!
# Seminorms and Local Convexity

This file introduces the following notions, defined for a vector space
over a normed field:

- the subset properties of being `absorbent` and `balanced`,

- a `seminorm`, a function to the reals that is positive-semidefinite,
  absolutely homogeneous, and subadditive.

We prove related properties.

This file defines the `gauge` (also known as the Minkowski functional) of a subset of a real vector
space, and shows the algebraic properties of this functional dependent on the geometric properties
of the given subset.

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
{E : Type*} [add_comm_group E] [module 𝕜 E]

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

lemma balanced.univ : balanced 𝕜 (univ : set E) :=
λ a ha, subset_univ _

lemma balanced.union {A₁ A₂ : set E} (hA₁ : balanced 𝕜 A₁) (hA₂ : balanced 𝕜 A₂) :
  balanced 𝕜 (A₁ ∪ A₂) :=
begin
  intros a ha t ht,
  rw [smul_set_union] at ht,
  exact ht.imp (λ x, hA₁ _ ha x) (λ x, hA₂ _ ha x),
end

lemma balanced.inter {A₁ A₂ : set E} (hA₁ : balanced 𝕜 A₁) (hA₂ : balanced 𝕜 A₂) :
  balanced 𝕜 (A₁ ∩ A₂) :=
begin
  rintro a ha _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩,
  exact ⟨hA₁ _ ha ⟨_, hx₁, rfl⟩, hA₂ _ ha ⟨_, hx₂, rfl⟩⟩,
end

lemma balanced.add {A₁ A₂ : set E} (hA₁ : balanced 𝕜 A₁) (hA₂ : balanced 𝕜 A₂) :
  balanced 𝕜 (A₁ + A₂) :=
begin
  rintro a ha _ ⟨_, ⟨x, y, hx, hy, rfl⟩, rfl⟩,
  rw smul_add,
  exact ⟨_, _, hA₁ _ ha ⟨_, hx, rfl⟩, hA₂ _ ha ⟨_, hy, rfl⟩, rfl⟩,
end

lemma balanced.smul (hA : balanced 𝕜 A) : balanced 𝕜 (a • A) :=
begin
  rintro b hb _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩,
  exact ⟨b • x, hA _ hb ⟨_, hx, rfl⟩, smul_comm _ _ _⟩,
end

lemma absorbent_iff_forall_absorbs_singleton :
  absorbent 𝕜 A ↔ ∀ x, absorbs 𝕜 A {x} :=
by simp [absorbs, absorbent]

/-!
Properties of balanced and absorbent sets in a topological vector space:
-/
variables [topological_space E] [has_continuous_smul 𝕜 E]

/-- Every neighbourhood of the origin is absorbent. -/
lemma absorbent_nhds_zero (hA : A ∈ 𝓝 (0 : E)) : absorbent 𝕜 A :=
begin
  intro x,
  rcases mem_nhds_iff.mp hA with ⟨w, hw₁, hw₂, hw₃⟩,
  have hc : continuous (λ t : 𝕜, t • x), from continuous_id.smul continuous_const,
  rcases metric.is_open_iff.mp (hw₂.preimage hc) 0 (by rwa [mem_preimage, zero_smul])
    with ⟨r, hr₁, hr₂⟩,
  have hr₃, from inv_pos.mpr (half_pos hr₁),
  use [(r/2)⁻¹, hr₃],
  intros a ha₁,
  have ha₂ : 0 < ∥a∥ := hr₃.trans_le ha₁,
  have ha₃ : a ⁻¹ • x ∈ w,
  { apply hr₂,
    rw [metric.mem_ball, dist_zero_right, norm_inv],
    calc ∥a∥⁻¹ ≤ r/2 : (inv_le (half_pos hr₁) ha₂).mp ha₁
    ...       < r : half_lt_self hr₁ },
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
    exacts [subset_union_left _ _, ⟨0, or.inl rfl⟩] },
  { rw [←image_smul, image_union],
    apply union_subset_union,
    { rw [image_singleton, smul_zero] },
    { calc a • interior A ⊆ interior (a • A) : (is_open_map_smul' h).image_interior_subset A
                      ... ⊆ interior A       : interior_mono (hA _ ha) } }
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
assume a ha,
calc _ ⊆ closure (a • A) : image_closure_subset_closure_image (continuous_id.const_smul _)
...    ⊆ _ : closure_mono (hA _ ha)

end

section
/-!
### Seminorms
-/

/-- A seminorm on a vector space over a normed field is a function to
the reals that is positive semidefinite, positive homogeneous, and
subadditive. -/
structure seminorm (𝕜 : Type*) (E : Type*)
  [normed_field 𝕜] [add_comm_group E] [module 𝕜 E] :=
(to_fun    : E → ℝ)
(smul'     : ∀ (a : 𝕜) (x : E), to_fun (a • x) = ∥a∥ * to_fun x)
(triangle' : ∀ x y : E, to_fun (x + y) ≤ to_fun x + to_fun y)

variables
{𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [add_comm_group E] [module 𝕜 E]

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
end

noncomputable theory
variables {E : Type*} [add_comm_group E] [module ℝ E]

/--
Given a subset `K` of a real vector space, we have a functional (sometimes called the Minkowski
functional) which sends `x : E` to `Inf {y ∈ set.Ioi 0 | x ∈ y • K}`, essentially the smallest
`y` such that `x` is in `K` expanded by `y`.
-/
def gauge (K : set E) (x : E) : ℝ :=
Inf {y ∈ set.Ioi 0 | x ∈ y • K}

variables {K : set E} {x : E}

lemma gauge_def : gauge K x = Inf {y ∈ set.Ioi 0 | x ∈ y • K} := rfl
/-- An alternate definition of the gauge which can be useful in certain situations. -/
lemma gauge_def' : gauge K x = Inf {y ∈ set.Ioi 0 | y⁻¹ • x ∈ K} :=
begin
  rw gauge_def,
  congr' 1,
  ext y,
  apply and_congr_right,
  intro hy,
  apply mem_smul_set_iff_inv_smul_mem (ne_of_gt hy),
end

/-- If the given subset is `absorbent` then the set we take an infimum over in `gauge` is nonempty,
which is useful for proving many properties about the gauge.  -/
lemma gauge_set_nonempty_of_absorbent (absorbs : absorbent ℝ K) :
  {y ∈ set.Ioi (0:ℝ) | x ∈ y • K}.nonempty :=
let ⟨θ, hθ₁, hθ₂⟩ := absorbs x in ⟨θ, hθ₁, hθ₂ θ (real.norm_of_nonneg (le_of_lt hθ₁)).ge⟩

lemma gauge_set_bdd_below :
  bdd_below {y ∈ set.Ioi (0:ℝ) | x ∈ y • K} :=
⟨0, λ y hy, le_of_lt hy.1⟩

/-- The gauge evaluated at `0` is always zero (mathematically this requires that `0` is in the
subset `K`, but as the real infimum of the empty set in Lean is defined to be `0`, it holds
unconditionally). -/
@[simp] lemma gauge_zero : gauge K 0 = 0 :=
begin
  rw gauge_def',
  by_cases (0:E) ∈ K,
  { simp [h] },
  { simp [h, real.Inf_empty] },
end

-- TODO: move this lemma to convex?
lemma smul_mem_of_convex (hK : convex K) (zero_mem : (0:E) ∈ K)
  {θ : ℝ} (hθ₁ : 0 ≤ θ) (hθ₂ : θ ≤ 1)
  (hx : x ∈ K) : θ • x ∈ K :=
begin
  have := hK.segment_subset zero_mem hx,
  rw segment_eq_image at this,
  apply this ⟨_, ⟨‹0 ≤ θ›, ‹_›⟩, by simp⟩,
end

-- TODO: move this lemma to convex?
lemma mem_smul_of_convex (hK : convex K) (zero_mem : (0:E) ∈ K)
  {θ : ℝ} (hθ₂ : 1 ≤ θ)
  (hx : x ∈ K) : x ∈ θ • K :=
begin
  rw mem_smul_set_iff_inv_smul_mem (zero_lt_one.trans_le hθ₂).ne',
  apply smul_mem_of_convex hK zero_mem (inv_nonneg.2 (zero_le_one.trans hθ₂)) (inv_le_one hθ₂) hx,
end

/-- The gauge is always nonnegative. -/
lemma gauge_nonneg (x : E) :
  0 ≤ gauge K x :=
real.Inf_nonneg _ (λ x hx, le_of_lt hx.1)

lemma gauge_le_one_eq (hK : convex K) (zero_mem : (0:E) ∈ K)
  (absorbs : absorbent ℝ K) :
  {x | gauge K x ≤ 1} = ⋂ (θ ∈ set.Ioi (1:ℝ)), θ • K :=
begin
  ext,
  simp only [set.mem_Ioi, set.mem_Inter, set.mem_set_of_eq],
  split,
  { intros h θ hθ,
    rw mem_smul_set_iff_inv_smul_mem (show θ ≠ 0, by linarith),
    rcases exists_lt_of_cInf_lt _ (lt_of_le_of_lt h hθ) with ⟨δ, ⟨hδ₁, hδ₂⟩, _⟩,
    { suffices : (θ⁻¹ * δ) • δ⁻¹ • x ∈ K,
      { rwa [smul_smul, mul_inv_cancel_right' ‹0 < δ›.ne'] at this },
      rw mem_smul_set_iff_inv_smul_mem ‹0 < δ›.ne' at hδ₂,
      apply smul_mem_of_convex hK zero_mem _ _ hδ₂,
      { refine mul_nonneg (inv_nonneg.2 (by linarith)) (le_of_lt hδ₁), },
      { rw [inv_mul_le_iff (lt_trans ‹0 < δ› ‹δ < θ›), mul_one],
        apply ‹δ < θ›.le } },
    apply gauge_set_nonempty_of_absorbent absorbs },
  { intro h,
    apply le_of_forall_pos_lt_add,
    intros ε hε,
    apply cInf_lt_of_lt gauge_set_bdd_below _ (add_lt_add_left (half_lt_self hε) _),
    exact ⟨by { simp, linarith }, h _ (by linarith)⟩ }
end

lemma gauge_lt_one_eq (absorbs : absorbent ℝ K) :
  {x | gauge K x < 1} = ⋃ (θ ∈ set.Ioo 0 (1:ℝ)), θ • K :=
begin
  ext,
  simp only [exists_prop, set.mem_Union, set.mem_Ioi, set.mem_set_of_eq, gauge_def],
  split,
  { intro h,
    obtain ⟨θ, ⟨h₁, h₂⟩, h₃⟩ := exists_lt_of_cInf_lt (gauge_set_nonempty_of_absorbent absorbs) h,
    exact ⟨θ, ⟨h₁, h₃⟩, h₂⟩ },
  { rintro ⟨θ, ⟨_, _⟩, _⟩,
    apply cInf_lt_of_lt gauge_set_bdd_below ⟨‹0 < θ›, ‹_›⟩ ‹θ < 1› }
end

lemma gauge_lt_one_subset_self (hK : convex K) (zero_mem : (0:E) ∈ K) (absorbs : absorbent ℝ K) :
  {x | gauge K x < 1} ⊆ K :=
begin
  rw gauge_lt_one_eq absorbs,
  apply set.bUnion_subset,
  intros θ hθ,
  rintro _ ⟨y, hy, rfl⟩,
  rw convex_iff_segment_subset at hK,
  simp_rw segment_eq_image at hK,
  apply hK zero_mem hy ⟨θ, set.Ioo_subset_Icc_self hθ, _⟩,
  simp,
end

lemma gauge_le_one_of_mem (x : E) (hx : x ∈ K) : gauge K x ≤ 1 :=
real.Inf_le _ ⟨0, λ y hy, le_of_lt hy.1⟩ ⟨by norm_num, by simpa⟩

lemma self_subset_gauge_le_one : K ⊆ {x | gauge K x ≤ 1} :=
λ x, gauge_le_one_of_mem _

lemma gauge_le_one_convex (hK : convex K) (zero_mem : (0:E) ∈ K) (absorbs : absorbent ℝ K) :
  convex {x | gauge K x ≤ 1} :=
begin
  rw gauge_le_one_eq hK zero_mem absorbs,
  refine convex_Inter (λ i, convex_Inter (λ (hi : _ < _), convex.smul _ hK)),
end

lemma gauge_le_of_mem (x : E) {θ : ℝ} (hθ : 0 < θ) (hx : x ∈ θ • K) :
  gauge K x ≤ θ :=
cInf_le gauge_set_bdd_below ⟨hθ, hx⟩

lemma interior_subset_gauge_lt_one [topological_space E] [has_continuous_smul ℝ E] :
  interior K ⊆ {x | gauge K x < 1} :=
begin
  intros x hx,
  let f : ℝ → E := λ t, t • x,
  have : continuous f,
  { continuity },
  let K' := f ⁻¹' (interior K),
  have : is_open K' := this.is_open_preimage _ is_open_interior,
  have one_mem : (1:ℝ) ∈ K',
  { change _ • _ ∈ interior K,
    simpa },
  obtain ⟨ε, _, hε₂⟩ := (metric.nhds_basis_closed_ball.1 _).1 (is_open_iff_mem_nhds.1 this 1 ‹_›),
  rw closed_ball_Icc at hε₂,
  have : (1 + ε)⁻¹ < 1,
  { rw inv_lt_one_iff,
    right,
    linarith },
  refine cInf_lt_of_lt gauge_set_bdd_below ⟨_, _⟩ ‹(1 + ε)⁻¹ < 1›,
  { change (0:ℝ) < _,
    rw inv_pos,
    linarith },
  change _ ∈ _,
  rw mem_inv_smul_set_iff (show 1 + ε ≠ 0, by linarith),
  apply interior_subset,
  apply hε₂,
  simp,
  linarith
end

lemma gauge_lt_one_eq_self_of_open [topological_space E] [has_continuous_smul ℝ E]
  (hK : convex K) (zero_mem : (0:E) ∈ K) (hK₂ : is_open K) :
  {x | gauge K x < 1} = K :=
begin
  apply set.subset.antisymm,
  { apply gauge_lt_one_subset_self hK ‹_› (absorbent_nhds_zero (hK₂.mem_nhds zero_mem)) },
  refine set.subset.trans _ interior_subset_gauge_lt_one,
  rw hK₂.interior_eq
end

lemma gauge_lt_one_of_mem_of_open [topological_space E] [has_continuous_smul ℝ E]
  (hK : convex K) (zero_mem : (0:E) ∈ K) (hK₂ : is_open K) (x : E) (hx : x ∈ K) :
  gauge K x < 1 :=
by rwa ←gauge_lt_one_eq_self_of_open hK zero_mem hK₂ at hx

lemma one_le_gauge_of_not_mem [topological_space E] [has_continuous_smul ℝ E]
  (hK : convex K) (zero_mem : (0:E) ∈ K)
  (hK₂ : is_open K) (x : E) (hx : x ∉ K) :
  1 ≤ gauge K x :=
begin
  rw ←gauge_lt_one_eq_self_of_open hK zero_mem hK₂ at hx,
  exact le_of_not_lt hx
end

lemma real.Inf_smul (K : set ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
  θ * Inf K = Inf (θ • K) :=
begin
  cases K.eq_empty_or_nonempty,
  { subst h,
    simp [real.Inf_empty] },
  by_cases h₁ : bdd_below K,
  { have : monotone (λ x, (θ:ℝ) * x),
    { exact monotone_mul_left_of_nonneg hθ },
    have z := map_cInf_of_continuous_at_of_monotone (continuous_mul_left θ).continuous_at
                  (monotone_mul_left_of_nonneg hθ) ‹_› ‹_›,
    dsimp at z,
    rw [z, ←set.image_smul],
    refl },
  { rw [real.Inf_of_not_bdd_below h₁, mul_zero],
    rcases eq_or_lt_of_le hθ with (rfl | hθ),
    { rw zero_smul_set h,
      have : (0 : set ℝ) = {0},
      { ext, simp },
      rw this,
      simp only [cInf_singleton] },
    { rw real.Inf_of_not_bdd_below,
      rintro ⟨t, ht⟩,
      apply h₁,
      refine ⟨t / θ, λ z hz, _⟩,
      rw div_le_iff hθ,
      apply ht,
      rw mul_comm,
      exact ⟨_, hz, smul_eq_mul _⟩ } },
end

lemma gauge_neg (symmetric : ∀ x ∈ K, -x ∈ K) (x : E) :
  gauge K (-x) = gauge K x :=
begin
  have : ∀ x, -x ∈ K ↔ x ∈ K := λ x, ⟨λ h, by simpa using symmetric _ h, symmetric x⟩,
  rw [gauge_def', gauge_def'],
  simp_rw [smul_neg, this],
end

lemma gauge_mul_nonneg
  {θ : ℝ} (hθ : 0 ≤ θ) (x : E) :
gauge K (θ • x) = θ * gauge K x :=
begin
  rcases eq_or_lt_of_le hθ with (rfl | hθ'),
  { simp },
  rw [gauge_def', gauge_def'],
  change Inf _ = _ * Inf _,
  rw real.Inf_smul _ ‹0 ≤ θ›,
  congr' 1,
  ext β,
  simp only [set.mem_smul_set, set.mem_sep_eq, smul_eq_mul, set.mem_Ioi],
  split,
  { rintro ⟨hβ₁, hβ₂⟩,
    refine ⟨β * θ⁻¹, ⟨mul_pos ‹0 < β› (inv_pos.2 ‹0 < θ›), _⟩, _⟩,
    rwa [mul_inv', inv_inv', mul_smul],
    rw [mul_left_comm, mul_inv_cancel (ne_of_gt ‹0 < θ›), mul_one] },
  { rintro ⟨β, ⟨_, _⟩, rfl⟩,
    refine ⟨mul_pos ‹0 < θ› ‹0 < β›, _⟩,
    rwa [mul_inv_rev', ←mul_smul, mul_assoc, inv_mul_cancel (ne_of_gt ‹0 < θ›), mul_one] }
end

lemma gauge_homogeneous (symmetric : ∀ x ∈ K, -x ∈ K)
  (θ : ℝ) (x : E) :
  gauge K (θ • x) = abs θ * gauge K x :=
begin
  rw ←gauge_mul_nonneg (abs_nonneg θ),
  cases le_total 0 θ,
  { rw abs_of_nonneg h },
  { rw [abs_of_nonpos h, neg_smul, gauge_neg symmetric] }
end

lemma gauge_subadditive (hK : convex K)
  (absorbs : absorbent ℝ K) (x y : E) :
  gauge K (x + y) ≤ gauge K x + gauge K y :=
begin
  apply le_of_forall_pos_lt_add,
  intros ε hε,
  obtain ⟨a, ⟨ha₁ : _ < _, ha₂⟩, ha₃ : _ < gauge _ _ + _⟩ :=
    exists_lt_of_cInf_lt (gauge_set_nonempty_of_absorbent absorbs)
      (lt_add_of_pos_right (gauge K x) (half_pos hε)),
  obtain ⟨b, ⟨hb₁ : _ < _, hb₂⟩, hb₃ : _ < gauge _ _ + _⟩ :=
    exists_lt_of_cInf_lt (gauge_set_nonempty_of_absorbent absorbs)
      (lt_add_of_pos_right (gauge K y) (half_pos hε)),
  suffices : gauge K (x + y) ≤ a + b,
  { linarith },
  rw convex_iff_div at hK,
  rw mem_smul_set_iff_inv_smul_mem ha₁.ne' at ha₂,
  rw mem_smul_set_iff_inv_smul_mem hb₁.ne' at hb₂,
  have := hK ha₂ hb₂ (le_of_lt ha₁) (le_of_lt hb₁) (by linarith),
  rw [smul_smul, smul_smul, mul_comm_div', mul_comm_div', ←mul_div_assoc, ←mul_div_assoc,
    mul_inv_cancel (ne_of_gt ha₁), mul_inv_cancel (ne_of_gt hb₁), ←smul_add] at this,
  apply gauge_le_of_mem,
  { linarith },
  rw mem_smul_set_iff_inv_smul_mem (show a + b ≠ 0, by linarith),
  simpa,
end

/-- If `K` is symmetric, convex and absorbent, it defines a seminorm. -/
def gauge_seminorm (symmetric : ∀ x ∈ K, -x ∈ K) (hK : convex K) (hK' : absorbent ℝ K) :
  seminorm ℝ E :=
{ to_fun := gauge K,
  smul' := λ θ x, by rw [gauge_homogeneous symmetric, real.norm_eq_abs],
  triangle' := gauge_subadditive hK hK' }

-- TODO: topology induced by family of seminorms, local convexity.
