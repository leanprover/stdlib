/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import analysis.normed_space.basic
import topology.sequences

/-!
# Normed groups homomorphisms

This file gathers definitions and elementary constructions about bounded group homomorphisms
between normed (abelian) groups (abbreviated to "normed group homs").

The main lemmas relate the boundedness condition to continuity and Lipschitzness.

The main construction is to endow the type of normed group homs between two given normed groups
with a group structure and a norm, giving rise to a normed group structure. We provide several
simple constructions for normed group homs, like kernel, range and equalizer.

Some easy other constructions are related to subgroups of normed groups.

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory of `semi_normed_group_hom` and we specialize to `normed_group_hom` when needed.
-/

noncomputable theory
open_locale nnreal big_operators

/-- A morphism of seminormed abelian groups is a bounded group homomorphism. -/
structure normed_group_hom (V W : Type*) [semi_normed_group V] [semi_normed_group W] :=
(to_fun : V → W)
(map_add' : ∀ v₁ v₂, to_fun (v₁ + v₂) = to_fun v₁ + to_fun v₂)
(bound' : ∃ C, ∀ v, ∥to_fun v∥ ≤ C * ∥v∥)

namespace add_monoid_hom

variables {V W : Type*} [semi_normed_group V] [semi_normed_group W] {f g : normed_group_hom V W}

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_normed_group_hom'` for a version that uses `ℝ≥0` for the bound. -/
def mk_normed_group_hom (f : V →+ W)
  (C : ℝ) (h : ∀ v, ∥f v∥ ≤ C * ∥v∥) : normed_group_hom V W :=
{ bound' := ⟨C, h⟩, ..f }

/-- Associate to a group homomorphism a bounded group homomorphism under a norm control condition.

See `add_monoid_hom.mk_normed_group_hom` for a version that uses `ℝ` for the bound. -/
def mk_normed_group_hom' (f : V →+ W) (C : ℝ≥0) (hC : ∀ x, nnnorm (f x) ≤ C * nnnorm x) :
  normed_group_hom V W :=
{ bound' := ⟨C, hC⟩ .. f}

end add_monoid_hom

lemma exists_pos_bound_of_bound {V W : Type*} [semi_normed_group V] [semi_normed_group W]
  {f : V → W} (M : ℝ) (h : ∀x, ∥f x∥ ≤ M * ∥x∥) :
  ∃ N, 0 < N ∧ ∀x, ∥f x∥ ≤ N * ∥x∥ :=
⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), λx, calc
  ∥f x∥ ≤ M * ∥x∥ : h x
  ... ≤ max M 1 * ∥x∥ : mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _) ⟩

namespace normed_group_hom

variables {V V₁ V₂ V₃ : Type*}
variables [semi_normed_group V] [semi_normed_group V₁] [semi_normed_group V₂] [semi_normed_group V₃]
variables {f g : normed_group_hom V₁ V₂}

instance : has_coe_to_fun (normed_group_hom V₁ V₂) := ⟨_, normed_group_hom.to_fun⟩

initialize_simps_projections normed_group_hom (to_fun → apply)

lemma coe_inj (H : ⇑f = g) : f = g :=
by cases f; cases g; congr'; exact funext H

lemma coe_injective : @function.injective (normed_group_hom V₁ V₂) (V₁ → V₂) coe_fn :=
by apply coe_inj

lemma coe_inj_iff : f = g ↔ ⇑f = g := ⟨congr_arg _, coe_inj⟩

@[ext] lemma ext (H : ∀ x, f x = g x) : f = g := coe_inj $ funext H

lemma ext_iff : f = g ↔ ∀ x, f x = g x := ⟨by rintro rfl x; refl, ext⟩

variables (f g)

@[simp] lemma to_fun_eq_coe : f.to_fun = f := rfl

@[simp] lemma coe_mk (f) (h₁) (h₂) (h₃) : ⇑(⟨f, h₁, h₂, h₃⟩ : normed_group_hom V₁ V₂) = f := rfl

@[simp] lemma coe_mk_normed_group_hom (f : V₁ →+ V₂) (C) (hC) :
  ⇑(f.mk_normed_group_hom C hC) = f := rfl

@[simp] lemma coe_mk_normed_group_hom' (f : V₁ →+ V₂) (C) (hC) :
  ⇑(f.mk_normed_group_hom' C hC) = f := rfl

/-- The group homomorphism underlying a bounded group homomorphism. -/
def to_add_monoid_hom (f : normed_group_hom V₁ V₂) : V₁ →+ V₂ :=
add_monoid_hom.mk' f f.map_add'

@[simp] lemma coe_to_add_monoid_hom : ⇑f.to_add_monoid_hom = f := rfl

lemma to_add_monoid_hom_injective :
  function.injective (@normed_group_hom.to_add_monoid_hom V₁ V₂ _ _) :=
λ f g h, coe_inj $ show ⇑f.to_add_monoid_hom = g, by { rw h, refl }

@[simp] lemma mk_to_add_monoid_hom (f) (h₁) (h₂) :
  (⟨f, h₁, h₂⟩ : normed_group_hom V₁ V₂).to_add_monoid_hom = add_monoid_hom.mk' f h₁ := rfl

@[simp] lemma map_zero : f 0 = 0 := f.to_add_monoid_hom.map_zero

@[simp] lemma map_add (x y) : f (x + y) = f x + f y := f.to_add_monoid_hom.map_add _ _

@[simp] lemma map_sum {ι : Type*} (v : ι → V₁) (s : finset ι) :
  f (∑ i in s, v i) = ∑ i in s, f (v i) :=
f.to_add_monoid_hom.map_sum _ _

@[simp] lemma map_sub (x y) : f (x - y) = f x - f y := f.to_add_monoid_hom.map_sub _ _

@[simp] lemma map_neg (x) : f (-x) = -(f x) := f.to_add_monoid_hom.map_neg _

lemma bound : ∃ C, 0 < C ∧ ∀ x, ∥f x∥ ≤ C * ∥x∥ :=
let ⟨C, hC⟩ := f.bound' in exists_pos_bound_of_bound _ hC

theorem antilipschitz_of_norm_ge {K : ℝ≥0} (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
  antilipschitz_with K f :=
antilipschitz_with.of_le_mul_dist $
λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

/-! ### The operator norm -/

/-- The operator norm of a seminormed group homomorphism is the inf of all its bounds. -/
def op_norm (f : normed_group_hom V₁ V₂) := Inf {c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥}
instance has_op_norm : has_norm (normed_group_hom V₁ V₂) := ⟨op_norm⟩

lemma norm_def : ∥f∥ = Inf {c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥} := rfl

-- So that invocations of `real.Inf_le` make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : normed_group_hom V₁ V₂} :
  ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : normed_group_hom V₁ V₂} :
  bdd_below {c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥} :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ∥f∥ :=
real.lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm: `∥f x∥ ≤ ∥f∥ * ∥x∥`. -/
theorem le_op_norm (x : V₁) : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
begin
  obtain ⟨C, Cpos, hC⟩ := f.bound,
  replace hC := hC x,
  by_cases h : ∥x∥ = 0,
  { rwa [h, mul_zero] at ⊢ hC },
  have hlt : 0 < ∥x∥ := lt_of_le_of_ne (norm_nonneg x) (ne.symm h),
  exact  (div_le_iff hlt).mp ((real.le_Inf _ bounds_nonempty bounds_bdd_below).2 (λ c ⟨_, hc⟩,
    (div_le_iff hlt).mpr $ by { apply hc })),
end

theorem le_op_norm_of_le {c : ℝ} {x} (h : ∥x∥ ≤ c) : ∥f x∥ ≤ ∥f∥ * c :=
le_trans (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)

theorem le_of_op_norm_le {c : ℝ} (h : ∥f∥ ≤ c) (x : V₁) : ∥f x∥ ≤ c * ∥x∥ :=
(f.le_op_norm x).trans (mul_le_mul_of_nonneg_right h (norm_nonneg x))

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : lipschitz_with ⟨∥f∥, op_norm_nonneg f⟩ f :=
lipschitz_with.of_dist_le_mul $ λ x y,
  by { rw [dist_eq_norm, dist_eq_norm, ←map_sub], apply le_op_norm }

protected lemma uniform_continuous (f : normed_group_hom V₁ V₂) :
  uniform_continuous f := f.lipschitz.uniform_continuous

@[continuity]
protected lemma continuous (f : normed_group_hom V₁ V₂) : continuous f :=
f.uniform_continuous.continuous

lemma ratio_le_op_norm (x : V₁) : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
div_le_of_nonneg_of_le_mul (norm_nonneg _) f.op_norm_nonneg (le_op_norm _ _)

/-- If one controls the norm of every `f x`, then one controls the norm of `f`. -/
lemma op_norm_le_bound {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M :=
real.Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

theorem op_norm_le_of_lipschitz {f : normed_group_hom V₁ V₂} {K : ℝ≥0} (hf : lipschitz_with K f) :
  ∥f∥ ≤ K :=
f.op_norm_le_bound K.2 $ λ x, by simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0

/-- If a bounded group homomorphism map is constructed from a group homomorphism via the constructor
`mk_normed_group_hom`, then its norm is bounded by the bound given to the constructor if it is
nonnegative. -/
lemma mk_normed_group_hom_norm_le (f : V₁ →+ V₂) {C : ℝ} (hC : 0 ≤ C) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ∥f.mk_normed_group_hom C h∥ ≤ C :=
op_norm_le_bound _ hC h

/-- If a bounded group homomorphism map is constructed from a group homomorphism
via the constructor `mk_normed_group_hom`, then its norm is bounded by the bound
given to the constructor or zero if this bound is negative. -/
lemma mk_normed_group_hom_norm_le' (f : V₁ →+ V₂) {C : ℝ} (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ∥f.mk_normed_group_hom C h∥ ≤ max C 0 :=
op_norm_le_bound _ (le_max_right _ _) $ λ x, (h x).trans $
  mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg x)

alias mk_normed_group_hom_norm_le ← add_monoid_hom.mk_normed_group_hom_norm_le
alias mk_normed_group_hom_norm_le' ← add_monoid_hom.mk_normed_group_hom_norm_le'

/-! ### Addition of normed group homs -/

/-- Addition of normed group homs. -/
instance : has_add (normed_group_hom V₁ V₂) :=
⟨λ f g, (f.to_add_monoid_hom + g.to_add_monoid_hom).mk_normed_group_hom (∥f∥ + ∥g∥) $ λ v, calc
  ∥f v + g v∥
      ≤ ∥f v∥ + ∥g v∥ : norm_add_le _ _
  ... ≤ ∥f∥ * ∥v∥ + ∥g∥ * ∥v∥ : add_le_add (le_op_norm f v) (le_op_norm g v)
  ... = (∥f∥ + ∥g∥) * ∥v∥ : by rw add_mul⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
mk_normed_group_hom_norm_le _ (add_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _

/--
Terms containing `@has_add.add (has_coe_to_fun.F ...) pi.has_add`
seem to cause leanchecker to [crash due to an out-of-memory
condition](https://github.com/leanprover-community/lean/issues/543).
As a workaround, we add a type annotation: `(f + g : V₁ → V₂)`
-/
library_note "addition on function coercions"

-- see Note [addition on function coercions]
@[simp] lemma coe_add (f g : normed_group_hom V₁ V₂) : ⇑(f + g) = (f + g : V₁ → V₂) := rfl
@[simp] lemma add_apply (f g : normed_group_hom V₁ V₂) (v : V₁) :
  (f + g : normed_group_hom V₁ V₂) v = f v + g v := rfl

/-! ### The zero normed group hom -/

instance : has_zero (normed_group_hom V₁ V₂) :=
⟨(0 : V₁ →+ V₂).mk_normed_group_hom 0 (by simp)⟩

instance : inhabited (normed_group_hom V₁ V₂) := ⟨0⟩

/-- The norm of the `0` operator is `0`. -/
theorem op_norm_zero : ∥(0 : normed_group_hom V₁ V₂)∥ = 0 :=
le_antisymm (real.Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by { rw [zero_mul], exact norm_zero })⟩)
    (op_norm_nonneg _)

/-- For normed groups, an operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff {V₁ V₂ : Type*} [normed_group V₁] [normed_group V₂]
  {f : normed_group_hom V₁ V₂} : ∥f∥ = 0 ↔ f = 0 :=
iff.intro
  (λ hn, ext (λ x, norm_le_zero_iff.1
    (calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
     ...     = _ : by rw [hn, zero_mul])))
  (λ hf, by rw [hf, op_norm_zero] )

-- see Note [addition on function coercions]
@[simp] lemma coe_zero : ⇑(0 : normed_group_hom V₁ V₂) = (0 : V₁ → V₂) := rfl
@[simp] lemma zero_apply (v : V₁) : (0 : normed_group_hom V₁ V₂) v = 0 := rfl

variables {f g}

/-! ### The identity normed group hom -/

variable (V)

/-- The identity as a continuous normed group hom. -/
@[simps]
def id : normed_group_hom V V :=
(add_monoid_hom.id V).mk_normed_group_hom 1 (by simp [le_refl])

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the norm of every
element vanishes, where it is `0`. (Since we are working with seminorms this can happen even if the
space is non-trivial.) It means that one can not do better than an inequality in general. -/
lemma norm_id_le : ∥(id V : normed_group_hom V V)∥ ≤ 1 :=
op_norm_le_bound _ zero_le_one (λx, by simp)

/-- If there is an element with norm different from `0`, then the norm of the identity equals `1`.
(Since we are working with seminorms supposing that the space is non-trivial is not enough.) -/
lemma norm_id_of_nontrivial_seminorm (h : ∃ (x : V), ∥x∥ ≠ 0 ) :
  ∥(id V)∥ = 1 :=
le_antisymm (norm_id_le V) $ let ⟨x, hx⟩ := h in
have _ := (id V).ratio_le_op_norm x,
by rwa [id_apply, div_self hx] at this

/-- If a normed space is non-trivial, then the norm of the identity equals `1`. -/
lemma norm_id {V : Type*} [normed_group V] [nontrivial V] : ∥(id V)∥ = 1 :=
begin
  refine norm_id_of_nontrivial_seminorm V _,
  obtain ⟨x, hx⟩ := exists_ne (0 : V),
  exact ⟨x, ne_of_gt (norm_pos_iff.2 hx)⟩,
end

lemma coe_id : ((normed_group_hom.id V) : V → V) = (_root_.id : V → V) := rfl

/-! ### The negation of a normed group hom -/

/-- Opposite of a normed group hom. -/
instance : has_neg (normed_group_hom V₁ V₂) :=
⟨λ f, (-f.to_add_monoid_hom).mk_normed_group_hom (∥f∥) (λ v, by simp [le_op_norm f v])⟩

-- see Note [addition on function coercions]
@[simp] lemma coe_neg (f : normed_group_hom V₁ V₂) : ⇑(-f) = (-f : V₁ → V₂) := rfl
@[simp] lemma neg_apply (f : normed_group_hom V₁ V₂) (v : V₁) :
  (-f : normed_group_hom V₁ V₂) v = - (f v) := rfl

lemma op_norm_neg (f : normed_group_hom V₁ V₂) : ∥-f∥ = ∥f∥ :=
by simp only [norm_def, coe_neg, norm_neg, pi.neg_apply]

/-! ### Subtraction of normed group homs -/

/-- Subtraction of normed group homs. -/
instance : has_sub (normed_group_hom V₁ V₂) :=
⟨λ f g,
{ bound' :=
  begin
    simp only [add_monoid_hom.sub_apply, add_monoid_hom.to_fun_eq_coe, sub_eq_add_neg],
    exact (f + -g).bound'
  end,
  .. (f.to_add_monoid_hom - g.to_add_monoid_hom) }⟩

-- see Note [addition on function coercions]
@[simp] lemma coe_sub (f g : normed_group_hom V₁ V₂) : ⇑(f - g) = (f - g : V₁ → V₂) := rfl
@[simp] lemma sub_apply (f g : normed_group_hom V₁ V₂) (v : V₁) :
  (f - g : normed_group_hom V₁ V₂) v = f v - g v := rfl

/-! ### Normed group structure on normed group homs -/

/-- Homs between two given normed groups form a commutative additive group. -/
instance : add_comm_group (normed_group_hom V₁ V₂) :=
coe_injective.add_comm_group _ rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl)

/-- Normed group homomorphisms themselves form a seminormed group with respect to
    the operator norm. -/
instance to_semi_normed_group : semi_normed_group (normed_group_hom V₁ V₂) :=
semi_normed_group.of_core _ ⟨op_norm_zero, op_norm_add_le, op_norm_neg⟩

/-- Normed group homomorphisms themselves form a normed group with respect to
    the operator norm. -/
instance to_normed_group {V₁ V₂ : Type*} [normed_group V₁] [normed_group V₂] :
  normed_group (normed_group_hom V₁ V₂) :=
normed_group.of_core _ ⟨λ f, op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

/-- Coercion of a `normed_group_hom` is an `add_monoid_hom`. Similar to `add_monoid_hom.coe_fn` -/
@[simps]
def coe_fn_add_hom : normed_group_hom V₁ V₂ →+ (V₁ → V₂) :=
{ to_fun := coe_fn, map_zero' := coe_zero, map_add' := coe_add}

@[simp] lemma coe_sum {ι : Type*} (s : finset ι) (f : ι → normed_group_hom V₁ V₂) :
  ⇑(∑ i in s, f i) = ∑ i in s, (f i) :=
(coe_fn_add_hom : _ →+ (V₁ → V₂)).map_sum f s

lemma sum_apply {ι : Type*} (s : finset ι) (f : ι → normed_group_hom V₁ V₂) (v : V₁) :
  (∑ i in s, f i) v = ∑ i in s, (f i v) :=
by simp only [coe_sum, finset.sum_apply]

/-! ### Composition of normed group homs -/

/-- The composition of continuous normed group homs. -/
@[simps]
protected def comp (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  normed_group_hom V₁ V₃ :=
(g.to_add_monoid_hom.comp f.to_add_monoid_hom).mk_normed_group_hom (∥g∥ * ∥f∥) $ λ v, calc
∥g (f v)∥ ≤ ∥g∥ * ∥f v∥ : le_op_norm _ _
... ≤ ∥g∥ * (∥f∥ * ∥v∥) : mul_le_mul_of_nonneg_left (le_op_norm _ _) (op_norm_nonneg _)
... = ∥g∥ * ∥f∥ * ∥v∥   : by rw mul_assoc

lemma norm_comp_le (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  ∥g.comp f∥ ≤ ∥g∥ * ∥f∥ :=
mk_normed_group_hom_norm_le _ (mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _)) _

lemma norm_comp_le_of_le {g : normed_group_hom V₂ V₃} {C₁ C₂ : ℝ} (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) :
  ∥g.comp f∥ ≤ C₂ * C₁ :=
le_trans (norm_comp_le g f) $ mul_le_mul hg hf (norm_nonneg _) (le_trans (norm_nonneg _) hg)

lemma norm_comp_le_of_le' {g : normed_group_hom V₂ V₃} (C₁ C₂ C₃ : ℝ) (h : C₃ = C₂ * C₁)
  (hg : ∥g∥ ≤ C₂) (hf : ∥f∥ ≤ C₁) : ∥g.comp f∥ ≤ C₃ :=
by { rw h, exact norm_comp_le_of_le hg hf }

/-- Composition of normed groups hom as an additive group morphism. -/
def comp_hom : (normed_group_hom V₂ V₃) →+ (normed_group_hom V₁ V₂) →+ (normed_group_hom V₁ V₃) :=
add_monoid_hom.mk' (λ g, add_monoid_hom.mk' (λ f, g.comp f)
  (by { intros, ext, exact g.map_add _ _ }))
  (by { intros, ext, simp only [comp_apply, pi.add_apply, function.comp_app,
                                add_monoid_hom.add_apply, add_monoid_hom.mk'_apply, coe_add] })

@[simp] lemma comp_zero (f : normed_group_hom V₂ V₃) : f.comp (0 : normed_group_hom V₁ V₂) = 0 :=
by { ext, exact f.map_zero }

@[simp] lemma zero_comp (f : normed_group_hom V₁ V₂) : (0 : normed_group_hom V₂ V₃).comp f = 0 :=
by { ext, refl }

lemma comp_assoc {V₄: Type* } [semi_normed_group V₄] (h : normed_group_hom V₃ V₄)
  (g : normed_group_hom V₂ V₃) (f : normed_group_hom V₁ V₂) :
  (h.comp g).comp f = h.comp (g.comp f) :=
by { ext, refl }

lemma coe_comp (f : normed_group_hom V₁ V₂) (g : normed_group_hom V₂ V₃) :
  (g.comp f : V₁ → V₃) = (g : V₂ → V₃) ∘ (f : V₁ → V₂) := rfl

end normed_group_hom

namespace normed_group_hom

variables {V W V₁ V₂ V₃ : Type*}
variables [semi_normed_group V] [semi_normed_group W] [semi_normed_group V₁] [semi_normed_group V₂]
[semi_normed_group V₃]

/-- The inclusion of an `add_subgroup`, as bounded group homomorphism. -/
@[simps] def incl (s : add_subgroup V) : normed_group_hom s V :=
{ to_fun := (coe : s → V),
  map_add' := λ v w, add_subgroup.coe_add _ _ _,
  bound' := ⟨1, λ v, by { rw [one_mul], refl }⟩ }

lemma norm_incl {V' : add_subgroup V} (x : V') : ∥incl _ x∥ = ∥x∥ :=
rfl

/-!### Kernel -/
section kernels
variables (f : normed_group_hom V₁ V₂) (g : normed_group_hom V₂ V₃)

/-- The kernel of a bounded group homomorphism. Naturally endowed with a
`semi_normed_group` instance. -/
def ker : add_subgroup V₁ := f.to_add_monoid_hom.ker

lemma mem_ker (v : V₁) : v ∈ f.ker ↔ f v = 0 :=
by { erw f.to_add_monoid_hom.mem_ker, refl }

/-- Given a normed group hom `f : V₁ → V₂` satisfying `g.comp f = 0` for some `g : V₂ → V₃`,
    the corestriction of `f` to the kernel of `g`. -/
@[simps] def ker.lift (h : g.comp f = 0) :
  normed_group_hom V₁ g.ker :=
{ to_fun := λ v, ⟨f v, by { erw g.mem_ker, show (g.comp f) v = 0, rw h, refl }⟩,
  map_add' := λ v w, by { simp only [map_add], refl },
  bound' := f.bound' }

@[simp] lemma ker.incl_comp_lift (h : g.comp f = 0) :
  (incl g.ker).comp (ker.lift f g h) = f :=
by { ext, refl }

@[simp]
lemma ker_zero : (0 : normed_group_hom V₁ V₂).ker = ⊤ :=
by { ext, simp [mem_ker] }

lemma coe_ker : (f.ker : set V₁) = (f : V₁ → V₂) ⁻¹' {0} := rfl

lemma is_closed_ker {V₂ : Type*} [normed_group V₂] (f : normed_group_hom V₁ V₂) :
  is_closed (f.ker : set V₁) :=
f.coe_ker ▸ is_closed.preimage f.continuous (t1_space.t1 0)

end kernels

/-! ### Range -/
section range

variables (f : normed_group_hom V₁ V₂) (g : normed_group_hom V₂ V₃)

/-- The image of a bounded group homomorphism. Naturally endowed with a
`semi_normed_group` instance. -/
def range : add_subgroup V₂ := f.to_add_monoid_hom.range

lemma mem_range (v : V₂) : v ∈ f.range ↔ ∃ w, f w = v :=
by { rw [range, add_monoid_hom.mem_range], refl }

lemma comp_range : (g.comp f).range = add_subgroup.map g.to_add_monoid_hom f.range :=
by { erw add_monoid_hom.map_range, refl }

lemma incl_range (s : add_subgroup V₁) : (incl s).range = s :=
by { ext x, exact ⟨λ ⟨y, hy⟩, by { rw ← hy; simp }, λ hx, ⟨⟨x, hx⟩, by simp⟩⟩ }

@[simp]
lemma range_comp_incl_top : (f.comp (incl (⊤ : add_subgroup V₁))).range = f.range :=
by simpa [comp_range, incl_range, ← add_monoid_hom.range_eq_map]

end range

variables {f : normed_group_hom V W}

/-- A `normed_group_hom` is *norm-nonincreasing* if `∥f v∥ ≤ ∥v∥` for all `v`. -/
def norm_noninc (f : normed_group_hom V W) : Prop :=
∀ v, ∥f v∥ ≤ ∥v∥

namespace norm_noninc

lemma norm_noninc_iff_norm_le_one : f.norm_noninc ↔ ∥f∥ ≤ 1 :=
begin
  refine ⟨λ h, _, λ h, λ v, _⟩,
  { refine op_norm_le_bound _ (zero_le_one) (λ v, _),
    simpa [one_mul] using h v },
  { simpa using le_of_op_norm_le f h v }
end

lemma zero : (0 : normed_group_hom V₁ V₂).norm_noninc :=
λ v, by simp

lemma id : (id V).norm_noninc :=
λ v, le_rfl

lemma comp {g : normed_group_hom V₂ V₃} {f : normed_group_hom V₁ V₂}
  (hg : g.norm_noninc) (hf : f.norm_noninc) :
  (g.comp f).norm_noninc :=
λ v, (hg (f v)).trans (hf v)

end norm_noninc

section isometry

lemma isometry_iff_norm (f : normed_group_hom V W) :
  isometry f ↔ ∀ v, ∥f v∥ = ∥v∥ :=
add_monoid_hom.isometry_iff_norm f.to_add_monoid_hom

lemma isometry_of_norm (f : normed_group_hom V W) (hf : ∀ v, ∥f v∥ = ∥v∥) :
  isometry f :=
f.isometry_iff_norm.mpr hf

lemma norm_eq_of_isometry {f : normed_group_hom V W} (hf : isometry f) (v : V) :
  ∥f v∥ = ∥v∥ :=
f.isometry_iff_norm.mp hf v

lemma isometry_id : @isometry V V _ _ (id V) :=
isometry_id

lemma isometry_comp {g : normed_group_hom V₂ V₃} {f : normed_group_hom V₁ V₂}
  (hg : isometry g) (hf : isometry f) :
  isometry (g.comp f) :=
hg.comp hf

lemma norm_noninc_of_isometry (hf : isometry f) : f.norm_noninc :=
λ v, le_of_eq $ norm_eq_of_isometry hf v

end isometry

variables {W₁ W₂ W₃ : Type*} [semi_normed_group W₁] [semi_normed_group W₂] [semi_normed_group W₃]
variables (f) (g : normed_group_hom V W)
variables {f₁ g₁ : normed_group_hom V₁ W₁}
variables {f₂ g₂ : normed_group_hom V₂ W₂}
variables {f₃ g₃ : normed_group_hom V₃ W₃}

/-- The equalizer of two morphisms `f g : normed_group_hom V W`. -/
def equalizer := (f - g).ker

namespace equalizer

/-- The inclusion of `f.equalizer g` as a `normed_group_hom`. -/
def ι : normed_group_hom (f.equalizer g) V := incl _

lemma comp_ι_eq : f.comp (ι f g) = g.comp (ι f g) :=
by { ext, rw [comp_apply, comp_apply, ← sub_eq_zero, ← normed_group_hom.sub_apply], exact x.2 }

variables {f g}

/-- If `φ : normed_group_hom V₁ V` is such that `f.comp φ = g.comp φ`, the induced morphism
`normed_group_hom V₁ (f.equalizer g)`. -/
@[simps]
def lift (φ : normed_group_hom V₁ V) (h : f.comp φ = g.comp φ) :
  normed_group_hom V₁ (f.equalizer g) :=
{ to_fun := λ v, ⟨φ v, show (f - g) (φ v) = 0,
    by rw [normed_group_hom.sub_apply, sub_eq_zero, ← comp_apply, h, comp_apply]⟩,
  map_add' := λ v₁ v₂, by { ext, simp only [map_add, add_subgroup.coe_add, subtype.coe_mk] },
  bound' := by { obtain ⟨C, C_pos, hC⟩ := φ.bound, exact ⟨C, hC⟩ } }

@[simp] lemma ι_comp_lift (φ : normed_group_hom V₁ V) (h : f.comp φ = g.comp φ) :
  (ι _ _).comp (lift φ h) = φ :=
by { ext, refl }

/-- The lifting property of the equalizer as an equivalence. -/
@[simps]
def lift_equiv : {φ : normed_group_hom V₁ V // f.comp φ = g.comp φ} ≃
  normed_group_hom V₁ (f.equalizer g) :=
{ to_fun := λ φ, lift φ φ.prop,
  inv_fun := λ ψ, ⟨(ι f g).comp ψ, by { rw [← comp_assoc, ← comp_assoc, comp_ι_eq] }⟩,
  left_inv := λ φ, by simp,
  right_inv := λ ψ, by { ext, refl } }

/-- Given `φ : normed_group_hom V₁ V₂` and `ψ : normed_group_hom W₁ W₂` such that
`ψ.comp f₁ = f₂.comp φ` and `ψ.comp g₁ = g₂.comp φ`, the induced morphism
`normed_group_hom (f₁.equalizer g₁) (f₂.equalizer g₂)`. -/
def map (φ : normed_group_hom V₁ V₂) (ψ : normed_group_hom W₁ W₂)
  (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) :
  normed_group_hom (f₁.equalizer g₁) (f₂.equalizer g₂) :=
lift (φ.comp $ ι _ _) $
by { simp only [← comp_assoc, ← hf, ← hg], simp only [comp_assoc, comp_ι_eq] }

variables {φ : normed_group_hom V₁ V₂} {ψ : normed_group_hom W₁ W₂}
variables {φ' : normed_group_hom V₂ V₃} {ψ' : normed_group_hom W₂ W₃}

@[simp] lemma ι_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ) :
  (ι f₂ g₂).comp (map φ ψ hf hg) = φ.comp (ι _ _) :=
ι_comp_lift _ _

@[simp] lemma map_id : map (id V₁) (id W₁) rfl rfl = id (f₁.equalizer g₁) :=
by { ext, refl }

lemma comm_sq₂ (hf : ψ.comp f₁ = f₂.comp φ) (hf' : ψ'.comp f₂ = f₃.comp φ') :
  (ψ'.comp ψ).comp f₁ = f₃.comp (φ'.comp φ) :=
by rw [comp_assoc, hf, ← comp_assoc, hf', comp_assoc]

lemma map_comp_map (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  (hf' : ψ'.comp f₂ = f₃.comp φ') (hg' : ψ'.comp g₂ = g₃.comp φ') :
  (map φ' ψ' hf' hg').comp (map φ ψ hf hg) =
    map (φ'.comp φ) (ψ'.comp ψ) (comm_sq₂ hf hf') (comm_sq₂ hg hg') :=
by { ext, refl }

lemma ι_norm_noninc : (ι f g).norm_noninc := λ v, le_rfl

/-- The lifting of a norm nonincreasing morphism is norm nonincreasing. -/
lemma lift_norm_noninc (φ : normed_group_hom V₁ V) (h : f.comp φ = g.comp φ) (hφ : φ.norm_noninc) :
  (lift φ h).norm_noninc :=
hφ

/-- If `φ` satisfies `∥φ∥ ≤ C`, then the same is true for the lifted morphism. -/
lemma norm_lift_le (φ : normed_group_hom V₁ V) (h : f.comp φ = g.comp φ)
  (C : ℝ) (hφ : ∥φ∥ ≤ C) : ∥(lift φ h)∥ ≤ C := hφ

lemma map_norm_noninc (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  (hφ : φ.norm_noninc) : (map φ ψ hf hg).norm_noninc :=
lift_norm_noninc _ _ $ hφ.comp ι_norm_noninc

lemma norm_map_le (hf : ψ.comp f₁ = f₂.comp φ) (hg : ψ.comp g₁ = g₂.comp φ)
  (C : ℝ) (hφ : ∥φ.comp (ι f₁ g₁)∥ ≤ C) : ∥map φ ψ hf hg∥ ≤ C :=
norm_lift_le _ _ _ hφ

end equalizer

end normed_group_hom
