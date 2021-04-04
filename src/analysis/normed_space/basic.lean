/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import topology.instances.nnreal
import topology.algebra.module
import topology.algebra.algebra
import topology.metric_space.antilipschitz

/-!
# Normed spaces

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory of `semi_normed_group` and we specialize to `normed_group` at the end.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

noncomputable theory
open filter metric
open_locale topological_space big_operators nnreal ennreal

/-- Auxiliary class, endowing a type `α` with a function `norm : α → ℝ`. This class is designed to
be extended in more interesting classes specifying the properties of the norm. -/
class has_norm (α : Type*) := (norm : α → ℝ)

export has_norm (norm)

notation `∥`:1024 e:1 `∥`:1 := norm e

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥`
defines a pseudometric space structure. -/
class semi_normed_group (α : Type*) extends has_norm α, add_comm_group α, pseudo_metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines
a metric space structure. -/
class normed_group (α : Type*) extends has_norm α, add_comm_group α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

/-- A normed group is a seminormed group. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_group.to_semi_normed_group [β : normed_group α] : semi_normed_group α :=
{ ..β }

/-- Construct a seminormed group from a translation invariant pseudodistance -/
def semi_normed_group.of_add_dist [has_norm α] [add_comm_group α] [pseudo_metric_space α]
  (H1 : ∀ x:α, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : α, dist x y ≤ dist (x + z) (y + z)) : semi_normed_group α :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 },
    { have := H2 (x-y) 0 y, rwa [sub_add_cancel, zero_add] at this }
  end }

/-- Construct a seminormed group from a translation invariant pseudodistance -/
def semi_normed_group.of_add_dist' [has_norm α] [add_comm_group α] [pseudo_metric_space α]
  (H1 : ∀ x:α, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : α, dist (x + z) (y + z) ≤ dist x y) : semi_normed_group α :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { have := H2 (x-y) 0 y, rwa [sub_add_cancel, zero_add] at this },
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 }
  end }

/-- A seminormed group can be built from a seminorm that satisfies algebraic properties. This is
formalised in this structure. -/
structure semi_normed_group.core (α : Type*) [add_comm_group α] [has_norm α] : Prop :=
(norm_zero : ∥(0 : α)∥ = 0)
(triangle : ∀ x y : α, ∥x + y∥ ≤ ∥x∥ + ∥y∥)
(norm_neg : ∀ x : α, ∥-x∥ = ∥x∥)

/-- Constructing a seminormed group from core properties of a seminorm, i.e., registering the
pseudodistance and the pseudometric space structure from the seminorm properties. -/
noncomputable def semi_normed_group.of_core (α : Type*) [add_comm_group α] [has_norm α]
  (C : semi_normed_group.core α) : semi_normed_group α :=
{ dist := λ x y, ∥x - y∥,
  dist_eq := assume x y, by refl,
  dist_self := assume x, by simp [C.norm_zero],
  dist_triangle := assume x y z,
    calc ∥x - z∥ = ∥x - y + (y - z)∥ : by rw sub_add_sub_cancel
            ... ≤ ∥x - y∥ + ∥y - z∥  : C.triangle _ _,
  dist_comm := assume x y,
    calc ∥x - y∥ = ∥ -(y - x)∥ : by simp
             ... = ∥y - x∥ : by { rw [C.norm_neg] } }

instance : normed_group ℝ :=
{ norm := λ x, abs x,
  dist_eq := assume x y, rfl }

lemma real.norm_eq_abs (r : ℝ) : ∥r∥ = abs r := rfl

section semi_normed_group
variables [semi_normed_group α] [semi_normed_group β]

lemma dist_eq_norm (g h : α) : dist g h = ∥g - h∥ :=
semi_normed_group.dist_eq _ _

lemma dist_eq_norm' (g h : α) : dist g h = ∥h - g∥ :=
by rw [dist_comm, dist_eq_norm]

lemma dist_eq_norm' (g h : α) : dist g h = ∥h - g∥ :=
by rw [dist_comm, dist_eq_norm]

@[simp] lemma dist_zero_right (g : α) : dist g 0 = ∥g∥ :=
by rw [dist_eq_norm, sub_zero]

@[simp] lemma dist_zero_left : dist (0:α) = norm :=
funext $ λ g, by rw [dist_comm, dist_zero_right]

lemma tendsto_norm_cocompact_at_top [proper_space α] :
  tendsto norm (cocompact α) at_top :=
by simpa only [dist_zero_right] using tendsto_dist_right_cocompact_at_top (0:α)

lemma norm_sub_rev (g h : α) : ∥g - h∥ = ∥h - g∥ :=
by simpa only [dist_eq_norm] using dist_comm g h

@[simp] lemma norm_neg (g : α) : ∥-g∥ = ∥g∥ :=
by simpa using norm_sub_rev 0 g

@[simp] lemma dist_add_left (g h₁ h₂ : α) : dist (g + h₁) (g + h₂) = dist h₁ h₂ :=
by simp [dist_eq_norm]

@[simp] lemma dist_add_right (g₁ g₂ h : α) : dist (g₁ + h) (g₂ + h) = dist g₁ g₂ :=
by simp [dist_eq_norm]

@[simp] lemma dist_neg_neg (g h : α) : dist (-g) (-h) = dist g h :=
by simp only [dist_eq_norm, neg_sub_neg, norm_sub_rev]

@[simp] lemma dist_sub_left (g h₁ h₂ : α) : dist (g - h₁) (g - h₂) = dist h₁ h₂ :=
by simp only [sub_eq_add_neg, dist_add_left, dist_neg_neg]

@[simp] lemma dist_sub_right (g₁ g₂ h : α) : dist (g₁ - h) (g₂ - h) = dist g₁ g₂ :=
by simpa only [sub_eq_add_neg] using dist_add_right _ _ _

/-- Triangle inequality for the norm. -/
lemma norm_add_le (g h : α) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ :=
by simpa [dist_eq_norm] using dist_triangle g 0 (-h)

lemma norm_add_le_of_le {g₁ g₂ : α} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) :
  ∥g₁ + g₂∥ ≤ n₁ + n₂ :=
le_trans (norm_add_le g₁ g₂) (add_le_add H₁ H₂)

lemma dist_add_add_le (g₁ g₂ h₁ h₂ : α) :
  dist (g₁ + g₂) (h₁ + h₂) ≤ dist g₁ h₁ + dist g₂ h₂ :=
by simpa only [dist_add_left, dist_add_right] using dist_triangle (g₁ + g₂) (h₁ + g₂) (h₁ + h₂)

lemma dist_add_add_le_of_le {g₁ g₂ h₁ h₂ : α} {d₁ d₂ : ℝ}
  (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
  dist (g₁ + g₂) (h₁ + h₂) ≤ d₁ + d₂ :=
le_trans (dist_add_add_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

lemma dist_sub_sub_le (g₁ g₂ h₁ h₂ : α) :
  dist (g₁ - g₂) (h₁ - h₂) ≤ dist g₁ h₁ + dist g₂ h₂ :=
by simpa only [sub_eq_add_neg, dist_neg_neg] using dist_add_add_le g₁ (-g₂) h₁ (-h₂)

lemma dist_sub_sub_le_of_le {g₁ g₂ h₁ h₂ : α} {d₁ d₂ : ℝ}
  (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
  dist (g₁ - g₂) (h₁ - h₂) ≤ d₁ + d₂ :=
le_trans (dist_sub_sub_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

lemma abs_dist_sub_le_dist_add_add (g₁ g₂ h₁ h₂ : α) :
  abs (dist g₁ h₁ - dist g₂ h₂) ≤ dist (g₁ + g₂) (h₁ + h₂) :=
by simpa only [dist_add_left, dist_add_right, dist_comm h₂]
  using abs_dist_sub_le (g₁ + g₂) (h₁ + h₂) (h₁ + g₂)

@[simp] lemma norm_nonneg (g : α) : 0 ≤ ∥g∥ :=
by { rw[←dist_zero_right], exact dist_nonneg }

@[simp] lemma norm_zero : ∥(0:α)∥ = 0 :=  by rw [← dist_zero_right, dist_self]

@[nontriviality] lemma norm_of_subsingleton [subsingleton α] (x : α) : ∥x∥ = 0 :=
by rw [subsingleton.elim x 0, norm_zero]

lemma norm_sum_le {β} : ∀(s : finset β) (f : β → α), ∥∑ a in s, f a∥ ≤ ∑ a in s, ∥ f a ∥ :=
finset.le_sum_of_subadditive norm norm_zero norm_add_le

lemma norm_sum_le_of_le {β} (s : finset β) {f : β → α} {n : β → ℝ} (h : ∀ b ∈ s, ∥f b∥ ≤ n b) :
  ∥∑ b in s, f b∥ ≤ ∑ b in s, n b :=
le_trans (norm_sum_le s f) (finset.sum_le_sum h)

lemma norm_sub_le (g h : α) : ∥g - h∥ ≤ ∥g∥ + ∥h∥ :=
by simpa [dist_eq_norm] using dist_triangle g 0 h

lemma norm_sub_le_of_le {g₁ g₂ : α} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) :
  ∥g₁ - g₂∥ ≤ n₁ + n₂ :=
le_trans (norm_sub_le g₁ g₂) (add_le_add H₁ H₂)

lemma dist_le_norm_add_norm (g h : α) : dist g h ≤ ∥g∥ + ∥h∥ :=
by { rw dist_eq_norm, apply norm_sub_le }

lemma abs_norm_sub_norm_le (g h : α) : abs(∥g∥ - ∥h∥) ≤ ∥g - h∥ :=
by simpa [dist_eq_norm] using abs_dist_sub_le g h 0

lemma norm_sub_norm_le (g h : α) : ∥g∥ - ∥h∥ ≤ ∥g - h∥ :=
le_trans (le_abs_self _) (abs_norm_sub_norm_le g h)

lemma dist_norm_norm_le (g h : α) : dist ∥g∥ ∥h∥ ≤ ∥g - h∥ :=
abs_norm_sub_norm_le g h

lemma norm_le_insert (u v : α) : ∥v∥ ≤ ∥u∥ + ∥u - v∥ :=
calc ∥v∥ = ∥u - (u - v)∥ : by abel
... ≤ ∥u∥ + ∥u - v∥ : norm_sub_le u _

lemma ball_0_eq (ε : ℝ) : ball (0:α) ε = {x | ∥x∥ < ε} :=
set.ext $ assume a, by simp

lemma mem_ball_iff_norm {g h : α} {r : ℝ} :
  h ∈ ball g r ↔ ∥h - g∥ < r :=
by rw [mem_ball, dist_eq_norm]

lemma mem_ball_iff_norm' {g h : α} {r : ℝ} :
  h ∈ ball g r ↔ ∥g - h∥ < r :=
by rw [mem_ball', dist_eq_norm]

lemma mem_closed_ball_iff_norm {g h : α} {r : ℝ} :
  h ∈ closed_ball g r ↔ ∥h - g∥ ≤ r :=
by rw [mem_closed_ball, dist_eq_norm]

lemma mem_closed_ball_iff_norm' {g h : α} {r : ℝ} :
  h ∈ closed_ball g r ↔ ∥g - h∥ ≤ r :=
by rw [mem_closed_ball', dist_eq_norm]

lemma norm_le_of_mem_closed_ball {g h : α} {r : ℝ} (H : h ∈ closed_ball g r) :
  ∥h∥ ≤ ∥g∥ + r :=
calc
  ∥h∥ = ∥g + (h - g)∥ : by rw [add_sub_cancel'_right]
  ... ≤ ∥g∥ + ∥h - g∥  : norm_add_le _ _
  ... ≤ ∥g∥ + r : by { apply add_le_add_left, rw ← dist_eq_norm, exact H }

lemma norm_lt_of_mem_ball {g h : α} {r : ℝ} (H : h ∈ ball g r) :
  ∥h∥ < ∥g∥ + r :=
calc
  ∥h∥ = ∥g + (h - g)∥ : by rw [add_sub_cancel'_right]
  ... ≤ ∥g∥ + ∥h - g∥  : norm_add_le _ _
  ... < ∥g∥ + r : by { apply add_lt_add_left, rw ← dist_eq_norm, exact H }

@[simp] lemma mem_sphere_iff_norm (v w : α) (r : ℝ) : w ∈ sphere v r ↔ ∥w - v∥ = r :=
by simp [dist_eq_norm]

@[simp] lemma mem_sphere_zero_iff_norm {w : α} {r : ℝ} : w ∈ sphere (0:α) r ↔ ∥w∥ = r :=
by simp [dist_eq_norm]

@[simp] lemma norm_eq_of_mem_sphere {r : ℝ} (x : sphere (0:α) r) : ∥(x:α)∥ = r :=
mem_sphere_zero_iff_norm.mp x.2

lemma ne_zero_of_norm_pos {g : α} : 0 < ∥ g ∥ → g ≠ 0 :=
begin
  intros hpos hzero,
  rw [hzero, norm_zero] at hpos,
  exact lt_irrefl 0 hpos,
end

lemma nonzero_of_mem_sphere {r : ℝ} (hr : 0 < r) (x : sphere (0:α) r) : (x:α) ≠ 0 :=
begin
  refine ne_zero_of_norm_pos _,
  rwa norm_eq_of_mem_sphere x,
end

lemma nonzero_of_mem_unit_sphere (x : sphere (0:α) 1) : (x:α) ≠ 0 :=
by { apply nonzero_of_mem_sphere, norm_num }

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : has_neg (sphere (0:α) r) :=
{ neg := λ w, ⟨-↑w, by simp⟩ }

@[simp] lemma coe_neg_sphere {r : ℝ} (v : sphere (0:α) r) :
  (((-v) : sphere _ _) : α) = - (v:α) :=
rfl

theorem normed_group.tendsto_nhds_zero {f : γ → α} {l : filter γ} :
  tendsto f l (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ x in l, ∥ f x ∥ < ε :=
metric.tendsto_nhds.trans $ by simp only [dist_zero_right]

lemma normed_group.tendsto_nhds_nhds {f : α → β} {x : α} {y : β} :
  tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ∥x' - x∥ < δ → ∥f x' - y∥ < ε :=
by simp_rw [metric.tendsto_nhds_nhds, dist_eq_norm]

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. The analogous condition for a linear map of
(semi)normed spaces is in `normed_space.operator_norm`. -/
lemma add_monoid_hom.lipschitz_of_bound (f :α →+ β) (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  lipschitz_with (nnreal.of_real C) f :=
lipschitz_with.of_dist_le' $ λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

lemma lipschitz_on_with_iff_norm_sub_le {f : α → β} {C : ℝ≥0} {s : set α} :
  lipschitz_on_with C f s ↔  ∀ (x ∈ s) (y ∈ s), ∥f x - f y∥ ≤ C * ∥x - y∥ :=
by simp only [lipschitz_on_with_iff_dist_le_mul, dist_eq_norm]

lemma lipschitz_on_with.norm_sub_le {f : α → β} {C : ℝ≥0} {s : set α} (h : lipschitz_on_with C f s)
  {x y : α} (x_in : x ∈ s) (y_in : y ∈ s) : ∥f x - f y∥ ≤ C * ∥x - y∥ :=
lipschitz_on_with_iff_norm_sub_le.mp h x x_in y y_in

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`.
The analogous condition for a linear map of normed spaces is in `normed_space.operator_norm`. -/
lemma add_monoid_hom.continuous_of_bound (f : α →+ β) (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  continuous f :=
(f.lipschitz_of_bound C h).continuous

section nnnorm

/-- Version of the norm taking values in nonnegative reals. -/
def nnnorm (a : α) : ℝ≥0 := ⟨norm a, norm_nonneg a⟩

@[simp, norm_cast] lemma coe_nnnorm (a : α) : (nnnorm a : ℝ) = norm a := rfl

lemma nndist_eq_nnnorm (a b : α) : nndist a b = nnnorm (a - b) := nnreal.eq $ dist_eq_norm _ _

@[simp] lemma nnnorm_zero : nnnorm (0 : α) = 0 :=
nnreal.eq norm_zero

lemma nnnorm_add_le (g h : α) : nnnorm (g + h) ≤ nnnorm g + nnnorm h :=
nnreal.coe_le_coe.2 $ norm_add_le g h

@[simp] lemma nnnorm_neg (g : α) : nnnorm (-g) = nnnorm g :=
nnreal.eq $ norm_neg g

lemma nndist_nnnorm_nnnorm_le (g h : α) : nndist (nnnorm g) (nnnorm h) ≤ nnnorm (g - h) :=
nnreal.coe_le_coe.2 $ dist_norm_norm_le g h

lemma of_real_norm_eq_coe_nnnorm (x : β) : ennreal.of_real ∥x∥ = (nnnorm x : ℝ≥0∞) :=
ennreal.of_real_eq_coe_nnreal _

lemma edist_eq_coe_nnnorm_sub (x y : β) : edist x y = (nnnorm (x - y) : ℝ≥0∞) :=
by rw [edist_dist, dist_eq_norm, of_real_norm_eq_coe_nnnorm]

lemma edist_eq_coe_nnnorm (x : β) : edist x 0 = (nnnorm x : ℝ≥0∞) :=
by rw [edist_eq_coe_nnnorm_sub, _root_.sub_zero]

lemma mem_emetric_ball_0_iff {x : β} {r : ℝ≥0∞} : x ∈ emetric.ball (0 : β) r ↔ ↑(nnnorm x) < r :=
by rw [emetric.mem_ball, edist_eq_coe_nnnorm]

lemma nndist_add_add_le (g₁ g₂ h₁ h₂ : α) :
  nndist (g₁ + g₂) (h₁ + h₂) ≤ nndist g₁ h₁ + nndist g₂ h₂ :=
nnreal.coe_le_coe.2 $ dist_add_add_le g₁ g₂ h₁ h₂

lemma edist_add_add_le (g₁ g₂ h₁ h₂ : α) :
  edist (g₁ + g₂) (h₁ + h₂) ≤ edist g₁ h₁ + edist g₂ h₂ :=
by { simp only [edist_nndist], norm_cast, apply nndist_add_add_le }

lemma nnnorm_sum_le {β} : ∀(s : finset β) (f : β → α),
  nnnorm (∑ a in s, f a) ≤ ∑ a in s, nnnorm (f a) :=
finset.le_sum_of_subadditive nnnorm nnnorm_zero nnnorm_add_le

end nnnorm

lemma lipschitz_with.neg {α : Type*} [pseudo_emetric_space α] {K : ℝ≥0} {f : α → β}
  (hf : lipschitz_with K f) : lipschitz_with K (λ x, -f x) :=
λ x y, by simpa only [edist_dist, dist_neg_neg] using hf x y

lemma lipschitz_with.add {α : Type*} [pseudo_emetric_space α] {Kf : ℝ≥0} {f : α → β}
  (hf : lipschitz_with Kf f) {Kg : ℝ≥0} {g : α → β} (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (λ x, f x + g x) :=
λ x y,
calc edist (f x + g x) (f y + g y) ≤ edist (f x) (f y) + edist (g x) (g y) :
  edist_add_add_le _ _ _ _
... ≤ Kf * edist x y + Kg * edist x y :
  add_le_add (hf x y) (hg x y)
... = (Kf + Kg) * edist x y :
  (add_mul _ _ _).symm

lemma lipschitz_with.sub {α : Type*} [pseudo_emetric_space α] {Kf : ℝ≥0} {f : α → β}
  (hf : lipschitz_with Kf f) {Kg : ℝ≥0} {g : α → β} (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (λ x, f x - g x) :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma antilipschitz_with.add_lipschitz_with {α : Type*} [pseudo_metric_space α] {Kf : ℝ≥0}
  {f : α → β} (hf : antilipschitz_with Kf f) {Kg : ℝ≥0} {g : α → β} (hg : lipschitz_with Kg g)
  (hK : Kg < Kf⁻¹) : antilipschitz_with (Kf⁻¹ - Kg)⁻¹ (λ x, f x + g x) :=
begin
  refine antilipschitz_with.of_le_mul_dist (λ x y, _),
  rw [nnreal.coe_inv, ← div_eq_inv_mul],
  rw le_div_iff (nnreal.coe_pos.2 $ nnreal.sub_pos.2 hK),
  rw [mul_comm, nnreal.coe_sub (le_of_lt hK), sub_mul],
  calc ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :
    sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
  ... ≤ _ : le_trans (le_abs_self _) (abs_dist_sub_le_dist_add_add _ _ _ _)
end

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
instance add_subgroup.semi_normed_group {E : Type*} [semi_normed_group E] (s : add_subgroup E) :
  semi_normed_group s :=
{ norm := λx, norm (x : E),
  dist_eq := λx y, dist_eq_norm (x : E) (y : E) }

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[simp] lemma coe_norm_subgroup {E : Type*} [semi_normed_group E] {s : add_subgroup E} (x : s) :
  ∥x∥ = ∥(x:E)∥ :=
rfl

/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance submodule.semi_normed_group {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [semi_normed_group E] {_ : module 𝕜 E} (s : submodule 𝕜 E) : semi_normed_group s :=
{ norm := λx, norm (x : E),
  dist_eq := λx y, dist_eq_norm (x : E) (y : E) }

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

See note [implicit instance arguments]. -/
@[simp, norm_cast] lemma submodule.norm_coe {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [semi_normed_group E] {_ : module 𝕜 E} {s : submodule 𝕜 E} (x : s) :
  ∥(x : E)∥ = ∥x∥ :=
rfl

@[simp] lemma submodule.norm_mk {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [semi_normed_group E] {_ : module 𝕜 E} {s : submodule 𝕜 E} (x : E) (hx : x ∈ s) :
  ∥(⟨x, hx⟩ : s)∥ = ∥x∥ :=
rfl

/-- seminormed group instance on the product of two seminormed groups, using the sup norm. -/
instance prod.semi_normed_group : semi_normed_group (α × β) :=
{ norm := λx, max ∥x.1∥ ∥x.2∥,
  dist_eq := assume (x y : α × β),
    show max (dist x.1 y.1) (dist x.2 y.2) = (max ∥(x - y).1∥ ∥(x - y).2∥), by simp [dist_eq_norm] }

lemma prod.semi_norm_def (x : α × β) : ∥x∥ = (max ∥x.1∥ ∥x.2∥) := rfl

lemma prod.nnsemi_norm_def (x : α × β) : nnnorm x = max (nnnorm x.1) (nnnorm x.2) :=
by { have := x.semi_norm_def, simp only [← coe_nnnorm] at this, exact_mod_cast this }

lemma semi_norm_fst_le (x : α × β) : ∥x.1∥ ≤ ∥x∥ :=
le_max_left _ _

lemma semi_norm_snd_le (x : α × β) : ∥x.2∥ ≤ ∥x∥ :=
le_max_right _ _

lemma semi_norm_prod_le_iff {x : α × β} {r : ℝ} :
  ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
max_le_iff

/-- seminormed group instance on the product of finitely many seminormed groups,
using the sup norm. -/
instance pi.semi_normed_group {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] :
  semi_normed_group (Πi, π i) :=
{ norm := λf, ((finset.sup finset.univ (λ b, nnnorm (f b)) : ℝ≥0) : ℝ),
  dist_eq := assume x y,
    congr_arg (coe : ℝ≥0 → ℝ) $ congr_arg (finset.sup finset.univ) $ funext $ assume a,
    show nndist (x a) (y a) = nnnorm (x a - y a), from nndist_eq_nnnorm _ _ }

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
lemma pi_semi_norm_le_iff {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] {r : ℝ}
  (hr : 0 ≤ r) {x : Πi, π i} : ∥x∥ ≤ r ↔ ∀i, ∥x i∥ ≤ r :=
by simp only [← dist_zero_right, dist_pi_le_iff hr, pi.zero_apply]

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
lemma pi_semi_norm_lt_iff {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] {r : ℝ}
  (hr : 0 < r) {x : Πi, π i} : ∥x∥ < r ↔ ∀i, ∥x i∥ < r :=
by simp only [← dist_zero_right, dist_pi_lt_iff hr, pi.zero_apply]

lemma semi_norm_le_pi_norm {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] (x : Πi, π i)
  (i : ι) : ∥x i∥ ≤ ∥x∥ :=
(pi_semi_norm_le_iff (norm_nonneg x)).1 (le_refl _) i

@[simp] lemma pi_semi_norm_const [nonempty ι] [fintype ι] (a : α) : ∥(λ i : ι, a)∥ = ∥a∥ :=
by simpa only [← dist_zero_right] using dist_pi_const a 0

@[simp] lemma pi_nnsemi_norm_const [nonempty ι] [fintype ι] (a : α) :
  nnnorm (λ i : ι, a) = nnnorm a :=
nnreal.eq $ pi_semi_norm_const a

lemma tendsto_iff_norm_tendsto_zero {f : ι → β} {a : filter ι} {b : β} :
  tendsto f a (𝓝 b) ↔ tendsto (λ e, ∥f e - b∥) a (𝓝 0) :=
by { convert tendsto_iff_dist_tendsto_zero, simp [dist_eq_norm] }

lemma tendsto_zero_iff_norm_tendsto_zero {f : γ → β} {a : filter γ} :
  tendsto f a (𝓝 0) ↔ tendsto (λ e, ∥f e∥) a (𝓝 0) :=
by { rw [tendsto_iff_norm_tendsto_zero], simp only [sub_zero] }

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `g` which tends to `0`, then `f` tends to `0`.
In this pair of lemmas (`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of
similar lemmas in `topology.metric_space.basic` and `topology.algebra.ordered`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
lemma squeeze_zero_norm' {f : γ → α} {g : γ → ℝ} {t₀ : filter γ}
  (h : ∀ᶠ n in t₀, ∥f n∥ ≤ g n)
  (h' : tendsto g t₀ (𝓝 0)) : tendsto f t₀ (𝓝 0) :=
tendsto_zero_iff_norm_tendsto_zero.mpr
  (squeeze_zero' (eventually_of_forall (λ n, norm_nonneg _)) h h')

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `g` which
tends to `0`, then `f` tends to `0`.  -/
lemma squeeze_zero_norm {f : γ → α} {g : γ → ℝ} {t₀ : filter γ}
  (h : ∀ (n:γ), ∥f n∥ ≤ g n)
  (h' : tendsto g t₀ (𝓝 0)) :
  tendsto f t₀ (𝓝 0) :=
squeeze_zero_norm' (eventually_of_forall h) h'

lemma tendsto_norm_sub_self (x : α) : tendsto (λ g : α, ∥g - x∥) (𝓝 x) (𝓝 0) :=
by simpa [dist_eq_norm] using tendsto_id.dist (tendsto_const_nhds : tendsto (λ g, (x:α)) (𝓝 x) _)

lemma tendsto_norm {x : α} : tendsto (λg : α, ∥g∥) (𝓝 x) (𝓝 ∥x∥) :=
by simpa using tendsto_id.dist (tendsto_const_nhds : tendsto (λ g, (0:α)) _ _)

lemma tendsto_norm_zero : tendsto (λg : α, ∥g∥) (𝓝 0) (𝓝 0) :=
by simpa using tendsto_norm_sub_self (0:α)

@[continuity]
lemma continuous_norm : continuous (λg:α, ∥g∥) :=
by simpa using continuous_id.dist (continuous_const : continuous (λ g, (0:α)))

@[continuity]
lemma continuous_nnnorm : continuous (nnnorm : α → ℝ≥0) :=
continuous_subtype_mk _ continuous_norm

lemma lipschitz_with_one_norm : lipschitz_with 1 (norm : α → ℝ) :=
by simpa only [dist_zero_left] using lipschitz_with.dist_right (0 : α)

lemma uniform_continuous_norm : uniform_continuous (norm : α → ℝ) :=
lipschitz_with_one_norm.uniform_continuous

lemma uniform_continuous_nnnorm : uniform_continuous (nnnorm : α → ℝ≥0) :=
uniform_continuous_subtype_mk uniform_continuous_norm _

section

variables {l : filter γ} {f : γ → α} {a : α}

lemma filter.tendsto.norm {a : α} (h : tendsto f l (𝓝 a)) : tendsto (λ x, ∥f x∥) l (𝓝 ∥a∥) :=
tendsto_norm.comp h

lemma filter.tendsto.nnnorm (h : tendsto f l (𝓝 a)) :
  tendsto (λ x, nnnorm (f x)) l (𝓝 (nnnorm a)) :=
tendsto.comp continuous_nnnorm.continuous_at h

end

section

variables [topological_space γ] {f : γ → α} {s : set γ} {a : γ} {b : α}

lemma continuous.norm (h : continuous f) : continuous (λ x, ∥f x∥) := continuous_norm.comp h

lemma continuous.nnnorm (h : continuous f) : continuous (λ x, nnnorm (f x)) :=
continuous_nnnorm.comp h

lemma continuous_at.norm (h : continuous_at f a) : continuous_at (λ x, ∥f x∥) a := h.norm

lemma continuous_at.nnnorm (h : continuous_at f a) : continuous_at (λ x, nnnorm (f x)) a := h.nnnorm

lemma continuous_within_at.norm (h : continuous_within_at f s a) :
  continuous_within_at (λ x, ∥f x∥) s a :=
h.norm

lemma continuous_within_at.nnnorm (h : continuous_within_at f s a) :
  continuous_within_at (λ x, nnnorm (f x)) s a :=
h.nnnorm

lemma continuous_on.norm (h : continuous_on f s) : continuous_on (λ x, ∥f x∥) s :=
λ x hx, (h x hx).norm

lemma continuous_on.nnnorm (h : continuous_on f s) : continuous_on (λ x, nnnorm (f x)) s :=
λ x hx, (h x hx).nnnorm

end

/-- If `∥y∥→∞`, then we can assume `y≠x` for any fixed `x`. -/
lemma eventually_ne_of_tendsto_norm_at_top {l : filter γ} {f : γ → α}
  (h : tendsto (λ y, ∥f y∥) l at_top) (x : α) :
  ∀ᶠ y in l, f y ≠ x :=
begin
  have : ∀ᶠ y in l, 1 + ∥x∥ ≤ ∥f y∥ := h (mem_at_top (1 + ∥x∥)),
  refine this.mono (λ y hy hxy, _),
  subst x,
  exact not_le_of_lt zero_lt_one (add_le_iff_nonpos_left.1 hy)
end

/-- A seminormed group is a uniform additive group, i.e., addition and subtraction are uniformly
continuous. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_uniform_group : uniform_add_group α :=
⟨(lipschitz_with.prod_fst.sub lipschitz_with.prod_snd).uniform_continuous⟩

@[priority 100] -- see Note [lower instance priority]
instance normed_top_monoid : has_continuous_add α :=
by apply_instance -- short-circuit type class inference
@[priority 100] -- see Note [lower instance priority]
instance normed_top_group : topological_add_group α :=
by apply_instance -- short-circuit type class inference

lemma nat.norm_cast_le [has_one α] : ∀ n : ℕ, ∥(n : α)∥ ≤ n * ∥(1 : α)∥
| 0 := by simp
| (n + 1) := by { rw [n.cast_succ, n.cast_succ, add_mul, one_mul],
                  exact norm_add_le_of_le (nat.norm_cast_le n) le_rfl }

end semi_normed_group

section normed_group

/-- Construct a normed group from a translation invariant distance -/
def normed_group.of_add_dist [has_norm α] [add_comm_group α] [metric_space α]
  (H1 : ∀ x:α, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : α, dist x y ≤ dist (x + z) (y + z)) : normed_group α :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 },
    { have := H2 (x-y) 0 y, rwa [sub_add_cancel, zero_add] at this }
  end }

/-- A normed group can be built from a norm that satisfies algebraic properties. This is
formalised in this structure. -/
structure normed_group.core (α : Type*) [add_comm_group α] [has_norm α] : Prop :=
(norm_eq_zero_iff : ∀ x : α, ∥x∥ = 0 ↔ x = 0)
(triangle : ∀ x y : α, ∥x + y∥ ≤ ∥x∥ + ∥y∥)
(norm_neg : ∀ x : α, ∥-x∥ = ∥x∥)

/-- The `semi_normed_group.core` induced by a `normed_group.core`. -/
lemma normed_group.core.to_semi_normed_group.core {α : Type*} [add_comm_group α] [has_norm α]
  (C : normed_group.core α) : semi_normed_group.core α :=
{ norm_zero := (C.norm_eq_zero_iff 0).2 rfl,
  triangle := C.triangle,
  norm_neg := C.norm_neg }

/-- Constructing a normed group from core properties of a norm, i.e., registering the distance and
the metric space structure from the norm properties. -/
noncomputable def normed_group.of_core (α : Type*) [add_comm_group α] [has_norm α]
  (C : normed_group.core α) : normed_group α :=
{ eq_of_dist_eq_zero := λ x y h,
  begin
    rw [dist_eq_norm] at h,
    exact sub_eq_zero.mp ((C.norm_eq_zero_iff _).1 h)
  end
  ..semi_normed_group.of_core α (normed_group.core.to_semi_normed_group.core C) }

variables [normed_group α] [normed_group β]

@[simp] lemma norm_eq_zero {g : α} : ∥g∥ = 0 ↔ g = 0 :=
dist_zero_right g ▸ dist_eq_zero

@[simp] lemma norm_pos_iff {g : α} : 0 < ∥ g ∥ ↔ g ≠ 0 :=
dist_zero_right g ▸ dist_pos

@[simp] lemma norm_le_zero_iff {g : α} : ∥g∥ ≤ 0 ↔ g = 0 :=
by { rw[←dist_zero_right], exact dist_le_zero }

lemma eq_of_norm_sub_le_zero {g h : α} (a : ∥g - h∥ ≤ 0) : g = h :=
by rwa [← sub_eq_zero, ← norm_le_zero_iff]

lemma eq_of_norm_sub_eq_zero {u v : α} (h : ∥u - v∥ = 0) : u = v :=
begin
  apply eq_of_dist_eq_zero,
  rwa dist_eq_norm
end

lemma norm_sub_eq_zero_iff {u v : α} : ∥u - v∥ = 0 ↔ u = v :=
begin
  convert dist_eq_zero,
  rwa dist_eq_norm
end

@[simp] lemma nnnorm_eq_zero {a : α} : nnnorm a = 0 ↔ a = 0 :=
by simp only [nnreal.eq_iff.symm, nnreal.coe_zero, coe_nnnorm, norm_eq_zero]

/-- A subgroup of a normed group is also a normed group, with the restriction of the norm. -/
instance add_subgroup.normed_group {E : Type*} [normed_group E] (s : add_subgroup E) :
  normed_group s :=
{ ..add_subgroup.semi_normed_group s }

/-- A submodule of a normed group is also a normed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance submodule.normed_group {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [normed_group E] {_ : module 𝕜 E} (s : submodule 𝕜 E) : normed_group s :=
{ ..submodule.semi_normed_group s }

/-- normed group instance on the product of two normed groups, using the sup norm. -/
instance prod.normed_group : normed_group (α × β) := { ..prod.semi_normed_group }

lemma prod.norm_def (x : α × β) : ∥x∥ = (max ∥x.1∥ ∥x.2∥) := rfl

lemma prod.nnnorm_def (x : α × β) : nnnorm x = max (nnnorm x.1) (nnnorm x.2) :=
by { have := x.norm_def, simp only [← coe_nnnorm] at this, exact_mod_cast this }

lemma norm_fst_le (x : α × β) : ∥x.1∥ ≤ ∥x∥ :=
le_max_left _ _

lemma norm_snd_le (x : α × β) : ∥x.2∥ ≤ ∥x∥ :=
le_max_right _ _

lemma norm_prod_le_iff {x : α × β} {r : ℝ} :
  ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
max_le_iff

/-- normed group instance on the product of finitely many normed groups, using the sup norm. -/
instance pi.normed_group {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] :
  normed_group (Πi, π i) := { ..pi.semi_normed_group }

/-- The norm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
lemma pi_norm_le_iff {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] {r : ℝ} (hr : 0 ≤ r)
  {x : Πi, π i} : ∥x∥ ≤ r ↔ ∀i, ∥x i∥ ≤ r :=
by simp only [← dist_zero_right, dist_pi_le_iff hr, pi.zero_apply]

/-- The norm of an element in a product space is `< r` if and only if the norm of each
component is. -/
lemma pi_norm_lt_iff {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] {r : ℝ} (hr : 0 < r)
  {x : Πi, π i} : ∥x∥ < r ↔ ∀i, ∥x i∥ < r :=
by simp only [← dist_zero_right, dist_pi_lt_iff hr, pi.zero_apply]

lemma norm_le_pi_norm {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] (x : Πi, π i) (i : ι) :
  ∥x i∥ ≤ ∥x∥ :=
(pi_norm_le_iff (norm_nonneg x)).1 (le_refl _) i

@[simp] lemma pi_norm_const [nonempty ι] [fintype ι] (a : α) : ∥(λ i : ι, a)∥ = ∥a∥ :=
by simpa only [← dist_zero_right] using dist_pi_const a 0

@[simp] lemma pi_nnnorm_const [nonempty ι] [fintype ι] (a : α) :
  nnnorm (λ i : ι, a) = nnnorm a :=
nnreal.eq $ pi_norm_const a

lemma tendsto_norm_nhds_within_zero : tendsto (norm : α → ℝ) (𝓝[{0}ᶜ] 0) (𝓝[set.Ioi 0] 0) :=
(continuous_norm.tendsto' (0 : α) 0 norm_zero).inf $ tendsto_principal_principal.2 $
  λ x, norm_pos_iff.2

end normed_group

section semi_normed_ring

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class semi_normed_ring (α : Type*) extends has_norm α, ring α, pseudo_metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class normed_ring (α : Type*) extends has_norm α, ring α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A normed ring is a seminormed ring. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_ring.to_semi_normed_ring [β : normed_ring α] : semi_normed_ring α :=
{ ..β }

/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class semi_normed_comm_ring (α : Type*) extends semi_normed_ring α :=
(mul_comm : ∀ x y : α, x * y = y * x)

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class normed_comm_ring (α : Type*) extends normed_ring α :=
(mul_comm : ∀ x y : α, x * y = y * x)

/-- A normed commutative ring is a seminormed commutative ring. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_comm_ring.to_semi_normed_comm_ring [β : normed_comm_ring α] :
  semi_normed_comm_ring α := { ..β }

/-- A mixin class with the axiom `∥1∥ = 1`. Many `normed_ring`s and all `normed_field`s satisfy this
axiom. -/
class norm_one_class (α : Type*) [has_norm α] [has_one α] : Prop :=
(norm_one : ∥(1:α)∥ = 1)

export norm_one_class (norm_one)

attribute [simp] norm_one

@[simp] lemma nnnorm_one [semi_normed_group α] [has_one α] [norm_one_class α] : nnnorm (1:α) = 1 :=
nnreal.eq norm_one

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_comm_ring.to_comm_ring [β : semi_normed_comm_ring α] : comm_ring α := { ..β }

@[priority 100] -- see Note [lower instance priority]
instance normed_ring.to_normed_group [β : normed_ring α] : normed_group α := { ..β }

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_ring.to_semi_normed_group [β : semi_normed_ring α] :
  semi_normed_group α := { ..β }

instance prod.norm_one_class [normed_group α] [has_one α] [norm_one_class α]
  [normed_group β] [has_one β] [norm_one_class β] :
  norm_one_class (α × β) :=
⟨by simp [prod.norm_def]⟩

variables [semi_normed_ring α]

lemma norm_mul_le (a b : α) : (∥a*b∥) ≤ (∥a∥) * (∥b∥) :=
semi_normed_ring.norm_mul _ _

lemma list.norm_prod_le' : ∀ {l : list α}, l ≠ [] → ∥l.prod∥ ≤ (l.map norm).prod
| [] h := (h rfl).elim
| [a] _ := by simp
| (a :: b :: l) _ :=
  begin
    rw [list.map_cons, list.prod_cons, @list.prod_cons _ _ _ ∥a∥],
    refine le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left _ (norm_nonneg _)),
    exact list.norm_prod_le' (list.cons_ne_nil b l)
  end

lemma list.norm_prod_le [norm_one_class α] : ∀ l : list α, ∥l.prod∥ ≤ (l.map norm).prod
| [] := by simp
| (a::l) := list.norm_prod_le' (list.cons_ne_nil a l)

lemma finset.norm_prod_le' {α : Type*} [normed_comm_ring α] (s : finset ι) (hs : s.nonempty)
  (f : ι → α) :
  ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ :=
begin
  rcases s with ⟨⟨l⟩, hl⟩,
  have : l.map f ≠ [], by simpa using hs,
  simpa using list.norm_prod_le' this
end

lemma finset.norm_prod_le {α : Type*} [normed_comm_ring α] [norm_one_class α] (s : finset ι)
  (f : ι → α) :
  ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ :=
begin
  rcases s with ⟨⟨l⟩, hl⟩,
  simpa using (l.map f).norm_prod_le
end

/-- If `α` is a seminormed ring, then `∥a^n∥≤ ∥a∥^n` for `n > 0`. See also `norm_pow_le`. -/
lemma norm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ∥a^n∥ ≤ ∥a∥^n
| 1 h := by simp
| (n+2) h :=
  le_trans (norm_mul_le a (a^(n+1)))
           (mul_le_mul (le_refl _)
                       (norm_pow_le' (nat.succ_pos _)) (norm_nonneg _) (norm_nonneg _))

/-- If `α` is a seminormed ring with `∥1∥=1`, then `∥a^n∥≤ ∥a∥^n`. See also `norm_pow_le'`. -/
lemma norm_pow_le [norm_one_class α] (a : α) : ∀ (n : ℕ), ∥a^n∥ ≤ ∥a∥^n
| 0 := by simp
| (n+1) := norm_pow_le' a n.zero_lt_succ

lemma eventually_norm_pow_le (a : α) : ∀ᶠ (n:ℕ) in at_top, ∥a ^ n∥ ≤ ∥a∥ ^ n :=
eventually_at_top.mpr ⟨1, λ b h, norm_pow_le' a (nat.succ_le_iff.mp h)⟩

/-- In a seminormed ring, the left-multiplication `add_monoid_hom` is bounded. -/
lemma mul_left_bound (x : α) :
  ∀ (y:α), ∥add_monoid_hom.mul_left x y∥ ≤ ∥x∥ * ∥y∥ :=
norm_mul_le x

/-- In a seminormed ring, the right-multiplication `add_monoid_hom` is bounded. -/
lemma mul_right_bound (x : α) :
  ∀ (y:α), ∥add_monoid_hom.mul_right x y∥ ≤ ∥x∥ * ∥y∥ :=
λ y, by {rw mul_comm, convert norm_mul_le y x}

/-- Seminormed ring structure on the product of two seminormed rings, using the sup norm. -/
instance prod.semi_normed_ring [semi_normed_ring β] : semi_normed_ring (α × β) :=
{ norm_mul := assume x y,
  calc
    ∥x * y∥ = ∥(x.1*y.1, x.2*y.2)∥ : rfl
        ... = (max ∥x.1*y.1∥  ∥x.2*y.2∥) : rfl
        ... ≤ (max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥)) :
          max_le_max (norm_mul_le (x.1) (y.1)) (norm_mul_le (x.2) (y.2))
        ... = (max (∥x.1∥*∥y.1∥) (∥y.2∥*∥x.2∥)) : by simp[mul_comm]
        ... ≤ (max (∥x.1∥) (∥x.2∥)) * (max (∥y.2∥) (∥y.1∥)) :
          by apply max_mul_mul_le_max_mul_max; simp [norm_nonneg]
        ... = (max (∥x.1∥) (∥x.2∥)) * (max (∥y.1∥) (∥y.2∥)) : by simp [max_comm]
        ... = (∥x∥*∥y∥) : rfl,
  ..prod.semi_normed_group }

end semi_normed_ring

section normed_ring

variables [normed_ring α]

lemma units.norm_pos [nontrivial α] (x : units α) : 0 < ∥(x:α)∥ :=
norm_pos_iff.mpr (units.ne_zero x)

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
instance prod.normed_ring [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := norm_mul_le,
  ..prod.semi_normed_group }

end normed_ring

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_ring_top_monoid [semi_normed_ring α] : has_continuous_mul α :=
⟨ continuous_iff_continuous_at.2 $ λ x, tendsto_iff_norm_tendsto_zero.2 $
    begin
      have : ∀ e : α × α, ∥e.1 * e.2 - x.1 * x.2∥ ≤ ∥e.1∥ * ∥e.2 - x.2∥ + ∥e.1 - x.1∥ * ∥x.2∥,
      { intro e,
        calc ∥e.1 * e.2 - x.1 * x.2∥ ≤ ∥e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2∥ :
          by rw [mul_sub, sub_mul, sub_add_sub_cancel]
        ... ≤ ∥e.1∥ * ∥e.2 - x.2∥ + ∥e.1 - x.1∥ * ∥x.2∥ :
          norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _) },
      refine squeeze_zero (λ e, norm_nonneg _) this _,
      convert ((continuous_fst.tendsto x).norm.mul ((continuous_snd.tendsto x).sub
        tendsto_const_nhds).norm).add
        (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _),
      show tendsto _ _ _, from tendsto_const_nhds,
      simp
    end ⟩

/-- A seminormed ring is a topological ring. -/
@[priority 100] -- see Note [lower instance priority]
instance semi_normed_top_ring [semi_normed_ring α] : topological_ring α :=
⟨ continuous_iff_continuous_at.2 $ λ x, tendsto_iff_norm_tendsto_zero.2 $
    have ∀ e : α, -e - -x = -(e - x), by intro; simp,
    by simp only [this, norm_neg]; apply tendsto_norm_sub_self ⟩

/-- A normed field is a field with a norm satisfying ∥x y∥ = ∥x∥ ∥y∥. -/
class normed_field (α : Type*) extends has_norm α, field α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul' : ∀ a b, norm (a * b) = norm a * norm b)

/-- A nondiscrete normed field is a normed field in which there is an element of norm different from
`0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by multiplication
by the powers of any element, and thus to relate algebra and topology. -/
class nondiscrete_normed_field (α : Type*) extends normed_field α :=
(non_trivial : ∃x:α, 1<∥x∥)

namespace normed_field

section normed_field

variables [normed_field α]

@[simp] lemma norm_mul (a b : α) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
normed_field.norm_mul' a b

@[priority 100] -- see Note [lower instance priority]
instance to_normed_comm_ring : normed_comm_ring α :=
{ norm_mul := λ a b, (norm_mul a b).le, ..‹normed_field α› }

@[priority 900]
instance to_norm_one_class : norm_one_class α :=
⟨mul_left_cancel' (mt norm_eq_zero.1 (@one_ne_zero α _ _)) $
  by rw [← norm_mul, mul_one, mul_one]⟩

@[simp] lemma nnnorm_mul (a b : α) : nnnorm (a * b) = nnnorm a * nnnorm b :=
nnreal.eq $ norm_mul a b

/-- `norm` as a `monoid_hom`. -/
@[simps] def norm_hom : monoid_with_zero_hom α ℝ := ⟨norm, norm_zero, norm_one, norm_mul⟩

/-- `nnnorm` as a `monoid_hom`. -/
@[simps] def nnnorm_hom : monoid_with_zero_hom α ℝ≥0 :=
⟨nnnorm, nnnorm_zero, nnnorm_one, nnnorm_mul⟩

@[simp] lemma norm_pow (a : α) : ∀ (n : ℕ), ∥a ^ n∥ = ∥a∥ ^ n :=
norm_hom.to_monoid_hom.map_pow a

@[simp] lemma nnnorm_pow (a : α) (n : ℕ) : nnnorm (a ^ n) = nnnorm a ^ n :=
nnnorm_hom.to_monoid_hom.map_pow a n

@[simp] lemma norm_prod (s : finset β) (f : β → α) :
  ∥∏ b in s, f b∥ = ∏ b in s, ∥f b∥ :=
(norm_hom.to_monoid_hom : α →* ℝ).map_prod f s

@[simp] lemma nnnorm_prod (s : finset β) (f : β → α) :
  nnnorm (∏ b in s, f b) = ∏ b in s, nnnorm (f b) :=
(nnnorm_hom.to_monoid_hom : α →* ℝ≥0).map_prod f s

@[simp] lemma norm_div (a b : α) : ∥a / b∥ = ∥a∥ / ∥b∥ :=
(norm_hom : monoid_with_zero_hom α ℝ).map_div a b

@[simp] lemma nnnorm_div (a b : α) : nnnorm (a / b) = nnnorm a / nnnorm b :=
(nnnorm_hom : monoid_with_zero_hom α ℝ≥0).map_div a b

@[simp] lemma norm_inv (a : α) : ∥a⁻¹∥ = ∥a∥⁻¹ :=
(norm_hom : monoid_with_zero_hom α ℝ).map_inv' a

@[simp] lemma nnnorm_inv (a : α) : nnnorm (a⁻¹) = (nnnorm a)⁻¹ :=
nnreal.eq $ by simp

@[simp] lemma norm_fpow : ∀ (a : α) (n : ℤ), ∥a^n∥ = ∥a∥^n :=
(norm_hom : monoid_with_zero_hom α ℝ).map_fpow

@[simp] lemma nnnorm_fpow : ∀ (a : α) (n : ℤ), nnnorm (a^n) = (nnnorm a)^n :=
(nnnorm_hom : monoid_with_zero_hom α ℝ≥0).map_fpow

@[priority 100] -- see Note [lower instance priority]
instance : has_continuous_inv' α :=
begin
  refine ⟨λ r r0, tendsto_iff_norm_tendsto_zero.2 _⟩,
  have r0' : 0 < ∥r∥ := norm_pos_iff.2 r0,
  rcases exists_between r0' with ⟨ε, ε0, εr⟩,
  have : ∀ᶠ e in 𝓝 r, ∥e⁻¹ - r⁻¹∥ ≤ ∥r - e∥ / ∥r∥ / ε,
  { filter_upwards [(is_open_lt continuous_const continuous_norm).eventually_mem εr],
    intros e he,
    have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he),
    calc ∥e⁻¹ - r⁻¹∥ = ∥r - e∥ / ∥r∥ / ∥e∥ : by field_simp [mul_comm]
    ... ≤ ∥r - e∥ / ∥r∥ / ε :
      div_le_div_of_le_left (div_nonneg (norm_nonneg _) (norm_nonneg _)) ε0 he.le },
  refine squeeze_zero' (eventually_of_forall $ λ _, norm_nonneg _) this _,
  refine (continuous_const.sub continuous_id).norm.div_const.div_const.tendsto' _ _ _,
  simp
end

end normed_field

variables (α) [nondiscrete_normed_field α]

lemma exists_one_lt_norm : ∃x : α, 1 < ∥x∥ := ‹nondiscrete_normed_field α›.non_trivial

lemma exists_norm_lt_one : ∃x : α, 0 < ∥x∥ ∧ ∥x∥ < 1 :=
begin
  rcases exists_one_lt_norm α with ⟨y, hy⟩,
  refine ⟨y⁻¹, _, _⟩,
  { simp only [inv_eq_zero, ne.def, norm_pos_iff],
    rintro rfl,
    rw norm_zero at hy,
    exact lt_asymm zero_lt_one hy },
  { simp [inv_lt_one hy] }
end

lemma exists_lt_norm (r : ℝ) : ∃ x : α, r < ∥x∥ :=
let ⟨w, hw⟩ := exists_one_lt_norm α in
let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw in
⟨w^n, by rwa norm_pow⟩

lemma exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < r :=
let ⟨w, hw⟩ := exists_one_lt_norm α in
let ⟨n, hle, hlt⟩ := exists_int_pow_near' hr hw in
⟨w^n, by { rw norm_fpow; exact fpow_pos_of_pos (lt_trans zero_lt_one hw) _},
by rwa norm_fpow⟩

variable {α}

@[instance]
lemma punctured_nhds_ne_bot (x : α) : ne_bot (𝓝[{x}ᶜ] x) :=
begin
  rw [← mem_closure_iff_nhds_within_ne_bot, metric.mem_closure_iff],
  rintros ε ε0,
  rcases normed_field.exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩,
  refine ⟨x + b, mt (set.mem_singleton_iff.trans add_right_eq_self).1 $ norm_pos_iff.1 hb0, _⟩,
  rwa [dist_comm, dist_eq_norm, add_sub_cancel'],
end

@[instance]
lemma nhds_within_is_unit_ne_bot : ne_bot (𝓝[{x : α | is_unit x}] 0) :=
by simpa only [is_unit_iff_ne_zero] using punctured_nhds_ne_bot (0:α)

end normed_field

instance : normed_field ℝ :=
{ norm_mul' := abs_mul,
  .. real.normed_group }

instance : nondiscrete_normed_field ℝ :=
{ non_trivial := ⟨2, by { unfold norm, rw abs_of_nonneg; norm_num }⟩ }

namespace real

lemma norm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥ = x :=
abs_of_nonneg hx

@[simp] lemma norm_coe_nat (n : ℕ) : ∥(n : ℝ)∥ = n := abs_of_nonneg n.cast_nonneg

@[simp] lemma nnnorm_coe_nat (n : ℕ) : nnnorm (n : ℝ) = n := nnreal.eq $ by simp

@[simp] lemma norm_two : ∥(2:ℝ)∥ = 2 := abs_of_pos (@zero_lt_two ℝ _ _)

@[simp] lemma nnnorm_two : nnnorm (2:ℝ) = 2 := nnreal.eq $ by simp

lemma nnnorm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : nnnorm x = ⟨x, hx⟩ :=
nnreal.eq $ norm_of_nonneg hx

lemma ennnorm_eq_of_real {x : ℝ} (hx : 0 ≤ x) : (nnnorm x : ℝ≥0∞) = ennreal.of_real x :=
by { rw [← of_real_norm_eq_coe_nnnorm, norm_of_nonneg hx] }

end real

namespace nnreal

open_locale nnreal

@[simp] lemma norm_eq (x : ℝ≥0) : ∥(x : ℝ)∥ = x :=
by rw [real.norm_eq_abs, x.abs_eq]

@[simp] lemma nnnorm_eq (x : ℝ≥0) : nnnorm (x : ℝ) = x :=
nnreal.eq $ real.norm_of_nonneg x.2

end nnreal

@[simp] lemma norm_norm [semi_normed_group α] (x : α) : ∥∥x∥∥ = ∥x∥ :=
real.norm_of_nonneg (norm_nonneg _)

@[simp] lemma nnnorm_norm [semi_normed_group α] (a : α) : nnnorm ∥a∥ = nnnorm a :=
by simp only [nnnorm, norm_norm]

/-- A restatement of `metric_space.tendsto_at_top` in terms of the norm. -/
lemma normed_group.tendsto_at_top [nonempty α] [semilattice_sup α] {β : Type*} [semi_normed_group β]
  {f : α → β} {b : β} :
  tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ∥f n - b∥ < ε :=
(at_top_basis.tendsto_iff metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

/--
A variant of `normed_group.tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
lemma normed_group.tendsto_at_top' [nonempty α] [semilattice_sup α] [no_top_order α]
  {β : Type*} [semi_normed_group β]
  {f : α → β} {b : β} :
  tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ∥f n - b∥ < ε :=
(at_top_basis_Ioi.tendsto_iff metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

instance : normed_comm_ring ℤ :=
{ norm := λ n, ∥(n : ℝ)∥,
  norm_mul := λ m n, le_of_eq $ by simp only [norm, int.cast_mul, abs_mul],
  dist_eq := λ m n, by simp only [int.dist_eq, norm, int.cast_sub],
  mul_comm := mul_comm }

@[norm_cast] lemma int.norm_cast_real (m : ℤ) : ∥(m : ℝ)∥ = ∥m∥ := rfl

instance : norm_one_class ℤ :=
⟨by simp [← int.norm_cast_real]⟩

instance : normed_field ℚ :=
{ norm := λ r, ∥(r : ℝ)∥,
  norm_mul' := λ r₁ r₂, by simp only [norm, rat.cast_mul, abs_mul],
  dist_eq := λ r₁ r₂, by simp only [rat.dist_eq, norm, rat.cast_sub] }

instance : nondiscrete_normed_field ℚ :=
{ non_trivial := ⟨2, by { unfold norm, rw abs_of_nonneg; norm_num }⟩ }

@[norm_cast, simp] lemma rat.norm_cast_real (r : ℚ) : ∥(r : ℝ)∥ = ∥r∥ := rfl

@[norm_cast, simp] lemma int.norm_cast_rat (m : ℤ) : ∥(m : ℚ)∥ = ∥m∥ :=
by rw [← rat.norm_cast_real, ← int.norm_cast_real]; congr' 1; norm_cast

section semi_normed_space

section prio
set_option extends_priority 920
-- Here, we set a rather high priority for the instance `[semi_normed_space α β] : semimodule α β`
-- to take precedence over `semiring.to_semimodule` as this leads to instance paths with better
-- unification properties.
-- see Note[vector space definition] for why we extend `semimodule`.
/-- A seminormed space over a normed field is a vector space endowed with a seminorm which satisfies
the equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class semi_normed_space (α : Type*) (β : Type*) [normed_field α] [semi_normed_group β]
  extends semimodule α β :=
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)

set_option extends_priority 920
-- Here, we set a rather high priority for the instance `[normed_space α β] : semimodule α β`
-- to take precedence over `semiring.to_semimodule` as this leads to instance paths with better
-- unification properties.
-- see Note[vector space definition] for why we extend `semimodule`.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class normed_space (α : Type*) (β : Type*) [normed_field α] [normed_group β]
  extends semimodule α β :=
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)

/-- A normed space is a seminormed space. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_space.to_semi_normed_space [normed_field α] [normed_group β]
  [γ : normed_space α β] : semi_normed_space α β := { ..γ }

end prio

variables [normed_field α] [semi_normed_group β]

instance normed_field.to_normed_space : normed_space α α :=
{ norm_smul_le := λ a b, le_of_eq (normed_field.norm_mul a b) }

lemma norm_smul [semi_normed_space α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ :=
begin
  by_cases h : s = 0,
  { simp [h] },
  { refine le_antisymm (semi_normed_space.norm_smul_le s x) _,
    calc ∥s∥ * ∥x∥ = ∥s∥ * ∥s⁻¹ • s • x∥     : by rw [inv_smul_smul' h]
               ... ≤ ∥s∥ * (∥s⁻¹∥ * ∥s • x∥) :
      mul_le_mul_of_nonneg_left (semi_normed_space.norm_smul_le _ _) (norm_nonneg _)
               ... = ∥s • x∥                 :
      by rw [normed_field.norm_inv, ← mul_assoc, mul_inv_cancel (mt norm_eq_zero.1 h), one_mul] }
end

@[simp] lemma abs_norm_eq_norm (z : β) : abs ∥z∥ = ∥z∥ :=
  (abs_eq (norm_nonneg z)).mpr (or.inl rfl)

lemma dist_smul [semi_normed_space α β] (s : α) (x y : β) : dist (s • x) (s • y) = ∥s∥ * dist x y :=
by simp only [dist_eq_norm, (norm_smul _ _).symm, smul_sub]

lemma nnnorm_smul [semi_normed_space α β] (s : α) (x : β) : nnnorm (s • x) = nnnorm s * nnnorm x :=
nnreal.eq $ norm_smul s x

lemma nndist_smul [semi_normed_space α β] (s : α) (x y : β) :
  nndist (s • x) (s • y) = nnnorm s * nndist x y :=
nnreal.eq $ dist_smul s x y

lemma norm_smul_of_nonneg [semi_normed_space ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) :
  ∥t • x∥ = t * ∥x∥ := by rw [norm_smul, real.norm_eq_abs, abs_of_nonneg ht]

variables {E : Type*} [semi_normed_group E] [semi_normed_space α E]
variables {F : Type*} [semi_normed_group F] [semi_normed_space α F]

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_space.has_continuous_smul : has_continuous_smul α E :=
begin
  refine { continuous_smul := continuous_iff_continuous_at.2 $
    λ p, tendsto_iff_norm_tendsto_zero.2 _ },
  refine squeeze_zero (λ _, norm_nonneg _) _ _,
  { exact λ q, ∥q.1 - p.1∥ * ∥q.2∥ + ∥p.1∥ * ∥q.2 - p.2∥ },
  { intro q,
    rw [← sub_add_sub_cancel, ← norm_smul, ← norm_smul, smul_sub, sub_smul],
    exact norm_add_le _ _ },
  { conv { congr, skip, skip, congr, rw [← zero_add (0:ℝ)], congr,
      rw [← zero_mul ∥p.2∥], skip, rw [← mul_zero ∥p.1∥] },
    exact ((tendsto_iff_norm_tendsto_zero.1 (continuous_fst.tendsto p)).mul
      (continuous_snd.tendsto p).norm).add
        (tendsto_const_nhds.mul (tendsto_iff_norm_tendsto_zero.1 (continuous_snd.tendsto p))) }
end

theorem eventually_nhds_norm_smul_sub_lt (c : α) (x : E) {ε : ℝ} (h : 0 < ε) :
  ∀ᶠ y in 𝓝 x, ∥c • (y - x)∥ < ε :=
have tendsto (λ y, ∥c • (y - x)∥) (𝓝 x) (𝓝 0),
  from (continuous_const.smul (continuous_id.sub continuous_const)).norm.tendsto' _ _ (by simp),
this.eventually (gt_mem_nhds h)

theorem closure_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  closure (ball x r) = closed_ball x r :=
begin
  refine set.subset.antisymm closure_ball_subset_closed_ball (λ y hy, _),
  have : continuous_within_at (λ c : ℝ, c • (y - x) + x) (set.Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).continuous_within_at,
  convert this.mem_closure _ _,
  { rw [one_smul, sub_add_cancel] },
  { simp [closure_Ico (@zero_lt_one ℝ _ _), zero_le_one] },
  { rintros c ⟨hc0, hc1⟩,
    rw [set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, real.norm_eq_abs,
      abs_of_nonneg hc0, mul_comm, ← mul_one r],
    rw [mem_closed_ball, dist_eq_norm] at hy,
    apply mul_lt_mul'; assumption }
end

theorem frontier_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  frontier (ball x r) = sphere x r :=
begin
  rw [frontier, closure_ball x hr, is_open_ball.interior_eq],
  ext x, exact (@eq_iff_le_not_lt ℝ _ _ _).symm
end

theorem interior_closed_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  interior (closed_ball x r) = ball x r :=
begin
  refine set.subset.antisymm _ ball_subset_interior_closed_ball,
  intros y hy,
  rcases le_iff_lt_or_eq.1 (mem_closed_ball.1 $ interior_subset hy) with hr|rfl, { exact hr },
  set f : ℝ → E := λ c : ℝ, c • (y - x) + x,
  suffices : f ⁻¹' closed_ball x (dist y x) ⊆ set.Icc (-1) 1,
  { have hfc : continuous f := (continuous_id.smul continuous_const).add continuous_const,
    have hf1 : (1:ℝ) ∈ f ⁻¹' (interior (closed_ball x $ dist y x)), by simpa [f],
    have h1 : (1:ℝ) ∈ interior (set.Icc (-1:ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1),
    contrapose h1,
    simp },
  intros c hc,
  rw [set.mem_Icc, ← abs_le, ← real.norm_eq_abs, ← mul_le_mul_right hr],
  simpa [f, dist_eq_norm, norm_smul] using hc
end

theorem frontier_closed_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  frontier (closed_ball x r) = sphere x r :=
by rw [frontier, closure_closed_ball, interior_closed_ball x hr,
  closed_ball_diff_ball]

variables (α)

lemma ne_neg_of_mem_sphere [char_zero α] {r : ℝ} (hr : 0 < r) (x : sphere (0:E) r) : x ≠ - x :=
λ h, nonzero_of_mem_sphere hr x (eq_zero_of_eq_neg α (by { conv_lhs {rw h}, simp }))

lemma ne_neg_of_mem_unit_sphere [char_zero α] (x : sphere (0:E) 1) : x ≠ - x :=
ne_neg_of_mem_sphere α  (by norm_num) x

variables {α}

open normed_field

/-- The product of two seminormed spaces is a seminormed space, with the sup norm. -/
instance prod.semi_normed_space : semi_normed_space α (E × F) :=
{ norm_smul_le := λ s x, le_of_eq $ by simp [prod.semi_norm_def, norm_smul, mul_max_of_nonneg],
  ..prod.normed_group,
  ..prod.semimodule }

/-- The product of finitely many seminormed spaces is a seminormed space, with the sup norm. -/
instance pi.semi_normed_space {E : ι → Type*} [fintype ι] [∀i, semi_normed_group (E i)]
  [∀i, semi_normed_space α (E i)] : semi_normed_space α (Πi, E i) :=
{ norm_smul_le := λ a f, le_of_eq $
    show (↑(finset.sup finset.univ (λ (b : ι), nnnorm (a • f b))) : ℝ) =
      nnnorm a * ↑(finset.sup finset.univ (λ (b : ι), nnnorm (f b))),
    by simp only [(nnreal.coe_mul _ _).symm, nnreal.mul_finset_sup, nnnorm_smul] }

/-- A subspace of a seminormed space is also a normed space, with the restriction of the norm. -/
instance submodule.semi_normed_space {𝕜 R : Type*} [has_scalar 𝕜 R] [normed_field 𝕜] [ring R]
  {E : Type*} [semi_normed_group E] [semi_normed_space 𝕜 E] [semimodule R E]
  [is_scalar_tower 𝕜 R E] (s : submodule R E) :
  semi_normed_space 𝕜 s :=
{ norm_smul_le := λc x, le_of_eq $ norm_smul c (x : E) }

/-- If there is a scalar `c` with `∥c∥>1`, then any element of with norm different from `0` can be
moved by scalar multiplication to any shell of width `∥c∥`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E}
  (hx : ∥x∥ ≠ 0) : ∃d:α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ (ε/∥c∥ ≤ ∥d • x∥) ∧ (∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥) :=
begin
  have xεpos : 0 < ∥x∥/ε := div_pos ((ne.symm hx).le_iff_lt.1 (norm_nonneg x)) εpos,
  rcases exists_int_pow_near xεpos hc with ⟨n, hn⟩,
  have cpos : 0 < ∥c∥ := lt_trans (zero_lt_one : (0 :ℝ) < 1) hc,
  have cnpos : 0 < ∥c^(n+1)∥ := by { rw norm_fpow, exact lt_trans xεpos hn.2 },
  refine ⟨(c^(n+1))⁻¹, _, _, _, _⟩,
  show (c ^ (n + 1))⁻¹  ≠ 0,
    by rwa [ne.def, inv_eq_zero, ← ne.def, ← norm_pos_iff],
  show ∥(c ^ (n + 1))⁻¹ • x∥ < ε,
  { rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_lt_iff cnpos, mul_comm, norm_fpow],
    exact (div_lt_iff εpos).1 (hn.2) },
  show ε / ∥c∥ ≤ ∥(c ^ (n + 1))⁻¹ • x∥,
  { rw [div_le_iff cpos, norm_smul, norm_inv, norm_fpow, fpow_add (ne_of_gt cpos),
        fpow_one, mul_inv_rev', mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel (ne_of_gt cpos),
        one_mul, ← div_eq_inv_mul, le_div_iff (fpow_pos_of_pos cpos _), mul_comm],
    exact (le_div_iff εpos).1 hn.1 },
  show ∥(c ^ (n + 1))⁻¹∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥,
  { have : ε⁻¹ * ∥c∥ * ∥x∥ = ε⁻¹ * ∥x∥ * ∥c∥, by ring,
    rw [norm_inv, inv_inv', norm_fpow, fpow_add (ne_of_gt cpos), fpow_one, this, ← div_eq_inv_mul],
    exact mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _) }
end

end semi_normed_space

section normed_space

variables [normed_field α]
variables {E : Type*} [normed_group E] [normed_space α E]
variables {F : Type*} [normed_group F] [normed_space α F]

open normed_field

theorem interior_closed_ball' [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) :
  interior (closed_ball x r) = ball x r :=
begin
  rcases lt_trichotomy r 0 with hr|rfl|hr,
  { simp [closed_ball_eq_empty_iff_neg.2 hr, ball_eq_empty_iff_nonpos.2 (le_of_lt hr)] },
  { suffices : x ∉ interior {x},
    { rw [ball_zero, closed_ball_zero, ← set.subset_empty_iff],
      intros y hy,
      obtain rfl : y = x := set.mem_singleton_iff.1 (interior_subset hy),
      exact this hy },
    rw [← set.mem_compl_iff, ← closure_compl],
    rcases exists_ne (0 : E) with ⟨z, hz⟩,
    suffices : (λ c : ℝ, x + c • z) 0 ∈ closure ({x}ᶜ : set E),
      by simpa only [zero_smul, add_zero] using this,
    have : (0:ℝ) ∈ closure (set.Ioi (0:ℝ)), by simp [closure_Ioi],
    refine (continuous_const.add (continuous_id.smul
      continuous_const)).continuous_within_at.mem_closure this _,
    intros c hc,
    simp [smul_eq_zero, hz, ne_of_gt hc] },
  { exact interior_closed_ball x hr }
end

theorem frontier_closed_ball' [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) :
  frontier (closed_ball x r) = sphere x r :=
by rw [frontier, closure_closed_ball, interior_closed_ball' x r, closed_ball_diff_ball]

variables {α}

/-- If there is a scalar `c` with `∥c∥>1`, then any element can be moved by scalar multiplication to
any shell of width `∥c∥`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
lemma rescale_to_shell {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) :
  ∃d:α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ (ε/∥c∥ ≤ ∥d • x∥) ∧ (∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥) :=
rescale_to_shell_semi_normed hc εpos (ne_of_lt (norm_pos_iff.2 hx)).symm

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance : normed_space α (E × F) := { ..prod.semi_normed_space }

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance pi.normed_space {E : ι → Type*} [fintype ι] [∀i, normed_group (E i)]
  [∀i, normed_space α (E i)] : normed_space α (Πi, E i) :=
{ ..pi.semi_normed_space }

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance submodule.normed_space {𝕜 R : Type*} [has_scalar 𝕜 R] [normed_field 𝕜] [ring R]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [semimodule R E]
  [is_scalar_tower 𝕜 R E] (s : submodule R E) :
  normed_space 𝕜 s :=
{ ..submodule.semi_normed_space s }

end normed_space

section normed_algebra

/-- A seminormed algebra `𝕜'` over `𝕜` is an algebra endowed with a seminorm for which the
embedding of `𝕜` in `𝕜'` is an isometry. -/
class semi_normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜']
  extends algebra 𝕜 𝕜' :=
(norm_algebra_map_eq : ∀x:𝕜, ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥)

/-- A normed algebra `𝕜'` over `𝕜` is an algebra endowed with a norm for which the embedding of
`𝕜` in `𝕜'` is an isometry. -/
class normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [normed_ring 𝕜']
  extends algebra 𝕜 𝕜' :=
(norm_algebra_map_eq : ∀x:𝕜, ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥)

/-- A normed algebra is a seminormed algebra. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_algebra.to_semi_normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜]
  [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] : semi_normed_algebra 𝕜 𝕜' :=
{ norm_algebra_map_eq := normed_algebra.norm_algebra_map_eq }

@[simp] lemma norm_algebra_map_eq {𝕜 : Type*} (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜']
  [h : semi_normed_algebra 𝕜 𝕜'] (x : 𝕜) : ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥ :=
semi_normed_algebra.norm_algebra_map_eq _

variables (𝕜 : Type*) [normed_field 𝕜]
variables (𝕜' : Type*) [semi_normed_ring 𝕜']

@[priority 100]
instance semi_normed_algebra.to_semi_normed_space [h : semi_normed_algebra 𝕜 𝕜'] :
  semi_normed_space 𝕜 𝕜' :=
{ norm_smul_le := λ s x, calc
    ∥s • x∥ = ∥((algebra_map 𝕜 𝕜') s) * x∥ : by { rw h.smul_def', refl }
    ... ≤ ∥algebra_map 𝕜 𝕜' s∥ * ∥x∥ : semi_normed_ring.norm_mul _ _
    ... = ∥s∥ * ∥x∥ : by rw norm_algebra_map_eq,
  ..h }

@[priority 100]
instance normed_algebra.to_normed_space (𝕜 : Type*) [normed_field 𝕜] (𝕜' : Type*)
  [normed_ring 𝕜'] [h : normed_algebra 𝕜 𝕜'] : normed_space 𝕜 𝕜' :=
{ norm_smul_le := semi_normed_space.norm_smul_le,
  ..h }

instance normed_algebra.id : normed_algebra 𝕜 𝕜 :=
{ norm_algebra_map_eq := by simp,
.. algebra.id 𝕜}

variables (𝕜') [semi_normed_algebra 𝕜 𝕜']
include 𝕜

lemma normed_algebra.norm_one : ∥(1:𝕜')∥ = 1 :=
by simpa using (norm_algebra_map_eq 𝕜' (1:𝕜))

lemma normed_algebra.norm_one_class : norm_one_class 𝕜' :=
⟨normed_algebra.norm_one 𝕜 𝕜'⟩

lemma normed_algebra.zero_ne_one : (0:𝕜') ≠ 1 :=
begin
  refine (ne_zero_of_norm_pos _).symm,
  rw normed_algebra.norm_one 𝕜 𝕜', norm_num,
end

lemma normed_algebra.nontrivial : nontrivial 𝕜' :=
⟨⟨0, 1, normed_algebra.zero_ne_one 𝕜 𝕜'⟩⟩

end normed_algebra

section restrict_scalars

variables (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
(E : Type*) [normed_group E] [normed_space 𝕜' E]
(F : Type*) [semi_normed_group F] [semi_normed_space 𝕜' F]

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-seminormed space structure induced by a `𝕜'`-seminormed space structure when `𝕜'` is a
seminormed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `semimodule.restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def semi_normed_space.restrict_scalars : semi_normed_space 𝕜 F :=
{ norm_smul_le := λc x, le_of_eq $ begin
    change ∥(algebra_map 𝕜 𝕜' c) • x∥ = ∥c∥ * ∥x∥,
    simp [norm_smul]
  end,
  ..restrict_scalars.semimodule 𝕜 𝕜' F }

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-normed space structure induced by a `𝕜'`-normed space structure when `𝕜'` is a
normed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `semimodule.restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def normed_space.restrict_scalars : normed_space 𝕜 E :=
{ norm_smul_le := λc x, le_of_eq $ begin
    change ∥(algebra_map 𝕜 𝕜' c) • x∥ = ∥c∥ * ∥x∥,
    simp [norm_smul]
  end,
  ..restrict_scalars.semimodule 𝕜 𝕜' E }

instance {𝕜 : Type*} {𝕜' : Type*} {F : Type*} [I : semi_normed_group F] :
  semi_normed_group (restrict_scalars 𝕜 𝕜' F) := I

instance {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [I : normed_group E] :
  normed_group (restrict_scalars 𝕜 𝕜' E) := I

instance semimodule.restrict_scalars.semi_normed_space_orig {𝕜 : Type*} {𝕜' : Type*} {F : Type*}
  [normed_field 𝕜'] [semi_normed_group F] [I : semi_normed_space 𝕜' F] :
  semi_normed_space 𝕜' (restrict_scalars 𝕜 𝕜' F) := I

instance semimodule.restrict_scalars.normed_space_orig {𝕜 : Type*} {𝕜' : Type*} {E : Type*}
  [normed_field 𝕜'] [normed_group E] [I : normed_space 𝕜' E] :
  normed_space 𝕜' (restrict_scalars 𝕜 𝕜' E) := I

instance : semi_normed_space 𝕜 (restrict_scalars 𝕜 𝕜' F) :=
(semi_normed_space.restrict_scalars 𝕜 𝕜' F : semi_normed_space 𝕜 F)

instance : normed_space 𝕜 (restrict_scalars 𝕜 𝕜' E) :=
(normed_space.restrict_scalars 𝕜 𝕜' E : normed_space 𝕜 E)

end restrict_scalars

section summable
open_locale classical
open finset filter
variables [semi_normed_group α] [semi_normed_group β]

lemma cauchy_seq_finset_iff_vanishing_norm {f : ι → α} :
  cauchy_seq (λ s : finset ι, ∑ i in s, f i) ↔
    ∀ε > (0 : ℝ), ∃s:finset ι, ∀t, disjoint t s → ∥ ∑ i in t, f i ∥ < ε :=
begin
  rw [cauchy_seq_finset_iff_vanishing, nhds_basis_ball.forall_iff],
  { simp only [ball_0_eq, set.mem_set_of_eq] },
  { rintros s t hst ⟨s', hs'⟩,
    exact ⟨s', λ t' ht', hst $ hs' _ ht'⟩ }
end

lemma summable_iff_vanishing_norm [complete_space α] {f : ι → α} :
  summable f ↔ ∀ε > (0 : ℝ), ∃s:finset ι, ∀t, disjoint t s → ∥ ∑ i in t, f i ∥ < ε :=
by rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing_norm]

lemma cauchy_seq_finset_of_norm_bounded {f : ι → α} (g : ι → ℝ) (hg : summable g)
  (h : ∀i, ∥f i∥ ≤ g i) : cauchy_seq (λ s : finset ι, ∑ i in s, f i) :=
cauchy_seq_finset_iff_vanishing_norm.2 $ assume ε hε,
  let ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hg ε hε in
  ⟨s, assume t ht,
    have ∥∑ i in t, g i∥ < ε := hs t ht,
    have nn : 0 ≤ ∑ i in t, g i := finset.sum_nonneg (assume a _, le_trans (norm_nonneg _) (h a)),
    lt_of_le_of_lt (norm_sum_le_of_le t (λ i _, h i)) $
      by rwa [real.norm_eq_abs, abs_of_nonneg nn] at this⟩

lemma cauchy_seq_finset_of_summable_norm {f : ι → α} (hf : summable (λa, ∥f a∥)) :
  cauchy_seq (λ s : finset ι, ∑ a in s, f a) :=
cauchy_seq_finset_of_norm_bounded _ hf (assume i, le_refl _)

/-- If a function `f` is summable in norm, and along some sequence of finsets exhausting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `f` is summable
with sum `a`. -/
lemma has_sum_of_subseq_of_summable {f : ι → α} (hf : summable (λa, ∥f a∥))
  {s : γ → finset ι} {p : filter γ} [ne_bot p]
  (hs : tendsto s p at_top) {a : α} (ha : tendsto (λ b, ∑ i in s b, f i) p (𝓝 a)) :
  has_sum f a :=
tendsto_nhds_of_cauchy_seq_of_subseq (cauchy_seq_finset_of_summable_norm hf) hs ha

lemma has_sum_iff_tendsto_nat_of_summable_norm {f : ℕ → α} {a : α} (hf : summable (λi, ∥f i∥)) :
  has_sum f a ↔ tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
⟨λ h, h.tendsto_sum_nat,
λ h, has_sum_of_subseq_of_summable hf tendsto_finset_range h⟩

/-- The direct comparison test for series:  if the norm of `f` is bounded by a real function `g`
which is summable, then `f` is summable. -/
lemma summable_of_norm_bounded
  [complete_space α] {f : ι → α} (g : ι → ℝ) (hg : summable g) (h : ∀i, ∥f i∥ ≤ g i) :
  summable f :=
by { rw summable_iff_cauchy_seq_finset, exact cauchy_seq_finset_of_norm_bounded g hg h }

lemma has_sum.norm_le_of_bounded {f : ι → α} {g : ι → ℝ} {a : α} {b : ℝ}
  (hf : has_sum f a) (hg : has_sum g b) (h : ∀ i, ∥f i∥ ≤ g i) :
  ∥a∥ ≤ b :=
le_of_tendsto_of_tendsto' hf.norm hg $ λ s, norm_sum_le_of_le _ $ λ i hi, h i

/-- Quantitative result associated to the direct comparison test for series:  If `∑' i, g i` is
summable, and for all `i`, `∥f i∥ ≤ g i`, then `∥∑' i, f i∥ ≤ ∑' i, g i`. Note that we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
lemma tsum_of_norm_bounded {f : ι → α} {g : ι → ℝ} {a : ℝ} (hg : has_sum g a)
  (h : ∀ i, ∥f i∥ ≤ g i) :
  ∥∑' i : ι, f i∥ ≤ a :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.norm_le_of_bounded hg h },
  { rw [tsum_eq_zero_of_not_summable hf, norm_zero],
    exact ge_of_tendsto' hg (λ s, sum_nonneg $ λ i hi, (norm_nonneg _).trans (h i)) }
end

/-- If `∑' i, ∥f i∥` is summable, then `∥∑' i, f i∥ ≤ (∑' i, ∥f i∥)`. Note that we do not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
lemma norm_tsum_le_tsum_norm {f : ι → α} (hf : summable (λi, ∥f i∥)) :
  ∥∑'i, f i∥ ≤ ∑' i, ∥f i∥ :=
tsum_of_norm_bounded hf.has_sum $ λ i, le_rfl

variable [complete_space α]

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
lemma summable_of_norm_bounded_eventually {f : ι → α} (g : ι → ℝ) (hg : summable g)
  (h : ∀ᶠ i in cofinite, ∥f i∥ ≤ g i) : summable f :=
begin
  replace h := mem_cofinite.1 h,
  refine h.summable_compl_iff.mp _,
  refine summable_of_norm_bounded _ (h.summable_compl_iff.mpr hg) _,
  rintros ⟨a, h'⟩,
  simpa using h'
end

lemma summable_of_nnnorm_bounded {f : ι → α} (g : ι → ℝ≥0) (hg : summable g)
  (h : ∀i, nnnorm (f i) ≤ g i) : summable f :=
summable_of_norm_bounded (λ i, (g i : ℝ)) (nnreal.summable_coe.2 hg) (λ i, by exact_mod_cast h i)

lemma summable_of_summable_norm {f : ι → α} (hf : summable (λa, ∥f a∥)) : summable f :=
summable_of_norm_bounded _ hf (assume i, le_refl _)

lemma summable_of_summable_nnnorm {f : ι → α} (hf : summable (λa, nnnorm (f a))) : summable f :=
summable_of_nnnorm_bounded _ hf (assume i, le_refl _)

end summable
