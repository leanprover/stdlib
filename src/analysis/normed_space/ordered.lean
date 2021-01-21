/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.asymptotics

/-!
# Ordered normed spaces

In this file, we define classes for fields and groups that are both normed and ordered.
These are mostly useful to avoid diamonds during type class inference.
-/

open filter asymptotics set
open_locale topological_space

/-- A `normed_linear_ordered_group` is an additive group that is both a `normed_group` and
    a `linear_ordered_add_comm_group`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_group (α : Type*)
extends linear_ordered_add_comm_group α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

@[priority 100] instance normed_linear_ordered_group.to_normed_group (α : Type*)
  [normed_linear_ordered_group α] : normed_group α :=
⟨normed_linear_ordered_group.dist_eq⟩

/-- A `normed_linear_ordered_field` is a field that is both a `normed_field` and a
    `linear_ordered_field`. This class is necessary to avoid diamonds. -/
class normed_linear_ordered_field (α : Type*)
extends linear_ordered_field α, has_norm α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul' : ∀ a b, norm (a * b) = norm a * norm b)

@[priority 100] instance normed_linear_ordered_field.to_normed_field (α : Type*)
  [normed_linear_ordered_field α] : normed_field α :=
{ dist_eq := normed_linear_ordered_field.dist_eq,
  norm_mul' := normed_linear_ordered_field.norm_mul' }

@[priority 100] instance normed_linear_ordered_field.to_normed_linear_ordered_group (α : Type*)
[normed_linear_ordered_field α] : normed_linear_ordered_group α :=
⟨normed_linear_ordered_field.dist_eq⟩

lemma tendsto_pow_div_pow_at_top_of_lt {α : Type*} [normed_linear_ordered_field α]
  [order_topology α] {p q : ℕ} (hpq : p < q) :
  tendsto (λ (x : α), x^p / x^q) at_top (𝓝 0) :=
begin
  suffices h : tendsto (λ (x : α), x ^ ((p : ℤ) - q)) at_top (𝓝 0),
  { refine h.congr' ((eventually_gt_at_top (0 : α)).mono (λ x hx, _)),
    simp [fpow_sub hx.ne'] },
  rw [← neg_sub, ← int.coe_nat_sub hpq.le],
  have : 1 ≤ q - p := nat.sub_pos_of_lt hpq,
  exact tendsto_pow_neg_at_top this
end

lemma is_o_pow_pow_at_top_of_lt {α : Type} [normed_linear_ordered_field α]
  [order_topology α] {p q : ℕ} (hpq : p < q) :
  is_o (λ (x : α), x^p) (λ (x : α), x^q) at_top :=
begin
  refine (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_at_top_of_lt hpq),
  exact (eventually_gt_at_top 0).mono (λ x hx hxq, (pow_ne_zero q hx.ne' hxq).elim),
end
