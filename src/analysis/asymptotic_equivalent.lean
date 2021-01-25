/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.asymptotics
import analysis.normed_space.ordered
import analysis.normed_space.bounded_linear_maps

/-!
# Asymptotic equivalence

In this file, we define the relation `is_equivalent u v l`, which means that `u-v` is little o of
`v` along the filter `l`.

Unlike `is_[oO]` relations, this one requires `u` and `v` to have the same codomaine `β`. While the
definition only requires `β` to be a `normed_group`, most interesting properties require it to be a
`normed_field`.

## Notations

We introduce the notation `u ~[l] v := is_equivalent u v l`, which you can use by opening the
`asymptotics` locale.

## Main results

If `β` is a `normed_group` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c ≠ 0`, this is true iff `tendsto u l (𝓝 c)` (see `is_equivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =ᶠ[l] 0` (see `is_equivalent_zero_iff_eventually_zero`)

If `β` is a `normed_field` :

- Alternative characterization of the relation (see `is_equivalent_iff_exists_eq_mul`) :

  `u ~[l] v ↔ ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v ↔ tendsto (u/v) l (𝓝 1)`
  (see `is_equivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `tendsto u l (𝓝 c) ↔ tendsto v l (𝓝 c)`
  (see `is_equivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `is_equivalent.mul` and `is_equivalent.div`)

If `β` is a `normed_linear_ordered_field` :

- If `u ~[l] v`, we have `tendsto u l at_top ↔ tendsto v l at_top`
  (see `is_equivalent.tendsto_at_top_iff`)

-/

namespace asymptotics

open filter function
open_locale topological_space

section normed_group

variables {α β : Type*} [normed_group β]

/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l` when
    `u x - v x = o(v x)` as x converges along `l`. -/
def is_equivalent (u v : α → β) (l : filter α) := is_o (u - v) v l

localized "notation u ` ~[`:50 l:50 `] `:0 v:50 := asymptotics.is_equivalent u v l" in asymptotics

variables {u v w : α → β} {l : filter α}

lemma is_equivalent.is_o (h : u ~[l] v) : is_o (u - v) v l := h

lemma is_equivalent.is_O (h : u ~[l] v) : is_O u v l :=
(is_O.congr_of_sub h.is_O.symm).mp (is_O_refl _ _)

lemma is_equivalent.is_O_symm (h : u ~[l] v) : is_O v u l :=
begin
  convert h.is_o.right_is_O_add,
  ext,
  simp
end

@[refl] lemma is_equivalent.refl : u ~[l] u :=
begin
  rw [is_equivalent, sub_self],
  exact is_o_zero _ _
end

@[symm] lemma is_equivalent.symm (h : u ~[l] v) : v ~[l] u :=
(h.is_o.trans_is_O h.is_O_symm).symm

@[trans] lemma is_equivalent.trans (huv : u ~[l] v) (hvw : v ~[l] w) : u ~[l] w :=
(huv.is_o.trans_is_O hvw.is_O).triangle hvw.is_o

lemma is_equivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 :=
begin
  rw [is_equivalent, sub_zero],
  exact is_o_zero_right_iff
end

lemma is_equivalent_const_iff_tendsto {c : β} (h : c ≠ 0) : u ~[l] const _ c ↔ tendsto u l (𝓝 c) :=
begin
  rw [is_equivalent, is_o_const_iff h],
  split; intro h;
  [ { have := h.sub tendsto_const_nhds, rw zero_sub (-c) at this },
    { have := h.sub tendsto_const_nhds, rw ← sub_self c} ];
  convert this; try { ext }; simp
end

lemma is_equivalent.tendsto_const {c : β} (hu : u ~[l] const _ c) : tendsto u l (𝓝 c) :=
begin
  rcases (em $ c = 0) with ⟨rfl, h⟩,
  { exact (tendsto_congr' $ is_equivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds },
  { exact (is_equivalent_const_iff_tendsto h).mp hu }
end

lemma is_equivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hu : tendsto u l (𝓝 c)) :
  tendsto v l (𝓝 c) :=
begin
  by_cases h : c = 0,
  { rw [h, ← is_o_one_iff ℝ] at *,
    convert (huv.symm.is_o.trans hu).add hu,
    simp },
  { rw ← is_equivalent_const_iff_tendsto h at hu ⊢,
    exact huv.symm.trans hu }
end

lemma is_equivalent.tendsto_nhds_iff {c : β} (huv : u ~[l] v) :
  tendsto u l (𝓝 c) ↔ tendsto v l (𝓝 c) := ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩

end normed_group

open_locale asymptotics

section normed_field

variables {α β : Type*} [normed_field β] {t u v w : α → β} {l : filter α}

lemma is_equivalent_iff_exists_eq_mul : u ~[l] v ↔
  ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
begin
  rw [is_equivalent, is_o_iff_exists_eq_mul],
  split; rintros ⟨φ, hφ, h⟩; [use (φ + 1), use (φ - 1)]; split,
  { conv in (𝓝 _) { rw ← zero_add (1 : β) },
    exact hφ.add (tendsto_const_nhds) },
  { convert h.add (eventually_eq.refl l v); ext; simp [add_mul] },
  { conv in (𝓝 _) { rw ← sub_self (1 : β) },
    exact hφ.sub (tendsto_const_nhds) },
  { convert h.sub (eventually_eq.refl l v); ext; simp [sub_mul] }
end

lemma is_equivalent.exists_eq_mul (huv : u ~[l] v) :
  ∃ (φ : α → β) (hφ : tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
is_equivalent_iff_exists_eq_mul.mp huv

lemma is_equivalent_of_tendsto_one (hz : ∀ᶠ x in l, v x = 0 → u x = 0)
  (huv : tendsto (u/v) l (𝓝 1)) : u ~[l] v :=
begin
  rw is_equivalent_iff_exists_eq_mul,
  refine ⟨u/v, huv, hz.mono $ λ x hz', (div_mul_cancel_of_imp hz').symm⟩,
end

lemma is_equivalent_of_tendsto_one' (hz : ∀ x, v x = 0 → u x = 0) (huv : tendsto (u/v) l (𝓝 1)) :
  u ~[l] v :=
is_equivalent_of_tendsto_one (eventually_of_forall hz) huv

lemma is_equivalent_iff_tendsto_one (hz : ∀ᶠ x in l, v x ≠ 0) :
  u ~[l] v ↔ tendsto (u/v) l (𝓝 1) :=
begin
  split,
  { intro hequiv,
    have := hequiv.is_o.tendsto_0,
    simp only [pi.sub_apply, sub_div] at this,
    have key : tendsto (λ x, v x / v x) l (𝓝 1),
    { exact (tendsto_congr' $ hz.mono $ λ x hnz, @div_self _ _ (v x) hnz).mpr tendsto_const_nhds },
    convert this.add key,
    { ext, simp },
    { norm_num } },
  { exact is_equivalent_of_tendsto_one (hz.mono $ λ x hnvz hz, (hnvz hz).elim) }
end

end normed_field

section smul

lemma is_equivalent.smul {α E 𝕜 : Type*} [normed_field 𝕜] [normed_group E]
  [normed_space 𝕜 E] {a b : α → 𝕜} {u v : α → E} {l : filter α} (hab : a ~[l] b) (huv : u ~[l] v) :
  (λ x, a x • u x) ~[l] (λ x, b x • v x) :=
begin
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩,
  have : (λ (x : α), a x • u x) - (λ (x : α), b x • v x) =ᶠ[l] λ x, b x • ((φ x • u x) - v x),
  { convert (habφ.comp₂ (•) $ eventually_eq.refl _ u).sub (eventually_eq.refl _ (λ x, b x • v x)),
    ext,
    rw [pi.mul_apply, mul_comm, mul_smul, ← smul_sub] },
  refine (is_o_congr this.symm $ eventually_eq.rfl).mp ((is_O_refl b l).smul_is_o _),

  rcases huv.is_O.exists_pos with ⟨C, hC, hCuv⟩,
  rw is_equivalent at *,
  rw is_o_iff at *,
  rw is_O_with at hCuv,
  simp only [metric.tendsto_nhds, dist_eq_norm] at hφ,
  intros c hc,
  specialize hφ ((c/2)/C) (div_pos (by linarith) hC),
  specialize huv (show 0 < c/2, by linarith),
  refine hφ.mp (huv.mp $ hCuv.mono $ λ x hCuvx huvx hφx, _),

  have key :=
    calc ∥φ x - 1∥ * ∥u x∥
            ≤ (c/2) / C * ∥u x∥ : mul_le_mul_of_nonneg_right hφx.le (norm_nonneg $ u x)
        ... ≤ (c/2) / C * (C*∥v x∥) : mul_le_mul_of_nonneg_left hCuvx (div_pos (by linarith) hC).le
        ... = c/2 * ∥v x∥ : by {field_simp [hC.ne.symm], ring},

  calc ∥((λ (x : α), φ x • u x) - v) x∥
          = ∥(φ x - 1) • u x + (u x - v x)∥ : by simp [sub_smul, sub_add]
      ... ≤ ∥(φ x - 1) • u x∥ + ∥u x - v x∥ : norm_add_le _ _
      ... = ∥φ x - 1∥ * ∥u x∥ + ∥u x - v x∥ : by rw norm_smul
      ... ≤ c / 2 * ∥v x∥ + ∥u x - v x∥ : add_le_add_right key _
      ... ≤ c / 2 * ∥v x∥ + c / 2 * ∥v x∥ : add_le_add_left huvx _
      ... = c * ∥v x∥ : by ring,
end

end smul

section mul_inv

variables {α β : Type*} [normed_field β] {t u v w : α → β} {l : filter α}

lemma is_equivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : t * v ~[l] u * w :=
htu.smul hvw

lemma is_equivalent.inv (huv : u ~[l] v) : (λ x, (u x)⁻¹) ~[l] (λ x, (v x)⁻¹) :=
begin
  rw is_equivalent_iff_exists_eq_mul at *,
  rcases huv with ⟨φ, hφ, h⟩,
  rw ← inv_one,
  refine ⟨λ x, (φ x)⁻¹, tendsto.inv' hφ (by norm_num) , _⟩,
  convert h.inv,
  ext,
  simp [mul_inv']
end

lemma is_equivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) :
  (λ x, t x / v x) ~[l] (λ x, u x / w x) :=
by simpa only [div_eq_mul_inv] using htu.mul hvw.inv

end mul_inv

section normed_linear_ordered_field

variables {α β : Type*} [normed_linear_ordered_field β] {u v : α → β} {l : filter α}

lemma is_equivalent.tendsto_at_top [order_topology β] (huv : u ~[l] v) (hu : tendsto u l at_top) :
  tendsto v l at_top :=
let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul in
tendsto.congr' h.symm ((mul_comm u φ) ▸ (hu.at_top_mul zero_lt_one hφ))

lemma is_equivalent.tendsto_at_top_iff [order_topology β] (huv : u ~[l] v) :
  tendsto u l at_top ↔ tendsto v l at_top := ⟨huv.tendsto_at_top, huv.symm.tendsto_at_top⟩

end normed_linear_ordered_field

end asymptotics
