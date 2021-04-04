/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import data.real.ennreal
import topology.metric_space.basic
import linear_algebra.affine_space.ordered
import analysis.normed_space.add_torsor
import analysis.specific_limits
import analysis.asymptotics

/-!
# Sub/sup-additive functions on boxes

Let `s` be a set in `ι → ℝ`. A subbox of `s` is a product of closed intervals which is included
in `s`.

A function `f : (ι → ℝ) → (ι → ℝ) → M` is called
`box_subadditive_on`/`box_additive_on`/`box_supadditive_on` a set `s` if for any `l u : ι → ℝ`, `l ≤
u`, `Icc l u ⊆ s` and any hyperplane `x i = c`, `l i ≤ c ≤ u i`, the sum of the values of `f` on the
two subboxes `[l, u] ∩ {x | x i ≤ c}` and `[l, u] ∩ {x | c ≤ x i}` is greater than or
equal/equal/less than or equal to its value on `[l, u]`.

The main result of this file is theorem `box_subadditive_on.eq_zero_of_forall_is_o_prod`. It says
that `f l u = 0` provided that `f` is `box_subadditive_on` the interval `[l, u]`, `l ≤ u`, and
for any `p ∈ [l, u]` we have `f l' u' = o(volume [l', u'])` as both `l'` tends to `p` along
`[l, p]`, `u'` tends to `p` along `[p, u]`, and the subbox `[l', u']` is homothetic to `[l, u]`.
-/

variables {ι α β M : Type*}

open set (univ pi Icc Ioi) function finset (hiding univ pi) filter
open_locale big_operators topological_space nnreal filter

/-!
### Definitions and basic properties

In this section we define `box_subadditive_on`, `box_additive_on`, and `box_supadditive_on`, and
prove some basic properties.
-/

/-- A function `f : (ι → α) → (ι → α) → M` is called `box_subadditive_on` a set `s : set (ι → α)`
if for any rectangular box `[l, u] ⊆ s` and a hyperplane `x i = c`, `l i ≤ c ≤ u i`,
we have `f' I ≤ f' (I ∩ {x | x i ≤ c}) + f' (I ∩ {x | c ≤ x i})`, where `I = [l, u]`, and
`f' [a, b]` means `f a b`. -/
def box_subadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
∀ ⦃l u⦄ (hsub : Icc l u ⊆ s) ⦃m : ι → α⦄ (hm : m ∈ Icc l u) i,
  f l u ≤ f l (update u i (m i)) + f (update l i (m i)) u

/-- A function `f : (ι → α) → (ι → α) → M` is called `box_additive_on` a set `s : set (ι → α)`
if for any rectangular box `[l, u] ⊆ s` and a hyperplane `x i = c`, `l i ≤ c ≤ u i`,
we have `f' (I ∩ {x | x i ≤ c}) + f' (I ∩ {x | c ≤ x i}) = f' I`, where `I = [l, u]`, and
`f' [a, b]` means `f a b`. -/
def box_additive_on [decidable_eq ι] [preorder α] [has_add M] (f : (ι → α) → (ι → α) → M)
  (s : set (ι → α)) :=
∀ ⦃l u⦄ (hsub : Icc l u ⊆ s) ⦃m : ι → α⦄ (hm : m ∈ Icc l u) i,
  f l (update u i (m i)) + f (update l i (m i)) u = f l u

/-- A function `f : (ι → α) → (ι → α) → M` is called `box_supadditive_on` a set `s : set (ι → α)`
if for any rectangular box `[l, u] ⊆ s` and a hyperplane `x i = c`, `l i ≤ c ≤ u i`,
we have `f' (I ∩ {x | x i ≤ c}) + f' (I ∩ {x | c ≤ x i}) ≤ f' I`, where `I = [l, u]`, and
`f' [a, b]` means `f a b`. -/
def box_supadditive_on [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M]
  (f : (ι → α) → (ι → α) → M) (s : set (ι → α)) :=
∀ ⦃l u⦄ (hsub : Icc l u ⊆ s) ⦃m : ι → α⦄ (hm : m ∈ Icc l u) i,
  f l (update u i (m i)) + f (update l i (m i)) u ≤ f l u

namespace box_subadditive_on

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}
  {f : (ι → α) → (ι → α) → M} {l m u : ι → α}

protected lemma mono (h : box_subadditive_on f s) {t} (ht : t ⊆ s) : box_subadditive_on f t :=
λ l u hsub, h (set.subset.trans hsub ht)

lemma le_sum_finset_subboxes (h : box_subadditive_on f s) (hsub : Icc l u ⊆ s)
  (hm : m ∈ Icc l u) (t : finset ι) :
  f l u ≤ ∑ t' in t.powerset, f (t'.piecewise m l) ((t \ t').piecewise m u) :=
begin
  induction t using finset.induction_on with j t hj iht, { simp },
  simp only [sum_powerset_insert hj, piecewise_insert, ← sum_add_distrib],
  refine iht.trans (sum_le_sum $ λ t' ht', _),
  rw [mem_powerset] at ht',
  rw [insert_sdiff_of_not_mem _ (mt (@ht' _) hj), piecewise_insert,
    insert_sdiff_insert, sdiff_insert_of_not_mem hj],
  refine h (set.subset.trans (set.Icc_subset_Icc _ _) hsub) ⟨_, _⟩ _;
    apply_rules [le_piecewise_of_le_of_le, piecewise_le_of_le_of_le, hm.1, hm.2, hm.1.trans hm.2];
    refl'
end

variables [fintype ι]

/-- Take a rectangular box `[lo, hi]` in `ι → α` and a point `mid ∈ [lo, hi]`. The hyperplanes `x i
= mid i` split the box `[lo, hi]` into `2^n` subboxes, where `n = card ι`.  If `f` is subadditive on
subboxes, then its value on `[lo, hi]` is less than or equal to the sum of its values on these `2^n`
subboxes. -/
lemma le_sum_subboxes (h : box_subadditive_on f s) (hsub : Icc l u ⊆ s) {m} (hm : m ∈ Icc l u) :
  f l u ≤ ∑ t : finset ι, f (t.piecewise m l) (t.piecewise u m) :=
begin
  convert h.le_sum_finset_subboxes hsub hm finset.univ,
  ext t,
  rw [← compl_eq_univ_sdiff, piecewise_compl]
end
/-
 TODO: why does `by simpa only [← compl_eq_univ_sdiff, piecewise_compl]
    using h.le_sum_finset_subboxes hsub hm finset.univ`
 times out?
-/

end box_subadditive_on

namespace box_additive_on

variables {G : Type*} [decidable_eq ι] [preorder α] {s : set (ι → α)}

protected lemma congr [has_add G] {f g : (ι → α) → (ι → α) → G}
  (hf : box_additive_on f s) (hfg : ∀ ⦃l u⦄, l ≤ u → Icc l u ⊆ s → f l u = g l u) :
  box_additive_on g s :=
begin
  refine λ l u hsub m hm i, _,
  have hle : l ≤ u := hm.1.trans hm.2,
  rw [← hfg (hm.1.trans hm.2), ← hfg, ← hfg, hf hsub hm];
    apply_rules [le_update_iff.2, update_le_iff.2, hsub, trans (set.Icc_subset_Icc _ _) hsub,
      and.intro, hm.1, hm.2, hle, le_refl l, le_refl u]; intros; apply_rules [le_refl, hle]
end

protected lemma mono [has_add G] {f : (ι → α) → (ι → α) → G}
  (h : box_additive_on f s) {t} (ht : t ⊆ s) : box_additive_on f t :=
λ l u hsub, h (set.subset.trans hsub ht)

lemma abs_of_nonneg [linear_ordered_add_comm_group G] {f : (ι → α) → (ι → α) → G}
  (h : box_additive_on f s) (h₀ : ∀ {l u}, l ≤ u → Icc l u ⊆ s → 0 ≤ f l u) :
  box_additive_on (λ x y, abs (f x y)) s :=
h.congr $ λ l u hle hsub, (abs_of_nonneg $ h₀ hle hsub).symm

lemma eq_zero_of_eq [add_left_cancel_monoid M] {f : (ι → α) → (ι → α) → M}
  (h : box_additive_on f s) {l u i} (hle : l ≤ u) (hsub : Icc l u ⊆ s) (hi : l i = u i) :
  f l u = 0 :=
begin
  have := h hsub (set.left_mem_Icc.2 hle) i,
  rwa [update_eq_self, hi, update_eq_self, add_eq_left_iff] at this
end

protected lemma add [add_comm_semigroup M] {f g : (ι → α) → (ι → α) → M}
  (hf : box_additive_on f s) (hg : box_additive_on g s) :
  box_additive_on (f + g) s :=
λ l u h m hm i, by simp [hf h hm i, hg h hm i, add_add_add_comm _ (g _ _)]

protected lemma neg [add_comm_group G] {f : (ι → α) → (ι → α) → G} (hf : box_additive_on f s) :
  box_additive_on (-f) s :=
λ l u h m hm i, by simp [← hf h hm i, add_comm]

protected lemma sub [add_comm_group G] {f g : (ι → α) → (ι → α) → G}
  (hf : box_additive_on f s) (hg : box_additive_on g s) :
  box_additive_on (f - g) s :=
by simp only [sub_eq_add_neg, hf.add hg.neg]

protected lemma prod [fintype ι] {R} [comm_semiring R] (f : α → α → R)
  (hf : ∀ ⦃x y z⦄, x ≤ y → y ≤ z → f x y + f y z = f x z) :
  box_additive_on (λ x y, ∏ i : ι, f (x i) (y i)) s :=
begin
  intros l u h m hm i,
  have := function.apply_update (λ j, f (l j)) u i (m i),
  have := function.apply_update (λ j y, f y (u j)) l i (m i),
  simp only at *,
  simp only [*, prod_update_of_mem, mem_univ, ← add_mul],
  rw [← prod_mul_prod_compl {i}, prod_singleton, compl_eq_univ_sdiff, hf (hm.1 i) (hm.2 i)]
end

protected lemma box_subadditive_on [ordered_add_comm_monoid M] {f : (ι → α) → (ι → α) → M}
  (hf : box_additive_on f s) : box_subadditive_on f s :=
λ l u h m hm i, (hf h hm i).ge

protected lemma box_supadditive_on [ordered_add_comm_monoid M] {f : (ι → α) → (ι → α) → M}
  (hf : box_additive_on f s) : box_supadditive_on f s :=
λ l u h m hm i, (hf h hm i).le

lemma norm_subadditive_on {E : Type*} [normed_group E] {f : (ι → α) → (ι → α) → E}
  (hf : box_additive_on f s) : box_subadditive_on (λ x y, ∥f x y∥) s :=
λ l u h m hm i, by simp only [← hf h hm i, norm_add_le]

end box_additive_on

namespace box_supadditive_on

variables [decidable_eq ι] [preorder α] [ordered_add_comm_monoid M] {s : set (ι → α)}
  {l m u : ι → α} {f : (ι → α) → (ι → α) → M}

protected lemma order_dual (hf : box_supadditive_on f s) :
  @box_subadditive_on ι α (order_dual M) _ _ _ f s :=
hf

protected lemma mono (h : box_supadditive_on f s) {t} (ht : t ⊆ s) : box_supadditive_on f t :=
λ l u hsub, h (set.subset.trans hsub ht)

lemma sum_finset_subboxes_le (h : box_supadditive_on f s) (hsub : Icc l u ⊆ s) (hm : m ∈ Icc l u)
  (t : finset ι) :
  ∑ t' in t.powerset, f (t'.piecewise m l) ((t \ t').piecewise m u) ≤ f l u :=
h.order_dual.le_sum_finset_subboxes hsub hm t

variables [fintype ι]

/-- Take a rectangular box `[lo, hi]` in `ι → α` and a point `mid ∈ [lo, hi]`. The hyperplanes `x i
= mid i` split the box `[lo, hi]` into `2^n` subboxes, where `n = card ι`.  If `f` is supadditive on
subboxes, then its value on `[lo, hi]` is greater than or equal to the sum of its values on these
`2^n` subboxes. -/
lemma sum_subboxes_le (h : box_supadditive_on f s) (hsub : Icc l u ⊆ s) (hm : m ∈ Icc l u) :
  ∑ t : finset ι, f (t.piecewise m l) (t.piecewise u m) ≤ f l u :=
h.order_dual.le_sum_subboxes hsub hm

end box_supadditive_on

section coe

variables {N : Type*} [decidable_eq ι] [preorder α] {s : set (ι → α)}

lemma box_subsupadditive_coe_helper [add_monoid M] [add_monoid N] {c : M → N} (rM : M → M → Prop)
  (rN : N → N → Prop) (hr : ∀ x y, rN (c x) (c y) ↔ rM x y)
  (hadd : ∀ x y, c (x + y) = c x + c y) {f : (ι → α) → (ι → α) → M} :
  (∀ ⦃l u : ι → α⦄ (h : Icc l u ⊆ s) ⦃m : ι → α⦄ (hm : m ∈ Icc l u) i, rN (c $ f l u) $
    (c $ f l (update u i (m i))) + (c $ f (update l i (m i)) u)) ↔
  (∀ ⦃l u : ι → α⦄ (h : Icc l u ⊆ s) ⦃m : ι → α⦄ (hm : m ∈ Icc l u) i, rM (f l u) $
    (f l (update u i (m i))) + (f (update l i (m i)) u)) :=
by simp only [← hadd, hr]

variables {f g : (ι → α) → (ι → α) → ℝ≥0}

@[simp, norm_cast]
lemma box_subadditive_on.coe_ennreal :
  box_subadditive_on (λ x y, (f x y : ennreal)) s ↔ box_subadditive_on f s :=
box_subsupadditive_coe_helper (≤) (≤) (λ _ _, ennreal.coe_le_coe) (λ _ _, ennreal.coe_add)

@[simp, norm_cast]
lemma box_additive_on.coe_ennreal :
  box_additive_on (λ l r, (f l r : ennreal)) s ↔ box_additive_on f s :=
box_subsupadditive_coe_helper (flip (=)) (flip (=)) (λ _ _, ennreal.coe_eq_coe)
  (λ _ _, ennreal.coe_add)

@[simp, norm_cast]
lemma box_supadditive_on.coe_ennreal :
  box_supadditive_on (λ l r, (f l r : ennreal)) s ↔ box_supadditive_on f s :=
box_subsupadditive_coe_helper (≥) (≥) (λ _ _, ennreal.coe_le_coe) (λ _ _, ennreal.coe_add)

@[simp, norm_cast]
lemma box_subadditive_on.coe_nnreal :
  box_subadditive_on (λ x y, (f x y : ℝ)) s ↔ box_subadditive_on f s :=
box_subsupadditive_coe_helper (≤) (≤) (λ _ _, nnreal.coe_le_coe) nnreal.coe_add

@[simp, norm_cast]
lemma box_additive_on.coe_nnreal :
  box_additive_on (λ l r, (f l r : ℝ)) s ↔ box_additive_on f s :=
box_subsupadditive_coe_helper (flip (=)) (flip (=)) (λ _ _, nnreal.coe_eq) nnreal.coe_add

@[simp, norm_cast]
lemma box_supadditive_on.coe_nnreal :
  box_supadditive_on (λ l r, (f l r : ℝ)) s ↔ box_supadditive_on f s :=
box_subsupadditive_coe_helper (≥) (≥) (λ _ _, nnreal.coe_le_coe) nnreal.coe_add

end coe

/-!
### Examples of `box_additive`, `box_subadditive, and `box_supadditive` functions
-/

section

lemma box_additive_on_prod_sub [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_additive_on (λ l r, ∏ i, (r i - l i)) s :=
box_additive_on.prod (λ x y : ℝ, y - x) $ λ x y z _ _, sub_add_sub_cancel' _ _ _

lemma box_additive_on_prod_dist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_additive_on (λ l r, ∏ i, dist (l i) (r i)) s :=
by simpa only [real.dist_eq, abs_prod, abs_sub]
  using (box_additive_on_prod_sub s).abs_of_nonneg
    (λ l u h _, prod_nonneg (λ i _, sub_nonneg.2 (h _)))

lemma box_additive_on_prod_nndist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_additive_on (λ l r, ∏ i, nndist (l i) (r i)) s :=
by simpa only [← box_additive_on.coe_nnreal, nnreal.coe_prod, coe_nndist]
  using box_additive_on_prod_dist s

lemma box_additive_on_prod_edist [decidable_eq ι] [fintype ι] (s : set (ι → ℝ)) :
  box_additive_on (λ l r, ∏ i, edist (l i) (r i)) s :=
by simpa only [edist_nndist, ← ennreal.coe_finset_prod, box_additive_on.coe_ennreal]
  using box_additive_on_prod_nndist s

end

namespace box_subadditive_on

section preorder

variables [decidable_eq ι] [fintype ι] [preorder α]
  {s : set (ι → α)} {f g : (ι → α) → (ι → α) → ennreal} {l m u : ι → α}

lemma exists_subbox_mul_lt_of_mul_lt (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (hsub : Icc l u ⊆ s) (hm : m ∈ Icc l u) {c : ennreal} (hlt : c * g l u < f l u) :
  ∃ t : finset ι,
    c * g (t.piecewise m l) (t.piecewise u m) < f (t.piecewise m l) (t.piecewise u m) :=
begin
  contrapose! hlt,
  calc f l u ≤ ∑ t : finset ι, f (t.piecewise m l) (t.piecewise u m) : hf.le_sum_subboxes hsub hm
  ... ≤ ∑ t : finset ι, c * g (t.piecewise m l) (t.piecewise u m) : sum_le_sum (λ t _, hlt t)
  ... = c * ∑ t : finset ι, g (t.piecewise m l) (t.piecewise u m) : mul_sum.symm
  ... ≤ c * g l u : canonically_ordered_semiring.mul_le_mul_left' (hg.sum_subboxes_le hsub hm) c
end

end preorder

variables [decidable_eq ι] [fintype ι]

noncomputable theory

variables {s : set (ι → ℝ)} {l u : ι → ℝ}

section ennreal

variables {f g : (ι → ℝ) → (ι → ℝ) → ennreal} {c : ennreal}

/-- An auxiliary type for the proof of `box_subadditive_on.eq_zero_of_forall_eventually_le_mul`. -/
@[nolint has_inhabited_instance]
structure subbox_mul_lt (s : set (ι → ℝ)) (f g : (ι → ℝ) → (ι → ℝ) → ennreal) (c : ennreal) :=
(left right : ι → ℝ)
(le : left ≤ right)
(sub : Icc left right ⊆ s)
(mul_lt : c * g left right < f left right)

lemma subbox_mul_lt.midpoint_mem (I : subbox_mul_lt s f g c) :
  midpoint ℝ I.left I.right ∈ Icc I.left I.right :=
⟨left_le_midpoint.2 I.le, midpoint_le_right.2 I.le⟩

/-- An auxiliary definition for `box_subadditive_on.eq_zero_of_forall_eventually_le_mul`. -/
def next (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subbox_mul_lt s f g c) :
  {I' : subbox_mul_lt s f g c // I.left ≤ I'.left ∧ I'.right ≤ I.right ∧
    ∀ i, I'.right i - I'.left i = (I.right i - I.left i) / 2} :=
begin
  obtain ⟨t, ht⟩ := classical.indefinite_description _
    (hf.exists_subbox_mul_lt_of_mul_lt hg I.sub I.midpoint_mem I.mul_lt),
  have hl : I.left ≤ t.piecewise (midpoint ℝ I.left I.right) I.left :=
    t.le_piecewise_of_le_of_le I.midpoint_mem.1 le_rfl,
  have hr : t.piecewise I.right (midpoint ℝ I.left I.right) ≤ I.right :=
    t.piecewise_le_of_le_of_le le_rfl I.midpoint_mem.2,
  refine ⟨⟨_, _, _, set.subset.trans (set.Icc_subset_Icc hl hr) I.sub, ht⟩, hl, hr, λ i, _⟩,
  { exact t.piecewise_le_piecewise I.midpoint_mem.2 I.midpoint_mem.1 },
  { by_cases hi : i ∈ t; simp [hi, div_eq_inv_mul] }
end

/-- An auxiliary definition for `box_subadditive_on.eq_zero_of_forall_eventually_le_mul`:
a decreasing sequence of subboxes `[l n, u n]` such that `c * g (l n) (u n) < f (l u) (u n)`. -/
def seq (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I₀ : subbox_mul_lt s f g c)
  (n : ℕ) : subbox_mul_lt s f g c :=
(λ I, hf.next hg I)^[n] I₀

/-- An auxiliary definition for `box_subadditive_on.eq_zero_of_forall_eventually_le_mul`:
the limit point of the sequence `box_subadditive_on.seq hf hg I hI`. -/
def fix (hf : box_subadditive_on f s) (hg : box_supadditive_on g s) (I : subbox_mul_lt s f g c) :
  ι → ℝ :=
⨆ n, (seq hf hg I n).left

@[simp] lemma seq_zero (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  seq hf hg I 0 = I := rfl

@[simp] lemma seq_succ (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) (n : ℕ) :
  seq hf hg I (n + 1) = next hf hg (seq hf hg I n) :=
iterate_succ_apply' _ _ _

@[simp] lemma seq_right_sub_left_apply (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) (n : ℕ) (i : ι) :
  (seq hf hg I n).right i - (seq hf hg I n).left i = (I.right i - I.left i) / 2 ^ n :=
begin
  induction n with n ihn, { simp },
  rw [seq_succ, (next hf hg _).coe_prop.2.2, ihn, pow_succ', div_div_eq_div_mul]
end

@[simp] lemma seq_right_sub_left (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) (n : ℕ) :
  (seq hf hg I n).right - (seq hf hg I n).left = ((1 / 2) ^ n : ℝ) • (I.right - I.left) :=
funext $ λ i, (seq_right_sub_left_apply hf hg I n i).trans $
  by simp only [div_eq_inv_mul, pi.smul_apply, pi.sub_apply, smul_eq_mul, mul_one, inv_pow']

lemma dist_seq_left_right (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) (n : ℕ) :
  dist (seq hf hg I n).left (seq hf hg I n).right = dist I.left I.right / 2 ^ n :=
by rw [dist_comm, dist_eq_norm, seq_right_sub_left, norm_smul, ← dist_eq_norm, dist_comm, mul_comm,
  one_div, inv_pow', normed_field.norm_inv, normed_field.norm_pow, real.norm_eq_abs,
  abs_of_pos (@zero_lt_two ℝ _ _), div_eq_mul_inv]

lemma seq_left_mono (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  monotone (λ n, (seq hf hg I n).left) :=
monotone_of_monotone_nat $ λ n, by simp only [seq_succ, (next _ _ _).coe_prop.1]

lemma seq_right_mono (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  ∀ ⦃m n⦄, m ≤ n → (seq hf hg I n).right ≤ (seq hf hg I m).right :=
begin
  refine @monotone_of_monotone_nat (order_dual (ι → ℝ)) _ _ (λ n, _),
  rw seq_succ,
  exact (next _ _ _).coe_prop.2.1
end

lemma tendsto_dist_seq_left_right (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  tendsto (λ n, dist (seq hf hg I n).left (seq hf hg I n).right) at_top (𝓝 0) :=
begin
  simp only [dist_seq_left_right],
  exact tendsto_const_nhds.div_at_top (tendsto_pow_at_top_at_top_of_one_lt one_lt_two)
end

lemma fix_mem_Inter_seq (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c):
  fix hf hg I ∈ ⋂ n, Icc (seq hf hg I n).left (seq hf hg I n).right :=
csupr_mem_Inter_Icc_of_mono_incr_of_mono_decr (seq_left_mono hf hg I) (seq_right_mono hf hg I) $
  λ n, (seq hf hg I n).le

lemma fix_mem_seq (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) (n : ℕ) :
  fix hf hg I ∈ Icc (seq hf hg I n).left (seq hf hg I n).right :=
have _ := set.mem_Inter.1 (fix_mem_Inter_seq hf hg I) n, this

lemma fix_mem (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  fix hf hg I ∈ Icc I.left I.right :=
fix_mem_seq hf hg I 0

lemma fix_mem_set (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  fix hf hg I ∈ s :=
I.sub $ fix_mem hf hg I

lemma tendsto_left_nhds_fix (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  tendsto (λ n, (seq hf hg I n).left) at_top (𝓝 (fix hf hg I)) :=
begin
  refine (tendsto_iff_dist_tendsto_zero.2 $
    squeeze_zero (λ _, dist_nonneg) (λ n, _) (tendsto_dist_seq_left_right hf hg I)),
  refine (dist_pi_le_iff dist_nonneg).2 (λ i, le_trans _ (dist_le_pi_dist _ _ i)),
  exact real.dist_left_le_of_mem_interval (set.Icc_subset_interval $
    ⟨(fix_mem_seq hf hg I _).1 _, (fix_mem_seq hf hg I _).2 _⟩)
end

lemma tendsto_left_nhds_within_fix (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  tendsto (λ n, (seq hf hg I n).left) at_top (𝓝[Icc I.left (fix hf hg I)] (fix hf hg I)) :=
tendsto_inf.2 ⟨tendsto_left_nhds_fix hf hg I, tendsto_principal.2 $ eventually_of_forall $
  λ n, ⟨seq_left_mono hf hg I (zero_le n), (fix_mem_seq hf hg I n).1⟩⟩

lemma tendsto_right_nhds_fix (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  tendsto (λ n, (seq hf hg I n).right) at_top (𝓝 (fix hf hg I)) :=
(tendsto_left_nhds_fix hf hg I).congr_dist (tendsto_dist_seq_left_right hf hg I)

lemma tendsto_right_nhds_within_fix (hf : box_subadditive_on f s) (hg : box_supadditive_on g s)
  (I : subbox_mul_lt s f g c) :
  tendsto (λ n, (seq hf hg I n).right) at_top (𝓝[Icc (fix hf hg I) I.right] (fix hf hg I)) :=
tendsto_inf.2 ⟨tendsto_right_nhds_fix hf hg I, tendsto_principal.2 $ eventually_of_forall $
  λ n, ⟨(fix_mem_seq hf hg I n).2, seq_right_mono hf hg I (zero_le n)⟩⟩

lemma le_mul_of_forall_eventually_le_mul (hle : l ≤ u)
  (hf : box_subadditive_on f (Icc l u)) (hg : box_supadditive_on g (Icc l u))
  (Hc : ∀ (b ∈ Icc l u),
    ∀ᶠ (p : ((ι → ℝ) × (ι → ℝ)) × ℝ) in 𝓝[(Icc l b)] b ×ᶠ 𝓝[Icc b u] b ×ᶠ 𝓝[Ioi 0] (0:ℝ),
    (p.1.2 - p.1.1 = p.2 • (u - l)) → f (p.1.1) p.1.2 ≤ c * g p.1.1 p.1.2) :
  f l u ≤ c * g l u :=
begin
  contrapose! Hc,
  set I : subbox_mul_lt (Icc l u) f g c := ⟨l, u, hle, refl _, Hc⟩,
  refine ⟨_, fix_mem hf hg I, λ H, _⟩,
  have : tendsto (λ n : ℕ, (1 / 2 : ℝ) ^ n) at_top (𝓝[Ioi 0] 0),
    from tendsto_pow_at_top_nhds_within_0_of_lt_1 one_half_pos one_half_lt_one,
  obtain ⟨n, hn⟩ := ((((tendsto_left_nhds_within_fix hf hg I).prod_mk
    (tendsto_right_nhds_within_fix hf hg I)).prod_mk this).eventually H).exists,
  exact (hn (seq_right_sub_left hf hg I n)).not_lt (seq hf hg I n).mul_lt
end

/-- Let `Icc l u` (a.k.a. `[l, u]`) be a non-trivial interval in a finite-dimensional space
`ι → ℝ`. Suppose that `f` is an `ennreal`-valued function such that `box_subadditive_on f [l, u]`
and for any `p ∈ [l, u]` we have `f l' u' = o(volume [l', u'])` as `l'` tends to `p` along `[l, p]`,
`u'` tends to `p` along `[p, u]`, and the subbox `[l', u']` is homothetic to `[l, u]`.
Then `f l u = 0`. -/
lemma eq_zero_of_forall_eventually_le_mul (hle : l ≤ u) (hf : box_subadditive_on f (Icc l u))
  (hg : box_supadditive_on g (Icc l u)) (h_inf : g l u ≠ ⊤)
  (Hc : ∀ (b ∈ Icc l u) (c : ℝ≥0), 0 < c →
    ∀ᶠ (p : ((ι → ℝ) × (ι → ℝ)) × ℝ) in 𝓝[Icc l b] b ×ᶠ 𝓝[Icc b u] b ×ᶠ 𝓝[Ioi 0] 0,
    (p.1.2 - p.1.1 = p.2 • (u - l)) → f p.1.1 p.1.2 ≤ (c : ℝ≥0) * g p.1.1 p.1.2) :
  f l u = 0 :=
begin
  by_contra h0,
  rcases ennreal.exists_nnreal_pos_mul_lt h_inf h0 with ⟨c, cpos, hc⟩,
  exact hc.not_le (le_mul_of_forall_eventually_le_mul hle hf hg $ λ b hb, Hc b hb c cpos)
end

end ennreal

section normed_group

variables {E F : Type*} [normed_group E] [normed_group F]
  {f : (ι → ℝ) → (ι → ℝ) → E} {g : (ι → ℝ) → (ι → ℝ) → F}

open asymptotics function

lemma eq_zero_of_forall_is_o (hle : l ≤ u) (hf : box_subadditive_on (λ x y, ∥f x y∥) (Icc l u))
  (hg : box_supadditive_on (λ x y, ∥g x y∥) (Icc l u))
  (Hc : ∀ (b ∈ Icc l u), is_o (λ p : _ × ℝ, uncurry f p.1) (λ p, uncurry g p.1)
    ((𝓝[Icc l b] b ×ᶠ 𝓝[Icc b u] b ×ᶠ 𝓝[Ioi 0] 0) ⊓ 𝓟 {p | p.1.2 - p.1.1 = p.2 • (u - l)}))
  : f l u = 0 :=
begin
  simp only [← coe_nnnorm, coe_nnreal, ← coe_ennreal] at hf,
  simp only [← coe_nnnorm, box_supadditive_on.coe_nnreal,
    ← box_supadditive_on.coe_ennreal] at hg,
  rw [← nnnorm_eq_zero, ← ennreal.coe_eq_zero],
  refine eq_zero_of_forall_eventually_le_mul hle hf hg ennreal.coe_ne_top _,
  intros b hb c hc,
  simpa [← coe_nnnorm, uncurry, ← nnreal.coe_mul, ← ennreal.coe_mul, eventually_inf_principal]
    using (Hc b hb).def hc
end

/-- Let `Icc l u` (a.k.a. `[l, u]`) be a non-trivial box in a finite-dimensional space
`ι → ℝ`. Suppose that `box_subadditive_on f [l, u]` and for any `p ∈ [l, u]` we have
`f l' u' = o(volume [l', u'])` as `l'` tends to `p` along `[l, p]`, `u'` tends to `p`
along `[p, u]`, and the subbox `[l', u']` is homothetic to `[l, u]`. Then `f l u = 0`. -/
lemma eq_zero_of_forall_is_o_prod (hle : l ≤ u)
  (hf : box_subadditive_on (λ x y, ∥f x y∥) (Icc l u))
  (Hc : ∀ (b ∈ Icc l u), is_o (λ p : _ × ℝ, uncurry f p.1) (λ p, ∏ i, (p.1.2 i - p.1.1 i))
    ((𝓝[Icc l b] b ×ᶠ 𝓝[Icc b u] b ×ᶠ 𝓝[Ioi 0] 0) ⊓ 𝓟 {p | p.1.2 - p.1.1 = p.2 • (u - l)})) :
  f l u = 0 :=
begin
  have : box_supadditive_on (λ l r, ∥∏ (i : ι), dist (l i) (r i)∥) (Icc l u) :=
    ((box_additive_on_prod_dist (Icc l u)).abs_of_nonneg
      (λ _ _ _ _, prod_nonneg $ λ _ _, dist_nonneg)).box_supadditive_on,
  refine eq_zero_of_forall_is_o hle hf this _,
  simpa only [dist_eq_norm', ← normed_field.norm_prod, uncurry, is_o_norm_right]
end

end normed_group

end box_subadditive_on
