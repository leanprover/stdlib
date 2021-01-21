/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.finset.fold
import data.multiset.lattice
import order.order_dual

/-!
# Lattice operations on finsets
-/

variables {α β γ : Type*}

namespace finset
open multiset order_dual

/-! ### sup -/
section sup
variables [semilattice_sup_bot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
def sup (s : finset β) (f : β → α) : α := s.fold (⊔) ⊥ f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma sup_def : s.sup f = (s.1.map f).sup := rfl

@[simp] lemma sup_empty : (∅ : finset β).sup f = ⊥ :=
fold_empty

@[simp] lemma sup_insert [decidable_eq β] {b : β} : (insert b s : finset β).sup f = f b ⊔ s.sup f :=
fold_insert_idem

@[simp] lemma sup_singleton {b : β} : ({b} : finset β).sup f = f b :=
sup_singleton

lemma sup_union [decidable_eq β] : (s₁ ∪ s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
finset.induction_on s₁ (by rw [empty_union, sup_empty, bot_sup_eq]) $ λ a s has ih,
by rw [insert_union, sup_insert, sup_insert, ih, sup_assoc]

theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a∈s₂, f a = g a) : s₁.sup f = s₂.sup g :=
by subst hs; exact finset.fold_congr hfg

@[simp] lemma sup_le_iff {a : α} : s.sup f ≤ a ↔ (∀b ∈ s, f b ≤ a) :=
begin
  apply iff.trans multiset.sup_le,
  simp only [multiset.mem_map, and_imp, exists_imp_distrib],
  exact ⟨λ k b hb, k _ _ hb rfl, λ k a' b hb h, h ▸ k _ hb⟩,
end

lemma sup_const {s : finset β} (h : s.nonempty) (c : α) : s.sup (λ _, c) = c :=
eq_of_forall_ge_iff $ λ b, sup_le_iff.trans h.forall_const

lemma sup_le {a : α} : (∀b ∈ s, f b ≤ a) → s.sup f ≤ a :=
sup_le_iff.2

lemma le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
sup_le_iff.1 (le_refl _) _ hb

lemma sup_mono_fun {g : β → α} (h : ∀b∈s, f b ≤ g b) : s.sup f ≤ s.sup g :=
sup_le (λ b hb, le_trans (h b hb) (le_sup hb))

lemma sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
sup_le $ assume b hb, le_sup (h hb)

@[simp] lemma sup_lt_iff [is_total α (≤)] {a : α} (ha : ⊥ < a) :
  s.sup f < a ↔ (∀b ∈ s, f b < a) :=
by letI := classical.dec_eq β; from
⟨ λh b hb, lt_of_le_of_lt (le_sup hb) h,
  finset.induction_on s (by simp [ha]) (by simp {contextual := tt}) ⟩

lemma comp_sup_eq_sup_comp [semilattice_sup_bot γ] {s : finset β}
  {f : β → α} (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) :
  g (s.sup f) = s.sup (g ∘ f) :=
by letI := classical.dec_eq β; from
finset.induction_on s (by simp [bot]) (by simp [g_sup] {contextual := tt})

lemma comp_sup_eq_sup_comp_of_is_total [is_total α (≤)] {γ : Type} [semilattice_sup_bot γ]
  (g : α → γ) (mono_g : monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
comp_sup_eq_sup_comp g mono_g.map_sup bot

/-- Computating `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
lemma sup_coe {P : α → Prop}
  {Pbot : P ⊥} {Psup : ∀{{x y}}, P x → P y → P (x ⊔ y)}
  (t : finset β) (f : β → {x : α // P x}) :
  (@sup _ _ (subtype.semilattice_sup_bot Pbot Psup) t f : α) = t.sup (λ x, f x) :=
by { classical, rw [comp_sup_eq_sup_comp coe]; intros; refl }

@[simp] lemma sup_to_finset {α β} [decidable_eq β]
  (s : finset α) (f : α → multiset β) :
  (s.sup f).to_finset = s.sup (λ x, (f x).to_finset) :=
comp_sup_eq_sup_comp multiset.to_finset to_finset_union rfl

theorem subset_range_sup_succ (s : finset ℕ) : s ⊆ range (s.sup id).succ :=
λ n hn, mem_range.2 $ nat.lt_succ_of_le $ le_sup hn

theorem exists_nat_subset_range (s : finset ℕ) : ∃n : ℕ, s ⊆ range n :=
⟨_, s.subset_range_sup_succ⟩

lemma sup_subset {α β} [semilattice_sup_bot β] {s t : finset α} (hst : s ⊆ t) (f : α → β) :
  s.sup f ≤ t.sup f :=
by classical;
calc t.sup f = (s ∪ t).sup f : by rw [finset.union_eq_right_iff_subset.mpr hst]
         ... = s.sup f ⊔ t.sup f : by rw finset.sup_union
         ... ≥ s.sup f : le_sup_left

lemma sup_closed_of_sup_closed {s : set α} (t : finset α) (htne : t.nonempty) (h_subset : ↑t ⊆ s)
  (h : ∀⦃a b⦄, a ∈ s → b ∈ s → a ⊔ b ∈ s) : t.sup id ∈ s :=
begin
  classical,
  induction t using finset.induction_on with x t h₀ h₁,
  { exfalso, apply finset.not_nonempty_empty htne, },
  { rw [finset.coe_insert, set.insert_subset] at h_subset,
    cases t.eq_empty_or_nonempty with hte htne,
    { subst hte, simp only [insert_emptyc_eq, id.def, finset.sup_singleton, h_subset], },
    { rw [finset.sup_insert, id.def], exact h h_subset.1 (h₁ htne h_subset.2), }, },
end

end sup

lemma sup_eq_supr [complete_lattice β] (s : finset α) (f : α → β) : s.sup f = (⨆a∈s, f a) :=
le_antisymm
  (finset.sup_le $ assume a ha, le_supr_of_le a $ le_supr _ ha)
  (supr_le $ assume a, supr_le $ assume ha, le_sup ha)

lemma sup_eq_Sup [complete_lattice α] (s : finset α) : s.sup id = Sup s :=
by simp [Sup_eq_supr, sup_eq_supr]

/-! ### inf -/
section inf
variables [semilattice_inf_top α]

/-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/
def inf (s : finset β) (f : β → α) : α := s.fold (⊓) ⊤ f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma inf_def : s.inf f = (s.1.map f).inf := rfl

@[simp] lemma inf_empty : (∅ : finset β).inf f = ⊤ :=
fold_empty

lemma le_inf_iff {a : α} : a ≤ s.inf f ↔ ∀b ∈ s, a ≤ f b :=
@sup_le_iff (order_dual α) _ _ _ _ _

@[simp] lemma inf_insert [decidable_eq β] {b : β} : (insert b s : finset β).inf f = f b ⊓ s.inf f :=
fold_insert_idem

@[simp] lemma inf_singleton {b : β} : ({b} : finset β).inf f = f b :=
inf_singleton

lemma inf_union [decidable_eq β] : (s₁ ∪ s₂).inf f = s₁.inf f ⊓ s₂.inf f :=
@sup_union (order_dual α) _ _ _ _ _ _

theorem inf_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a∈s₂, f a = g a) : s₁.inf f = s₂.inf g :=
by subst hs; exact finset.fold_congr hfg

lemma inf_le {b : β} (hb : b ∈ s) : s.inf f ≤ f b :=
le_inf_iff.1 (le_refl _) _ hb

lemma le_inf {a : α} : (∀b ∈ s, a ≤ f b) → a ≤ s.inf f :=
le_inf_iff.2

lemma inf_mono_fun {g : β → α} (h : ∀b∈s, f b ≤ g b) : s.inf f ≤ s.inf g :=
le_inf (λ b hb, le_trans (inf_le hb) (h b hb))

lemma inf_mono (h : s₁ ⊆ s₂) : s₂.inf f ≤ s₁.inf f :=
le_inf $ assume b hb, inf_le (h hb)

lemma lt_inf_iff [h : is_total α (≤)] {a : α} (ha : a < ⊤) : a < s.inf f ↔ (∀b ∈ s, a < f b) :=
@sup_lt_iff (order_dual α) _ _ _ _ (@is_total.swap α _ h) _ ha

lemma comp_inf_eq_inf_comp [semilattice_inf_top γ] {s : finset β}
  {f : β → α} (g : α → γ) (g_inf : ∀ x y, g (x ⊓ y) = g x ⊓ g y) (top : g ⊤ = ⊤) :
  g (s.inf f) = s.inf (g ∘ f) :=
@comp_sup_eq_sup_comp (order_dual α) _ (order_dual γ) _ _ _ _ _ g_inf top

lemma comp_inf_eq_inf_comp_of_is_total [h : is_total α (≤)] {γ : Type} [semilattice_inf_top γ]
  (g : α → γ) (mono_g : monotone g) (top : g ⊤ = ⊤) : g (s.inf f) = s.inf (g ∘ f) :=
comp_inf_eq_inf_comp g mono_g.map_inf top

/-- Computating `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/
lemma inf_coe {P : α → Prop}
  {Ptop : P ⊤} {Pinf : ∀{{x y}}, P x → P y → P (x ⊓ y)}
  (t : finset β) (f : β → {x : α // P x}) :
  (@inf _ _ (subtype.semilattice_inf_top Ptop Pinf) t f : α) = t.inf (λ x, f x) :=
by { classical, rw [comp_inf_eq_inf_comp coe]; intros; refl }

end inf

lemma inf_eq_infi [complete_lattice β] (s : finset α) (f : α → β) : s.inf f = (⨅a∈s, f a) :=
@sup_eq_supr _ (order_dual β) _ _ _

lemma inf_eq_Inf [complete_lattice α] (s : finset α) : s.inf id = Inf s :=
by simp [Inf_eq_infi, inf_eq_infi]

/-! ### max and min of finite sets -/
section max_min
variables [linear_order α]

/-- Let `s` be a finset in a linear order. Then `s.max` is the maximum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.max'`. -/
protected def max : finset α → option α :=
fold (option.lift_or_get max) none some

theorem max_eq_sup_with_bot (s : finset α) :
  s.max = @sup (with_bot α) α _ s some := rfl

@[simp] theorem max_empty : (∅ : finset α).max = none := rfl

@[simp] theorem max_insert {a : α} {s : finset α} :
  (insert a s).max = option.lift_or_get max (some a) s.max := fold_insert_idem

@[simp] theorem max_singleton {a : α} : finset.max {a} = some a :=
by { rw [← insert_emptyc_eq], exact max_insert }

theorem max_of_mem {s : finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.max :=
(@le_sup (with_bot α) _ _ _ _ _ h _ rfl).imp $ λ b, Exists.fst

theorem max_of_nonempty {s : finset α} (h : s.nonempty) : ∃ a, a ∈ s.max :=
let ⟨a, ha⟩ := h in max_of_mem ha

theorem max_eq_none {s : finset α} : s.max = none ↔ s = ∅ :=
⟨λ h, s.eq_empty_or_nonempty.elim id
  (λ H, let ⟨a, ha⟩ := max_of_nonempty H in by rw h at ha; cases ha),
  λ h, h.symm ▸ max_empty⟩

theorem mem_of_max {s : finset α} : ∀ {a : α}, a ∈ s.max → a ∈ s :=
finset.induction_on s (λ _ H, by cases H)
  (λ b s _ (ih : ∀ {a}, a ∈ s.max → a ∈ s) a (h : a ∈ (insert b s).max),
  begin
    by_cases p : b = a,
    { induction p, exact mem_insert_self b s },
    { cases option.lift_or_get_choice max_choice (some b) s.max with q q;
      rw [max_insert, q] at h,
      { cases h, cases p rfl },
      { exact mem_insert_of_mem (ih h) } }
  end)

theorem le_max_of_mem {s : finset α} {a b : α} (h₁ : a ∈ s) (h₂ : b ∈ s.max) : a ≤ b :=
by rcases @le_sup (with_bot α) _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩;
   cases h₂.symm.trans hb; assumption

/-- Let `s` be a finset in a linear order. Then `s.min` is the minimum of `s` if `s` is not empty,
and `none` otherwise. It belongs to `option α`. If you want to get an element of `α`, see
`s.min'`. -/
protected def min : finset α → option α :=
fold (option.lift_or_get min) none some

theorem min_eq_inf_with_top (s : finset α) :
  s.min = @inf (with_top α) α _ s some := rfl

@[simp] theorem min_empty : (∅ : finset α).min = none := rfl

@[simp] theorem min_insert {a : α} {s : finset α} :
  (insert a s).min = option.lift_or_get min (some a) s.min :=
fold_insert_idem

@[simp] theorem min_singleton {a : α} : finset.min {a} = some a :=
by { rw ← insert_emptyc_eq, exact min_insert }

theorem min_of_mem {s : finset α} {a : α} (h : a ∈ s) : ∃ b, b ∈ s.min :=
(@inf_le (with_top α) _ _ _ _ _ h _ rfl).imp $ λ b, Exists.fst

theorem min_of_nonempty {s : finset α} (h : s.nonempty) : ∃ a, a ∈ s.min :=
let ⟨a, ha⟩ := h in min_of_mem ha

theorem min_eq_none {s : finset α} : s.min = none ↔ s = ∅ :=
⟨λ h, s.eq_empty_or_nonempty.elim id
  (λ H, let ⟨a, ha⟩ := min_of_nonempty H in by rw h at ha; cases ha),
  λ h, h.symm ▸ min_empty⟩

theorem mem_of_min {s : finset α} : ∀ {a : α}, a ∈ s.min → a ∈ s :=
finset.induction_on s (λ _ H, by cases H) $
  λ b s _ (ih : ∀ {a}, a ∈ s.min → a ∈ s) a (h : a ∈ (insert b s).min),
  begin
    by_cases p : b = a,
    { induction p, exact mem_insert_self b s },
    { cases option.lift_or_get_choice min_choice (some b) s.min with q q;
      rw [min_insert, q] at h,
      { cases h, cases p rfl },
      { exact mem_insert_of_mem (ih h) } }
  end

theorem min_le_of_mem {s : finset α} {a b : α} (h₁ : b ∈ s) (h₂ : a ∈ s.min) : a ≤ b :=
by rcases @inf_le (with_top α) _ _ _ _ _ h₁ _ rfl with ⟨b', hb, ab⟩;
   cases h₂.symm.trans hb; assumption

/-- Given a nonempty finset `s` in a linear order `α `, then `s.min' h` is its minimum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.min`,
taking values in `option α`. -/
def min' (s : finset α) (H : s.nonempty) : α :=
@option.get _ s.min $
  let ⟨k, hk⟩ := H in
  let ⟨b, hb⟩ := min_of_mem hk in by simp at hb; simp [hb]

/-- Given a nonempty finset `s` in a linear order `α `, then `s.max' h` is its maximum, as an
element of `α`, where `h` is a proof of nonemptiness. Without this assumption, use instead `s.max`,
taking values in `option α`. -/
def max' (s : finset α) (H : s.nonempty) : α :=
@option.get _ s.max $
  let ⟨k, hk⟩ := H in
  let ⟨b, hb⟩ := max_of_mem hk in by simp at hb; simp [hb]

variables (s : finset α) (H : s.nonempty)

theorem min'_mem : s.min' H ∈ s := mem_of_min $ by simp [min']

theorem min'_le (x) (H2 : x ∈ s) : s.min' ⟨x, H2⟩ ≤ x := min_le_of_mem H2 $ option.get_mem _

theorem le_min' (x) (H2 : ∀ y ∈ s, x ≤ y) : x ≤ s.min' H := H2 _ $ min'_mem _ _

/-- `{a}.min' _` is `a`. -/
@[simp] lemma min'_singleton (a : α) :
  ({a} : finset α).min' (singleton_nonempty _) = a :=
by simp [min']

theorem max'_mem : s.max' H ∈ s := mem_of_max $ by simp [max']

theorem le_max' (x) (H2 : x ∈ s) : x ≤ s.max' ⟨x, H2⟩ := le_max_of_mem H2 $ option.get_mem _

theorem max'_le (x) (H2 : ∀ y ∈ s, y ≤ x) : s.max' H ≤ x := H2 _ $ max'_mem _ _

/-- `{a}.max' _` is `a`. -/
@[simp] lemma max'_singleton (a : α) :
  ({a} : finset α).max' (singleton_nonempty _) = a :=
by simp [max']

theorem min'_lt_max' {i j} (H1 : i ∈ s) (H2 : j ∈ s) (H3 : i ≠ j) :
  s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
begin
  rcases lt_trichotomy i j with H4 | H4 | H4,
  { have H5 := min'_le s i H1,
    have H6 := le_max' s j H2,
    apply lt_of_le_of_lt H5,
    apply lt_of_lt_of_le H4 H6 },
  { cc },
  { have H5 := min'_le s j H2,
    have H6 := le_max' s i H1,
    apply lt_of_le_of_lt H5,
    apply lt_of_lt_of_le H4 H6 }
end

/--
If there's more than 1 element, the min' is less than the max'. An alternate version of
`min'_lt_max'` which is sometimes more convenient.
-/
lemma min'_lt_max'_of_card (h₂ : 1 < card s) :
  s.min' (finset.card_pos.mp $ lt_trans zero_lt_one h₂) <
  s.max' (finset.card_pos.mp $ lt_trans zero_lt_one h₂) :=
begin
  apply lt_of_not_ge,
  intro a,
  apply not_le_of_lt h₂ (le_of_eq _),
  rw card_eq_one,
  use (max' s (finset.card_pos.mp $ lt_trans zero_lt_one h₂)),
  rw eq_singleton_iff_unique_mem,
  refine ⟨max'_mem _ _, λ t Ht, le_antisymm (le_max' s t Ht) (le_trans a (min'_le s t Ht))⟩,
end

lemma max'_eq_of_dual_min' {s : finset α} (hs : s.nonempty) :
  max' s hs = of_dual (min' (image to_dual s) (nonempty.image hs to_dual)) :=
begin
  rw [of_dual, to_dual, equiv.coe_fn_mk, equiv.coe_fn_symm_mk, id.def],
  simp_rw (@image_id (order_dual α) (s : finset (order_dual α))),
  refl,
end

lemma min'_eq_of_dual_max' {s : finset α} (hs : s.nonempty) :
  min' s hs = of_dual (max' (image to_dual s) (nonempty.image hs to_dual)) :=
begin
  rw [of_dual, to_dual, equiv.coe_fn_mk, equiv.coe_fn_symm_mk, id.def],
  simp_rw (@image_id (order_dual α) (s : finset (order_dual α))),
  refl,
end

@[simp] lemma of_dual_max_eq_min_of_dual {a b : α} :
  of_dual (max a b) = min (of_dual a) (of_dual b) := rfl

@[simp] lemma of_dual_min_eq_max_of_dual {a b : α} :
  of_dual (min a b) = max (of_dual a) (of_dual b) := rfl

end max_min

section exists_max_min

variables [linear_order α]
lemma exists_max_image (s : finset β) (f : β → α) (h : s.nonempty) :
  ∃ x ∈ s, ∀ x' ∈ s, f x' ≤ f x :=
begin
  cases max_of_nonempty (h.image f) with y hy,
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩,
  exact ⟨x, hx, λ x' hx', le_max_of_mem (mem_image_of_mem f hx') hy⟩,
end

lemma exists_min_image (s : finset β) (f : β → α) (h : s.nonempty) :
  ∃ x ∈ s, ∀ x' ∈ s, f x ≤ f x' :=
@exists_max_image (order_dual α) β _ s f h

end exists_max_min
end finset

namespace multiset

lemma count_sup [decidable_eq β] (s : finset α) (f : α → multiset β) (b : β) :
  count b (s.sup f) = s.sup (λa, count b (f a)) :=
begin
  letI := classical.dec_eq α,
  refine s.induction _ _,
  { exact count_zero _ },
  { assume i s his ih,
    rw [finset.sup_insert, sup_eq_union, count_union, finset.sup_insert, ih],
    refl }
end

lemma mem_sup {α β} [decidable_eq β] {s : finset α} {f : α → multiset β}
  {x : β} : x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v :=
begin
  classical,
  apply s.induction_on,
  { simp },
  { intros a s has hxs,
    rw [finset.sup_insert, multiset.sup_eq_union, multiset.mem_union],
    split,
    { intro hxi,
      cases hxi with hf hf,
      { refine ⟨a, _, hf⟩,
        simp only [true_or, eq_self_iff_true, finset.mem_insert] },
      { rcases hxs.mp hf with ⟨v, hv, hfv⟩,
        refine ⟨v, _, hfv⟩,
        simp only [hv, or_true, finset.mem_insert] } },
    { rintros ⟨v, hv, hfv⟩,
      rw [finset.mem_insert] at hv,
      rcases hv with rfl | hv,
      { exact or.inl hfv },
      { refine or.inr (hxs.mpr ⟨v, hv, hfv⟩) } } },
end

end multiset

namespace finset

lemma mem_sup {α β} [decidable_eq β] {s : finset α} {f : α → finset β}
  {x : β} : x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v :=
begin
  change _ ↔ ∃ v ∈ s, x ∈ (f v).val,
  rw [←multiset.mem_sup, ←multiset.mem_to_finset, sup_to_finset],
  simp_rw [val_to_finset],
end

lemma sup_eq_bind {α β} [decidable_eq β] (s : finset α) (t : α → finset β) :
  s.sup t = s.bind t :=
by { ext, rw [mem_sup, mem_bind], }

end finset

section lattice
variables {ι : Type*} {ι' : Sort*} [complete_lattice α]

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `supr_eq_supr_finset'` for a version
that works for `ι : Sort*`. -/
lemma supr_eq_supr_finset (s : ι → α) :
  (⨆i, s i) = (⨆t:finset ι, ⨆i∈t, s i) :=
begin
  classical,
  exact le_antisymm
    (supr_le $ assume b, le_supr_of_le {b} $ le_supr_of_le b $ le_supr_of_le
      (by simp) $ le_refl _)
    (supr_le $ assume t, supr_le $ assume b, supr_le $ assume hb, le_supr _ _)
end

/-- Supremum of `s i`, `i : ι`, is equal to the supremum over `t : finset ι` of suprema
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `supr_eq_supr_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
lemma supr_eq_supr_finset' (s : ι' → α) :
  (⨆i, s i) = (⨆t:finset (plift ι'), ⨆i∈t, s (plift.down i)) :=
by rw [← supr_eq_supr_finset, ← equiv.plift.surjective.supr_comp]; refl

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨆ i ∈ t, s i`. This version assumes `ι` is a `Type*`. See `infi_eq_infi_finset'` for a version
that works for `ι : Sort*`. -/
lemma infi_eq_infi_finset (s : ι → α) :
  (⨅i, s i) = (⨅t:finset ι, ⨅i∈t, s i) :=
@supr_eq_supr_finset (order_dual α) _ _ _

/-- Infimum of `s i`, `i : ι`, is equal to the infimum over `t : finset ι` of infima
`⨆ i ∈ t, s i`. This version works for `ι : Sort*`. See `infi_eq_infi_finset` for a version
that assumes `ι : Type*` but has no `plift`s. -/
lemma infi_eq_infi_finset' (s : ι' → α) :
  (⨅i, s i) = (⨅t:finset (plift ι'), ⨅i∈t, s (plift.down i)) :=
@supr_eq_supr_finset' (order_dual α) _ _ _

end lattice

namespace set
variables {ι : Type*} {ι' : Sort*}

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version assumes `ι : Type*`. See also `Union_eq_Union_finset'` for
a version that works for `ι : Sort*`. -/
lemma Union_eq_Union_finset (s : ι → set α) :
  (⋃i, s i) = (⋃t:finset ι, ⋃i∈t, s i) :=
supr_eq_supr_finset s

/-- Union of an indexed family of sets `s : ι → set α` is equal to the union of the unions
of finite subfamilies. This version works for `ι : Sort*`. See also `Union_eq_Union_finset` for
a version that assumes `ι : Type*` but avoids `plift`s in the right hand side. -/
lemma Union_eq_Union_finset' (s : ι' → set α) :
  (⋃i, s i) = (⋃t:finset (plift ι'), ⋃i∈t, s (plift.down i)) :=
supr_eq_supr_finset' s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version assumes `ι : Type*`. See also
`Inter_eq_Inter_finset'` for a version that works for `ι : Sort*`. -/
lemma Inter_eq_Inter_finset (s : ι → set α) :
  (⋂i, s i) = (⋂t:finset ι, ⋂i∈t, s i) :=
infi_eq_infi_finset s

/-- Intersection of an indexed family of sets `s : ι → set α` is equal to the intersection of the
intersections of finite subfamilies. This version works for `ι : Sort*`. See also
`Inter_eq_Inter_finset` for a version that assumes `ι : Type*` but avoids `plift`s in the right
hand side. -/
lemma Inter_eq_Inter_finset' (s : ι' → set α) :
  (⋂i, s i) = (⋂t:finset (plift ι'), ⋂i∈t, s (plift.down i)) :=
infi_eq_infi_finset' s

end set

namespace finset

open function

/-! ### Interaction with big lattice/set operations -/

section lattice

lemma supr_coe [has_Sup β] (f : α → β) (s : finset α) :
  (⨆ x ∈ (↑s : set α), f x) = ⨆ x ∈ s, f x :=
rfl

lemma infi_coe [has_Inf β] (f : α → β) (s : finset α) :
  (⨅ x ∈ (↑s : set α), f x) = ⨅ x ∈ s, f x :=
rfl

variables [complete_lattice β]

theorem supr_singleton (a : α) (s : α → β) : (⨆ x ∈ ({a} : finset α), s x) = s a :=
by simp

theorem infi_singleton (a : α) (s : α → β) : (⨅ x ∈ ({a} : finset α), s x) = s a :=
by simp

lemma supr_option_to_finset (o : option α) (f : α → β) :
  (⨆ x ∈ o.to_finset, f x) = ⨆ x ∈ o, f x :=
by { congr, ext, rw [option.mem_to_finset] }

lemma infi_option_to_finset (o : option α) (f : α → β) :
  (⨅ x ∈ o.to_finset, f x) = ⨅ x ∈ o, f x :=
@supr_option_to_finset _ (order_dual β) _ _ _

variables [decidable_eq α]

theorem supr_union {f : α → β} {s t : finset α} :
  (⨆ x ∈ s ∪ t, f x) = (⨆x∈s, f x) ⊔ (⨆x∈t, f x) :=
by simp [supr_or, supr_sup_eq]

theorem infi_union {f : α → β} {s t : finset α} :
  (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x) ⊓ (⨅ x ∈ t, f x) :=
by simp [infi_or, infi_inf_eq]

lemma supr_insert (a : α) (s : finset α) (t : α → β) :
  (⨆ x ∈ insert a s, t x) = t a ⊔ (⨆ x ∈ s, t x) :=
by { rw insert_eq, simp only [supr_union, finset.supr_singleton] }

lemma infi_insert (a : α) (s : finset α) (t : α → β) :
  (⨅ x ∈ insert a s, t x) = t a ⊓ (⨅ x ∈ s, t x) :=
by { rw insert_eq, simp only [infi_union, finset.infi_singleton] }

lemma supr_finset_image {f : γ → α} {g : α → β} {s : finset γ} :
  (⨆ x ∈ s.image f, g x) = (⨆ y ∈ s, g (f y)) :=
by rw [← supr_coe, coe_image, supr_image, supr_coe]

lemma infi_finset_image {f : γ → α} {g : α → β} {s : finset γ} :
  (⨅ x ∈ s.image f, g x) = (⨅ y ∈ s, g (f y)) :=
by rw [← infi_coe, coe_image, infi_image, infi_coe]

lemma supr_insert_update {x : α} {t : finset α} (f : α → β) {s : β} (hx : x ∉ t) :
  (⨆ (i ∈ insert x t), function.update f x s i) = (s ⊔ ⨆ (i ∈ t), f i) :=
begin
  simp only [finset.supr_insert, update_same],
  rcongr i hi, apply update_noteq, rintro rfl, exact hx hi
end

lemma infi_insert_update {x : α} {t : finset α} (f : α → β) {s : β} (hx : x ∉ t) :
  (⨅ (i ∈ insert x t), update f x s i) = (s ⊓ ⨅ (i ∈ t), f i) :=
@supr_insert_update α (order_dual β) _ _ _ _ f _ hx

lemma supr_bind (s : finset γ) (t : γ → finset α) (f : α → β) :
  (⨆ y ∈ s.bind t, f y) = ⨆ (x ∈ s) (y ∈ t x), f y :=
calc (⨆ y ∈ s.bind t, f y) = ⨆ y (hy : ∃ x ∈ s, y ∈ t x), f y :
  congr_arg _ $ funext $ λ y, by rw [mem_bind]
... = _ : by simp only [supr_exists, @supr_comm _ α]

lemma infi_bind (s : finset γ) (t : γ → finset α) (f : α → β) :
  (⨅ y ∈ s.bind t, f y) = ⨅ (x ∈ s) (y ∈ t x), f y :=
@supr_bind _ (order_dual β) _ _ _ _ _ _

end lattice

@[simp] theorem bUnion_coe (s : finset α) (t : α → set β) :
  (⋃ x ∈ (↑s : set α), t x) = ⋃ x ∈ s, t x :=
rfl

@[simp] theorem bInter_coe (s : finset α) (t : α → set β) :
  (⋂ x ∈ (↑s : set α), t x) = ⋂ x ∈ s, t x :=
rfl

@[simp] theorem bUnion_singleton (a : α) (s : α → set β) : (⋃ x ∈ ({a} : finset α), s x) = s a :=
supr_singleton a s

@[simp] theorem bInter_singleton (a : α) (s : α → set β) : (⋂ x ∈ ({a} : finset α), s x) = s a :=
infi_singleton a s

@[simp] lemma bUnion_preimage_singleton (f : α → β) (s : finset β) :
  (⋃ y ∈ s, f ⁻¹' {y}) = f ⁻¹' ↑s :=
set.bUnion_preimage_singleton f ↑s

@[simp] lemma bUnion_option_to_finset (o : option α) (f : α → set β) :
  (⋃ x ∈ o.to_finset, f x) = ⋃ x ∈ o, f x :=
supr_option_to_finset o f

@[simp] lemma bInter_option_to_finset (o : option α) (f : α → set β) :
  (⋂ x ∈ o.to_finset, f x) = ⋂ x ∈ o, f x :=
infi_option_to_finset o f

variables [decidable_eq α]

lemma bUnion_union (s t : finset α) (u : α → set β) :
  (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ (⋃ x ∈ t, u x) :=
supr_union

lemma bInter_inter (s t : finset α) (u : α → set β) :
  (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ (⋂ x ∈ t, u x) :=
infi_union

@[simp] lemma bUnion_insert (a : α) (s : finset α) (t : α → set β) :
  (⋃ x ∈ insert a s, t x) = t a ∪ (⋃ x ∈ s, t x) :=
supr_insert a s t

@[simp] lemma bInter_insert (a : α) (s : finset α) (t : α → set β) :
  (⋂ x ∈ insert a s, t x) = t a ∩ (⋂ x ∈ s, t x) :=
infi_insert a s t

@[simp] lemma bUnion_finset_image {f : γ → α} {g : α → set β} {s : finset γ} :
  (⋃x ∈ s.image f, g x) = (⋃y ∈ s, g (f y)) :=
supr_finset_image

@[simp] lemma bInter_finset_image {f : γ → α} {g : α → set β} {s : finset γ} :
  (⋂ x ∈ s.image f, g x) = (⋂ y ∈ s, g (f y)) :=
infi_finset_image

lemma bUnion_insert_update {x : α} {t : finset α} (f : α → set β) {s : set β} (hx : x ∉ t) :
  (⋃ (i ∈ insert x t), @update _ _ _ f x s i) = (s ∪ ⋃ (i ∈ t), f i) :=
supr_insert_update f hx

lemma bInter_insert_update {x : α} {t : finset α} (f : α → set β) {s : set β} (hx : x ∉ t) :
  (⋂ (i ∈ insert x t), @update _ _ _ f x s i) = (s ∩ ⋂ (i ∈ t), f i) :=
infi_insert_update f hx

@[simp] lemma bUnion_bind (s : finset γ) (t : γ → finset α) (f : α → set β) :
  (⋃ y ∈ s.bind t, f y) = ⋃ (x ∈ s) (y ∈ t x), f y :=
supr_bind s t f

@[simp] lemma bInter_bind (s : finset γ) (t : γ → finset α) (f : α → set β) :
  (⋂ y ∈ s.bind t, f y) = ⋂ (x ∈ s) (y ∈ t x), f y :=
infi_bind s t f

end finset
