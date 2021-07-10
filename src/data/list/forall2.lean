/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import data.list.basic

/-!
# Double universal quantification on a list

This file provides an API for `list.forall₂` (definition in `data.list.defs`).
`forall₂ r l₁ l₂` means that `∀ a ∈ l₁, ∀ b ∈ l₂, r a b`, where `l₁`, `l₂` are lists.
-/

open nat function

namespace list

variables {α β γ δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}
open relator

mk_iff_of_inductive_prop list.forall₂ list.forall₂_iff

@[simp] theorem forall₂_cons {R : α → β → Prop} {a b l₁ l₂} :
  forall₂ R (a :: l₁) (b :: l₂) ↔ R a b ∧ forall₂ R l₁ l₂ :=
⟨λ h, by cases h with h₁ h₂; split; assumption, λ ⟨h₁, h₂⟩, forall₂.cons h₁ h₂⟩

theorem forall₂.imp {R S : α → β → Prop}
  (H : ∀ a b, R a b → S a b) {l₁ l₂}
  (h : forall₂ R l₁ l₂) : forall₂ S l₁ l₂ :=
by induction h; constructor; solve_by_elim

lemma forall₂.mp {r q s : α → β → Prop} (h : ∀ a b, r a b → q a b → s a b) :
  ∀ {l₁ l₂}, forall₂ r l₁ l₂ → forall₂ q l₁ l₂ → forall₂ s l₁ l₂
| []        []        forall₂.nil           forall₂.nil           := forall₂.nil
| (a :: l₁) (b :: l₂) (forall₂.cons hr hrs) (forall₂.cons hq hqs) :=
  forall₂.cons (h a b hr hq) (forall₂.mp hrs hqs)

lemma forall₂.flip : ∀ {a b}, forall₂ (flip r) b a → forall₂ r a b
| _ _                 forall₂.nil          := forall₂.nil
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) := forall₂.cons h₁ h₂.flip

lemma forall₂_same {r : α → α → Prop} : ∀ {l}, (∀ x∈l, r x x) → forall₂ r l l
| []        _ := forall₂.nil
| (a :: as) h := forall₂.cons
    (h _ (mem_cons_self _ _))
    (forall₂_same $ λ a ha, h a $ mem_cons_of_mem _ ha)

lemma forall₂_refl {r} [is_refl α r] (l : list α) : forall₂ r l l :=
forall₂_same $ λ a h, is_refl.refl _

lemma forall₂_eq_eq_eq : forall₂ ((=) : α → α → Prop) = (=) :=
begin
  funext a b, apply propext,
  split,
  { intro h, induction h, {refl}, simp only [*]; split; refl },
  { intro h, subst h, exact forall₂_refl _ }
end

@[simp, priority 900] lemma forall₂_nil_left_iff {l} : forall₂ r nil l ↔ l = nil :=
⟨λ H, by cases H; refl, by rintro rfl; exact forall₂.nil⟩

@[simp, priority 900] lemma forall₂_nil_right_iff {l} : forall₂ r l nil ↔ l = nil :=
⟨λ H, by cases H; refl, by rintro rfl; exact forall₂.nil⟩

lemma forall₂_cons_left_iff {a l u} :
  forall₂ r (a :: l) u ↔ (∃b u', r a b ∧ forall₂ r l u' ∧ u = b :: u') :=
iff.intro
  (λ h, match u, h with (b :: u'), forall₂.cons h₁ h₂ := ⟨b, u', h₁, h₂, rfl⟩ end)
  (λ h, match u, h with _, ⟨b, u', h₁, h₂, rfl⟩ := forall₂.cons h₁ h₂ end)

lemma forall₂_cons_right_iff {b l u} :
  forall₂ r u (b :: l) ↔ (∃a u', r a b ∧ forall₂ r u' l ∧ u = a :: u') :=
iff.intro
  (λ h, match u, h with (b :: u'), forall₂.cons h₁ h₂ := ⟨b, u', h₁, h₂, rfl⟩ end)
  (λ h, match u, h with _, ⟨b, u', h₁, h₂, rfl⟩ := forall₂.cons h₁ h₂ end)

lemma forall₂_and_left {r : α → β → Prop} {p : α → Prop} :
  ∀ l u, forall₂ (λa b, p a ∧ r a b) l u ↔ (∀ a∈l, p a) ∧ forall₂ r l u
| []     u := by simp only [forall₂_nil_left_iff, forall_prop_of_false (not_mem_nil _),
    imp_true_iff, true_and]
| (a :: l) u := by simp only [forall₂_and_left l, forall₂_cons_left_iff, forall_mem_cons,
    and_assoc, and_comm, and.left_comm, exists_and_distrib_left.symm]

@[simp] lemma forall₂_map_left_iff {f : γ → α} :
  ∀ {l u}, forall₂ r (map f l) u ↔ forall₂ (λc b, r (f c) b) l u
| []     _ := by simp only [map, forall₂_nil_left_iff]
| (a :: l) _ := by simp only [map, forall₂_cons_left_iff, forall₂_map_left_iff]

@[simp] lemma forall₂_map_right_iff {f : γ → β} :
  ∀ {l u}, forall₂ r l (map f u) ↔ forall₂ (λa c, r a (f c)) l u
| _ []     := by simp only [map, forall₂_nil_right_iff]
| _ (b :: u) := by simp only [map, forall₂_cons_right_iff, forall₂_map_right_iff]

lemma left_unique_forall₂' (hr : left_unique r) :
  ∀ {a b c}, forall₂ r a b → forall₂ r c b → a = c
| a₀ nil a₁ forall₂.nil forall₂.nil := rfl
| (a₀ :: l₀) (b :: l) (a₁ :: l₁) (forall₂.cons ha₀ h₀) (forall₂.cons ha₁ h₁) :=
  hr.unique ha₀ ha₁ ▸ left_unique_forall₂' h₀ h₁ ▸ rfl

lemma left_unique_forall₂ (hr : left_unique r) : left_unique (forall₂ r) :=
⟨@left_unique_forall₂' _ _ _ hr⟩

lemma right_unique_forall₂' (hr : right_unique r) : ∀ {a b c}, forall₂ r a b → forall₂ r a c → b = c
| nil a₀ a₁ forall₂.nil forall₂.nil := rfl
| (b :: l) (a₀ :: l₀) (a₁ :: l₁) (forall₂.cons ha₀ h₀) (forall₂.cons ha₁ h₁) :=
  hr.unique ha₀ ha₁ ▸ right_unique_forall₂' h₀ h₁ ▸ rfl

lemma right_unique_forall₂ (hr : right_unique r) : right_unique (forall₂ r) :=
⟨@right_unique_forall₂' _ _ _ hr⟩

lemma bi_unique_forall₂ (hr : bi_unique r) : bi_unique (forall₂ r) :=
@@bi_unique.mk _ (left_unique_forall₂ hr.1) (right_unique_forall₂ hr.2)

theorem forall₂_length_eq {R : α → β → Prop} :
  ∀ {l₁ l₂}, forall₂ R l₁ l₂ → length l₁ = length l₂
| _ _ forall₂.nil          := rfl
| _ _ (forall₂.cons h₁ h₂) := congr_arg succ (forall₂_length_eq h₂)

theorem forall₂_zip {R : α → β → Prop} :
  ∀ {l₁ l₂}, forall₂ R l₁ l₂ → ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b
| _ _ (forall₂.cons h₁ h₂) x y (or.inl rfl) := h₁
| _ _ (forall₂.cons h₁ h₂) x y (or.inr h₃) := forall₂_zip h₂ h₃

theorem forall₂_iff_zip {R : α → β → Prop} {l₁ l₂} : forall₂ R l₁ l₂ ↔
  length l₁ = length l₂ ∧ ∀ {a b}, (a, b) ∈ zip l₁ l₂ → R a b :=
⟨λ h, ⟨forall₂_length_eq h, @forall₂_zip _ _ _ _ _ h⟩,
 λ h, begin
  cases h with h₁ h₂,
  induction l₁ with a l₁ IH generalizing l₂,
  { cases length_eq_zero.1 h₁.symm, constructor },
  { cases l₂ with b l₂; injection h₁ with h₁,
    exact forall₂.cons (h₂ $ or.inl rfl) (IH h₁ $ λ a b h, h₂ $ or.inr h) }
end⟩

theorem forall₂_take {R : α → β → Prop} :
  ∀ n {l₁ l₂}, forall₂ R l₁ l₂ → forall₂ R (take n l₁) (take n l₂)
| 0 _ _ _ := by simp only [forall₂.nil, take]
| (n+1) _ _ (forall₂.nil) := by simp only [forall₂.nil, take]
| (n+1) _ _ (forall₂.cons h₁ h₂) := by simp [and.intro h₁ h₂, forall₂_take n]

theorem forall₂_drop {R : α → β → Prop} :
  ∀ n {l₁ l₂}, forall₂ R l₁ l₂ → forall₂ R (drop n l₁) (drop n l₂)
| 0 _ _ h := by simp only [drop, h]
| (n+1) _ _ (forall₂.nil) := by simp only [forall₂.nil, drop]
| (n+1) _ _ (forall₂.cons h₁ h₂) := by simp [and.intro h₁ h₂, forall₂_drop n]

theorem forall₂_take_append {R : α → β → Prop} (l : list α) (l₁ : list β) (l₂ : list β)
  (h : forall₂ R l (l₁ ++ l₂)) : forall₂ R (list.take (length l₁) l) l₁ :=
have h': forall₂ R (take (length l₁) l) (take (length l₁) (l₁ ++ l₂)),
from forall₂_take (length l₁) h,
by rwa [take_left] at h'

theorem forall₂_drop_append {R : α → β → Prop} (l : list α) (l₁ : list β) (l₂ : list β)
  (h : forall₂ R l (l₁ ++ l₂)) : forall₂ R (list.drop (length l₁) l) l₂ :=
have h': forall₂ R (drop (length l₁) l) (drop (length l₁) (l₁ ++ l₂)),
from forall₂_drop (length l₁) h,
by rwa [drop_left] at h'

lemma rel_mem (hr : bi_unique r) : (r ⇒ forall₂ r ⇒ iff) (∈) (∈)
| a b h [] [] forall₂.nil := by simp only [not_mem_nil]
| a b h (a' :: as) (b' :: bs) (forall₂.cons h₁ h₂) := rel_or (rel_eq hr h h₁) (rel_mem h h₂)

lemma rel_map : ((r ⇒ p) ⇒ forall₂ r ⇒ forall₂ p) map map
| f g h [] [] forall₂.nil := forall₂.nil
| f g h (a :: as) (b :: bs) (forall₂.cons h₁ h₂) := forall₂.cons (h h₁) (rel_map @h h₂)

lemma rel_append : (forall₂ r ⇒ forall₂ r ⇒ forall₂ r) append append
| [] [] h l₁ l₂ hl := hl
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) l₁ l₂ hl := forall₂.cons h₁ (rel_append h₂ hl)

lemma rel_reverse : (forall₂ r ⇒ forall₂ r) reverse reverse
| [] [] forall₂.nil := forall₂.nil
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) := begin
  simp only [reverse_cons],
  exact rel_append (rel_reverse h₂) (forall₂.cons h₁ forall₂.nil)
end

@[simp]
lemma forall₂_reverse_iff {l₁ l₂} : forall₂ r (reverse l₁) (reverse l₂) ↔ forall₂ r l₁ l₂ :=
iff.intro
  (λ h, by { rw [← reverse_reverse l₁, ← reverse_reverse l₂], exact rel_reverse h })
  (λ h, rel_reverse h)

lemma rel_join : (forall₂ (forall₂ r) ⇒ forall₂ r) join join
| [] [] forall₂.nil := forall₂.nil
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) := rel_append h₁ (rel_join h₂)

lemma rel_bind : (forall₂ r ⇒ (r ⇒ forall₂ p) ⇒ forall₂ p) list.bind list.bind :=
λ a b h₁ f g h₂, rel_join (rel_map @h₂ h₁)

lemma rel_foldl : ((p ⇒ r ⇒ p) ⇒ p ⇒ forall₂ r ⇒ p) foldl foldl
| f g hfg _ _ h _ _ forall₂.nil := h
| f g hfg x y hxy _ _ (forall₂.cons hab hs) := rel_foldl @hfg (hfg hxy hab) hs

lemma rel_foldr : ((r ⇒ p ⇒ p) ⇒ p ⇒ forall₂ r ⇒ p) foldr foldr
| f g hfg _ _ h _ _ forall₂.nil := h
| f g hfg x y hxy _ _ (forall₂.cons hab hs) := hfg hab (rel_foldr @hfg hxy hs)

lemma rel_filter {p : α → Prop} {q : β → Prop} [decidable_pred p] [decidable_pred q]
  (hpq : (r ⇒ (↔)) p q) :
  (forall₂ r ⇒ forall₂ r) (filter p) (filter q)
| _ _ forall₂.nil := forall₂.nil
| (a :: as) (b :: bs) (forall₂.cons h₁ h₂) :=
  begin
    by_cases p a,
    { have : q b, { rwa [← hpq h₁] },
      simp only [filter_cons_of_pos _ h, filter_cons_of_pos _ this, forall₂_cons, h₁, rel_filter h₂,
        and_true], },
    { have : ¬ q b, { rwa [← hpq h₁] },
      simp only [filter_cons_of_neg _ h, filter_cons_of_neg _ this, rel_filter h₂], },
  end

theorem filter_map_cons (f : α → option β) (a : α) (l : list α) :
  filter_map f (a :: l) = option.cases_on (f a) (filter_map f l) (λb, b :: filter_map f l) :=
begin
  generalize eq : f a = b,
  cases b,
  { rw filter_map_cons_none _ _ eq },
  { rw filter_map_cons_some _ _ _ eq },
end

lemma rel_filter_map : ((r ⇒ option.rel p) ⇒ forall₂ r ⇒ forall₂ p) filter_map filter_map
| f g hfg _ _ forall₂.nil := forall₂.nil
| f g hfg (a :: as) (b :: bs) (forall₂.cons h₁ h₂) :=
  by rw [filter_map_cons, filter_map_cons];
  from match f a, g b, hfg h₁ with
  | _, _, option.rel.none := rel_filter_map @hfg h₂
  | _, _, option.rel.some h := forall₂.cons h (rel_filter_map @hfg h₂)
  end

@[to_additive]
lemma rel_prod [monoid α] [monoid β]
  (h : r 1 1) (hf : (r ⇒ r ⇒ r) (*) (*)) : (forall₂ r ⇒ r) prod prod :=
rel_foldl hf h

/-- Given a relation `r`, `sublist_forall₂ r l₁ l₂` indicates that there is a sublist of `l₂` such
  that `forall₂ r l₁ l₂`. -/
inductive sublist_forall₂ (r : α → β → Prop) : list α → list β → Prop
| nil {l} : sublist_forall₂ [] l
| cons {a₁ a₂ l₁ l₂} : r a₁ a₂ → sublist_forall₂ l₁ l₂ →
  sublist_forall₂ (a₁ :: l₁) (a₂ :: l₂)
| cons_right {a l₁ l₂} : sublist_forall₂ l₁ l₂ → sublist_forall₂ l₁ (a :: l₂)

lemma sublist_forall₂_iff {l₁ : list α} {l₂ : list β} :
  sublist_forall₂ r l₁ l₂ ↔ ∃ l, forall₂ r l₁ l ∧ l <+ l₂ :=
begin
  split; intro h,
  { induction h with _ a b l1 l2 rab rll ih b l1 l2 hl ih,
    { exact ⟨nil, forall₂.nil, nil_sublist _⟩ },
    { obtain ⟨l, hl1, hl2⟩ := ih,
      refine ⟨b :: l, forall₂.cons rab hl1, cons_sublist_cons b hl2⟩ },
    { obtain ⟨l, hl1, hl2⟩ := ih,
      exact ⟨l, hl1, hl2.trans (sublist.cons _ _ _ (sublist.refl _))⟩ } },
  { obtain ⟨l, hl1, hl2⟩ := h,
    revert l₁,
    induction hl2 with _ _ _ _ ih _ _ _ _ ih; intros l₁ hl1,
    { rw [forall₂_nil_right_iff.1 hl1],
      exact sublist_forall₂.nil },
    { exact sublist_forall₂.cons_right (ih hl1) },
    { cases hl1 with _ _ _ _ hr hl _,
      exact sublist_forall₂.cons hr (ih hl) } }
end

variable {ra : α → α → Prop}

instance sublist_forall₂.is_refl [is_refl α ra] :
  is_refl (list α) (sublist_forall₂ ra) :=
⟨λ l, sublist_forall₂_iff.2 ⟨l, forall₂_refl l, sublist.refl l⟩⟩

instance sublist_forall₂.is_trans [is_trans α ra] :
  is_trans (list α) (sublist_forall₂ ra) :=
⟨λ a b c, begin
  revert a b,
  induction c with _ _ ih,
  { rintros _ _ h1 (_ | _ | _),
    exact h1 },
  { rintros a b h1 h2,
    cases h2 with _ _ _ _ _ hbc tbc _ _ y1 btc,
    { cases h1,
      exact sublist_forall₂.nil },
    { cases h1 with _ _ _ _ _ hab tab _ _ _ atb,
      { exact sublist_forall₂.nil },
      { exact sublist_forall₂.cons (trans hab hbc) (ih _ _ tab tbc) },
      { exact sublist_forall₂.cons_right (ih _ _ atb tbc) } },
    { exact sublist_forall₂.cons_right (ih _ _ h1 btc), } }
end⟩

lemma sublist.sublist_forall₂ {l₁ l₂ : list α} (h : l₁ <+ l₂) (r : α → α → Prop) [is_refl α r] :
  sublist_forall₂ r l₁ l₂ :=
sublist_forall₂_iff.2 ⟨l₁, forall₂_refl l₁, h⟩

lemma tail_sublist_forall₂_self [is_refl α ra] (l : list α) :
  sublist_forall₂ ra l.tail l :=
l.tail_sublist.sublist_forall₂ ra

end list
