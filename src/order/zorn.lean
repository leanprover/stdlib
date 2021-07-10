/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import data.set.lattice

/-!
# Chains and Zorn's lemmas

This file defines chains for an arbitrary relation and proves several formulations of Zorn's Lemma,
along with Hausdorff's Maximality Principle.

## Main declarations

* `chain c`: A chain `c` is a set of comparable elements.
* `max_chain_spec`: Hausdorff's Maximality Principle.
* `exists_maximal_of_chains_bounded`: Zorn's Lemma. Many variants are offered.

## Variants

The primary statement of Zorn's lemma is `exists_maximal_of_chains_bounded`. Then it is specialized
to particular relations:
* `(≤)` with `zorn_partial_order`
* `(⊆)` with `zorn_subset`
* `(⊇)` with `zorn_superset`

Lemma names carry modifiers:
* `₀`: Quantifies over a set, as opposed to over a type.
* `_nonempty`: Doesn't ask to prove that the empty chain is bounded and lets you give an element
  that will be smaller than the maximal element found (the maximal element is no smaller than any
  other element, but it can also be incomparable to some).

## How-to

This file comes across as confusing to those who haven't yet used it, so here is a detailed
walkthrough:
1. Know what relation on which type/set you're looking for. See Variants above. You can discharge
  some conditions to Zorn's lemma directly using a `_nonempty` variant.
2. Write down the definition of your type/set, put a `suffices : ∃ m, ∀ a, m ≺ a → a ≺ m, { ... },`
  (or whatever you actually need) followed by a `apply some_version_of_zorn`.
3. Fill in the details. This is where you start talking about chains.

A typical proof using Zorn could look like this
```lean
lemma zorny_lemma : zorny_statement :=
begin
  let s : set α := {x | whatever x},
  suffices : ∃ x ∈ s, ∀ y ∈ s, y ⊆ x → y = x, -- or with another operator
  { exact proof_post_zorn },
  apply zorn.zorn_subset, -- or another variant
  rintro c hcs hc,
  obtain rfl | hcnemp := c.eq_empty_or_nonempty, -- you might need to disjunct on c empty or not
  { exact ⟨edge_case_construction,
      proof_that_edge_case_construction_respects_whatever,
      proof_that_edge_case_construction_contains_all_stuff_in_c⟩ },
  exact ⟨construction,
    proof_that_construction_respects_whatever,
    proof_that_construction_contains_all_stuff_in_c⟩,
end
```

## Notes

Originally ported from Isabelle/HOL. The
[original file](https://isabelle.in.tum.de/dist/library/HOL/HOL/Zorn.html) was written by Jacques D.
Fleuriot, Tobias Nipkow, Christian Sternagel.
-/

noncomputable theory

universes u
open set classical
open_locale classical

namespace zorn

section chain
parameters {α : Type u} (r : α → α → Prop)
local infix ` ≺ `:50  := r

/-- A chain is a subset `c` satisfying `x ≺ y ∨ x = y ∨ y ≺ x` for all `x y ∈ c`. -/
def chain (c : set α) := pairwise_on c (λ x y, x ≺ y ∨ y ≺ x)
parameters {r}

lemma chain.total_of_refl [is_refl α r]
  {c} (H : chain c) {x y} (hx : x ∈ c) (hy : y ∈ c) :
  x ≺ y ∨ y ≺ x :=
if e : x = y then or.inl (e ▸ refl _) else H _ hx _ hy e

lemma chain.mono {c c'} :
  c' ⊆ c → chain c → chain c' :=
pairwise_on.mono

lemma chain.directed_on [is_refl α r] {c} (H : chain c) :
  directed_on (≺) c :=
λ x hx y hy,
match H.total_of_refl hx hy with
| or.inl h := ⟨y, hy, h, refl _⟩
| or.inr h := ⟨x, hx, refl _, h⟩
end

lemma chain_insert {c : set α} {a : α} (hc : chain c) (ha : ∀ b ∈ c, b ≠ a → a ≺ b ∨ b ≺ a) :
  chain (insert a c) :=
forall_insert_of_forall
  (λ x hx, forall_insert_of_forall (hc x hx) (λ hneq, (ha x hx hneq).symm))
  (forall_insert_of_forall
    (λ x hx hneq, ha x hx $ λ h', hneq h'.symm) (λ h, (h rfl).rec _))

/-- `super_chain c₁ c₂` means that `c₂` is a chain that strictly includes `c₁`. -/
def super_chain (c₁ c₂ : set α) : Prop := chain c₂ ∧ c₁ ⊂ c₂

/-- A chain `c` is a maximal chain if there does not exists a chain strictly including `c`. -/
def is_max_chain (c : set α) := chain c ∧ ¬ (∃ c', super_chain c c')

/-- Given a set `c`, if there exists a chain `c'` strictly including `c`, then `succ_chain c`
is one of these chains. Otherwise it is `c`. -/
def succ_chain (c : set α) : set α :=
if h : ∃ c', chain c ∧ super_chain c c' then some h else c

lemma succ_spec {c : set α} (h : ∃ c', chain c ∧ super_chain c c') :
  super_chain c (succ_chain c) :=
let ⟨c', hc'⟩ := h in
have chain c ∧ super_chain c (some h),
  from @some_spec _ (λ c', chain c ∧ super_chain c c') _,
by simp [succ_chain, dif_pos, h, this.right]

lemma chain_succ {c : set α} (hc : chain c) :
  chain (succ_chain c) :=
if h : ∃ c', chain c ∧ super_chain c c' then
  (succ_spec h).left
else
  by simp [succ_chain, dif_neg, h]; exact hc

lemma super_of_not_max {c : set α} (hc₁ : chain c) (hc₂ : ¬ is_max_chain c) :
  super_chain c (succ_chain c) :=
begin
  simp [is_max_chain, not_and_distrib, not_forall_not] at hc₂,
  cases hc₂.neg_resolve_left hc₁ with c' hc',
  exact succ_spec ⟨c', hc₁, hc'⟩
end

lemma succ_increasing {c : set α} :
  c ⊆ succ_chain c :=
if h : ∃ c', chain c ∧ super_chain c c' then
  have super_chain c (succ_chain c), from succ_spec h,
  this.right.left
else by simp [succ_chain, dif_neg, h, subset.refl]

/-- Set of sets reachable from `∅` using `succ_chain` and `⋃₀`. -/
inductive chain_closure : set (set α)
| succ : ∀ {s}, chain_closure s → chain_closure (succ_chain s)
| union : ∀ {s}, (∀ a ∈ s, chain_closure a) → chain_closure (⋃₀ s)

lemma chain_closure_empty :
  ∅ ∈ chain_closure :=
have chain_closure (⋃₀ ∅),
  from chain_closure.union $ λ a h, h.rec _,
by simp at this; assumption

lemma chain_closure_closure :
  ⋃₀ chain_closure ∈ chain_closure :=
chain_closure.union $ λ s hs, hs

variables {c c₁ c₂ c₃ : set α}

private lemma chain_closure_succ_total_aux (hc₁ : c₁ ∈ chain_closure) (hc₂ : c₂ ∈ chain_closure)
  (h : ∀ {c₃}, c₃ ∈ chain_closure → c₃ ⊆ c₂ → c₂ = c₃ ∨ succ_chain c₃ ⊆ c₂) :
  c₁ ⊆ c₂ ∨ succ_chain c₂ ⊆ c₁ :=
begin
  induction hc₁,
  case succ : c₃ hc₃ ih {
    cases ih with ih ih,
    { have h := h hc₃ ih,
      cases h with h h,
      { exact or.inr (h ▸ subset.refl _) },
      { exact or.inl h } },
    { exact or.inr (subset.trans ih succ_increasing) } },
  case union : s hs ih {
    refine (or_iff_not_imp_right.2 $ λ hn, sUnion_subset $ λ a ha, _),
    apply (ih a ha).resolve_right,
    apply mt (λ h, _) hn,
    exact subset.trans h (subset_sUnion_of_mem ha) }
end

private lemma chain_closure_succ_total (hc₁ : c₁ ∈ chain_closure) (hc₂ : c₂ ∈ chain_closure)
  (h : c₁ ⊆ c₂) :
  c₂ = c₁ ∨ succ_chain c₁ ⊆ c₂ :=
begin
  induction hc₂ generalizing c₁ hc₁ h,
  case succ : c₂ hc₂ ih {
    have h₁ : c₁ ⊆ c₂ ∨ @succ_chain α r c₂ ⊆ c₁ :=
      (chain_closure_succ_total_aux hc₁ hc₂ $ λ c₁, ih),
    cases h₁ with h₁ h₁,
    { have h₂ := ih hc₁ h₁,
      cases h₂ with h₂ h₂,
      { exact (or.inr $ h₂ ▸ subset.refl _) },
      { exact (or.inr $ subset.trans h₂ succ_increasing) } },
    { exact (or.inl $ subset.antisymm h₁ h) } },
  case union : s hs ih {
    apply or.imp_left (λ h', subset.antisymm h' h),
    apply classical.by_contradiction,
    simp [not_or_distrib, sUnion_subset_iff, not_forall],
    intros c₃ hc₃ h₁ h₂,
    have h := chain_closure_succ_total_aux hc₁ (hs c₃ hc₃) (λ c₄, ih _ hc₃),
    cases h with h h,
    { have h' := ih c₃ hc₃ hc₁ h,
      cases h' with h' h',
      { exact (h₁ $ h' ▸ subset.refl _) },
      { exact (h₂ $ subset.trans h' $ subset_sUnion_of_mem hc₃) } },
    { exact (h₁ $ subset.trans succ_increasing h) } }
end

lemma chain_closure_total (hc₁ : c₁ ∈ chain_closure) (hc₂ : c₂ ∈ chain_closure) :
  c₁ ⊆ c₂ ∨ c₂ ⊆ c₁ :=
or.imp_right succ_increasing.trans $ chain_closure_succ_total_aux hc₁ hc₂ $ λ c₃ hc₃,
  chain_closure_succ_total hc₃ hc₂

lemma chain_closure_succ_fixpoint (hc₁ : c₁ ∈ chain_closure) (hc₂ : c₂ ∈ chain_closure)
  (h_eq : succ_chain c₂ = c₂) :
  c₁ ⊆ c₂ :=
begin
  induction hc₁,
  case succ : c₁ hc₁ h {
    exact or.elim (chain_closure_succ_total hc₁ hc₂ h)
      (λ h, h ▸ h_eq.symm ▸ subset.refl c₂) id },
  case union : s hs ih {
    exact (sUnion_subset $ λ c₁ hc₁, ih c₁ hc₁) }
end

lemma chain_closure_succ_fixpoint_iff (hc : c ∈ chain_closure) :
  succ_chain c = c ↔ c = ⋃₀ chain_closure :=
⟨λ h, (subset_sUnion_of_mem hc).antisymm
    (chain_closure_succ_fixpoint chain_closure_closure hc h),
  λ h,
  subset.antisymm
    (calc succ_chain c ⊆ ⋃₀{c : set α | c ∈ chain_closure} :
        subset_sUnion_of_mem $ chain_closure.succ hc
      ... = c : h.symm)
    succ_increasing⟩

lemma chain_chain_closure (hc : c ∈ chain_closure) :
  chain c :=
begin
  induction hc,
  case succ : c hc h {
    exact chain_succ h },
  case union : s hs h {
    have h : ∀ c ∈ s, zorn.chain c := h,
    exact λ c₁ ⟨t₁, ht₁, (hc₁ : c₁ ∈ t₁)⟩ c₂ ⟨t₂, ht₂, (hc₂ : c₂ ∈ t₂)⟩ hneq,
      have t₁ ⊆ t₂ ∨ t₂ ⊆ t₁, from chain_closure_total (hs _ ht₁) (hs _ ht₂),
      or.elim this
        (λ ht, h t₂ ht₂ c₁ (ht hc₁) c₂ hc₂ hneq)
        (λ ht, h t₁ ht₁ c₁ hc₁ c₂ (ht hc₂) hneq) }
end

/-- An explicit maximal chain. `max_chain` is taken to be the union of all sets in `chain_closure`.
-/
def max_chain := ⋃₀ chain_closure

/-- Hausdorff's maximality principle

There exists a maximal totally ordered subset of `α`.
Note that we do not require `α` to be partially ordered by `r`. -/
theorem max_chain_spec :
  is_max_chain max_chain :=
classical.by_contradiction $ λ h,
begin
  obtain ⟨h₁, H⟩ := super_of_not_max (chain_chain_closure chain_closure_closure) h,
  obtain ⟨h₂, h₃⟩ := ssubset_iff_subset_ne.1 H,
  exact h₃ ((chain_closure_succ_fixpoint_iff chain_closure_closure).mpr rfl).symm,
end

/-- Zorn's lemma

If every chain has an upper bound, then there exists a maximal element. -/
theorem exists_maximal_of_chains_bounded (h : ∀ c, chain c → ∃ ub, ∀ a ∈ c, a ≺ ub)
  (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃ m, ∀ a, m ≺ a → a ≺ m :=
have ∃ ub, ∀ a ∈ max_chain, a ≺ ub,
  from h _ $ max_chain_spec.left,
let ⟨ub, (hub : ∀ a ∈ max_chain, a ≺ ub)⟩ := this in
⟨ub, λ a ha,
  have chain (insert a max_chain),
    from chain_insert max_chain_spec.left $ λ b hb _, or.inr $ trans (hub b hb) ha,
  have a ∈ max_chain, from
    classical.by_contradiction $ λ h : a ∉ max_chain,
    max_chain_spec.right $ ⟨insert a max_chain, this, ssubset_insert h⟩,
  hub a this⟩

/-- A variant of Zorn's lemma. If every nonempty chain of a nonempty type has an upper bound, then
there is a maximal element.
-/
theorem exists_maximal_of_nonempty_chains_bounded [nonempty α]
  (h : ∀ c, chain c → c.nonempty → ∃ ub, ∀ a ∈ c, a ≺ ub)
  (trans : ∀ {a b c}, a ≺ b → b ≺ c → a ≺ c) :
  ∃ m, ∀ a, m ≺ a → a ≺ m :=
exists_maximal_of_chains_bounded
  (λ c hc,
    (eq_empty_or_nonempty c).elim
      (λ h, ⟨classical.arbitrary α, λ x hx, (h ▸ hx : x ∈ (∅ : set α)).elim⟩)
      (h c hc))
  (λ a b c, trans)

end chain

--This lemma isn't under section `chain` because `parameters` messes up with it. Feel free to fix it
/-- This can be used to turn `zorn.chain (≥)` into `zorn.chain (≤)` and vice-versa. -/
lemma chain.symm {α : Type u} {s : set α} {q : α → α → Prop} (h : chain q s) :
  chain (flip q) s :=
h.mono' (λ _ _, or.symm)

theorem zorn_partial_order {α : Type u} [partial_order α]
  (h : ∀ c : set α, chain (≤) c → ∃ ub, ∀ a ∈ c, a ≤ ub) :
  ∃ m : α, ∀ a, m ≤ a → a = m :=
let ⟨m, hm⟩ := @exists_maximal_of_chains_bounded α (≤) h (λ a b c, le_trans) in
⟨m, λ a ha, le_antisymm (hm a ha) ha⟩

theorem zorn_nonempty_partial_order {α : Type u} [partial_order α] [nonempty α]
  (h : ∀ (c : set α), chain (≤) c → c.nonempty → ∃ ub, ∀ a ∈ c, a ≤ ub) :
  ∃ (m : α), ∀ a, m ≤ a → a = m :=
let ⟨m, hm⟩ := @exists_maximal_of_nonempty_chains_bounded α (≤) _ h (λ a b c, le_trans) in
⟨m, λ a ha, le_antisymm (hm a ha) ha⟩

theorem zorn_partial_order₀ {α : Type u} [partial_order α] (s : set α)
  (ih : ∀ c ⊆ s, chain (≤) c → ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) :
  ∃ m ∈ s, ∀ z ∈ s, m ≤ z → z = m :=
let ⟨⟨m, hms⟩, h⟩ := @zorn_partial_order {m // m ∈ s} _
  (λ c hc,
    let ⟨ub, hubs, hub⟩ := ih (subtype.val '' c) (λ _ ⟨⟨x, hx⟩, _, h⟩, h ▸ hx)
      (by { rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq;
        refine hc _ hpc _ hqc (λ t, hpq (subtype.ext_iff.1 t)) })
    in ⟨⟨ub, hubs⟩, λ ⟨y, hy⟩ hc, hub _ ⟨_, hc, rfl⟩⟩)
in ⟨m, hms, λ z hzs hmz, congr_arg subtype.val (h ⟨z, hzs⟩ hmz)⟩

theorem zorn_nonempty_partial_order₀ {α : Type u} [partial_order α] (s : set α)
  (ih : ∀ c ⊆ s, chain (≤) c → ∀ y ∈ c, ∃ ub ∈ s, ∀ z ∈ c, z ≤ ub) (x : α) (hxs : x ∈ s) :
  ∃ m ∈ s, x ≤ m ∧ ∀ z ∈ s, m ≤ z → z = m :=
let ⟨⟨m, hms, hxm⟩, h⟩ := @zorn_partial_order {m // m ∈ s ∧ x ≤ m} _
  (λ c hc, c.eq_empty_or_nonempty.elim
    (λ hce, hce.symm ▸ ⟨⟨x, hxs, le_refl _⟩, λ _, false.elim⟩)
    (λ ⟨m, hmc⟩,
      let ⟨ub, hubs, hub⟩ := ih (subtype.val '' c) (image_subset_iff.2 $ λ z hzc, z.2.1)
        (by rintro _ ⟨p, hpc, rfl⟩ _ ⟨q, hqc, rfl⟩ hpq;
          exact hc p hpc q hqc (mt (by rintro rfl; refl) hpq)) m.1 (mem_image_of_mem _ hmc) in
    ⟨⟨ub, hubs, le_trans m.2.2 $ hub m.1 $ mem_image_of_mem _ hmc⟩,
      λ a hac, hub a.1 ⟨a, hac, rfl⟩⟩)) in
⟨m, hms, hxm, λ z hzs hmz, congr_arg subtype.val $ h ⟨z, hzs, le_trans hxm hmz⟩ hmz⟩

theorem zorn_subset {α : Type u} (S : set (set α))
  (h : ∀ c ⊆ S, chain (⊆) c → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) :
  ∃ m ∈ S, ∀ a ∈ S, m ⊆ a → a = m :=
zorn_partial_order₀ S h

theorem zorn_subset_nonempty {α : Type u} (S : set (set α))
  (H : ∀ c ⊆ S, chain (⊆) c → c.nonempty → ∃ ub ∈ S, ∀ s ∈ c, s ⊆ ub) (x) (hx : x ∈ S) :
  ∃ m ∈ S, x ⊆ m ∧ ∀ a ∈ S, m ⊆ a → a = m :=
zorn_nonempty_partial_order₀ _ (λ c cS hc y yc, H _ cS hc ⟨y, yc⟩) _ hx

theorem zorn_superset {α : Type u} (S : set (set α))
  (h : ∀ c ⊆ S, chain (⊆) c → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) :
  ∃ m ∈ S, ∀ a ∈ S, a ⊆ m → a = m :=
@zorn_partial_order₀ (order_dual (set α)) _ S $ λ c cS hc, h c cS hc.symm

theorem zorn_superset_nonempty {α : Type u} (S : set (set α))
  (H : ∀ c ⊆ S, chain (⊆) c → c.nonempty → ∃ lb ∈ S, ∀ s ∈ c, lb ⊆ s) (x) (hx : x ∈ S) :
  ∃ m ∈ S, m ⊆ x ∧ ∀ a ∈ S, a ⊆ m → a = m :=
@zorn_nonempty_partial_order₀ (order_dual (set α)) _ S (λ c cS hc y yc, H _ cS
  hc.symm ⟨y, yc⟩) _ hx

lemma chain.total {α : Type u} [preorder α] {c : set α} (H : chain (≤) c) :
  ∀ {x y}, x ∈ c → y ∈ c → x ≤ y ∨ y ≤ x :=
λ x y, H.total_of_refl

lemma chain.image {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) (f : α → β)
  (h : ∀ x y, r x y → s (f x) (f y)) {c : set α} (hrc : chain r c) :
  chain s (f '' c) :=
λ x ⟨a, ha₁, ha₂⟩ y ⟨b, hb₁, hb₂⟩, ha₂ ▸ hb₂ ▸ λ hxy,
  (hrc a ha₁ b hb₁ (mt (congr_arg f) $ hxy)).elim
    (or.inl ∘ h _ _) (or.inr ∘ h _ _)

end zorn

lemma directed_of_chain {α β r} [is_refl β r] {f : α → β} {c : set α}
  (h : zorn.chain (f ⁻¹'o r) c) :
  directed r (λ x : {a : α // a ∈ c}, f x) :=
λ ⟨a, ha⟩ ⟨b, hb⟩, classical.by_cases
  (λ hab : a = b, by simp only [hab, exists_prop, and_self, subtype.exists];
    exact ⟨b, hb, refl _⟩)
  (λ hab, (h a ha b hb hab).elim
    (λ h : r (f a) (f b), ⟨⟨b, hb⟩, h, refl _⟩)
    (λ h : r (f b) (f a), ⟨⟨a, ha⟩, refl _, h⟩))
