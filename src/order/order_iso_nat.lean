/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.equiv.denumerable
import order.preorder_hom
import order.conditionally_complete_lattice

/-!
# Relation embeddings from the naturals

This file allows translation from monotone functions `ℕ → α` to order embeddings `ℕ ↪ α` and
defines the limit value of an eventually-constant sequence.

## Main declarations

* `nat_lt`/`nat_gt`: Make an order embedding `ℕ ↪ α` from an increasing/decreasing function `ℕ → α`.
* `monotonic_sequence_limit`: The limit of an eventually-constant monotone sequence `ℕ →ₘ α`.
* `monotonic_sequence_limit_index`: The index of the first occurence of `monotonic_sequence_limit`
  in the sequence.
-/
namespace rel_embedding

variables {α : Type*} {r : α → α → Prop} [is_strict_order α r]

/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
def nat_lt (f : ℕ → α) (H : ∀ n : ℕ, r (f n) (f (n + 1))) :
  ((<) : ℕ → ℕ → Prop) ↪r r :=
of_monotone f $ λ a b h, begin
  induction b with b IH, {exact (nat.not_lt_zero _ h).elim},
  cases nat.lt_succ_iff_lt_or_eq.1 h with h e,
  { exact trans (IH h) (H _) },
  { subst b, apply H }
end

@[simp]
lemma nat_lt_apply {f : ℕ → α} {H : ∀ n : ℕ, r (f n) (f (n + 1))} {n : ℕ} :
  nat_lt f H n = f n :=
rfl

/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def nat_gt (f : ℕ → α) (H : ∀ n : ℕ, r (f (n + 1)) (f n)) :
  ((>) : ℕ → ℕ → Prop) ↪r r :=
by haveI := is_strict_order.swap r; exact rel_embedding.swap (nat_lt f H)

theorem well_founded_iff_no_descending_seq :
  well_founded r ↔ ¬ nonempty (((>) : ℕ → ℕ → Prop) ↪r r) :=
⟨λ ⟨h⟩ ⟨⟨f, o⟩⟩,
  suffices ∀ a, acc r a → ∀ n, a ≠ f n, from this (f 0) (h _) 0 rfl,
  λ a ac, begin
    induction ac with a _ IH, intros n h, subst a,
    exact IH (f (n+1)) (o.2 (nat.lt_succ_self _)) _ rfl
  end,
λ N, ⟨λ a, classical.by_contradiction $ λ na,
  let ⟨f, h⟩ := classical.axiom_of_choice $
    show ∀ x : {a // ¬ acc r a}, ∃ y : {a // ¬ acc r a}, r y.1 x.1,
    from λ ⟨x, h⟩, classical.by_contradiction $ λ hn, h $
      ⟨_, λ y h, classical.by_contradiction $ λ na, hn ⟨⟨y, na⟩, h⟩⟩ in
  N ⟨nat_gt (λ n, (f^[n] ⟨a, na⟩).1) $ λ n,
    by { rw [function.iterate_succ'], apply h }⟩⟩⟩

end rel_embedding

namespace nat
variables (s : set ℕ) [decidable_pred (∈ s)] [infinite s]

/-- An order embedding from `ℕ` to itself with a specified range -/
def order_embedding_of_set : ℕ ↪o ℕ :=
(rel_embedding.order_embedding_of_lt_embedding
  (rel_embedding.nat_lt (nat.subtype.of_nat s) (λ n, nat.subtype.lt_succ_self _))).trans
  (order_embedding.subtype s)

/-- `nat.subtype.of_nat` as an order isomorphism between `ℕ` and an infinite decidable subset. -/
noncomputable def subtype.order_iso_of_nat  :
  ℕ ≃o s :=
rel_iso.of_surjective (rel_embedding.order_embedding_of_lt_embedding
  (rel_embedding.nat_lt (nat.subtype.of_nat s) (λ n, nat.subtype.lt_succ_self _)))
  nat.subtype.of_nat_surjective

variable {s}

@[simp]
lemma order_embedding_of_set_apply {n : ℕ} : order_embedding_of_set s n = subtype.of_nat s n :=
rfl

@[simp]
lemma subtype.order_iso_of_nat_apply {n : ℕ} :
  subtype.order_iso_of_nat s n = subtype.of_nat s n :=
by { simp [subtype.order_iso_of_nat] }

variable (s)

@[simp]
lemma order_embedding_of_set_range : set.range (nat.order_embedding_of_set s) = s :=
begin
  ext x,
  rw [set.mem_range, nat.order_embedding_of_set],
  split; intro h,
  { obtain ⟨y, rfl⟩ := h,
    simp },
  { refine ⟨(nat.subtype.order_iso_of_nat s).symm ⟨x, h⟩, _⟩,
    simp only [rel_embedding.coe_trans, rel_embedding.order_embedding_of_lt_embedding_apply,
      rel_embedding.nat_lt_apply, function.comp_app, order_embedding.subtype_apply],
    rw [← subtype.order_iso_of_nat_apply, order_iso.apply_symm_apply, subtype.coe_mk] }
end

end nat

theorem exists_increasing_or_nonincreasing_subseq' {α : Type*} (r : α → α → Prop) (f : ℕ → α) :
  ∃ (g : ℕ ↪o ℕ), (∀ n : ℕ, r (f (g n)) (f (g (n + 1)))) ∨
    (∀ m n : ℕ, m < n → ¬ r (f (g m)) (f (g n))) :=
begin
  classical,
  let bad : set ℕ := { m | ∀ n, m < n → ¬ r (f m) (f n) },
  by_cases hbad : infinite bad,
  { haveI := hbad,
    refine ⟨nat.order_embedding_of_set bad, or.intro_right _ (λ m n mn, _)⟩,
    have h := set.mem_range_self m,
    rw nat.order_embedding_of_set_range bad at h,
    exact h _ ((order_embedding.lt_iff_lt _).2 mn) },
  { rw [set.infinite_coe_iff, set.infinite, not_not] at hbad,
    obtain ⟨m, hm⟩ : ∃ m, ∀ n, m ≤ n → ¬ n ∈ bad,
    { by_cases he : hbad.to_finset.nonempty,
      { refine ⟨(hbad.to_finset.max' he).succ, λ n hn nbad, nat.not_succ_le_self _
        (hn.trans (hbad.to_finset.le_max' n (hbad.mem_to_finset.2 nbad)))⟩ },
      { exact ⟨0, λ n hn nbad, he ⟨n, hbad.mem_to_finset.2 nbad⟩⟩ } },
    have h : ∀ (n : ℕ), ∃ (n' : ℕ), n < n' ∧ r (f (n + m)) (f (n' + m)),
    { intro n,
      have h := hm _ (le_add_of_nonneg_left n.zero_le),
      simp only [exists_prop, not_not, set.mem_set_of_eq, not_forall] at h,
      obtain ⟨n', hn1, hn2⟩ := h,
      obtain ⟨x, hpos, rfl⟩ := exists_pos_add_of_lt hn1,
      refine ⟨n + x, add_lt_add_left hpos n, _⟩,
      rw [add_assoc, add_comm x m, ← add_assoc],
      exact hn2 },
    let g' : ℕ → ℕ := @nat.rec (λ _, ℕ) m (λ n gn, nat.find (h gn)),
    exact ⟨(rel_embedding.nat_lt (λ n, g' n + m)
      (λ n, nat.add_lt_add_right (nat.find_spec (h (g' n))).1 m)).order_embedding_of_lt_embedding,
      or.intro_left _ (λ n, (nat.find_spec (h (g' n))).2)⟩ }
end

theorem exists_increasing_or_nonincreasing_subseq
  {α : Type*} (r : α → α → Prop) [is_trans α r] (f : ℕ → α) :
  ∃ (g : ℕ ↪o ℕ), (∀ m n : ℕ, m < n → r (f (g m)) (f (g n))) ∨
    (∀ m n : ℕ, m < n → ¬ r (f (g m)) (f (g n))) :=
begin
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f,
  { refine ⟨g, or.intro_left _ (λ m n mn, _)⟩,
    obtain ⟨x, rfl⟩ := le_iff_exists_add.1 (nat.succ_le_iff.2 mn),
    induction x with x ih,
    { apply hr },
    { apply is_trans.trans _ _ _ _ (hr _),
      exact ih (lt_of_lt_of_le m.lt_succ_self (nat.le_add_right _ _)) } },
  { exact ⟨g, or.intro_right _ hnr⟩ }
end

/-- The "monotone chain condition" below is sometimes a convenient form of well foundedness. -/
lemma well_founded.monotone_chain_condition (α : Type*) [partial_order α] :
  well_founded ((>) : α → α → Prop) ↔ ∀ (a : ℕ →ₘ α), ∃ n, ∀ m, n ≤ m → a n = a m :=
begin
  split; intros h,
  { rw well_founded.well_founded_iff_has_max' at h,
    intros a, have hne : (set.range a).nonempty, { use a 0, simp, },
    obtain ⟨x, ⟨n, hn⟩, range_bounded⟩ := h _ hne,
    use n, intros m hm, rw ← hn at range_bounded, symmetry,
    apply range_bounded (a m) (set.mem_range_self _) (a.monotone hm), },
  { rw rel_embedding.well_founded_iff_no_descending_seq, rintros ⟨a⟩,
    obtain ⟨n, hn⟩ := h (a.swap : ((<) : ℕ → ℕ → Prop) →r ((<) : α → α → Prop)).to_preorder_hom,
    exact n.succ_ne_self.symm (rel_embedding.to_preorder_hom_injective _ (hn _ n.le_succ)), },
end

/-- Given an eventually-constant monotonic sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a partially-ordered
type, `monotonic_sequence_limit_index a` is the least natural number `n` for which `aₙ` reaches the
constant value. For sequences that are not eventually constant, `monotonic_sequence_limit_index a`
is defined, but is a junk value. -/
noncomputable def monotonic_sequence_limit_index {α : Type*} [partial_order α] (a : ℕ →ₘ α) : ℕ :=
Inf { n | ∀ m, n ≤ m → a n = a m }

/-- The constant value of an eventually-constant monotonic sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a
partially-ordered type. -/
noncomputable def monotonic_sequence_limit {α : Type*} [partial_order α] (a : ℕ →ₘ α) :=
a (monotonic_sequence_limit_index a)

lemma well_founded.supr_eq_monotonic_sequence_limit {α : Type*} [complete_lattice α]
  (h : well_founded ((>) : α → α → Prop)) (a : ℕ →ₘ α) :
  (⨆ m, a m) = monotonic_sequence_limit a :=
begin
  suffices : (⨆ (m : ℕ), a m) ≤ monotonic_sequence_limit a,
  { exact le_antisymm this (le_supr a _), },
  apply supr_le,
  intros m,
  by_cases hm : m ≤ monotonic_sequence_limit_index a,
  { exact a.monotone hm, },
  { replace hm := le_of_not_le hm,
    let S := { n | ∀ m, n ≤ m → a n = a m },
    have hInf : Inf S ∈ S,
    { refine nat.Inf_mem _, rw well_founded.monotone_chain_condition at h, exact h a, },
    change Inf S ≤ m at hm,
    change a m ≤ a (Inf S),
    rw hInf m hm, },
end
