/-
Copyright (c) 2021 Alena Gusakov, Bhavik Mehta, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov, Bhavik Mehta, Kyle Miller
-/
import data.fintype.basic
import data.rel
import data.set.finite

/-!
# Hall's Marriage Theorem

Given a list of finite subsets $X_1,X_2,\dots,X_n$ of some given set
$S$, Hall in [Hall1935] gave a necessary and sufficient condition for
there to be a list of distinct elements $x_1,x_2,\dots,x_n$ with
$x_i\in X_i$ for each $i$: it is when for each $k$, the union of every
$k$ of these subsets has at least $k$ elements.

This file proves this for an indexed family `t : ι → finset α` of
finite sets, with `[fintype ι]`, along with some variants of the
statement.  The list of distinct representatives is given by an
injective function `f : ι → α` such that `∀ i, f i ∈ t i`.

A description of this formalization is in [Gusakov2021].

## Main statements
* `finset.all_card_le_bUnion_card_iff_exists_injective` is in terms of `t : ι → finset α`.
* `fintype.all_card_le_rel_image_card_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` such that `rel.image r {a}` is a finite set for all `a : α`.
* `fintype.all_card_le_filter_rel_iff_exists_injective` is in terms of a relation
  `r : α → β → Prop` on finite types, with the Hall condition given in terms of
  `finset.univ.filter`.

## Todo

* The theorem is still true even if `ι` is not a finite type.  The infinite case
  follows from a compactness argument.
* The statement of the theorem in terms of bipartite graphs is in preparation.

## Tags

Hall's Marriage Theorem, indexed families
-/

open finset

universes u v

namespace hall_marriage_theorem

variables {ι : Type u} {α : Type v} [fintype ι]

theorem hall_hard_inductive_zero (t : ι → finset α) (hn : fintype.card ι = 0) :
  ∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x :=
begin
  rw fintype.card_eq_zero_iff at hn,
  exactI ⟨is_empty_elim, is_empty_elim, is_empty_elim⟩,
end

variables {t : ι → finset α} [decidable_eq α]

lemma hall_cond_of_erase {x : ι} (a : α)
  (ha : ∀ (s : finset ι), s.nonempty → s ≠ univ → s.card < (s.bUnion t).card)
  (s' : finset {x' : ι | x' ≠ x}) :
  s'.card ≤ (s'.bUnion (λ x', (t x').erase a)).card :=
begin
  haveI := classical.dec_eq ι,
  specialize ha (s'.image coe),
  rw [nonempty.image_iff, finset.card_image_of_injective s' subtype.coe_injective] at ha,
  by_cases he : s'.nonempty,
  { have ha' : s'.card < (s'.bUnion (λ x, t x)).card,
    { specialize ha he (λ h, by { have h' := mem_univ x, rw ←h at h', simpa using h' }),
      convert ha using 2,
      ext x,
      simp only [mem_image, mem_bUnion, exists_prop, set_coe.exists,
                 exists_and_distrib_right, exists_eq_right, subtype.coe_mk], },
    rw ←erase_bUnion,
    by_cases hb : a ∈ s'.bUnion (λ x, t x),
    { rw card_erase_of_mem hb,
      exact nat.le_pred_of_lt ha' },
    { rw erase_eq_of_not_mem hb,
      exact nat.le_of_lt ha' }, },
  { rw [nonempty_iff_ne_empty, not_not] at he,
    subst s',
    simp },
end

/--
First case of the inductive step: assuming that
`∀ (s : finset ι), s.nonempty → s ≠ univ → s.card < (s.bUnion t).card`
and that the statement of **Hall's Marriage Theorem** is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
lemma hall_hard_inductive_step_A {n : ℕ} (hn : fintype.card ι = n + 1)
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card)
  (ih : ∀ {ι' : Type u} [fintype ι'] (t' : ι' → finset α),
        by exactI fintype.card ι' ≤ n →
                  (∀ (s' : finset ι'), s'.card ≤ (s'.bUnion t').card) →
                  ∃ (f : ι' → α), function.injective f ∧ ∀ x, f x ∈ t' x)
  (ha : ∀ (s : finset ι), s.nonempty → s ≠ univ → s.card < (s.bUnion t).card) :
  ∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x :=
begin
  haveI : nonempty ι := fintype.card_pos_iff.mp (hn.symm ▸ nat.succ_pos _),
  haveI := classical.dec_eq ι,
  /- Choose an arbitrary element `x : ι` and `y : t x`. -/
  let x := classical.arbitrary ι,
  have tx_ne : (t x).nonempty,
  { rw ←finset.card_pos,
    apply nat.lt_of_lt_of_le nat.one_pos,
    convert ht {x},
    rw finset.singleton_bUnion, },
  rcases classical.indefinite_description _ tx_ne with ⟨y, hy⟩,
  /- Restrict to everything except `x` and `y`. -/
  let ι' := {x' : ι | x' ≠ x},
  let t' : ι' → finset α := λ x', (t x').erase y,
  have card_ι' : fintype.card ι' = n,
  { convert congr_arg (λ m, m - 1) hn,
    convert set.card_ne_eq _, },
  rcases ih t' card_ι'.le (hall_cond_of_erase y ha) with ⟨f', hfinj, hfr⟩,
  /- Extend the resulting function. -/
  refine ⟨λ z, if h : z = x then y else f' ⟨z, h⟩, _, _⟩,
  { rintro z₁ z₂,
    have key : ∀ {x}, y ≠ f' x,
    { intros x h,
      specialize hfr x,
      rw ←h at hfr,
      simpa using hfr, },
    by_cases h₁ : z₁ = x; by_cases h₂ : z₂ = x; simp [h₁, h₂, hfinj.eq_iff, key, key.symm], },
  { intro z,
    split_ifs with hz,
    { rwa hz },
    { specialize hfr ⟨z, hz⟩,
      rw mem_erase at hfr,
      exact hfr.2, }, },
end

lemma hall_cond_of_restrict {ι : Type u} {t : ι → finset α} {s : finset ι}
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card)
  (s' : finset (s : set ι)) :
  s'.card ≤ (s'.bUnion (λ a', t a')).card :=
begin
  haveI := classical.dec_eq ι,
  convert ht (s'.image coe) using 1,
  { rw card_image_of_injective _ subtype.coe_injective, },
  { apply congr_arg,
    ext y,
    simp, },
end

lemma hall_cond_of_compl {ι : Type u} {t : ι → finset α} {s : finset ι}
  (hus : s.card = (s.bUnion t).card)
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card)
  (s' : finset (sᶜ : set ι)) :
  s'.card ≤ (s'.bUnion (λ x', t x' \ s.bUnion t)).card :=
begin
  haveI := classical.dec_eq ι,
  have : s'.card = (s ∪ s'.image coe).card - s.card,
  { rw [card_disjoint_union, nat.add_sub_cancel_left,
        card_image_of_injective _ subtype.coe_injective],
    simp only [disjoint_left, not_exists, mem_image, exists_prop, set_coe.exists,
               exists_and_distrib_right, exists_eq_right, subtype.coe_mk],
    intros x hx hc h,
    exact (hc hx).elim },
  rw [this, hus],
  apply (nat.sub_le_sub_right (ht _) _).trans _,
  rw ← card_sdiff,
  { have : (s ∪ s'.image subtype.val).bUnion t \ s.bUnion t ⊆ s'.bUnion (λ x', t x' \ s.bUnion t),
    { intros t,
      simp only [mem_bUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union,
                 exists_and_distrib_right, exists_imp_distrib],
      rintro x (hx | ⟨x', hx', rfl⟩) rat hs,
      { exact (hs x hx rat).elim },
      { exact ⟨⟨x', hx', rat⟩, hs⟩, } },
    exact (card_le_of_subset this).trans le_rfl, },
  { apply bUnion_subset_bUnion_of_subset_left,
    apply subset_union_left }
end

/--
Second case of the inductive step: assuming that
`∃ (s : finset ι), s ≠ univ → s.card = (s.bUnion t).card`
and that the statement of Hall's Marriage Theorem is true for all
`ι'` of cardinality ≤ `n`, then it is true for `ι` of cardinality `n + 1`.
-/
lemma hall_hard_inductive_step_B {n : ℕ} (hn : fintype.card ι = n + 1)
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card)
  (ih : ∀ {ι' : Type u} [fintype ι'] (t' : ι' → finset α),
        by exactI fintype.card ι' ≤ n →
                  (∀ (s' : finset ι'), s'.card ≤ (s'.bUnion t').card) →
                  ∃ (f : ι' → α), function.injective f ∧ ∀ x, f x ∈ t' x)
  (s : finset ι)
  (hs : s.nonempty)
  (hns : s ≠ univ)
  (hus : s.card = (s.bUnion t).card) :
  ∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x :=
begin
  haveI := classical.dec_eq ι,
  /- Restrict to `s` -/
  let t' : s → finset α := λ x', t x',
  rw nat.add_one at hn,
  have card_ι'_le : fintype.card s ≤ n,
  { apply nat.le_of_lt_succ,
    rw ←hn,
    convert (card_lt_iff_ne_univ _).mpr hns,
    convert fintype.card_coe _ },
  rcases ih t' card_ι'_le (hall_cond_of_restrict ht) with ⟨f', hf', hsf'⟩,
  /- Restrict to `sᶜ` in the domain and `(s.bUnion t)ᶜ` in the codomain. -/
  set ι'' := (s : set ι)ᶜ with ι''_def,
  let t'' : ι'' → finset α := λ a'', t a'' \ s.bUnion t,
  have card_ι''_le : fintype.card ι'' ≤ n,
  { apply nat.le_of_lt_succ,
    rw ←hn,
    convert (card_compl_lt_iff_nonempty _).mpr hs,
    convert fintype.card_coe (sᶜ),
    exact (finset.coe_compl s).symm },
  rcases ih t'' card_ι''_le (hall_cond_of_compl hus ht) with ⟨f'', hf'', hsf''⟩,
  /- Put them together -/
  have f'_mem_bUnion : ∀ {x'} (hx' : x' ∈ s), f' ⟨x', hx'⟩ ∈ s.bUnion t,
  { intros x' hx',
    rw mem_bUnion,
    exact ⟨x', hx', hsf' _⟩, },
  have f''_not_mem_bUnion : ∀ {x''} (hx'' : ¬ x'' ∈ s), ¬ f'' ⟨x'', hx''⟩ ∈ s.bUnion t,
  { intros x'' hx'',
    have h := hsf'' ⟨x'', hx''⟩,
    rw mem_sdiff at h,
    exact h.2, },
  have im_disj : ∀ {x' x'' : ι} {hx' : x' ∈ s} {hx'' : ¬x'' ∈ s}, f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩,
  { intros _ _ hx' hx'' h,
    apply f''_not_mem_bUnion hx'',
    rw ←h,
    apply f'_mem_bUnion, },
  refine ⟨λ x, if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, _, _⟩,
  { exact hf'.dite _ hf'' @im_disj },
  { intro x,
    split_ifs,
    { exact hsf' ⟨x, h⟩ },
    { exact sdiff_subset _ _ (hsf'' ⟨x, h⟩) } }
end

/--
If `ι` has cardinality `n + 1` and the statement of Hall's Marriage Theorem
is true for all `ι'` of cardinality ≤ `n`, then it is true for `ι`.
-/
theorem hall_hard_inductive_step {n : ℕ} (hn : fintype.card ι = n + 1)
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card)
  (ih : ∀ {ι' : Type u} [fintype ι'] (t' : ι' → finset α),
        by exactI fintype.card ι' ≤ n →
                  (∀ (s' : finset ι'), s'.card ≤ (s'.bUnion t').card) →
                  ∃ (f : ι' → α), function.injective f ∧ ∀ x, f x ∈ t' x) :
  ∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x :=
begin
  by_cases h : ∀ (s : finset ι), s.nonempty → s ≠ univ → s.card < (s.bUnion t).card,
  { exact hall_hard_inductive_step_A hn ht @ih h, },
  { push_neg at h,
    rcases h with ⟨s, sne, snu, sle⟩,
    have seq := nat.le_antisymm (ht _) sle,
    exact hall_hard_inductive_step_B hn ht @ih s sne snu seq, },
end

/--
Here we combine the base case and the inductive step into
a full strong induction proof, thus completing the proof
of the second direction.
-/
theorem hall_hard_inductive {n : ℕ} (hn : fintype.card ι = n)
  (ht : ∀ (s : finset ι), s.card ≤ (s.bUnion t).card) :
  ∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x :=
begin
  tactic.unfreeze_local_instances,
  revert ι,
  refine nat.strong_induction_on n (λ n' ih, _),
  intros _ _ t hn ht,
  rcases n' with (_|_),
  { exact hall_hard_inductive_zero t hn },
  { apply hall_hard_inductive_step hn ht,
    introsI ι' _ _ hι',
    exact ih (fintype.card ι') (nat.lt_succ_of_le hι') rfl, },
end

end hall_marriage_theorem

/--
This the version of **Hall's Marriage Theorem** in terms of indexed
families of finite sets `t : ι → finset α`.  It states that there is a
set of distinct representatives if and only if every union of `k` of the
sets has at least `k` elements.

Recall that `s.bUnion t` is the union of all the sets `t i` for `i ∈ s`.
-/
theorem finset.all_card_le_bUnion_card_iff_exists_injective
  {ι α : Type*} [fintype ι] [decidable_eq α] (t : ι → finset α) :
  (∀ (s : finset ι), s.card ≤ (s.bUnion t).card) ↔
    (∃ (f : ι → α), function.injective f ∧ ∀ x, f x ∈ t x) :=
begin
  split,
  { exact hall_marriage_theorem.hall_hard_inductive rfl },
  { rintro ⟨f, hf₁, hf₂⟩ s,
    rw ←card_image_of_injective s hf₁,
    apply card_le_of_subset,
    intro _,
    rw [mem_image, mem_bUnion],
    rintros ⟨x, hx, rfl⟩,
    exact ⟨x, hx, hf₂ x⟩, },
end

/-- Given a relation such that the image of every singleton set is finite, then the image of every
finite set is finite. -/
instance {α β : Type*} [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})]
  (A : finset α) : fintype (rel.image r A) :=
begin
  have h : rel.image r A = (A.bUnion (λ a, (rel.image r {a}).to_finset) : set β),
  { ext, simp [rel.image], },
  rw [h],
  apply finset_coe.fintype,
end

/--
This is a version of **Hall's Marriage Theorem** in terms of a relation
between types `α` and `β` such that `α` is finite and the image of
each `x : α` is finite (it suffices for `β` to be finite).  There is
an injective function `α → β` respecting the relation iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

If `[fintype β]`, then `[∀ (a : α), fintype (rel.image r {a})]` is automatically implied.
-/
theorem fintype.all_card_le_rel_image_card_iff_exists_injective
  {α β : Type*} [fintype α] [decidable_eq β]
  (r : α → β → Prop) [∀ (a : α), fintype (rel.image r {a})] :
  (∀ (A : finset α), A.card ≤ fintype.card (rel.image r A)) ↔
    (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x)) :=
begin
  let r' := λ a, (rel.image r {a}).to_finset,
  have h : ∀ (A : finset α), fintype.card (rel.image r A) = (A.bUnion r').card,
  { intro A,
    rw ←set.to_finset_card,
    apply congr_arg,
    ext b,
    simp [rel.image], },
  have h' : ∀ (f : α → β) x, r x (f x) ↔ f x ∈ r' x,
  { simp [rel.image], },
  simp only [h, h'],
  apply finset.all_card_le_bUnion_card_iff_exists_injective,
end

/--
This is a version of **Hall's Marriage Theorem** in terms of a relation between finite types.
There is an injective function `α → β` respecting the relation iff every subset of
`k` terms of `α` is related to at least `k` terms of `β`.

It is like `fintype.all_card_le_rel_image_card_iff_exists_injective` but uses `finset.filter`
rather than `rel.image`.
-/
theorem fintype.all_card_le_filter_rel_iff_exists_injective
  {α β : Type*} [fintype α] [fintype β]
  (r : α → β → Prop) [∀ a, decidable_pred (r a)] :
  (∀ (A : finset α), A.card ≤ (univ.filter (λ (b : β), ∃ a ∈ A, r a b)).card) ↔
    (∃ (f : α → β), function.injective f ∧ ∀ x, r x (f x)) :=
begin
  haveI := classical.dec_eq β,
  let r' := λ a, univ.filter (λ b, r a b),
  have h : ∀ (A : finset α), (univ.filter (λ (b : β), ∃ a ∈ A, r a b)) = (A.bUnion r'),
  { intro A,
    ext b,
    simp, },
  have h' : ∀ (f : α → β) x, r x (f x) ↔ f x ∈ r' x,
  { simp, },
  simp_rw [h, h'],
  apply finset.all_card_le_bUnion_card_iff_exists_injective,
end
