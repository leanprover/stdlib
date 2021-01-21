/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Yury Kudryashov
-/
import algebra.big_operators.order

/-!
# Pigeonhole principles

Given pigeons (possibly infinitely many) in pigeonholes, the
pigeonhole principle states that, if there are more pigeons than
pigeonholes, then there is a pigeonhole with two or more pigeons.

There are a few variations on this statement, and the conclusion can
be made stronger depending on how many pigeons you know you might
have.

The basic statements of the pigeonhole principle appear in the
following locations:

* `data.finset.basic` has `finset.exists_ne_map_eq_of_card_lt_of_maps_to`
* `data.fintype.basic` has `fintype.exists_ne_map_eq_of_card_lt`
* `data.fintype.basic` has `fintype.exists_ne_map_eq_of_infinite`
* `data.fintype.basic` has `fintype.exists_infinite_fiber`

This module gives access to these pigeonhole principles along with 20 more.
The versions vary by:

* using a function between `fintype`s or a function between possibly infinite types restricted to
  `finset`s;
* counting pigeons by a general weight function (`∑ x in s, w x`) or by heads (`finset.card s`);
* using strict or non-strict inequalities;
* establishing upper or lower estimate on the number (or the total weight) of the pigeons in one
  pigeonhole;
* in case when we count pigeons by some weight function `w` and consider a function `f` between
  `finset`s `s` and `t`, we can either assume that each pigeon is in one of the pigeonholes
  (`∀ x ∈ s, f x ∈ t`), or assume that for `y ∉ t`, the total weight of the pigeons in this
  pigeonhole `∑ x in s.filter (λ x, f x = y), w x` is nonpositive or nonnegative depending on
  the inequality we are proving.

Lemma names follow `mathlib` convention (e.g.,
`finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`); "pigeonhole principle" is mentioned in the
docstrings instead of the names.

## See also

* `ordinal.infinite_pigeonhole`: pigeonhole principle for cardinals, formulated using cofinality;

* `measure_theory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure`,
  `measure_theory.exists_nonempty_inter_of_measure_univ_lt_sum_measure`: pigeonhole principle in a
  measure space.

## Tags

pigeonhole principle
-/

universes u v w
variables {α : Type u} {β : Type v} {M : Type w} [linear_ordered_cancel_add_comm_monoid M]
  [decidable_eq β]

open_locale big_operators

namespace finset

variables {s : finset α} {t : finset β} {f : α → β} {w : α → M} {b : M} {n : ℕ}

/-!
### The pigeonhole principles on `finset`s, pigeons counted by weight

In this section we prove the following version of the pigeonhole principle: if the total weight of a
finite set of pigeons is greater than `n •ℕ b`, and they are sorted into `n` pigeonholes, then for
some pigeonhole, the total weight of the pigeons in this pigeonhole is greateer than `b`, and a few
variations of this theorem.

The principle is formalized in the following way, see
`finset.exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum`: if `f : α → β` is a function which maps all
elements of `s : finset α` to `t : finset β` and `card t •ℕ b < ∑ x in s, w x`, where `w : α → M` is
a weight function taking values in a `linear_ordered_cancel_add_comm_monoid`, then for
some `y ∈ t`, the sum of the weights of all `x ∈ s` such that `f x = y` is greater than `b`.

There are a few bits we can change in this theorem:

* reverse all inequalities, with obvious adjustments to the name;
* replace the assumption `∀ a ∈ s, f a ∈ t` with
  `∀ y ∉ t, (∑ x in s.filter (λ x, f x = y), w x) ≤ 0`,
  and replace `of_maps_to` with `of_sum_fiber_nonpos` in the name;
* use non-strict inequalities assuming `t` is nonempty.

We can do all these variations independently, so we have eight versions of the theorem.
-/

/-!
#### Strict inequality versions
-/

/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is greater than `n •ℕ b`, and they are sorted into
`n` pigeonholes, then for some pigeonhole, the total weight of the pigeons in this pigeonhole is
greater than `b`. -/
lemma exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (hf : ∀ a ∈ s, f a ∈ t)
  (hb : t.card •ℕ b < ∑ x in s, w x) :
  ∃ y ∈ t, b < ∑ x in s.filter (λ x, f x = y), w x :=
exists_lt_of_sum_lt $ by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is less than `n •ℕ b`, and they are sorted into `n`
pigeonholes, then for some pigeonhole, the total weight of the pigeons in this pigeonhole is less
than `b`. -/
lemma exists_sum_fiber_lt_of_maps_to_of_sum_lt_nsmul (hf : ∀ a ∈ s, f a ∈ t)
  (hb : (∑ x in s, w x) < t.card •ℕ b) :
  ∃ y ∈ t, (∑ x in s.filter (λ x, f x = y), w x) < b :=
@exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum α β (order_dual M) _ _ _ _ _ _ _ hf hb

/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is greater than `n •ℕ b`, they are sorted into some
pigeonholes, and for all but `n` pigeonholes the total weight of the pigeons there is nonpositive,
then for at least one of these `n` pigeonholes, the total weight of the pigeons in this pigeonhole
is greater than `b`. -/
lemma exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum
  (ht : ∀ y ∉ t, (∑ x in s.filter (λ x, f x = y), w x) ≤ 0) (hb : t.card •ℕ b < ∑ x in s, w x) :
  ∃ y ∈ t, b < ∑ x in s.filter (λ x, f x = y), w x :=
exists_lt_of_sum_lt $
calc (∑ y in t, b) < ∑ x in s, w x : by simpa
... ≤ ∑ y in t, ∑ x in s.filter (λ x, f x = y), w x :
  sum_le_sum_fiberwise_of_sum_fiber_nonpos ht

/-- The pigeonhole principle for finitely many pigeons counted by weight, strict inequality version:
if the total weight of a finite set of pigeons is less than `n •ℕ b`, they are sorted into some
pigeonholes, and for all but `n` pigeonholes the total weight of the pigeons there is nonnegative,
then for at least one of these `n` pigeonholes, the total weight of the pigeons in this pigeonhole
is less than `b`. -/
lemma exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul
  (ht : ∀ y ∉ t, (0:M) ≤ ∑ x in s.filter (λ x, f x = y), w x) (hb : (∑ x in s, w x) < t.card •ℕ b) :
  ∃ y ∈ t, (∑ x in s.filter (λ x, f x = y), w x) < b :=
@exists_lt_sum_fiber_of_sum_fiber_nonpos_of_nsmul_lt_sum α β (order_dual M) _ _ _ _ _ _ _ ht hb

/-!
#### Non-strict inequality versions
-/

/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is greater than or equal to `n •ℕ b`, and
they are sorted into `n > 0` pigeonholes, then for some pigeonhole, the total weight of the pigeons
in this pigeonhole is greater than or equal to `b`. -/
lemma exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (hf : ∀ a ∈ s, f a ∈ t) (ht : t.nonempty)
  (hb : t.card •ℕ b ≤ ∑ x in s, w x) :
  ∃ y ∈ t, b ≤ ∑ x in s.filter (λ x, f x = y), w x :=
exists_le_of_sum_le ht $ by simpa only [sum_fiberwise_of_maps_to hf, sum_const]

/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is less than or equal to `n •ℕ b`, and they
are sorted into `n > 0` pigeonholes, then for some pigeonhole, the total weight of the pigeons in
this pigeonhole is less than or equal to `b`. -/
lemma exists_sum_fiber_le_of_maps_to_of_sum_le_nsmul (hf : ∀ a ∈ s, f a ∈ t) (ht : t.nonempty)
  (hb : (∑ x in s, w x) ≤ t.card •ℕ b) :
  ∃ y ∈ t, (∑ x in s.filter (λ x, f x = y), w x) ≤ b :=
@exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum α β (order_dual M) _ _ _ _ _ _ _ hf ht hb

/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is greater than or equal to `n •ℕ b`, they
are sorted into some pigeonholes, and for all but `n > 0` pigeonholes the total weight of the
pigeons there is nonpositive, then for at least one of these `n` pigeonholes, the total weight of
the pigeons in this pigeonhole is greater than or equal to `b`. -/
lemma exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum
  (hf : ∀ y ∉ t, (∑ x in s.filter (λ x, f x = y), w x) ≤ 0) (ht : t.nonempty)
  (hb : t.card •ℕ b ≤ ∑ x in s, w x) :
  ∃ y ∈ t, b ≤ ∑ x in s.filter (λ x, f x = y), w x :=
exists_le_of_sum_le ht $
calc (∑ y in t, b) ≤ ∑ x in s, w x : by simpa
... ≤ ∑ y in t, ∑ x in s.filter (λ x, f x = y), w x :
  sum_le_sum_fiberwise_of_sum_fiber_nonpos hf

/-- The pigeonhole principle for finitely many pigeons counted by weight, non-strict inequality
version: if the total weight of a finite set of pigeons is less than or equal to `n •ℕ b`, they are
sorted into some pigeonholes, and for all but `n > 0` pigeonholes the total weight of the pigeons
there is nonnegative, then for at least one of these `n` pigeonholes, the total weight of the
pigeons in this pigeonhole is less than or equal to `b`. -/
lemma exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul
  (hf : ∀ y ∉ t, (0:M) ≤ ∑ x in s.filter (λ x, f x = y), w x) (ht : t.nonempty)
  (hb : (∑ x in s, w x) ≤ t.card •ℕ b) :
  ∃ y ∈ t, (∑ x in s.filter (λ x, f x = y), w x) ≤ b :=
@exists_le_sum_fiber_of_sum_fiber_nonpos_of_nsmul_le_sum α β (order_dual M) _ _ _ _ _ _ _ hf ht hb

/-!
### The pigeonhole principles on `finset`s, pigeons counted by heads

In this section we formalize a few versions of the following pigeonhole principle: there is a
pigeonhole with at least as many pigeons as the ceiling of the average number of pigeons across all
pigeonholes.

First, we can use strict or non-strict inequalities. While the versions with non-strict inequalities
are weaker than those with strict inequalities, sometimes it might be more convenient to apply the
weaker version. Second, we can either state that there exists a pigeonhole with at least `n`
pigeons, or state that there exists a pigeonhole with at most `n` pigeons. In the latter case we do
not need the assumption `∀ a ∈ s, f a ∈ t`.

So, we prove four theorems: `finset.exists_lt_card_fiber_of_maps_to_of_mul_lt_card`,
`finset.exists_le_card_fiber_of_maps_to_of_mul_le_card`,
`finset.exists_card_fiber_lt_of_card_lt_mul`, and `finset.exists_card_fiber_le_of_card_le_mul`. -/

/-- The pigeonhole principle for finitely many pigeons counted by heads: there is a pigeonhole with
at least as many pigeons as the ceiling of the average number of pigeons across all pigeonholes.
("The maximum is at least the mean" specialized to integers.)

More formally, given a function between finite sets `s` and `t` and a natural number `n` such that
`card t * n < card s`, there exists `y ∈ t` such that its preimage in `s` has more than `n`
elements. -/
lemma exists_lt_card_fiber_of_mul_lt_card_of_maps_to (hf : ∀ a ∈ s, f a ∈ t)
  (hn : t.card * n < s.card) :
  ∃ y ∈ t, n < (s.filter (λ x, f x = y)).card :=
begin
  simp only [card_eq_sum_ones],
  apply exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum hf,
  simpa
end

/-- The pigeonhole principle for finitely many pigeons counted by heads: there is a pigeonhole with
at most as many pigeons as the floor of the average number of pigeons across all pigeonholes.  ("The
minimum is at most the mean" specialized to integers.)

More formally, given a function `f`, a finite sets `s` in its domain, a finite set `t` in its
codomain, and a natural number `n` such that `card s < card t * n`, there exists `y ∈ t` such that
its preimage in `s` has less than `n` elements. -/
lemma exists_card_fiber_lt_of_card_lt_mul (hn : s.card < t.card * n) :
  ∃ y ∈ t, (s.filter (λ x, f x = y)).card < n:=
begin
  simp only [card_eq_sum_ones],
  apply exists_sum_fiber_lt_of_sum_fiber_nonneg_of_sum_lt_nsmul (λ _ _, nat.zero_le _),
  simpa
end

/-- The pigeonhole principle for finitely many pigeons counted by heads: given a function between
finite sets `s` and `t` and a natural number `n` such that `card t * n ≤ card s`, there exists `y ∈
t` such that its preimage in `s` has at least `n` elements. See also
`finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to` for a stronger statement. -/
lemma exists_le_card_fiber_of_mul_le_card_of_maps_to (hf : ∀ a ∈ s, f a ∈ t) (ht : t.nonempty)
  (hn : t.card * n ≤ s.card) :
  ∃ y ∈ t, n ≤ (s.filter (λ x, f x = y)).card :=
begin
  simp only [card_eq_sum_ones],
  apply exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum hf ht,
  simpa
end

/-- The pigeonhole principle for finitely many pigeons counted by heads: given a function `f`, a
finite sets `s` in its domain, a finite set `t` in its codomain, and a natural number `n` such that
`card s ≤ card t * n`, there exists `y ∈ t` such that its preimage in `s` has no more than `n`
elements. See also `finset.exists_card_fiber_lt_of_card_lt_mul` for a stronger statement. -/
lemma exists_card_fiber_le_of_card_le_mul (ht : t.nonempty) (hn : s.card ≤ t.card * n) :
  ∃ y ∈ t, (s.filter (λ x, f x = y)).card ≤ n:=
begin
  simp only [card_eq_sum_ones],
  apply exists_sum_fiber_le_of_sum_fiber_nonneg_of_sum_le_nsmul (λ _ _, nat.zero_le _) ht,
  simpa
end

end finset

namespace fintype
open finset

variables [fintype α] [fintype β] (f : α → β) {w : α → M} {b : M} {n : ℕ}

/-!
### The pigeonhole principles on `fintypes`s, pigeons counted by weight

In this section we specialize theorems from the previous section to the special case of functions
between `fintype`s and `s = univ`, `t = univ`. In this case the assumption `∀ x ∈ s, f x ∈ t` always
holds, so we have four theorems instead of eight. -/

/-- The pigeonhole principle for finitely many pigeons of different weights, strict inequality
version: there is a pigeonhole with the total weight of pigeons in it greater than `b` provided that
the total number of pigeonholes times `b` is less than the total weight of all pigeons. -/
lemma exists_lt_sum_fiber_of_nsmul_lt_sum (hb : card β •ℕ b < ∑ x, w x) :
  ∃ y, b < ∑ x in univ.filter (λ x, f x = y), w x :=
let ⟨y, _, hy⟩ := exists_lt_sum_fiber_of_maps_to_of_nsmul_lt_sum (λ _ _, mem_univ _) hb in ⟨y, hy⟩

/-- The pigeonhole principle for finitely many pigeons of different weights, non-strict inequality
version: there is a pigeonhole with the total weight of pigeons in it greater than or equal to `b`
provided that the total number of pigeonholes times `b` is less than or equal to the total weight of
all pigeons. -/
lemma exists_le_sum_fiber_of_nsmul_le_sum [nonempty β] (hb : card β •ℕ b ≤ ∑ x, w x) :
  ∃ y, b ≤ ∑ x in univ.filter (λ x, f x = y), w x :=
let ⟨y, _, hy⟩ :=
  exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum (λ _ _, mem_univ _) univ_nonempty hb
in ⟨y, hy⟩

/-- The pigeonhole principle for finitely many pigeons of different weights, strict inequality
version: there is a pigeonhole with the total weight of pigeons in it less than `b` provided that
the total number of pigeonholes times `b` is greater than the total weight of all pigeons. -/
lemma exists_sum_fiber_lt_of_sum_lt_nsmul (hb : (∑ x, w x) < card β •ℕ b) :
  ∃ y, (∑ x in univ.filter (λ x, f x = y), w x) < b :=
@exists_lt_sum_fiber_of_nsmul_lt_sum α β (order_dual M) _ _ _ _ _ w b hb

/-- The pigeonhole principle for finitely many pigeons of different weights, non-strict inequality
version: there is a pigeonhole with the total weight of pigeons in it less than or equal to `b`
provided that the total number of pigeonholes times `b` is greater than or equal to the total weight
of all pigeons. -/
lemma exists_sum_fiber_le_of_sum_le_nsmul [nonempty β] (hb : (∑ x, w x) ≤ card β •ℕ b) :
  ∃ y, (∑ x in univ.filter (λ x, f x = y), w x) ≤ b :=
@exists_le_sum_fiber_of_nsmul_le_sum α β (order_dual M) _ _ _ _ _ w b _ hb

/--
The strong pigeonhole principle for finitely many pigeons and pigeonholes.
There is a pigeonhole with at least as many pigeons as
the ceiling of the average number of pigeons across all pigeonholes.
("The maximum is at least the mean" specialized to integers.)

More formally, given a function `f` between finite types `α` and `β` and a number `n` such that
`card β * n < card α`, there exists an element `y : β` such that its preimage has more than `n`
elements. -/
lemma exists_lt_card_fiber_of_mul_lt_card (hn : card β * n < card α) :
  ∃ y : β, n < (univ.filter (λ x, f x = y)).card :=
let ⟨y, _, h⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to (λ _ _, mem_univ _) hn in ⟨y, h⟩

/--
The strong pigeonhole principle for finitely many pigeons and pigeonholes.
There is a pigeonhole with at most as many pigeons as
the floor of the average number of pigeons across all pigeonholes.
("The minimum is at most the mean" specialized to integers.)

More formally, given a function `f` between finite types `α` and `β` and a number `n` such that
`card α < card β * n`, there exists an element `y : β` such that its preimage has less than `n`
elements. -/
lemma exists_card_fiber_lt_of_card_lt_mul (hn : card α < card β * n) :
  ∃ y : β, (univ.filter (λ x, f x = y)).card < n :=
let ⟨y, _, h⟩ := exists_card_fiber_lt_of_card_lt_mul hn in ⟨y, h⟩

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.  Given a function `f`
between finite types `α` and `β` and a number `n` such that `card β * n ≤ card α`, there exists an
element `y : β` such that its preimage has at least `n` elements. See also
`fintype.exists_lt_card_fiber_of_mul_lt_card` for a stronger statement. -/
lemma exists_le_card_fiber_of_mul_le_card [nonempty β] (hn : card β * n ≤ card α) :
  ∃ y : β, n ≤ (univ.filter (λ x, f x = y)).card :=
let ⟨y, _, h⟩ := exists_le_card_fiber_of_mul_le_card_of_maps_to (λ _ _, mem_univ _) univ_nonempty hn
in ⟨y, h⟩

/-- The strong pigeonhole principle for finitely many pigeons and pigeonholes.  Given a function `f`
between finite types `α` and `β` and a number `n` such that `card α ≤ card β * n`, there exists an
element `y : β` such that its preimage has at most `n` elements. See also
`fintype.exists_card_fiber_lt_of_card_lt_mul` for a stronger statement. -/
lemma exists_card_fiber_le_of_card_le_mul [nonempty β] (hn : card α ≤ card β * n) :
  ∃ y : β, (univ.filter (λ x, f x = y)).card ≤ n :=
let ⟨y, _, h⟩ := exists_card_fiber_le_of_card_le_mul univ_nonempty hn in ⟨y, h⟩

end fintype
