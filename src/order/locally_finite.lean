/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice
import data.finset.preimage
import data.finset.sort
import data.set.finite
import data.set.intervals.basic
import data.int.basic

/-!
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

## Main declarations

In a `locally_finite_order`,
* `finset.` `Icc`/`Ico`/`Ioc`/`Ioo`: Closed/open-closed/open interval as a finset.
* `finset.` `Ici`/`Ioi`: Closed/open-infinite interval as a finset if the order is also an
  `order_top`.
* `finset.` `Iic`/`Iio`: Infinite-closed/open interval as a finset if the order is also an
  `order_bot`.

## Instances

We provide a `locally_finite_order` instance for
* ℕ, see `nat.locally_finite_order`
* ℤ, see `int.locally_finite_order`
* a subtype of a locally finite order
* any fintype (but it is noncomputable), see `fintype.locally_finite_order`

## TODO

TODO: All the API in `set.intervals.basic` could be copied here. But this is unfortunately labor-
and maintenance-intensive.

TODO:nce we have the `has_enum` typeclass (any non-top element has a least greater element or any
non-bot element has a greatest lesser element), we can provide an `has_enum` typeclass using

```lean
lemma exists_min_greater [linear_order α] [locally_finite_order α] {x ub : α} (hx : x < ub) :
  ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y :=
begin -- very non golfed
  have h : (finset.Ioc x ub).nonempty := ⟨ub, finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩⟩,
  use finset.min' (finset.Ioc x ub) h,
  split,
  { have := finset.min'_mem _ h,
    simp * at * },
  rintro y hxy,
  obtain hy | hy := le_total y ub,
  apply finset.min'_le,
  simp * at *,
  exact (finset.min'_le _ _ (finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩)).trans hy,
end
```

Note that the converse is not true. Consider `{-2^z | z : ℤ} ∪ {2^z | z : ℤ}`. Any element has a
least greater element and a greatest lesser element, so it `has_enum` (both ways!), but it's not
locally finite as `Icc (-1) 1` is infinite.

TODO: From `linear_order α`, `no_top_order α`, `locally_finite_order α`, we can also define an
order isomorphism `α ≃ ℕ` or `α ≃ ℤ`, depending on whether we have `order_bot α` or
`no_bot_order α` and `nonempty α`. When `order_bot α`, we can match `a : α` to `(Iio a).card`.
-/

open finset

class locally_finite_order (α : Type*) [preorder α] :=
(finset_Icc : α → α → finset α)
(coe_finset_Icc : ∀ a b : α, (finset_Icc a b : set α) = set.Icc a b)

namespace set
variables {α : Type*} [preorder α] [locally_finite_order α]

lemma Icc_finite (a b : α) : (Icc a b).finite :=
begin
  rw ←locally_finite_order.coe_finset_Icc,
  exact (locally_finite_order.finset_Icc a b).finite_to_set,
end

lemma Ico_finite (a b : α) : (Ico a b).finite :=
(Icc_finite a b).subset Ico_subset_Icc_self

lemma Ioc_finite (a b : α) : (Ioc a b).finite :=
(Icc_finite a b).subset Ioc_subset_Icc_self

lemma Ioo_finite (a b : α) : (Ioo a b).finite :=
(Icc_finite a b).subset Ioo_subset_Icc_self

end set

/-! ### Intervals as finsets -/

namespace finset
section preorder
variables {α : Type*} [decidable_eq α] [preorder α] [locally_finite_order α]

/-- The finset of elements `x` such that `a ≤ x ∧ x ≤ b`. Basically `set.Icc a b` as a finset. -/
def Icc (a b : α) : finset α :=
locally_finite_order.finset_Icc a b

/-- The finset of elements `x` such that `a ≤ x ∧ x < b`. Basically `set.Ico a b` as a finset. -/
def Ico (a b : α) : finset α :=
(Icc a b).erase b

/-- The finset of elements `x` such that `a < x ∧ x ≤ b`. Basically `set.Ioc a b` as a finset. -/
def Ioc (a b : α) : finset α :=
(Icc a b).erase a

/-- The finset of elements `x` such that `a < x ∧ x < b`. Basically `set.Ioo a b` as a finset. -/
def Ioo (a b : α) : finset α :=
(Ioc a b).erase b

/- `Icc` is treated separately from `Ico`, `Ioc`, `Ioo` because it allows to relax `partial_order`
to `preorder` in simple constructions, eg `subtype.locally_finite_order`. -/
@[simp] lemma coe_Icc (a b : α) : (Icc a b : set α) = set.Icc a b :=
locally_finite_order.coe_finset_Icc a b

@[simp] lemma mem_Icc_iff {a b x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
by rw [←set.mem_Icc, ←coe_Icc, mem_coe]

end preorder

section partial_order
variables {α : Type*} [decidable_eq α] [partial_order α] [locally_finite_order α]

@[simp] lemma coe_Ico (a b : α) : (Ico a b : set α) = set.Ico a b :=
by rw [Ico, coe_erase, coe_Icc, set.Icc_diff_right]

@[simp] lemma coe_Ioc (a b : α) : (Ioc a b : set α) = set.Ioc a b :=
by rw [Ioc, coe_erase, coe_Icc, set.Icc_diff_left]

@[simp] lemma coe_Ioo (a b : α) : (Ioo a b : set α) = set.Ioo a b :=
by rw [Ioo, coe_erase, coe_Ioc, set.Ioc_diff_right]

@[simp] lemma mem_Ico_iff {a b x : α} : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
by rw [←set.mem_Ico, ←coe_Ico, mem_coe]

@[simp] lemma mem_Ioc_iff {a b x : α} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
by rw [←set.mem_Ioc, ←coe_Ioc, mem_coe]

@[simp] lemma mem_Ioo_iff {a b x : α} : x ∈ Ioo a b ↔ a < x ∧ x < b :=
by rw [←set.mem_Ioo, ←coe_Ioo, mem_coe]

end partial_order

section order_top
variables {α : Type*} [decidable_eq α] [order_top α] [locally_finite_order α]

/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a finset. -/
def Ici (a : α) : finset α :=
Icc a ⊤

/-- The finset of elements `x` such that `a < x`. Basically `set.Ioi a` as a finset. -/
def Ioi (a : α) : finset α :=
Ioc a ⊤

@[simp] lemma coe_Ici (a : α) : (Ici a : set α) = set.Ici a :=
by rw [Ici, coe_Icc, set.Icc_top]

@[simp] lemma coe_Ioi (a : α) : (Ioi a : set α) = set.Ioi a :=
by rw [Ioi, coe_Ioc, set.Ioc_top]

@[simp] lemma mem_Ici_iff {a x : α} : x ∈ Ici a ↔ a ≤ x :=
by rw [←set.mem_Ici, ←coe_Ici, mem_coe]

@[simp] lemma mem_Ioi_iff {a x : α} : x ∈ Ioi a ↔ a < x :=
by rw [←set.mem_Ioi, ←coe_Ioi, mem_coe]

end order_top

section order_bot
variables {α : Type*} [decidable_eq α] [order_bot α] [locally_finite_order α]

/-- The finset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a finset. -/
def Iic (b : α) : finset α :=
Icc ⊥ b

/-- The finset of elements `x` such that `x < b`. Basically `set.Iio b` as a finset. -/
def Iio (b : α) : finset α :=
Ico ⊥ b

@[simp] lemma coe_Iic (b : α) : (Iic b : set α) = set.Iic b :=
by rw [Iic, coe_Icc, set.Icc_bot]

@[simp] lemma coe_Iio (b : α) : (Iio b : set α) = set.Iio b :=
by rw [Iio, coe_Ico, set.Ico_bot]

@[simp] lemma mem_Iic_iff {b x : α} : x ∈ Iic b ↔ x ≤ b :=
by rw [←set.mem_Iic, ←coe_Iic, mem_coe]

@[simp] lemma mem_Iio_iff {b x : α} : x ∈ Iio b ↔ x < b :=
by rw [←set.mem_Iio, ←coe_Iio, mem_coe]

end order_bot

end finset

open finset

/-! ### Instances -/

noncomputable def locally_finite_order_of_finite_Icc {α : Type*} [preorder α]
  (h : ∀ x y : α, (set.Icc x y).finite) :
  locally_finite_order α :=
{ finset_Icc := λ x y, (h x y).to_finset,
  coe_finset_Icc := λ x y, (h x y).coe_to_finset }

@[priority 900]
noncomputable instance fintype.locally_finite_order {α : Type*} [preorder α] [fintype α] :
  locally_finite_order α :=
{ finset_Icc := λ a b, (set.finite.of_fintype (set.Icc a b)).to_finset,
  coe_finset_Icc := λ a b, set.finite.coe_to_finset _ }

-- Should this be called `order_embedding.locally_finite_order`?
/-- Given an order embedding `α ↪o β`, pulls back to `α` the `locally_finite_order` on `β`. -/
noncomputable def locally_finite_order.lift {α β : Type*} [partial_order β] [locally_finite_order β]
  [decidable_eq β] [partial_order α] [decidable_eq α] (f : α ↪o β) :
  locally_finite_order α :=
{ finset_Icc := λ a b, (Icc (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  coe_finset_Icc := λ a b, begin
    ext,
    simp only [coe_Icc, coe_preimage, iff_self, set.mem_preimage, set.mem_Icc,
      order_embedding.le_iff_le],
  end }

instance subtype.locally_finite_order {α : Type*} [preorder α] [locally_finite_order α]
  [decidable_eq α] {p : α → Prop} [decidable_pred p] :
  locally_finite_order (subtype p) :=
begin
  haveI : preorder (subtype p) := by apply_instance,
  haveI : decidable_eq (subtype p) := by apply_instance,
  exact
  { finset_Icc := λ a b, finset.subtype p (Icc a.val b.val),
    coe_finset_Icc := λ a b, begin
      ext,
      rw [finset.subtype, coe_map, set.mem_image, set.mem_Icc],
      dsimp,
      split,
      { rintro ⟨⟨y, hy⟩, -, h⟩,
        rw [←h, ←subtype.coe_le_coe, ←subtype.coe_le_coe],
        rw [mem_filter, mem_Icc_iff] at hy,
        exact hy.1 },
      rintro hx,
      refine ⟨⟨x, _⟩, mem_coe.2 (mem_attach _ _), _⟩,
      { rw [mem_filter, mem_Icc_iff, subtype.coe_le_coe, subtype.coe_le_coe],
        exact ⟨hx, x.2⟩ },
      simp only [subtype.coe_eta, subtype.coe_mk],
    end },
end

instance nat.locally_finite_order : locally_finite_order ℕ :=
{ finset_Icc := λ a b, (list.range' a (b + 1 - a)).to_finset,
  coe_finset_Icc := λ a b, begin
    ext,
    rw [mem_coe, list.mem_to_finset, list.mem_range', set.mem_Icc],
    cases le_or_lt a b,
    { rw [nat.add_sub_cancel' (nat.lt_succ_of_le h).le, nat.lt_succ_iff] },
    rw [nat.sub_eq_zero_iff_le.2 h, add_zero],
    exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2)),
end }

instance int.locally_finite_order : locally_finite_order ℤ :=
{ finset_Icc := λ a b, (Iio (b + 1 - a).to_nat).map ⟨λ n, n + a, λ _, by simp only
  [imp_self, forall_const, add_left_inj, int.coe_nat_inj']⟩,
  coe_finset_Icc := λ a b, begin
    ext,
    rw [mem_coe, mem_map, set.mem_Icc, function.embedding.coe_fn_mk],
    split,
    { rintro ⟨n, hn, hx⟩,
      rw [←hx, le_add_iff_nonneg_left],
      rw [mem_Iio_iff, int.lt_to_nat, lt_sub_iff_add_lt, int.lt_add_one_iff] at hn,
      exact ⟨int.coe_nat_nonneg _, hn⟩ },
    rintro h,
    refine ⟨(x - a).to_nat, _, by rw [int.to_nat_sub_of_le h.1, int.sub_add_cancel]⟩,
    rw mem_Iio_iff,
    have hb := int.lt_add_one_of_le h.2,
    exact (int.to_nat_lt_to_nat (sub_pos.2 (h.1.trans_lt hb))).2 (sub_lt_sub_right hb _),
  end }
