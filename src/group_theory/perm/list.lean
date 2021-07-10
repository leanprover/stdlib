/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.list.rotate
import group_theory.perm.support

/-!
# Permutations from a list

A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.

When there are duplicate elements in `l`, how and in what arrangement with respect to the other
elements they appear in the list determines the formed permutation.
This is because `list.form_perm` is implemented as a product of `equiv.swap`s.
That means that presence of a sublist of two adjacent duplicates like `[..., x, x, ...]`
will produce the same permutation as if the adjacent duplicates were not present.

The `list.form_perm` definition is meant to primarily be used with `nodup l`, so that
the resulting permutation is cyclic (if `l` has at least two elements).
The presence of duplicates in a particular placement can lead `list.form_perm` to produce a
nontrivial permutation that is noncyclic.
-/

namespace list

variables {α β : Type*}

section form_perm

variables [decidable_eq α] (l : list α)

open equiv equiv.perm

/--
A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.
-/
def form_perm : equiv.perm α :=
(zip_with equiv.swap l l.tail).prod

@[simp] lemma form_perm_nil : form_perm ([] : list α) = 1 := rfl

@[simp] lemma form_perm_singleton (x : α) : form_perm [x] = 1 := rfl

@[simp] lemma form_perm_cons_cons (x y : α) (l : list α) :
  form_perm (x :: y :: l) = swap x y * form_perm (y :: l) :=
prod_cons

lemma form_perm_pair (x y : α) : form_perm [x, y] = swap x y := rfl

lemma form_perm_apply_of_not_mem (x : α) (l : list α) (h : x ∉ l) :
  form_perm l x = x :=
begin
  cases l with y l,
  { simp },
  induction l with z l IH generalizing x y,
  { simp },
  { specialize IH x z (mt (mem_cons_of_mem y) h),
    simp only [not_or_distrib, mem_cons_iff] at h,
    simp [IH, swap_apply_of_ne_of_ne, h] }
end

lemma form_perm_apply_mem_of_mem (x : α) (l : list α) (h : x ∈ l) :
  form_perm l x ∈ l :=
begin
  cases l with y l,
  { simpa },
  induction l with z l IH generalizing x y,
  { simpa using h },
  { by_cases hx : x ∈ z :: l,
    { rw [form_perm_cons_cons, mul_apply, swap_apply_def],
      split_ifs;
      simp [IH _ _ hx] },
    { replace h : x = y := or.resolve_right h hx,
      simp [form_perm_apply_of_not_mem _ _ hx, ←h] } }
end

@[simp] lemma form_perm_cons_concat_apply_last (x y : α) (xs : list α) :
  form_perm (x :: (xs ++ [y])) y = x :=
begin
  induction xs with z xs IH generalizing x y,
  { simp },
  { simp [IH] }
end

@[simp] lemma form_perm_apply_last (x : α) (xs : list α) :
  form_perm (x :: xs) ((x :: xs).last (cons_ne_nil x xs)) = x :=
begin
  induction xs using list.reverse_rec_on with xs y IH generalizing x;
  simp
end

@[simp] lemma form_perm_apply_nth_le_length (x : α) (xs : list α) :
  form_perm (x :: xs) ((x :: xs).nth_le xs.length (by simp)) = x :=
by rw [nth_le_cons_length, form_perm_apply_last]

lemma form_perm_apply_head (x y : α) (xs : list α) (h : nodup (x :: y :: xs)) :
  form_perm (x :: y :: xs) x = y :=
by simp [form_perm_apply_of_not_mem _ _ (not_mem_of_nodup_cons h)]

lemma form_perm_apply_nth_le_zero (l : list α) (h : nodup l) (hl : 1 < l.length) :
  form_perm l (l.nth_le 0 (zero_lt_one.trans hl)) = l.nth_le 1 hl :=
begin
  rcases l with (_|⟨x, _|⟨y, tl⟩⟩),
  { simp },
  { simp },
  { simpa using form_perm_apply_head _ _ _ h }
end

lemma form_perm_eq_head_iff_eq_last (x y : α) :
  form_perm (y :: l) x = y ↔ x = last (y :: l) (cons_ne_nil _ _) :=
iff.trans (by rw form_perm_apply_last) (form_perm (y :: l)).injective.eq_iff

lemma zip_with_swap_prod_support' (l l' : list α) :
  {x | (zip_with swap l l').prod x ≠ x} ≤ l.to_finset ⊔ l'.to_finset :=
begin
  simp only [set.sup_eq_union, set.le_eq_subset],
  induction l with y l hl generalizing l',
  { simp },
  { cases l' with z l',
    { simp },
    { intro x,
      simp only [set.union_subset_iff, mem_cons_iff, zip_with_cons_cons, foldr, prod_cons,
                 mul_apply],
      intro hx,
      by_cases h : x ∈ {x | (zip_with swap l l').prod x ≠ x},
      { specialize hl l' h,
        refine set.mem_union.elim hl (λ hm, _) (λ hm, _);
        { simp only [finset.coe_insert, set.mem_insert_iff, finset.mem_coe, to_finset_cons,
                     mem_to_finset] at hm ⊢,
          simp [hm] } },
      { simp only [not_not, set.mem_set_of_eq] at h,
        simp only [h, set.mem_set_of_eq] at hx,
        rw swap_apply_ne_self_iff at hx,
        rcases hx with ⟨hyz, rfl|rfl⟩;
        simp } } }
end

lemma zip_with_swap_prod_support [fintype α] (l l' : list α) :
  (zip_with swap l l').prod.support ≤ l.to_finset ⊔ l'.to_finset :=
begin
  intros x hx,
  have hx' : x ∈ {x | (zip_with swap l l').prod x ≠ x} := by simpa using hx,
  simpa using zip_with_swap_prod_support' _ _ hx'
end

lemma support_form_perm_le' : {x | form_perm l x ≠ x} ≤ l.to_finset :=
begin
  refine (zip_with_swap_prod_support' l l.tail).trans _,
  simpa [finset.subset_iff] using tail_subset l
end

lemma support_form_perm_le [fintype α] : support (form_perm l) ≤ l.to_finset :=
begin
  intros x hx,
  have hx' : x ∈ {x | form_perm l x ≠ x} := by simpa using hx,
  simpa using support_form_perm_le' _ hx'
end

lemma form_perm_apply_lt (xs : list α) (h : nodup xs) (n : ℕ) (hn : n + 1 < xs.length) :
  form_perm xs (xs.nth_le n ((nat.lt_succ_self n).trans hn)) = xs.nth_le (n + 1) hn :=
begin
  induction n with n IH generalizing xs,
  { simpa using form_perm_apply_nth_le_zero _ h _ },
  { rcases xs with (_|⟨x, _|⟨y, l⟩⟩),
    { simp },
    { simp },
    { specialize IH (y :: l) (nodup_of_nodup_cons h) _,
      { simpa [nat.succ_lt_succ_iff] using hn },
      simp only [swap_apply_eq_iff, coe_mul, form_perm_cons_cons, nth_le],
      generalize_proofs at IH,
      rw [IH, swap_apply_of_ne_of_ne, nth_le];
      { rintro rfl,
        simpa [nth_le_mem _ _ _] using h } } }
end

lemma form_perm_apply_nth_le (xs : list α) (h : nodup xs) (n : ℕ) (hn : n < xs.length) :
  form_perm xs (xs.nth_le n hn) = xs.nth_le ((n + 1) % xs.length)
    (nat.mod_lt _ (n.zero_le.trans_lt hn)) :=
begin
  cases xs with x xs,
  { simp },
  { have : n ≤ xs.length,
    { refine nat.le_of_lt_succ _,
      simpa using hn },
    rcases this.eq_or_lt with rfl|hn',
    { simp },
    { simp [form_perm_apply_lt, h, nat.mod_eq_of_lt, nat.succ_lt_succ hn'] } }
end

lemma support_form_perm_of_nodup' (l : list α) (h : nodup l) (h' : ∀ (x : α), l ≠ [x]) :
  {x | form_perm l x ≠ x} = l.to_finset :=
begin
  apply le_antisymm,
  { exact support_form_perm_le' l },
  { intros x hx,
    simp only [finset.mem_coe, mem_to_finset] at hx,
    obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx,
    rw [set.mem_set_of_eq, form_perm_apply_nth_le _ h],
    intro H,
    rw nodup_iff_nth_le_inj at h,
    specialize h _ _ _ _ H,
    cases (nat.succ_le_of_lt hn).eq_or_lt with hn' hn',
    { simp only [←hn', nat.mod_self] at h,
      refine not_exists.mpr h' _,
      simpa [←h, eq_comm, length_eq_one] using hn' },
    { simpa [nat.mod_eq_of_lt hn'] using h } }
end

lemma support_form_perm_of_nodup [fintype α] (l : list α) (h : nodup l) (h' : ∀ (x : α), l ≠ [x]) :
  support (form_perm l) = l.to_finset :=
begin
  rw ←finset.coe_inj,
  convert support_form_perm_of_nodup' _ h h',
  simp [set.ext_iff]
end

lemma form_perm_rotate_one (l : list α) (h : nodup l) :
  form_perm (l.rotate 1) = form_perm l :=
begin
  have h' : nodup (l.rotate 1),
  { simpa using h },
  by_cases hl : ∀ (x : α), l ≠ [x],
  { have hl' : ∀ (x : α), l.rotate 1 ≠ [x],
    { intro,
      rw [ne.def, rotate_eq_iff],
      simpa using hl _ },
    ext x,
    by_cases hx : x ∈ l.rotate 1,
    { obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
      rw [form_perm_apply_nth_le _ h', nth_le_rotate l, nth_le_rotate l,
        form_perm_apply_nth_le _ h],
      simp },
    { rw [form_perm_apply_of_not_mem _ _ hx, form_perm_apply_of_not_mem],
      simpa using hx } },
  { push_neg at hl,
    obtain ⟨x, rfl⟩ := hl,
    simp }
end

lemma form_perm_rotate (l : list α) (h : nodup l) (n : ℕ) :
  form_perm (l.rotate n) = form_perm l :=
begin
  induction n with n hn,
  { simp },
  { rw [nat.succ_eq_add_one, ←rotate_rotate, form_perm_rotate_one, hn],
    rwa is_rotated.nodup_iff,
    exact is_rotated.forall l n }
end

lemma form_perm_eq_of_is_rotated {l l' : list α} (hd : nodup l) (h : l ~r l') :
  form_perm l = form_perm l' :=
begin
  obtain ⟨n, rfl⟩ := h,
  exact (form_perm_rotate l hd n).symm
end

lemma form_perm_reverse (l : list α) (h : nodup l) :
  form_perm l.reverse = (form_perm l)⁻¹ :=
begin
  -- Let's show `form_perm l` is an inverse to `form_perm l.reverse`.
  rw [eq_comm, inv_eq_iff_mul_eq_one],
  ext x,
  -- We only have to check for `x ∈ l` that `form_perm l (form_perm l.reverse x)`
  rw [mul_apply, one_apply],
  by_cases hx : x ∈ l,
  swap,
  { rw [form_perm_apply_of_not_mem x l.reverse, form_perm_apply_of_not_mem _ _ hx],
    simpa using hx },
  { obtain ⟨k, hk, rfl⟩ := nth_le_of_mem (mem_reverse.mpr hx),
    rw [form_perm_apply_nth_le l.reverse (nodup_reverse.mpr h),
        nth_le_reverse', form_perm_apply_nth_le _ h, nth_le_reverse'],
    { congr,
      rw [length_reverse, ←nat.succ_le_iff, nat.succ_eq_add_one] at hk,
      cases hk.eq_or_lt with hk' hk',
      { simp [←hk'] },
      { rw [length_reverse, nat.mod_eq_of_lt hk', ←nat.sub_add_comm (nat.le_pred_of_lt hk'),
            nat.mod_eq_of_lt],
        { simp },
        { rw nat.sub_add_cancel,
          refine nat.sub_lt_self _ (nat.zero_lt_succ _),
          all_goals { simpa using (nat.zero_le _).trans_lt hk' } } } },
    all_goals { rw [nat.sub_sub, ←length_reverse],
      refine nat.sub_lt_self _ (zero_lt_one.trans_le (le_add_right le_rfl)),
      exact k.zero_le.trans_lt hk } },
end

lemma form_perm_pow_apply_nth_le (l : list α) (h : nodup l) (n k : ℕ) (hk : k < l.length) :
  (form_perm l ^ n) (l.nth_le k hk) = l.nth_le ((k + n) % l.length)
    (nat.mod_lt _ (k.zero_le.trans_lt hk)) :=
begin
  induction n with n hn,
  { simp [nat.mod_eq_of_lt hk] },
  { simp [pow_succ, mul_apply, hn, form_perm_apply_nth_le _ h, nat.succ_eq_add_one,
          ←nat.add_assoc] }
end

lemma form_perm_ext_iff {x y x' y' : α} {l l' : list α}
  (hd : nodup (x :: y :: l)) (hd' : nodup (x' :: y' :: l')) :
  form_perm (x :: y :: l) = form_perm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l') :=
begin
  refine ⟨λ h, _, λ hr, form_perm_eq_of_is_rotated hd hr⟩,
  rw equiv.perm.ext_iff at h,
  have hx : x' ∈ (x :: y :: l),
    { have : x' ∈ {z | form_perm (x :: y :: l) z ≠ z},
      { rw [set.mem_set_of_eq, h x', form_perm_apply_head _ _ _ hd'],
        simp only [mem_cons_iff, nodup_cons] at hd',
        push_neg at hd',
        exact hd'.left.left.symm },
      simpa using support_form_perm_le' _ this },
  obtain ⟨n, hn, hx'⟩ := nth_le_of_mem hx,
  have hl : (x :: y :: l).length = (x' :: y' :: l').length,
  { rw [←erase_dup_eq_self.mpr hd, ←erase_dup_eq_self.mpr hd',
        ←card_to_finset, ←card_to_finset],
    refine congr_arg finset.card _,
    rw [←finset.coe_inj, ←support_form_perm_of_nodup' _ hd (by simp),
        ←support_form_perm_of_nodup' _ hd' (by simp)],
    simp only [h] },
  use n,
  apply list.ext_le,
  { rw [length_rotate, hl] },
  { intros k hk hk',
    rw nth_le_rotate,
    induction k with k IH,
    { simp_rw [nat.zero_add, nat.mod_eq_of_lt hn],
      simpa },
    { have : k.succ = (k + 1) % (x' :: y' :: l').length,
      { rw [←nat.succ_eq_add_one, nat.mod_eq_of_lt hk'] },
      simp_rw this,
      rw [←form_perm_apply_nth_le _ hd' k (k.lt_succ_self.trans hk'),
          ←IH (k.lt_succ_self.trans hk), ←h, form_perm_apply_nth_le _ hd],
      congr' 1,
      have h1 : 1 = 1 % (x' :: y' :: l').length := by simp,
      rw [hl, nat.mod_eq_of_lt hk', h1, ←nat.add_mod, nat.succ_add] } }
end

end form_perm

end list
