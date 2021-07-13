/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.finset.basic
import data.multiset.intervals

/-!
# Intervals in ℕ as finsets

For now this only covers `Ico n m`, the "closed-open" interval containing `[n, ..., m-1]`.
-/

namespace finset
open multiset

/-! ### intervals -/
/- Ico (a closed open interval) -/
variables {n m l : ℕ}

/-- `Ico n m` is the set of natural numbers `n ≤ k < m`. -/
def Ico (n m : ℕ) : finset ℕ := ⟨_, Ico.nodup n m⟩

namespace Ico

@[simp] theorem val (n m : ℕ) : (Ico n m).1 = multiset.Ico n m := rfl

@[simp] theorem to_finset (n m : ℕ) : (multiset.Ico n m).to_finset = Ico n m :=
(multiset.to_finset_eq _).symm

theorem image_add (n m k : ℕ) : (Ico n m).image ((+) k) = Ico (n + k) (m + k) :=
by simp [image, multiset.Ico.map_add]

theorem image_sub (n m k : ℕ) (h : k ≤ n) : (Ico n m).image (λ x, x - k) = Ico (n - k) (m - k) :=
begin
  dsimp [image],
  rw [multiset.Ico.map_sub _ _ _ h, ←multiset.to_finset_eq],
  refl,
end

theorem zero_bot (n : ℕ) : Ico 0 n = range n :=
eq_of_veq $ multiset.Ico.zero_bot _

@[simp] theorem card (n m : ℕ) : (Ico n m).card = m - n :=
multiset.Ico.card _ _

@[simp] theorem mem {n m l : ℕ} : l ∈ Ico n m ↔ n ≤ l ∧ l < m :=
multiset.Ico.mem

@[simp, norm_cast] lemma coe_eq_Ico {n m : ℕ} : ↑(Ico n m) = set.Ico n m :=
begin
  ext,
  rw [set.mem_Ico, mem_coe, finset.Ico.mem],
end

theorem eq_empty_of_le {n m : ℕ} (h : m ≤ n) : Ico n m = ∅ :=
eq_of_veq $ multiset.Ico.eq_zero_of_le h

@[simp] theorem self_eq_empty (n : ℕ) : Ico n n = ∅ :=
eq_empty_of_le $ le_refl n

@[simp] theorem eq_empty_iff {n m : ℕ} : Ico n m = ∅ ↔ m ≤ n :=
iff.trans val_eq_zero.symm multiset.Ico.eq_zero_iff

theorem subset_iff {m₁ n₁ m₂ n₂ : ℕ} (hmn : m₁ < n₁) :
  Ico m₁ n₁ ⊆ Ico m₂ n₂ ↔ (m₂ ≤ m₁ ∧ n₁ ≤ n₂) :=
begin
  simp only [subset_iff, mem],
  refine ⟨λ h, ⟨_, _⟩, _⟩,
  { exact (h ⟨le_refl _, hmn⟩).1 },
  { refine nat.le_of_pred_lt (@h n₁.pred ⟨nat.le_pred_of_lt hmn, nat.pred_lt _⟩).2,
    exact ne_of_gt (lt_of_le_of_lt (nat.zero_le m₁) hmn) },
  { rintros ⟨hm, hn⟩ k ⟨hmk, hkn⟩,
    exact ⟨le_trans hm hmk, lt_of_lt_of_le hkn hn⟩ }
end

protected theorem subset {m₁ n₁ m₂ n₂ : ℕ} (hmm : m₂ ≤ m₁) (hnn : n₁ ≤ n₂) :
  Ico m₁ n₁ ⊆ Ico m₂ n₂ :=
begin
  simp only [finset.subset_iff, Ico.mem],
  assume x hx,
  exact ⟨le_trans hmm hx.1, lt_of_lt_of_le hx.2 hnn⟩
end

lemma union_consecutive {n m l : ℕ} (hnm : n ≤ m) (hml : m ≤ l) :
  Ico n m ∪ Ico m l = Ico n l :=
by rw [← to_finset, ← to_finset, ← multiset.to_finset_add,
  multiset.Ico.add_consecutive hnm hml, to_finset]

lemma union' {n m l k : ℕ} (hlm : l ≤ m) (hnk : n ≤ k) :
  Ico n m ∪ Ico l k = Ico (min n l) (max m k) :=
by simp [←coe_inj, set.Ico_union_Ico' hlm hnk]

lemma union {n m l k : ℕ} (h₁ : min n m ≤ max l k) (h₂ : min l k ≤ max n m) :
  Ico n m ∪ Ico l k = Ico (min n l) (max m k) :=
by simp [←coe_inj, set.Ico_union_Ico h₁ h₂]

@[simp] lemma inter_consecutive (n m l : ℕ) : Ico n m ∩ Ico m l = ∅ :=
begin
  rw [← to_finset, ← to_finset, ← multiset.to_finset_inter, multiset.Ico.inter_consecutive],
  simp,
end

lemma inter {n m l k : ℕ} : Ico n m ∩ Ico l k = Ico (max n l) (min m k) :=
by simp [←coe_inj, ←inf_eq_min, ←sup_eq_max, set.Ico_inter_Ico]

lemma disjoint_consecutive (n m l : ℕ) : disjoint (Ico n m) (Ico m l) :=
le_of_eq $ inter_consecutive n m l

@[simp] theorem succ_singleton (n : ℕ) : Ico n (n+1) = {n} :=
eq_of_veq $ multiset.Ico.succ_singleton

theorem succ_top {n m : ℕ} (h : n ≤ m) : Ico n (m + 1) = insert m (Ico n m) :=
by rw [← to_finset, multiset.Ico.succ_top h, multiset.to_finset_cons, to_finset]

theorem succ_top' {n m : ℕ} (h : n < m) : Ico n m = insert (m - 1) (Ico n (m - 1)) :=
begin
  have w : m = m - 1 + 1 := (nat.sub_add_cancel (nat.one_le_of_lt h)).symm,
  conv { to_lhs, rw w },
  rw succ_top,
  exact nat.le_pred_of_lt h
end

theorem insert_succ_bot {n m : ℕ} (h : n < m) : insert n (Ico (n + 1) m) = Ico n m :=
by rw [eq_comm, ← to_finset, multiset.Ico.eq_cons h, multiset.to_finset_cons, to_finset]

@[simp] theorem pred_singleton {m : ℕ} (h : 0 < m) : Ico (m - 1) m = {m - 1} :=
eq_of_veq $ multiset.Ico.pred_singleton h

@[simp] theorem not_mem_top {n m : ℕ} : m ∉ Ico n m :=
multiset.Ico.not_mem_top

lemma filter_lt_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico n m).filter (λ x, x < l) = Ico n m :=
eq_of_veq $ multiset.Ico.filter_lt_of_top_le hml

lemma filter_lt_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico n m).filter (λ x, x < l) = ∅ :=
eq_of_veq $ multiset.Ico.filter_lt_of_le_bot hln

lemma filter_Ico_bot {n m : ℕ} (hnm : n < m) : (Ico n m).filter (λ x, x ≤ n) = {n} :=
eq_of_veq $ multiset.Ico.filter_le_of_bot hnm

lemma filter_lt_of_ge {n m l : ℕ} (hlm : l ≤ m) : (Ico n m).filter (λ x, x < l) = Ico n l :=
eq_of_veq $ multiset.Ico.filter_lt_of_ge hlm

@[simp] lemma filter_lt (n m l : ℕ) : (Ico n m).filter (λ x, x < l) = Ico n (min m l) :=
eq_of_veq $ multiset.Ico.filter_lt n m l

lemma filter_le_of_le_bot {n m l : ℕ} (hln : l ≤ n) : (Ico n m).filter (λ x, l ≤ x) = Ico n m :=
eq_of_veq $ multiset.Ico.filter_le_of_le_bot hln

lemma filter_le_of_top_le {n m l : ℕ} (hml : m ≤ l) : (Ico n m).filter (λ x, l ≤ x) = ∅ :=
eq_of_veq $ multiset.Ico.filter_le_of_top_le hml

lemma filter_le_of_le {n m l : ℕ} (hnl : n ≤ l) : (Ico n m).filter (λ x, l ≤ x) = Ico l m :=
eq_of_veq $ multiset.Ico.filter_le_of_le hnl

@[simp] lemma filter_le (n m l : ℕ) : (Ico n m).filter (λ x, l ≤ x) = Ico (max n l) m :=
eq_of_veq $ multiset.Ico.filter_le n m l

@[simp] lemma diff_left (l n m : ℕ) : (Ico n m) \ (Ico n l) = Ico (max n l) m :=
by ext k; by_cases n ≤ k; simp [h, and_comm]

@[simp] lemma diff_right (l n m : ℕ) : (Ico n m) \ (Ico l m) = Ico n (min m l) :=
have ∀k, (k < m ∧ (l ≤ k → m ≤ k)) ↔ (k < m ∧ k < l) :=
  assume k, and_congr_right $ assume hk, by rw [← not_imp_not]; simp [hk],
by ext k; by_cases n ≤ k; simp [h, this]

lemma image_const_sub {k m n : ℕ} (hkn : k ≤ n) :
  (Ico k m).image (λ j, n - j) = Ico (n + 1 - m) (n + 1 - k) :=
begin
  rw [nat.sub_add_comm hkn],
  ext j,
  simp only [mem, mem_image, exists_prop, lt_iff_add_one_le, add_le_add_iff_right],
  split,
  { rintros ⟨j, ⟨hjk, hjm⟩, rfl⟩,
    split,
    { simp only [← nat.add_sub_add_right n 1 j, nat.sub_le_sub_left, hjm] },
    { exact nat.sub_le_sub_left _ hjk } },
  { rintros ⟨hm, hk⟩,
    have hj : j ≤ n := le_trans hk (nat.sub_le_self _ _),
    refine ⟨n - j, ⟨_, _⟩, _⟩,
    { apply nat.le_sub_right_of_add_le,
      rwa nat.le_sub_left_iff_add_le hkn at hk },
    { rwa [← nat.sub_add_comm hj, nat.sub_le_iff] },
    { exact nat.sub_sub_self hj } }
end

end Ico

lemma range_eq_Ico (n : ℕ) : finset.range n = finset.Ico 0 n :=
by { ext i, simp }

lemma range_image_pred_top_sub (n : ℕ) :
  (finset.range n).image (λ j, n - 1 - j) = finset.range n :=
begin
  cases n,
  { simp },
  { simp [range_eq_Ico, Ico.image_const_sub] }
end

-- TODO We don't yet attempt to reproduce the entire interface for `Ico` for `Ico_ℤ`.

/-- `Ico_ℤ l u` is the set of integers `l ≤ k < u`. -/
def Ico_ℤ (l u : ℤ) : finset ℤ :=
(finset.range (u - l).to_nat).map
  { to_fun := λ n, n + l,
    inj' := λ n m h, by simpa using h }

@[simp] lemma Ico_ℤ.mem {n m l : ℤ} : l ∈ Ico_ℤ n m ↔ n ≤ l ∧ l < m :=
begin
  dsimp [Ico_ℤ],
  simp only [int.lt_to_nat, exists_prop, mem_range, add_comm, function.embedding.coe_fn_mk,
    mem_map],
  split,
  { rintro ⟨a, ⟨h, rfl⟩⟩,
    exact ⟨int.le.intro rfl, lt_sub_iff_add_lt'.mp h⟩ },
  { rintro ⟨h₁, h₂⟩,
    use (l - n).to_nat,
    split; simp [h₁, h₂], }
end

@[simp] lemma Ico_ℤ.card (l u : ℤ) : (Ico_ℤ l u).card = (u - l).to_nat := by simp [Ico_ℤ]

end finset
