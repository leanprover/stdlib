/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.set.intervals
import data.set.finite
import data.pnat.intervals

/-!
# fintype instances for intervals

We provide `fintype` instances for `Ico l u`, for `l u : ℕ`, and for `l u : ℤ`.
-/

namespace set

instance Ico_ℕ_fintype (l u : ℕ) : fintype (Ico l u) :=
fintype.of_finset (finset.Ico l u) $
  (λ n, by { simp only [mem_Ico, finset.Ico.mem], })

@[simp] lemma Ico_ℕ_card (l u : ℕ) : fintype.card (Ico l u) = u - l :=
calc fintype.card (Ico l u) = (finset.Ico l u).card : fintype.card_of_finset _ _
                        ... = u - l                 : finset.Ico.card l u

instance Ico_pnat_fintype (l u : ℕ+) : fintype (Ico l u) :=
fintype.of_finset (pnat.Ico l u) $
  (λ n, by { simp only [mem_Ico, pnat.Ico.mem], })

@[simp] lemma Ico_pnat_card (l u : ℕ+) : fintype.card (Ico l u) = u - l :=
calc fintype.card (Ico l u) = (pnat.Ico l u).card : fintype.card_of_finset _ _
                        ... = u - l               : pnat.Ico.card l u

instance Ico_ℤ_fintype (l u : ℤ) : fintype (Ico l u) :=
fintype.of_finset (finset.Ico_ℤ l u) $
  (λ n, by { simp only [mem_Ico, finset.Ico_ℤ.mem], })

instance Ioo_ℤ_fintype (l u : ℤ) : fintype (Ioo l u) :=
fintype.of_finset (finset.Ico_ℤ (l+1) u) $ λ n,
  by simp only [mem_Ioo, finset.Ico_ℤ.mem, int.add_one_le_iff, iff_self, implies_true_iff]

instance Icc_ℤ_fintype (l u : ℤ) : fintype (Icc l u) :=
fintype.of_finset (finset.Ico_ℤ l (u+1)) $ λ n,
  by simp only [mem_Icc, finset.Ico_ℤ.mem, int.lt_add_one_iff, iff_self, implies_true_iff]

instance Ioc_ℤ_fintype (l u : ℤ) : fintype (Ioc l u) :=
fintype.of_finset (finset.Ico_ℤ (l+1) (u+1)) $ λ n,
  by simp only [mem_Ioc, finset.Ico_ℤ.mem, int.add_one_le_iff, int.lt_add_one_iff,
    iff_self, implies_true_iff]

lemma Ico_ℤ_finite (l u : ℤ) : set.finite (Ico l u) := ⟨set.Ico_ℤ_fintype l u⟩
lemma Ioo_ℤ_finite (l u : ℤ) : set.finite (Ioo l u) := ⟨set.Ioo_ℤ_fintype l u⟩
lemma Icc_ℤ_finite (l u : ℤ) : set.finite (Icc l u) := ⟨set.Icc_ℤ_fintype l u⟩
lemma Ioc_ℤ_finite (l u : ℤ) : set.finite (Ioc l u) := ⟨set.Ioc_ℤ_fintype l u⟩

@[simp] lemma Ico_ℤ_card (l u : ℤ) : fintype.card (Ico l u) = (u - l).to_nat :=
calc fintype.card (Ico l u) = (finset.Ico_ℤ l u).card : fintype.card_of_finset _ _
                        ... = (u - l).to_nat          : finset.Ico_ℤ.card l u

@[simp] lemma Ioo_ℤ_card (l u : ℤ) : fintype.card (Ioo l u) = (u - l - 1).to_nat :=
calc fintype.card (Ioo l u) = (finset.Ico_ℤ (l+1) u).card : fintype.card_of_finset _ _
                        ... = (u - (l+1)).to_nat          : finset.Ico_ℤ.card (l+1) u
                        ... = (u - l - 1).to_nat          : congr_arg _ $ sub_add_eq_sub_sub u l 1

@[simp] lemma Icc_ℤ_card (l u : ℤ) : fintype.card (Icc l u) = (u + 1 - l).to_nat :=
calc fintype.card (Icc l u) = (finset.Ico_ℤ l (u+1)).card : fintype.card_of_finset _ _
                        ... = (u + 1 - l).to_nat          : finset.Ico_ℤ.card l (u+1)

@[simp] lemma Ioc_ℤ_card (l u : ℤ) : fintype.card (Ioc l u) = (u - l).to_nat :=
calc fintype.card (Ioc l u) = (finset.Ico_ℤ (l+1) (u+1)).card : fintype.card_of_finset _ _
                        ... = ((u+1) - (l+1)).to_nat : finset.Ico_ℤ.card (l+1) (u+1)
                        ... = (u - l).to_nat         : congr_arg _ $ add_sub_add_right_eq_sub u l 1

-- TODO other useful instances: fin n, zmod?

end set
