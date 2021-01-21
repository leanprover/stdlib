/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.set.intervals
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

@[simp] lemma Ico_ℤ_card (l u : ℤ) : fintype.card (Ico l u) = (u - l).to_nat :=
calc fintype.card (Ico l u) = (finset.Ico_ℤ l u).card : fintype.card_of_finset _ _
                        ... = (u - l).to_nat          : finset.Ico_ℤ.card l u

-- TODO other useful instances: fin n, zmod?

end set
