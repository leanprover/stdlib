/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import data.set.intervals.basic
import data.set.function

/-!
# Monotone surjective functions are surjective on intervals

A monotone surjective function sends any interval in the domain onto the interval with corresponding
endpoints in the range.  This is expressed in this file using `set.surj_on`, and provided for all
permutations of interval endpoints.
-/

variables {α : Type*} {β : Type*} [linear_order α] [partial_order β] {f : α → β}

open set function

lemma surj_on_Ioo_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a b : α) :
  surj_on f (Ioo a b) (Ioo (f a) (f b)) :=
begin
  classical,
  intros p hp,
  rcases h_surj p with ⟨x, rfl⟩,
  refine ⟨x, mem_Ioo.2 _, rfl⟩,
  by_contra h,
  cases not_and_distrib.mp h with ha hb,
  { exact has_lt.lt.false (lt_of_lt_of_le hp.1 (h_mono (not_lt.mp ha))) },
  { exact has_lt.lt.false (lt_of_le_of_lt (h_mono (not_lt.mp hb)) hp.2) }
end

lemma surj_on_Ico_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a b : α) :
  surj_on f (Ico a b) (Ico (f a) (f b)) :=
begin
  obtain hab | hab := lt_or_le a b,
  { intros p hp,
    rcases mem_Ioo_or_eq_left_of_mem_Ico hp with hp'|hp',
    { rw hp',
      exact ⟨a, left_mem_Ico.mpr hab, rfl⟩ },
    { have := surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp',
      cases this with x hx,
      exact ⟨x, Ioo_subset_Ico_self hx.1, hx.2⟩ } },
  { rw Ico_eq_empty (h_mono hab).not_lt,
    exact surj_on_empty f _ }
end

lemma surj_on_Ioc_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a b : α) :
  surj_on f (Ioc a b) (Ioc (f a) (f b)) :=
begin
  convert @surj_on_Ico_of_monotone_surjective _ _ _ _ _ h_mono.order_dual h_surj b a;
  simp
end

-- to see that the hypothesis `a ≤ b` is necessary, consider a constant function
lemma surj_on_Icc_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) {a b : α} (hab : a ≤ b) :
  surj_on f (Icc a b) (Icc (f a) (f b)) :=
begin
  rcases lt_or_eq_of_le hab with hab|hab,
  { intros p hp,
    rcases mem_Ioo_or_eq_endpoints_of_mem_Icc hp with hp'|⟨hp'|hp'⟩,
    { rw hp',
      refine ⟨a, left_mem_Icc.mpr (le_of_lt hab), rfl⟩ },
    { rw hp',
      refine ⟨b, right_mem_Icc.mpr (le_of_lt hab), rfl⟩ },
    { have := surj_on_Ioo_of_monotone_surjective h_mono h_surj a b hp',
      cases this with x hx,
      exact ⟨x, Ioo_subset_Icc_self hx.1, hx.2⟩ } },
  { simp only [hab, Icc_self],
    intros _ hp,
    exact ⟨b, mem_singleton _, (mem_singleton_iff.mp hp).symm⟩ }
end

lemma surj_on_Ioi_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a : α) :
  surj_on f (Ioi a) (Ioi (f a)) :=
begin
  classical,
  intros p hp,
  rcases h_surj p with ⟨x, rfl⟩,
  refine ⟨x, _, rfl⟩,
  simp only [mem_Ioi],
  by_contra h,
  exact has_lt.lt.false (lt_of_lt_of_le hp (h_mono (not_lt.mp h)))
end

lemma surj_on_Iio_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a : α) :
  surj_on f (Iio a) (Iio (f a)) :=
@surj_on_Ioi_of_monotone_surjective _ _ _ _ _ (monotone.order_dual h_mono) h_surj a

lemma surj_on_Ici_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a : α) :
  surj_on f (Ici a) (Ici (f a)) :=
begin
  intros p hp,
  rw [mem_Ici, le_iff_lt_or_eq] at hp,
  rcases hp with hp'|hp',
  { cases (surj_on_Ioi_of_monotone_surjective h_mono h_surj a hp') with x hx,
    exact ⟨x, Ioi_subset_Ici_self hx.1, hx.2⟩ },
  { rw ← hp',
    refine ⟨a, left_mem_Ici, rfl⟩ }
end

lemma surj_on_Iic_of_monotone_surjective
  (h_mono : monotone f) (h_surj : function.surjective f) (a : α) :
  surj_on f (Iic a) (Iic (f a)) :=
@surj_on_Ici_of_monotone_surjective _ _ _ _ _ (monotone.order_dual h_mono) h_surj a
