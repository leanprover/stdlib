/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import analysis.normed_space.basic

/-!
# Indicator function and norm

This file contains a few simple lemmas about `set.indicator` and `norm`.

## Tags
indicator, norm
-/

variables {α E : Type*} [normed_group E] {s t : set α} (f : α → E) (a : α)

open set

lemma norm_indicator_eq_indicator_norm :
  ∥indicator s f a∥ = indicator s (λa, ∥f a∥) a :=
flip congr_fun a (indicator_comp_of_zero norm_zero).symm

lemma nnnorm_indicator_eq_indicator_nnnorm :
  nnnorm (indicator s f a) = indicator s (λa, nnnorm (f a)) a :=
flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm

lemma norm_indicator_le_of_subset (h : s ⊆ t) (f : α → E) (a : α) :
  ∥indicator s f a∥ ≤ ∥indicator t f a∥ :=
begin
  simp only [norm_indicator_eq_indicator_norm],
  exact indicator_le_indicator_of_subset ‹_› (λ _, norm_nonneg _) _
end

lemma indicator_norm_le_norm_self : indicator s (λa, ∥f a∥) a ≤ ∥f a∥ :=
indicator_le_self' (λ _ _, norm_nonneg _) a

lemma norm_indicator_le_norm_self : ∥indicator s f a∥ ≤ ∥f a∥ :=
by { rw norm_indicator_eq_indicator_norm, apply indicator_norm_le_norm_self }
