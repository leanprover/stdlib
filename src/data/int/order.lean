/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import order.conditionally_complete_lattice

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/

open int
open_locale classical
noncomputable theory

instance : conditionally_complete_linear_order ℤ :=
{ Sup := λ s, if h : s.nonempty ∧ bdd_above s then
    greatest_of_bdd (classical.some h.2) (classical.some_spec h.2) h.1 else 0,
  Inf := λ s, if h : s.nonempty ∧ bdd_below s then
    least_of_bdd (classical.some h.2) (classical.some_spec h.2) h.1 else 0,
  le_cSup := begin
    intros s n hs hns,
    have : s.nonempty ∧ bdd_above s := ⟨⟨n, hns⟩, hs⟩,
    rw [dif_pos this],
    exact (greatest_of_bdd _ _ _).2.2 n hns
  end,
  cSup_le := begin
    intros s n hs hns,
    have : s.nonempty ∧ bdd_above s := ⟨hs, ⟨n, hns⟩⟩,
    rw [dif_pos this],
    exact hns (greatest_of_bdd _ (classical.some_spec this.2) _).2.1
  end,
  cInf_le := begin
    intros s n hs hns,
    have : s.nonempty ∧ bdd_below s := ⟨⟨n, hns⟩, hs⟩,
    rw [dif_pos this],
    exact (least_of_bdd _ _ _).2.2 n hns
  end,
  le_cInf := begin
    intros s n hs hns,
    have : s.nonempty ∧ bdd_below s := ⟨hs, ⟨n, hns⟩⟩,
    rw [dif_pos this],
    exact hns (least_of_bdd _ (classical.some_spec this.2) _).2.1
  end,
  .. int.linear_order, ..lattice_of_linear_order }

namespace int

lemma cSup_eq_greatest_of_bdd {s : set ℤ} [decidable_pred (∈ s)]
  (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b) (Hinh : ∃ z : ℤ, z ∈ s) :
  Sup s = greatest_of_bdd b Hb Hinh :=
begin
  convert dif_pos _ using 1,
  { convert coe_greatest_of_bdd_eq _ (classical.some_spec (⟨b, Hb⟩ : bdd_above s)) _ },
  { exact ⟨Hinh, b, Hb⟩, }
end

@[simp]
lemma cSup_empty : Sup (∅ : set ℤ) = 0 := dif_neg (by simp)

lemma cSup_of_not_bdd_above {s : set ℤ} (h : ¬ bdd_above s) : Sup s = 0 := dif_neg (by simp [h])

lemma cInf_eq_least_of_bdd {s : set ℤ} [decidable_pred (∈ s)]
  (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z) (Hinh : ∃ z : ℤ, z ∈ s) :
  Inf s = least_of_bdd b Hb Hinh :=
begin
  convert dif_pos _ using 1,
  { convert coe_least_of_bdd_eq _ (classical.some_spec (⟨b, Hb⟩ : bdd_below s)) _ },
  { exact ⟨Hinh, b, Hb⟩, }
end

@[simp]
lemma cInf_empty : Inf (∅ : set ℤ) = 0 := dif_neg (by simp)

lemma cInf_of_not_bdd_below {s : set ℤ} (h : ¬ bdd_below s) : Inf s = 0 := dif_neg (by simp [h])

lemma cSup_mem {s : set ℤ} (h1 : s.nonempty) (h2 : bdd_above s) : Sup s ∈ s :=
begin
  convert (greatest_of_bdd _ (classical.some_spec h2) h1).2.1,
  exact dif_pos ⟨h1, h2⟩,
end

lemma cInf_mem {s : set ℤ} (h1 : s.nonempty) (h2 : bdd_below s) : Inf s ∈ s :=
begin
  convert (least_of_bdd _ (classical.some_spec h2) h1).2.1,
  exact dif_pos ⟨h1, h2⟩,
end

end int
