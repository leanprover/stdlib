/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.big_operators.pi
import algebra.big_operators.ring
import data.finsupp

/-!
# Big operators for finsupps

This file contains theorems relevant to big operators in finitely supported functions.
-/

open_locale big_operators

variables {α ι γ A B C : Type*} [add_comm_monoid A] [add_comm_monoid B] [add_comm_monoid C]
variables {t : ι → A → C} (h0 : ∀ i, t i 0 = 0) (h1 : ∀ i x y, t i (x + y) = t i x + t i y)
variables {s : finset α} {f : α → (ι →₀ A)} (i : ι)
variables (g : ι →₀ A) (k : ι → A → γ → B) (x : γ)

theorem finset.sum_apply' : (∑ k in s, f k) i = ∑ k in s, f k i :=
(finsupp.apply_add_hom i : (ι →₀ A) →+ A).map_sum f s

theorem finsupp.sum_apply' : g.sum k x = g.sum (λ i b, k i b x) :=
finset.sum_apply _ _ _

section
include h0 h1

open_locale classical

theorem finsupp.sum_sum_index' : (∑ x in s, f x).sum t = ∑ x in s, (f x).sum t :=
finset.induction_on s rfl $ λ a s has ih,
by simp_rw [finset.sum_insert has, finsupp.sum_add_index h0 h1, ih]

end

section
variables {R S : Type*} [non_unital_non_assoc_semiring R] [non_unital_non_assoc_semiring S]

lemma finsupp.sum_mul (b : S) (s : α →₀ R) {f : α → R → S} :
  (s.sum f) * b = s.sum (λ a c, (f a c) * b) :=
by simp only [finsupp.sum, finset.sum_mul]

lemma finsupp.mul_sum (b : S) (s : α →₀ R) {f : α → R → S} :
  b * (s.sum f) = s.sum (λ a c, b * (f a c)) :=
by simp only [finsupp.sum, finset.mul_sum]

end
