/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import logic.function.iterate
import data.nat.basic

/-!
# Inequalities on iterates

In this file we prove some inequalities comparing `f^[n] x` and `g^[n] x` where `f` and `g` are
two self-maps that commute with each other.

Current selection of inequalities is motivated by formalization of the rotation number of
a circle homeomorphism.
-/
variables {α : Type*}

namespace monotone

variables [preorder α] {f : α → α} {x y : ℕ → α}

lemma seq_le_seq (hf : monotone f) (n : ℕ) (h₀ : x 0 ≤ y 0)
  (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) :
  x n ≤ y n :=
begin
  induction n with n ihn,
  { exact h₀ },
  { refine (hx _ n.lt_succ_self).trans ((hf $ ihn _ _).trans (hy _ n.lt_succ_self)),
    exact λ k hk, hx _ (hk.trans n.lt_succ_self),
    exact λ k hk, hy _ (hk.trans n.lt_succ_self) }
end

lemma seq_pos_lt_seq_of_lt_of_le (hf : monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
  (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) :
  x n < y n :=
begin
  induction n with n ihn, { exact hn.false.elim },
  suffices : x n ≤ y n,
    from (hx n n.lt_succ_self).trans_le ((hf this).trans $ hy n n.lt_succ_self),
  cases n, { exact h₀ },
  refine (ihn n.zero_lt_succ (λ k hk, hx _ _) (λ k hk, hy _ _)).le;
    exact hk.trans n.succ.lt_succ_self
end

lemma seq_pos_lt_seq_of_le_of_lt (hf : monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
  (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) :
  x n < y n :=
hf.order_dual.seq_pos_lt_seq_of_lt_of_le hn h₀ hy hx

lemma seq_lt_seq_of_lt_of_le (hf : monotone f) (n : ℕ) (h₀ : x 0 < y 0)
  (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) :
  x n < y n :=
by { cases n, exacts [h₀, hf.seq_pos_lt_seq_of_lt_of_le n.zero_lt_succ h₀.le hx hy] }

lemma seq_lt_seq_of_le_of_lt (hf : monotone f) (n : ℕ) (h₀ : x 0 < y 0)
  (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) :
  x n < y n :=
hf.order_dual.seq_lt_seq_of_lt_of_le n h₀ hy hx

end monotone

namespace function

namespace commute

section preorder

variables [preorder α] {f g : α → α}

lemma iterate_le_of_map_le (h : commute f g) (hf : monotone f)  (hg : monotone g)
  {x} (hx : f x ≤ g x) (n : ℕ) :
  f^[n] x ≤ (g^[n]) x :=
by refine hf.seq_le_seq n _ (λ k hk, _) (λ k hk, _);
  simp [iterate_succ' f, h.iterate_right _ _, hg.iterate _ hx]

lemma iterate_pos_lt_of_map_lt (h : commute f g) (hf : monotone f) (hg : strict_mono g)
  {x} (hx : f x < g x) {n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x :=
by refine hf.seq_pos_lt_seq_of_le_of_lt hn _ (λ k hk, _) (λ k hk, _);
  simp [iterate_succ' f, h.iterate_right _ _, hg.iterate _ hx]

lemma iterate_pos_lt_of_map_lt' (h : commute f g) (hf : strict_mono f) (hg : monotone g)
  {x} (hx : f x < g x) {n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x :=
@iterate_pos_lt_of_map_lt (order_dual α) _ g f h.symm hg.order_dual hf.order_dual x hx n hn

end preorder

variables [linear_order α] {f g : α → α}

lemma iterate_pos_lt_iff_map_lt (h : commute f g) (hf : monotone f)
  (hg : strict_mono g) {x n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x ↔ f x < g x :=
begin
  rcases lt_trichotomy (f x) (g x) with H|H|H,
  { simp only [*, iterate_pos_lt_of_map_lt] },
  { simp only [*, h.iterate_eq_of_map_eq, lt_irrefl] },
  { simp only [lt_asymm H, lt_asymm (h.symm.iterate_pos_lt_of_map_lt' hg hf H hn)] }
end

lemma iterate_pos_lt_iff_map_lt' (h : commute f g) (hf : strict_mono f)
  (hg : monotone g) {x n} (hn : 0 < n) :
  f^[n] x < (g^[n]) x ↔ f x < g x :=
@iterate_pos_lt_iff_map_lt (order_dual α) _ _ _ h.symm hg.order_dual hf.order_dual x n hn

lemma iterate_pos_le_iff_map_le (h : commute f g) (hf : monotone f)
  (hg : strict_mono g) {x n} (hn : 0 < n) :
  f^[n] x ≤ (g^[n]) x ↔ f x ≤ g x :=
by simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt' hg hf hn)

lemma iterate_pos_le_iff_map_le' (h : commute f g) (hf : strict_mono f)
  (hg : monotone g) {x n} (hn : 0 < n) :
  f^[n] x ≤ (g^[n]) x ↔ f x ≤ g x :=
by simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt hg hf hn)

lemma iterate_pos_eq_iff_map_eq (h : commute f g) (hf : monotone f)
  (hg : strict_mono g) {x n} (hn : 0 < n) :
  f^[n] x = (g^[n]) x ↔ f x = g x :=
by simp only [le_antisymm_iff, h.iterate_pos_le_iff_map_le hf hg hn,
  h.symm.iterate_pos_le_iff_map_le' hg hf hn]

end commute

end function

namespace monotone

variables [preorder α] {f g : α → α}

open function

/-- If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`. -/
lemma iterate_le_of_le (hf : monotone f) (h : f ≤ g) (n : ℕ) :
  f^[n] ≤ (g^[n]) :=
λ x, by refine hf.seq_le_seq n _ (λ k hk, _) (λ k hk, _); simp [iterate_succ', h _]

/-- If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`. -/
lemma iterate_ge_of_ge (hg : monotone g) (h : f ≤ g) (n : ℕ) :
  f^[n] ≤ (g^[n]) :=
hg.order_dual.iterate_le_of_le h n

end monotone
