/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Fox Thomson.
-/
import tactic.omega
import computability.language

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

TODO
* Show that this regular expressions and DFA/NFA's are equivalent.
* `attribute [pattern] has_mul.mul` has been added into this file, it could be moved.
-/

universe u

variables {α : Type u} [dec : decidable_eq α]

/--
This is the definition of regular expressions. The names used here is to mirror the definition
of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings which match `P`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive regular_expression (α : Type u) : Type u
| zero : regular_expression
| epsilon : regular_expression
| char : α → regular_expression
| plus : regular_expression → regular_expression → regular_expression
| comp : regular_expression → regular_expression → regular_expression
| star : regular_expression → regular_expression

namespace regular_expression

instance : inhabited (regular_expression α) := ⟨zero⟩

instance : has_add (regular_expression α) := ⟨plus⟩
instance : has_mul (regular_expression α) := ⟨comp⟩
instance : has_one (regular_expression α) := ⟨epsilon⟩
instance : has_zero (regular_expression α) := ⟨zero⟩

attribute [pattern] has_mul.mul

@[simp] lemma zero_def : (zero : regular_expression α) = 0 := rfl
@[simp] lemma one_def : (epsilon : regular_expression α) = 1 := rfl

@[simp] lemma plus_def (P Q : regular_expression α) : plus P Q = P + Q := rfl
@[simp] lemma comp_def (P Q : regular_expression α) : comp P Q = P * Q := rfl

/-- `matches P` provides a language which contains all strings that `P` matches -/
def matches : regular_expression α → language α
| 0 := 0
| 1 := 1
| (char a) := {[a]}
| (P + Q) := P.matches + Q.matches
| (P * Q) := P.matches * Q.matches
| (star P) := P.matches.star

@[simp] lemma matches_zero_def : (0 : regular_expression α).matches = 0 := rfl
@[simp] lemma matches_epsilon_def : (1 : regular_expression α).matches = 1 := rfl
@[simp] lemma matches_add_def (P Q : regular_expression α) :
  (P + Q).matches = P.matches + Q.matches := rfl
@[simp] lemma matches_mul_def (P Q : regular_expression α) :
  (P * Q).matches = P.matches * Q.matches := rfl
@[simp] lemma matches_star_def (P : regular_expression α) : P.star.matches = P.matches.star := rfl

/-- `match_epsilon P` is true if and only if `P` matches the empty string -/
def match_epsilon : regular_expression α → bool
| 0 := ff
| 1 := tt
| (char _) := ff
| (P + Q) := P.match_epsilon || Q.match_epsilon
| (P * Q) := P.match_epsilon && Q.match_epsilon
| (star P) := tt

include dec

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : regular_expression α → α → regular_expression α
| 0 _ := 0
| 1 _ := 0
| (char a₁) a₂ := if a₁ = a₂ then 1 else 0
| (P + Q) a := deriv P a + deriv Q a
| (P * Q) a :=
  if P.match_epsilon then
    deriv P a * Q + deriv Q a
  else
    deriv P a * Q
| (star P) a := deriv P a * star P

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches`. -/
def rmatch : regular_expression α → list α → bool
| P [] := match_epsilon P
| P (a::as) := rmatch (P.deriv a) as

@[simp] lemma zero_rmatch (x : list α) : rmatch 0 x = ff :=
by induction x; simp [rmatch, match_epsilon, deriv, *]

lemma one_rmatch_iff (x : list α) : rmatch 1 x ↔ x = [] :=
by induction x; simp [rmatch, match_epsilon, deriv, *]

lemma char_rmatch_iff (a : α) (x : list α) : rmatch (char a) x ↔ x = [a] :=
begin
  cases x with _ x,
    dec_trivial,
  cases x,
    rw [rmatch, deriv],
    split_ifs;
    tauto,
  rw [rmatch, deriv],
  split_ifs,
    rw one_rmatch_iff,
    tauto,
  rw zero_rmatch,
  tauto
end

lemma add_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x :=
begin
  induction x with _ _ ih generalizing P Q,
  { repeat {rw rmatch},
    rw match_epsilon,
    finish },
  { repeat {rw rmatch},
    rw deriv,
    exact ih _ _ }
end

lemma mul_rmatch_iff (P Q : regular_expression α) (x : list α) :
  (P * Q).rmatch x ↔ ∃ t u : list α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u :=
begin
  induction x with a x ih generalizing P Q,
  { rw [rmatch, match_epsilon],
    split,
    { intro h,
      refine ⟨ [], [], rfl, _ ⟩,
      rw [rmatch, rmatch],
      rwa band_coe_iff at h },
    { rintro ⟨ t, u, h₁, h₂ ⟩,
      cases list.append_eq_nil.1 h₁.symm with ht hu,
      subst ht,
      subst hu,
      repeat {rw rmatch at h₂},
      finish } },
  { rw [rmatch, deriv],
    split_ifs with hepsilon,
    { rw [add_rmatch_iff, ih],
      split,
      { rintro (⟨ t, u, _ ⟩ | h),
        { exact ⟨ a :: t, u, by tauto ⟩ },
        { exact ⟨ [], a :: x, rfl, hepsilon, h ⟩ } },
      { rintro ⟨ t, u, h, hP, hQ ⟩,
        cases t with b t,
        { right,
          rw list.nil_append at h,
          rw ←h at hQ,
          exact hQ },
        { left,
          refine ⟨ t, u, by finish, _, hQ ⟩,
          rw rmatch at hP,
          convert hP,
          finish } } },
    { rw ih,
      split;
      rintro ⟨ t, u, h, hP, hQ ⟩,
      { exact ⟨ a :: t, u, by tauto ⟩ },
      { cases t with b t,
        { contradiction },
        { refine ⟨ t, u, by finish, _, hQ ⟩,
          rw rmatch at hP,
          convert hP,
          finish } } } }
end

lemma star_rmatch_iff (P : regular_expression α) : ∀ (x : list α),
  (star P).rmatch x ↔ ∃ S : list (list α), x = S.join ∧ ∀ t ∈ S, t ≠ [] ∧ P.rmatch t
| x :=
begin
  have IH := λ t (h : list.length t < list.length x), star_rmatch_iff t,
  clear star_rmatch_iff,
  split,
  { cases x with a x,
    { intro,
      fconstructor,
      exact [],
      tauto },
    { rw [rmatch, deriv, mul_rmatch_iff],
      rintro ⟨ t, u, hs, ht, hu ⟩,
      have hwf : u.length < (list.cons a x).length,
      { rw [hs, list.length_cons, list.length_append],
        omega },
      rw IH _ hwf at hu,
      rcases hu with ⟨ S', hsum, helem ⟩,
      use (a :: t) :: S',
      split,
      { finish },
      { intros t' ht',
        cases ht' with ht' ht',
        { rw ht',
          exact ⟨ dec_trivial, ht ⟩ },
        { exact helem _ ht' } } } },
  { rintro ⟨ S, hsum, helem ⟩,
    cases x with a x,
    { dec_trivial },
    { rw [rmatch, deriv, mul_rmatch_iff],
      cases S with t' U,
      { exact ⟨ [], [], by tauto ⟩ },
      { cases t' with b t,
        { finish },
        refine ⟨ t, U.join, by finish, _, _ ⟩,
        { specialize helem (b :: t) _,
          rw rmatch at helem,
          convert helem.2,
          finish,
          finish },
        { have hwf : U.join.length < (list.cons a x).length,
          { rw hsum,
            simp only
              [list.join, list.length_append, list.cons_append, list.length_join, list.length],
            omega },
          rw IH _ hwf,
          refine ⟨ U, rfl, λ t h, helem t _ ⟩,
          right,
          assumption } } } }
end
using_well_founded {
  rel_tac := λ _ _, `[exact ⟨(λ L₁ L₂ : list _, L₁.length < L₂.length), inv_image.wf _ nat.lt_wf⟩]
}

@[simp] lemma rmatch_iff_matches (P : regular_expression α) :
  ∀ x : list α, P.rmatch x ↔ x ∈ P.matches :=
begin
  intro x,
  induction P generalizing x,
  all_goals
  { try {rw zero_def},
    try {rw one_def},
    try {rw plus_def},
    try {rw comp_def},
    rw matches },
  case zero : {
    rw zero_rmatch,
    tauto },
  case epsilon : {
    rw one_rmatch_iff,
    refl },
  case char : {
    rw char_rmatch_iff,
    refl },
  case plus : _ _ ih₁ ih₂ {
    rw [add_rmatch_iff, ih₁, ih₂],
    refl },
  case comp : P Q ih₁ ih₂ {
    simp only [mul_rmatch_iff, comp_def, language.mul_def, exists_and_distrib_left, set.mem_image2,
      set.image_prod],
    split,
    { rintro ⟨ x, y, hsum, hmatch₁, hmatch₂ ⟩,
      rw ih₁ at hmatch₁,
      rw ih₂ at hmatch₂,
      exact ⟨ x, hmatch₁, y, hmatch₂, hsum.symm ⟩ },
    { rintro ⟨ x, hmatch₁, y, hmatch₂, hsum ⟩,
      rw ←ih₁ at hmatch₁,
      rw ←ih₂ at hmatch₂,
      exact ⟨ x, y, hsum.symm, hmatch₁, hmatch₂ ⟩ } },
  case star : _ ih {
    rw [star_rmatch_iff, language.star_def_nonempty],
    split,
    all_goals
    { rintro ⟨ S, hx, hS ⟩,
      refine ⟨ S, hx, _ ⟩,
      intro y,
      specialize hS y },
    { rw ←ih y,
      tauto },
    { rw ih y,
      tauto } }
end

instance (P : regular_expression α) : decidable_pred P.matches :=
begin
  intro x,
  change decidable (x ∈ P.matches),
  rw ←rmatch_iff_matches,
  exact eq.decidable _ _
end

end regular_expression
