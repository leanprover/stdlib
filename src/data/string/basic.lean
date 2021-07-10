/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.basic
import data.char

/-!
# Strings

Supplementary theorems about the `string` type.
-/

namespace string

/-- `<` on string iterators. This coincides with `<` on strings as lists. -/
def ltb : iterator → iterator → bool
| s₁ s₂ := begin
  cases s₂.has_next, {exact ff},
  cases h₁ : s₁.has_next, {exact tt},
  exact if s₁.curr = s₂.curr then
    have s₁.next.2.length < s₁.2.length, from
    match s₁, h₁ with ⟨_, a::l⟩, h := nat.lt_succ_self _ end,
    ltb s₁.next s₂.next
  else s₁.curr < s₂.curr,
end
using_well_founded {rel_tac :=
  λ _ _, `[exact ⟨_, measure_wf (λ s, s.1.2.length)⟩]}

instance has_lt' : has_lt string :=
⟨λ s₁ s₂, ltb s₁.mk_iterator s₂.mk_iterator⟩

instance decidable_lt : @decidable_rel string (<) :=
by apply_instance -- short-circuit type class inference

@[simp] theorem lt_iff_to_list_lt :
  ∀ {s₁ s₂ : string}, s₁ < s₂ ↔ s₁.to_list < s₂.to_list
| ⟨i₁⟩ ⟨i₂⟩ :=
  suffices ∀ {p₁ p₂ s₁ s₂}, ltb ⟨p₁, s₁⟩ ⟨p₂, s₂⟩ ↔ s₁ < s₂, from this,
  begin
    intros,
    induction s₁ with a s₁ IH generalizing p₁ p₂ s₂;
      cases s₂ with b s₂; rw ltb; simp [iterator.has_next],
    { refl, },
    { exact iff_of_true rfl list.lex.nil },
    { exact iff_of_false bool.ff_ne_tt (not_lt_of_lt list.lex.nil) },
    { dsimp [iterator.has_next,
        iterator.curr, iterator.next],
      split_ifs,
      { subst b, exact IH.trans list.lex.cons_iff.symm },
      { simp, refine ⟨list.lex.rel, λ e, _⟩,
        cases e, {cases h rfl}, assumption } }
  end

instance has_le : has_le string := ⟨λ s₁ s₂, ¬ s₂ < s₁⟩

instance decidable_le : @decidable_rel string (≤) :=
by apply_instance -- short-circuit type class inference

@[simp] theorem le_iff_to_list_le
  {s₁ s₂ : string} : s₁ ≤ s₂ ↔ s₁.to_list ≤ s₂.to_list :=
(not_congr lt_iff_to_list_lt).trans not_lt

theorem to_list_inj : ∀ {s₁ s₂}, to_list s₁ = to_list s₂ ↔ s₁ = s₂
| ⟨s₁⟩ ⟨s₂⟩ := ⟨congr_arg _, congr_arg _⟩

lemma nil_as_string_eq_empty : [].as_string = "" := rfl

@[simp] lemma to_list_empty : "".to_list = [] := rfl

lemma as_string_inv_to_list (s : string) : s.to_list.as_string = s :=
by { cases s, refl }

@[simp] lemma to_list_singleton (c : char) : (string.singleton c).to_list = [c] := rfl

lemma to_list_nonempty : ∀ {s : string}, s ≠ string.empty →
  s.to_list = s.head :: (s.popn 1).to_list
| ⟨s⟩ h := by cases s; [cases h rfl, refl]

@[simp] lemma head_empty : "".head = default _ := rfl

@[simp] lemma popn_empty {n : ℕ} : "".popn n = "" :=
begin
  induction n with n hn,
  { refl },
  { rcases hs : "" with ⟨_ | ⟨hd, tl⟩⟩,
    { rw hs at hn,
      conv_rhs { rw ←hn },
      simp only [popn, mk_iterator, iterator.nextn, iterator.next] },
    { simpa only [←to_list_inj] using hs } }
end

instance : linear_order string :=
by refine_struct {
    lt := (<), le := (≤),
    decidable_lt := by apply_instance,
    decidable_le := string.decidable_le,
    decidable_eq := by apply_instance, .. };
  { simp only [le_iff_to_list_le, lt_iff_to_list_lt, ← to_list_inj], introv,
    apply_field }

end string

open string

lemma list.to_list_inv_as_string (l : list char) : l.as_string.to_list = l :=
by { cases hl : l.as_string, exact string_imp.mk.inj hl.symm }

@[simp] lemma list.length_as_string (l : list char) : l.as_string.length = l.length := rfl

@[simp] lemma list.as_string_inj {l l' : list char} : l.as_string = l'.as_string ↔ l = l' :=
⟨λ h, by rw [←list.to_list_inv_as_string l, ←list.to_list_inv_as_string l', to_list_inj, h],
 λ h, h ▸ rfl⟩

@[simp] lemma string.length_to_list (s : string) : s.to_list.length = s.length :=
by rw [←string.as_string_inv_to_list s, list.to_list_inv_as_string, list.length_as_string]

lemma list.as_string_eq {l : list char} {s : string} :
  l.as_string = s ↔ l = s.to_list :=
by rw [←as_string_inv_to_list s, list.as_string_inj, as_string_inv_to_list s]
