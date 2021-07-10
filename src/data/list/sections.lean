/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.list.forall2

/-!
# List sections

This file proves some stuff about `list.sections` (definition in `data.list.defs`). A section of a
list of lists `[l₁, ..., lₙ]` is a list whose `i`-th element comes from the `i`-th list.
-/


open nat function

namespace list
variables {α β : Type*}

theorem mem_sections {L : list (list α)} {f} : f ∈ sections L ↔ forall₂ (∈) f L :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { induction L generalizing f, {cases mem_singleton.1 h, exact forall₂.nil},
    simp only [sections, bind_eq_bind, mem_bind, mem_map] at h,
    rcases h with ⟨_, _, _, _, rfl⟩,
    simp only [*, forall₂_cons, true_and] },
  { induction h with a l f L al fL fs, {exact or.inl rfl},
    simp only [sections, bind_eq_bind, mem_bind, mem_map],
    exact ⟨_, fs, _, al, rfl, rfl⟩ }
end

theorem mem_sections_length {L : list (list α)} {f} (h : f ∈ sections L) : length f = length L :=
forall₂_length_eq (mem_sections.1 h)

lemma rel_sections {r : α → β → Prop} :
  (forall₂ (forall₂ r) ⇒ forall₂ (forall₂ r)) sections sections
| _ _ forall₂.nil := forall₂.cons forall₂.nil forall₂.nil
| _ _ (forall₂.cons h₀ h₁) :=
  rel_bind (rel_sections h₁) (assume _ _ hl, rel_map (assume _ _ ha, forall₂.cons ha hl) h₀)

end list
