/-
Copyright (c) 2020 Chris A. Upshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris A. Upshaw.

Type class hierarchy for Heyting algebras.
-/
import order.bounded_lattice

set_option old_structure_cmd true

/-!
# Heyting algebra

In this file we introduce Heyting algebras.

A Heyting algebra is a bounded distributed lattice with an internal implication.

Having an internal implication and a bottom allows for defining an (possilbe intuitionistic)
complement.

## Notation

 - ` ⇨ ` : implication as an operator internal to a lattice.

-/

universes u v
variables {α : Type u} {w x y z : α}

class has_internal_imp (α : Type*) :=
  (imp : α → α → α)

infixr ` ⇨ `:60 := has_internal_imp.imp

/-- A heyting algebra is a bounded distributive lattice with a internal implication right adjoint to
 the meet. This also allows the definition of a psudo-complement `ᶜ` such that `x ⊓ xᶜ = ⊥`,
 (but not nessarily `x ⊔ xᶜ = ⊤`).

  This is a generalization of the logic of propositions and of open sets of a topology, though
  heyting algebra morphisms are distinct from images of continous functions.
  -/
class heyting_algebra α extends bounded_distrib_lattice α, has_internal_imp α :=
  (imp_adjoint : ∀ x y z : α, x ⊓ y ≤ z ↔ x ≤ y ⇨ z)

export heyting_algebra (imp_adjoint)

section heyting_algebra
variables [heyting_algebra α]

@[simp] lemma internal_imp_refl : x ⇨ x = ⊤ :=
  begin
    rw le_antisymm_iff,
    split,
      {exact le_top},
      {
        rw ← imp_adjoint,
        exact inf_le_right
      },
  end

lemma internal_imp_mp : x ⊓ (x ⇨ y) ≤ y :=
  begin
    rw inf_comm,
    rw imp_adjoint,
    reflexivity,
  end

lemma le_internal_imp : x ≤ (y ⇨ x) :=
  begin
    rw ← imp_adjoint,
    exact inf_le_left,
  end

@[simp]
lemma inf_imp_eq_inf_left : x ⊓ (x ⇨ y) = x ⊓ y :=
  le_antisymm (le_inf inf_le_left internal_imp_mp) (inf_le_inf (le_refl x) le_internal_imp)

lemma imp_app : (x ⇨ y) ⊓ x ≤ y :=
  begin
    rw inf_comm,
    exact internal_imp_mp
  end

@[simp]
lemma imp_inf_eq_left_inf : (x ⇨ y) ⊓ x = y ⊓ x:=
  le_antisymm (le_inf imp_app inf_le_right) (inf_le_inf le_internal_imp rfl.ge)
end heyting_algebra

instance has_internal_imp_prop : has_internal_imp Prop := ⟨λ x y, x → y⟩

lemma imp_adjoint_prop (a b c : Prop) : (a ⊓ b ≤ c) ↔ (a ≤ b ⇨ c) :=
  begin
    unfold has_internal_imp.imp,
    simp,
    split; intros iff_hyp hyp; try {intro hyp_b}; apply iff_hyp;
      try {cases hyp}; try {split}; assumption
  end

instance heyting_algebra_prop : heyting_algebra Prop :=
  {
    imp_adjoint := imp_adjoint_prop,
    ..has_internal_imp_prop,
    ..bounded_distrib_lattice_Prop
  }

instance pi.heyting_algebra {α : Type u} {β : Type v} [heyting_algebra β] :
  heyting_algebra (α → β) :=
  begin
    pi_instance,
    intros,
    simp only [],
    transitivity ∀ i, (x i) ⊓ (y i) ≤ z i,
    {
      have inf_unfolded : ∀ i : α, (x ⊓ y) i = x i ⊓ y i := λ i, begin simp end,
      split; intros hyp i;
        try { rw inf_unfolded i}; try {rw ← inf_unfolded i};
        exact hyp i,
    },
    symmetry,
    transitivity (∀ i : α, x i ≤ heyting_algebra.imp (y i) (z i)),
    {
      have h : ∀ x' : α → β, x ≤ x' ↔ ∀ i, x i ≤ x' i,
        {
          unfold_projs,
          intros, split; intros x_le_x'; apply x_le_x',
        },
      rw h,
    },
    have h : ∀ p q : α → Prop, (∀ i, p i ↔ q i) → ((∀ i, p i) ↔ (∀ i, q i))
      := λ p q hyp, begin finish end,
    rw h, clear h,
    intros,
    symmetry,
    apply heyting_algebra.imp_adjoint,
  end
