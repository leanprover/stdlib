/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import algebra.ordered_pi
import order.well_founded

variables {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop)
  (s : Π {i}, β i → β i → Prop)

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
  and each `β i` is ordered by `s`. -/
def pi.lex (x y : Π i, β i) : Prop :=
∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

/-- The cartesian product of an indexed family, equipped with the lexicographic order. -/
def pilex (α : Type*) (β : α → Type*) : Type* := Π a, β a

instance [has_lt ι] [∀ a, has_lt (β a)] : has_lt (pilex ι β) :=
{ lt := pi.lex (<) (λ _, (<)) }

instance [∀ a, inhabited (β a)] : inhabited (pilex ι β) :=
by unfold pilex; apply_instance

set_option eqn_compiler.zeta true

instance [linear_order ι] [∀ a, partial_order (β a)] : partial_order (pilex ι β) :=
have lt_not_symm : ∀ {x y : pilex ι β}, ¬ (x < y ∧ y < x),
  from λ x y ⟨⟨i, hi⟩, ⟨j, hj⟩⟩, begin
      rcases lt_trichotomy i j with hij | hij | hji,
      { exact lt_irrefl (x i) (by simpa [hj.1 _ hij] using hi.2) },
      { exact not_le_of_gt hj.2 (hij ▸ le_of_lt hi.2) },
      { exact lt_irrefl (x j) (by simpa [hi.1 _ hji] using hj.2) },
    end,
{ le := λ x y, x < y ∨ x = y,
  le_refl := λ _, or.inr rfl,
  le_antisymm := λ x y hxy hyx,
    hxy.elim (λ hxy, hyx.elim (λ hyx, false.elim (lt_not_symm ⟨hxy, hyx⟩)) eq.symm) id,
  le_trans :=
    λ x y z hxy hyz,
    hxy.elim
      (λ ⟨i, hi⟩, hyz.elim
        (λ ⟨j, hj⟩, or.inl
          ⟨by exactI min i j, by resetI; exact
            λ k hk, by rw [hi.1 _ (lt_min_iff.1 hk).1, hj.1 _ (lt_min_iff.1 hk).2],
            by resetI; exact (le_total i j).elim
              (λ hij, by rw [min_eq_left hij];
                exact lt_of_lt_of_le hi.2
                  ((lt_or_eq_of_le hij).elim (λ h, le_of_eq (hj.1 _ h))
                    (λ h, h.symm ▸ le_of_lt hj.2)))
              (λ hji, by rw [min_eq_right hji];
                exact lt_of_le_of_lt
                  ((lt_or_eq_of_le hji).elim (λ h, le_of_eq (hi.1 _ h))
                    (λ h, h.symm ▸ le_of_lt hi.2))
                  hj.2)⟩)
        (λ hyz, hyz ▸ hxy))
      (λ hxy, hxy.symm ▸ hyz),
  lt_iff_le_not_le := λ x y, show x < y ↔ (x < y ∨ x = y) ∧ ¬ (y < x ∨ y = x),
    from ⟨λ ⟨i, hi⟩, ⟨or.inl ⟨i, hi⟩,
        λ h, h.elim (λ ⟨j, hj⟩, begin
            rcases lt_trichotomy i j with hij | hij | hji,
            { exact lt_irrefl (x i) (by simpa [hj.1 _ hij] using hi.2) },
            { exact not_le_of_gt hj.2 (hij ▸ le_of_lt hi.2) },
            { exact lt_irrefl (x j) (by simpa [hi.1 _ hji] using hj.2) },
          end)
        (λ hyx, lt_irrefl (x i) (by simpa [hyx] using hi.2))⟩, by tauto⟩,
  ..pilex.has_lt }

/-- `pilex` is a linear order if the original order is well-founded.
This cannot be an instance, since it depends on the well-foundedness of `<`. -/
protected noncomputable def pilex.linear_order [linear_order ι]
  (wf : well_founded ((<) : ι → ι → Prop)) [∀ a, linear_order (β a)] :
  linear_order (pilex ι β) :=
{ le_total := λ x y, by classical; exact
    or_iff_not_imp_left.2 (λ hxy, begin
      have := not_or_distrib.1 hxy,
      let i : ι := well_founded.min wf _ (not_forall.1 (this.2 ∘ funext)),
      have hjiyx : ∀ j < i, y j = x j,
      { assume j,
        rw [eq_comm, ← not_imp_not],
        exact λ h, well_founded.not_lt_min wf _ _ h },
      refine or.inl ⟨i, hjiyx, _⟩,
      { refine lt_of_not_ge (λ hyx, _),
        exact this.1 ⟨i, (λ j hj, (hjiyx j hj).symm),
          lt_of_le_of_ne hyx (well_founded.min_mem _ {i | x i ≠ y i} _)⟩ }
    end),
  decidable_le := classical.dec_rel _,
  ..pilex.partial_order }

instance [linear_order ι] [∀ a, ordered_add_comm_group (β a)] : ordered_add_comm_group (pilex ι β) :=
{ add_le_add_left := λ x y hxy z,
    hxy.elim
      (λ ⟨i, hi⟩,
        or.inl ⟨i, λ j hji, show z j + x j = z j + y j, by rw [hi.1 j hji],
          add_lt_add_left hi.2 _⟩)
      (λ hxy, hxy ▸ le_refl _),
  ..pilex.partial_order,
  ..pi.add_comm_group }
