/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Type class hierarchy for Boolean algebras.
-/
import order.bounded_lattice
import order.heyting_algebra

set_option old_structure_cmd true

universes u v
variables {α : Type u} {w x y z : α}

/-- Set / lattice complement -/
class has_compl (α : Type*) := (compl : α → α)

export has_compl (compl)

postfix `ᶜ`:(max+1) := compl

/-- A boolean algebra is a bounded distributive lattice with a
  complementation operation `-` such that `x ⊓ - x = ⊥` and `x ⊔ - x = ⊤`.
  This is a generalization of (classical) logic of propositions, or
  the powerset lattice. -/
class boolean_algebra α extends bounded_distrib_lattice α, has_compl α, has_sdiff α :=
(inf_compl_le_bot : ∀x:α, x ⊓ xᶜ ≤ ⊥)
(top_le_sup_compl : ∀x:α, ⊤ ≤ x ⊔ xᶜ)
(sdiff_eq : ∀x y:α, x \ y = x ⊓ yᶜ)

section boolean_algebra
variables [boolean_algebra α]

@[simp] theorem inf_compl_eq_bot : x ⊓ xᶜ = ⊥ :=
bot_unique $ boolean_algebra.inf_compl_le_bot x

@[simp] theorem compl_inf_eq_bot : xᶜ ⊓ x = ⊥ :=
eq.trans inf_comm inf_compl_eq_bot

@[simp] theorem sup_compl_eq_top : x ⊔ xᶜ = ⊤ :=
top_unique $ boolean_algebra.top_le_sup_compl x

@[simp] theorem compl_sup_eq_top : xᶜ ⊔ x = ⊤ :=
eq.trans sup_comm sup_compl_eq_top

theorem is_compl_compl : is_compl x xᶜ :=
is_compl.of_eq inf_compl_eq_bot sup_compl_eq_top

theorem is_compl.eq_compl (h : is_compl x y) : x = yᶜ :=
h.left_unique is_compl_compl.symm

theorem is_compl.compl_eq (h : is_compl x y) : xᶜ = y :=
(h.right_unique is_compl_compl).symm

theorem disjoint_compl_right : disjoint x xᶜ := is_compl_compl.disjoint
theorem disjoint_compl_left : disjoint xᶜ x := disjoint_compl_right.symm

theorem sdiff_eq : x \ y = x ⊓ yᶜ :=
boolean_algebra.sdiff_eq x y

theorem compl_unique (i : x ⊓ y = ⊥) (s : x ⊔ y = ⊤) : xᶜ = y :=
(is_compl.of_eq i s).compl_eq

@[simp] theorem compl_top : ⊤ᶜ = (⊥:α) :=
is_compl_top_bot.compl_eq

@[simp] theorem compl_bot : ⊥ᶜ = (⊤:α) :=
is_compl_bot_top.compl_eq

@[simp] theorem compl_compl (x : α) : xᶜᶜ = x :=
is_compl_compl.symm.compl_eq

theorem compl_injective : function.injective (compl : α → α) :=
function.involutive.injective compl_compl

@[simp] theorem compl_inj_iff : xᶜ = yᶜ ↔ x = y :=
compl_injective.eq_iff

theorem is_compl.compl_eq_iff (h : is_compl x y) : zᶜ = y ↔ z = x :=
h.compl_eq ▸ compl_inj_iff

@[simp] theorem compl_eq_top : xᶜ = ⊤ ↔ x = ⊥ :=
is_compl_bot_top.compl_eq_iff

@[simp] theorem compl_eq_bot : xᶜ = ⊥ ↔ x = ⊤ :=
is_compl_top_bot.compl_eq_iff

@[simp] theorem compl_inf : (x ⊓ y)ᶜ = xᶜ ⊔ yᶜ :=
(is_compl_compl.inf_sup is_compl_compl).compl_eq

@[simp] theorem compl_sup : (x ⊔ y)ᶜ = xᶜ ⊓ yᶜ :=
(is_compl_compl.sup_inf is_compl_compl).compl_eq

theorem compl_le_compl (h : y ≤ x) : xᶜ ≤ yᶜ :=
is_compl_compl.antimono is_compl_compl h

@[simp] theorem compl_le_compl_iff_le : yᶜ ≤ xᶜ ↔ x ≤ y :=
⟨assume h, by have h := compl_le_compl h; simp at h; assumption,
  compl_le_compl⟩

theorem le_compl_of_le_compl (h : y ≤ xᶜ) : x ≤ yᶜ :=
by simpa only [compl_compl] using compl_le_compl h

theorem compl_le_of_compl_le (h : yᶜ ≤ x) : xᶜ ≤ y :=
by simpa only [compl_compl] using compl_le_compl h

theorem le_compl_iff_le_compl : y ≤ xᶜ ↔ x ≤ yᶜ :=
⟨le_compl_of_le_compl, le_compl_of_le_compl⟩

theorem compl_le_iff_compl_le : xᶜ ≤ y ↔ yᶜ ≤ x :=
⟨compl_le_of_compl_le, compl_le_of_compl_le⟩

theorem sup_sdiff_same : x ⊔ (y \ x) = x ⊔ y :=
by simp [sdiff_eq, sup_inf_left]

theorem sdiff_eq_left (h : x ⊓ y = ⊥) : x \ y = x :=
by rwa [sdiff_eq, inf_eq_left, is_compl_compl.le_right_iff, disjoint_iff]

theorem sdiff_le_sdiff (h₁ : w ≤ y) (h₂ : z ≤ x) : w \ x ≤ y \ z :=
by rw [sdiff_eq, sdiff_eq]; from inf_le_inf h₁ (compl_le_compl h₂)

@[simp] lemma sdiff_idem_right : x \ y \ y = x \ y :=
by rw [sdiff_eq, sdiff_eq, inf_assoc, inf_idem]

namespace boolean_algebra

@[priority 100]
instance : is_complemented α := ⟨λ x, ⟨xᶜ, is_compl_compl⟩⟩

end boolean_algebra

end boolean_algebra

instance boolean_algebra_Prop : boolean_algebra Prop :=
{ compl := not,
  sdiff := λ p q, p ∧ ¬ q,
  sdiff_eq := λ _ _, rfl,
  inf_compl_le_bot := λ p ⟨Hp, Hpc⟩, Hpc Hp,
  top_le_sup_compl := λ p H, classical.em p,
  .. bounded_distrib_lattice_Prop }

instance pi.boolean_algebra {α : Type u} {β : Type v} [boolean_algebra β] :
  boolean_algebra (α → β) :=
by pi_instance

instance has_internal_imp_of_boolean {α} [H : boolean_algebra α] : has_internal_imp α :=
  {imp := λ x y, xᶜ ⊔ y}

@[simp] lemma boolean_imp_eq {α} [H : boolean_algebra α] (x y : α) : (x ⇨ y) = xᶜ ⊔ y := rfl

lemma heyting_of_boolean_aux_aux {α}
  [H : boolean_algebra α]
  (x y z : α)
  (h_1 : x ≤ yᶜ ⊔ z)
  (h_2 : x ≤ y)
  : x ≤ z :=
  calc
    x ≤ (y ⊓ (yᶜ ⊔ z)) : le_inf h_2 h_1
    ... = (y ⊓ yᶜ) ⊔ (y ⊓ z) : inf_sup_left
    ... ≤ ((y ⊓ yᶜ) ⊔ z) : sup_le_sup_left inf_le_right (y ⊓ yᶜ)
    ... = ⊥ ⊔ z : by {congr, exact inf_compl_eq_bot}
    ... = z : by {exact bot_sup_eq}

lemma heyting_of_boolean_aux {α}
  [H : boolean_algebra α]
  (x y z : α)
  (h : x ⊓ y ≤ yᶜ ⊔ z) :
  x ⊓ y ≤ z := heyting_of_boolean_aux_aux (x ⊓ y) y z h inf_le_right

instance heyting_of_boolean {α} [H : boolean_algebra α] : heyting_algebra α :=
  {
    imp_adjoint := λ x y z,
      begin
        rw boolean_imp_eq,
        symmetry,
        split; intros h,
        refine heyting_of_boolean_aux x y z (le_trans inf_le_left h),
        {
          transitivity x ⊓ (y ⊔ yᶜ),
          refine le_inf (le_refl x) (le_trans le_top (boolean_algebra.top_le_sup_compl y)),
          refine le_trans inf_sup_left.le (le_trans (sup_le_sup h inf_le_right) sup_comm.le),
        }
      end,
    ..H,
    .. @has_internal_imp_of_boolean α H,
  }
