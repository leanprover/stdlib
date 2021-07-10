/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import order.complete_lattice
import dynamics.fixed_points.basic

/-!
# Fixed point construction on complete lattices

This file sets up the basic theory of fixed points of a monotone function in a complete lattice

## Main definitions

* `lfp`: The least fixed point of a monotone function.
* `gfp`: The greatest fixed point of a monotone function.
* `prev_fixed`: The least fixed point of a monotone function greater than a given element.
* `next_fixed`: The greatest fixed point of a monotone function smaller than a given element.
* `fixed_points.complete_lattice`: The Knaster-Tarski theorem: fixed points form themselves a
  complete lattice.

## Tags

fixed point, complete lattice, monotone function
-/

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open function (fixed_points)

section fixedpoint
variables [complete_lattice α] {f : α → α}

/-- Least fixed point of a monotone function -/
def lfp (f : α → α) : α := Inf {a | f a ≤ a}
/-- Greatest fixed point of a monotone function -/
def gfp (f : α → α) : α := Sup {a | a ≤ f a}

lemma lfp_le {a : α} (h : f a ≤ a) : lfp f ≤ a :=
Inf_le h

lemma le_lfp {a : α} (h : ∀ b, f b ≤ b → a ≤ b) : a ≤ lfp f :=
le_Inf h

lemma lfp_fixed_point (hf : monotone f) : f (lfp f) = lfp f :=
have h : f (lfp f) ≤ lfp f,
  from le_lfp (λ b hb, (hf (lfp_le hb)).trans hb),
h.antisymm (lfp_le (hf h))

lemma lfp_induction {p : α → Prop} (hf : monotone f) (step : ∀ a, p a → a ≤ lfp f → p (f a))
  (hSup : ∀ s, (∀ a ∈ s, p a) → p (Sup s)) :
  p (lfp f) :=
begin
  let s := {a | a ≤ lfp f ∧ p a},
  have hpSup := hSup s (λ a ha, ha.2),
  have h : Sup s ≤ lfp f := le_lfp (λ a ha, Sup_le (λ b hb, hb.1.trans (lfp_le ha))),
  rw ←h.antisymm (lfp_le (le_Sup ⟨(hf h).trans (lfp_fixed_point hf).le, step _ hpSup h⟩)),
  exact hpSup,
end

lemma monotone_lfp : monotone (@lfp α _) :=
λ f g h, le_lfp $ λ a ha, lfp_le $ (h a).trans ha

lemma le_gfp {a : α} (h : a ≤ f a) : a ≤ gfp f :=
le_Sup h

lemma gfp_le {a : α} (h : ∀ b, b ≤ f b → b ≤ a) : gfp f ≤ a :=
Sup_le h

lemma gfp_fixed_point (hf : monotone f) : f (gfp f) = gfp f :=
have h : gfp f ≤ f (gfp f),
  from gfp_le $ λ a ha, ha.trans (hf (le_gfp ha)),
(le_gfp (hf h)).antisymm h

lemma gfp_induction {p : α → Prop} (hf : monotone f)
  (step : ∀ a, p a → gfp f ≤ a → p (f a)) (hInf : ∀ s, (∀ a ∈ s, p a) → p (Inf s)) :
  p (gfp f) :=
begin
  let s := {a | gfp f ≤ a ∧ p a},
  have hpInf := hInf s (λ a ha, ha.2),
  have h : gfp f ≤ Inf s := gfp_le (λ a ha, le_Inf (λ b hb, (le_gfp ha).trans hb.1)),
  rw h.antisymm (le_gfp (Inf_le ⟨(gfp_fixed_point hf).ge.trans (hf h), step _ hpInf h⟩)),
  exact hpInf,
end

lemma monotone_gfp : monotone (@gfp α _) :=
λ f g h, gfp_le $ λ a ha, le_gfp $ ha.trans (h a)

end fixedpoint

section fixedpoint_eqn
variables [complete_lattice α] [complete_lattice β] {f : β → α} {g : α → β}

-- Rolling rule
lemma lfp_comp (hf : monotone f) (hg : monotone g) : lfp (f ∘ g) = f (lfp (g ∘ f)) :=
le_antisymm (lfp_le $ hf (lfp_fixed_point (hg.comp hf)).le)
  (le_lfp $ λ a ha, (hf $ lfp_le $ show (g ∘ f) (g a) ≤ g a, from hg ha).trans ha)

lemma gfp_comp (hf : monotone f) (hg : monotone g) : gfp (f ∘ g) = f (gfp (g ∘ f)) :=
(gfp_le $ λ a ha, ha.trans $ hf $ le_gfp $ show g a ≤ (g ∘ f) (g a), from hg ha).antisymm
  (le_gfp $ hf (gfp_fixed_point (hg.comp hf)).ge)

-- Diagonal rule
lemma lfp_lfp {h : α → α → α} (m : ∀ ⦃a b c d⦄, a ≤ b → c ≤ d → h a c ≤ h b d) :
  lfp (lfp ∘ h) = lfp (λ x, h x x) :=
begin
  let a := lfp (lfp ∘ h),
  refine (lfp_le _).antisymm (lfp_le (eq.le _)),
  { exact lfp_le (lfp_fixed_point (λ a b hab, m hab hab)).le },
  have ha : (lfp ∘ h) a = a := lfp_fixed_point
    ((monotone_lfp : monotone (_ : _ → α)).comp (λ b c hbc x, m hbc le_rfl)),
  calc h a a = h a (lfp (h a)) : congr_arg (h a) ha.symm
       ... = (lfp ∘ h) a       : lfp_fixed_point $ λ b c hbc, m le_rfl hbc
       ... = a                 : ha,
end

lemma gfp_gfp {h : α → α → α} (m : ∀ ⦃a b c d⦄, a ≤ b → c ≤ d → h a c ≤ h b d) :
  gfp (gfp ∘ h) = gfp (λ x, h x x) :=
begin
  let a := gfp (gfp ∘ h),
  refine (le_gfp (eq.ge _)).antisymm (le_gfp (le_gfp (gfp_fixed_point (λ a b hab, m hab hab)).ge)),
  have ha : (gfp ∘ h) a = a := gfp_fixed_point
    ((monotone_gfp : monotone (_ : _ → α)).comp (λ b c hbc x, m hbc le_rfl)),
  calc h a a = h a (gfp (h a)) : congr_arg (h a) ha.symm
         ... = (gfp ∘ h) a     : gfp_fixed_point $ λ b c hbc, m le_rfl hbc
         ... = a               : ha,
end

end fixedpoint_eqn

/- The complete lattice of fixed points of a function f -/
namespace fixed_points
variables [complete_lattice α] (f : α → α) (hf : monotone f)

def prev (x : α) : α := gfp (λ z, x ⊓ f z)
def next (x : α) : α := lfp (λ z, x ⊔ f z)

variable {f}

lemma prev_le {x : α} : prev f x ≤ x := gfp_le $ λ z hz, hz.trans inf_le_left

lemma prev_eq (hf : monotone f) {a : α} (h : f a ≤ a) : f (prev f a) = prev f a :=
calc f (prev f a) = a ⊓ f (prev f a) : (inf_of_le_right $ (hf prev_le).trans h).symm
              ... = prev f a         : gfp_fixed_point $ λ x y h, inf_le_inf_left _ (hf h)

def prev_fixed (hf : monotone f) (a : α) (h : f a ≤ a) : fixed_points f :=
⟨prev f a, prev_eq hf h⟩

lemma le_next {x : α} : x ≤ next f x := le_lfp $ λ z hz, le_sup_left.trans hz

lemma next_eq (hf : monotone f) {a : α} (h : a ≤ f a) : f (next f a) = next f a :=
calc f (next f a) = a ⊔ f (next f a) : (sup_of_le_right $ h.trans (hf le_next)).symm
              ... = next f a         : lfp_fixed_point $ λ x y h, sup_le_sup_left (hf h) _

def next_fixed (hf : monotone f) (a : α) (h : a ≤ f a) : fixed_points f :=
⟨next f a, next_eq hf h⟩

variable f

lemma sup_le_f_of_fixed_points (x y : fixed_points f) : x.1 ⊔ y.1 ≤ f (x.1 ⊔ y.1) :=
sup_le (x.2.ge.trans (hf le_sup_left)) (y.2.ge.trans (hf le_sup_right))

lemma f_le_inf_of_fixed_points (x y : fixed_points f) : f (x.1 ⊓ y.1) ≤ x.1 ⊓ y.1 :=
le_inf ((hf inf_le_left).trans x.2.le) ((hf inf_le_right).trans y.2.le)

lemma Sup_le_f_of_fixed_points (A : set α) (hA : A ⊆ fixed_points f) : Sup A ≤ f (Sup A) :=
Sup_le $ λ x hx, (hA hx) ▸ (hf $ le_Sup hx)

lemma f_le_Inf_of_fixed_points (A : set α) (hA : A ⊆ fixed_points f) : f (Inf A) ≤ Inf A :=
le_Inf $ λ x hx, (hA hx) ▸ (hf $ Inf_le hx)

/-- **Knaster-Tarski Theorem**: The fixed points of `f` form a complete lattice.
This cannot be an instance, since it depends on the monotonicity of `f`. -/
protected def complete_lattice : complete_lattice (fixed_points f) :=
{ le           := (≤),
  le_refl      := le_refl,
  le_trans     := λ x y z, le_trans,
  le_antisymm  := λ x y, le_antisymm,

  sup          := λ x y, next_fixed hf (x.1 ⊔ y.1) (sup_le_f_of_fixed_points f hf x y),
  le_sup_left  := λ x y, (le_sup_left.trans le_next : x.1 ≤ _),
  le_sup_right := λ x y, (le_sup_right.trans le_next : y.1 ≤ _),
  sup_le       := λ x y z hxz hyz, lfp_le $ sup_le (sup_le hxz hyz) (z.2.symm ▸ le_refl z.1),

  inf          := λ x y, prev_fixed hf (x.1 ⊓ y.1) (f_le_inf_of_fixed_points f hf x y),
  inf_le_left  := λ x y, (prev_le.trans inf_le_left : _ ≤ x.1),
  inf_le_right := λ x y, (prev_le.trans inf_le_right : _ ≤ y.1),
  le_inf       := λ x y z hxy hxz, le_gfp $ le_inf (le_inf hxy hxz) (x.2.symm ▸ le_refl x),

  top          := prev_fixed hf ⊤ le_top,
  le_top       := λ ⟨x, hx⟩, le_gfp $ le_inf le_top (hx.symm ▸ le_rfl),

  bot          := next_fixed hf ⊥ bot_le,
  bot_le       := λ ⟨x, hx⟩, lfp_le $ sup_le bot_le (hx.symm ▸ le_rfl),

  Sup          := λ A, next_fixed hf (Sup $ subtype.val '' A)
    (Sup_le_f_of_fixed_points f hf (subtype.val '' A) (λ z ⟨x, hx⟩, hx.2 ▸ x.2)),
  le_Sup       := λ A x hx, (le_Sup $ show x.1 ∈ subtype.val '' A, from ⟨x, hx, rfl⟩).trans le_next,
  Sup_le       := λ A x hx, lfp_le $ sup_le (Sup_le $ λ z ⟨y, hyA, hyz⟩, hyz ▸ hx y hyA)
    (x.2.symm ▸ le_rfl),

  Inf          := λ A, prev_fixed hf (Inf $ subtype.val '' A)
    (f_le_Inf_of_fixed_points f hf (subtype.val '' A) (λ z ⟨x, hx⟩, hx.2 ▸ x.2)),
  le_Inf       := λ A x hx, le_gfp $ le_inf (le_Inf $ λ z ⟨y, hyA, hyz⟩, hyz ▸ hx y hyA)
    (x.2.symm ▸ le_rfl),
  Inf_le       := λ A x hx, prev_le.trans (Inf_le $ show x.1 ∈ subtype.val '' A, from ⟨x, hx, rfl⟩)}

end fixed_points
