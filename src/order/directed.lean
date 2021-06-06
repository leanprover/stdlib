/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.lattice
import order.order_dual
import data.set.basic

universes u v w

variables {α : Type u} {β : Type v} {ι : Sort w} (r : α → α → Prop)
local infix ` ≼ ` : 50 := r

/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def directed (f : ι → α) := ∀x y, ∃z, f x ≼ f z ∧ f y ≼ f z

/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def directed_on (s : set α) := ∀ (x ∈ s) (y ∈ s), ∃z ∈ s, x ≼ z ∧ y ≼ z

variables {r}

theorem directed_on_iff_directed {s} : @directed_on α r s ↔ directed r (coe : s → α) :=
by simp [directed, directed_on]; refine ball_congr (λ x hx, by simp; refl)

alias directed_on_iff_directed ↔ directed_on.directed_coe _

theorem directed_on_image {s} {f : β → α} :
  directed_on r (f '' s) ↔ directed_on (f ⁻¹'o r) s :=
by simp only [directed_on, set.ball_image_iff, set.bex_image_iff, order.preimage]

theorem directed_on.mono {s : set α} (h : directed_on r s)
  {r' : α → α → Prop} (H : ∀ {a b}, r a b → r' a b) :
  directed_on r' s :=
λ x hx y hy, let ⟨z, zs, xz, yz⟩ := h x hx y hy in ⟨z, zs, H xz, H yz⟩

theorem directed_comp {ι} {f : ι → β} {g : β → α} :
  directed r (g ∘ f) ↔ directed (g ⁻¹'o r) f := iff.rfl

theorem directed.mono {s : α → α → Prop} {ι} {f : ι → α}
  (H : ∀ a b, r a b → s a b) (h : directed r f) : directed s f :=
λ a b, let ⟨c, h₁, h₂⟩ := h a b in ⟨c, H _ _ h₁, H _ _ h₂⟩

theorem directed.mono_comp {ι} {rb : β → β → Prop} {g : α → β} {f : ι → α}
  (hg : ∀ ⦃x y⦄, x ≼ y → rb (g x) (g y)) (hf : directed r f) :
  directed rb (g ∘ f) :=
directed_comp.2 $ hf.mono hg

/-- A `preorder` is a `directed_order` if for any two elements `i`, `j`
there is an element `k` such that `i ≤ k` and `j ≤ k`. -/
class directed_order (α : Type u) extends preorder α :=
(directed : ∀ i j : α, ∃ k, i ≤ k ∧ j ≤ k)

/-- A `preorder` is a `anti_directed_order` if for any two elements `i`, `j`
there is an element `k` such that `k ≤ i` and `k ≤ j`. -/
class anti_directed_order (α : Type u) extends preorder α :=
(directed : ∀ i j : α, ∃ k, k ≤ i ∧ k ≤ j)

@[priority 100]  -- see Note [lower instance priority]
instance semilattice_sup.to_directed_order (α) [semilattice_sup α] : directed_order α :=
⟨λ i j, ⟨i ⊔ j, le_sup_left, le_sup_right⟩⟩

@[priority 100]  -- see Note [lower instance priority]
instance semilattice_inf.to_anti_directed_order (α) [semilattice_inf α] : anti_directed_order α :=
⟨λ i j, ⟨i ⊓ j, inf_le_left, inf_le_right⟩⟩

instance (α) [anti_directed_order α] : directed_order (order_dual α) :=
⟨anti_directed_order.directed⟩

instance (α) [directed_order α] : anti_directed_order (order_dual α) :=
⟨directed_order.directed⟩

/-- A monotone function on a directed order (in particular a sup-semilattice) is directed. -/
lemma directed_of_sup [directed_order α] {f : α → β} {r : β → β → Prop}
  (H : ∀ ⦃i j⦄, i ≤ j → r (f i) (f j)) : directed r f :=
λ a b, (directed_order.directed a b).imp $ λ c, and.imp @@H @@H

/-- An antimonotone function on an anti-directed order (in particular an inf-semilattice) is
directed. -/
lemma directed_of_inf [anti_directed_order α] {r : β → β → Prop} {f : α → β}
  (H : ∀ ⦃i j⦄, i ≤ j → r (f j) (f i)) : directed r f :=
λ a b, (anti_directed_order.directed a b).imp $ λ c, and.imp @@H @@H

/-- A version of `directed_of_sup` acting on `monotone` -/
lemma monotone.directed_le [directed_order α] [preorder β] {f : α → β} :
  monotone f → directed (≤) f :=
directed_of_sup

/-! Lemmas about `order_dual`. -/

lemma directed.le_to_dual [has_le β] {f : α → β} (h : directed (≤) f) :
  directed (≥) (order_dual.to_dual ∘ f) :=
h

lemma directed.ge_to_dual [has_le β] {f : α → β} (h : directed (≥) f) :
  directed (≤) (order_dual.to_dual ∘ f) :=
h

lemma directed.le_of_dual [has_le β] {f : α → order_dual β} (h : directed (≤) f) :
  directed (≥) (order_dual.of_dual ∘ f) :=
h

lemma directed.ge_of_dual [has_le β] {f : α → order_dual β} (h : directed (≥) f) :
  directed (≤) (order_dual.of_dual ∘ f) :=
h
