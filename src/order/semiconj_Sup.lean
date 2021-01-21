/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import order.ord_continuous

/-!
# Semiconjugate by `Sup`

In this file we prove two facts about semiconjugate (families of) functions.

First, if an order isomorphism `fa : α → α` is semiconjugate to an order embedding `fb : β → β` by
`g : α → β`, then `fb` is semiconjugate to `fa` by `y ↦ Sup {x | g x ≤ y}`, see
`semiconj.symm_adjoint`.

Second, consider two actions `f₁ f₂ : G → α → α` of a group on a complete lattice by order
isomorphisms. Then the map `x ↦ ⨆ g : G, (f₁ g)⁻¹ (f₂ g x)` semiconjugates each `f₁ g'` to `f₂ g'`,
see `function.Sup_div_semiconj`.  In the case of a conditionally complete lattice, a similar
statement holds true under an additional assumption that each set `{(f₁ g)⁻¹ (f₂ g x) | g : G}` is
bounded above, see `function.cSup_div_semiconj`.

The lemmas come from [Étienne Ghys, Groupes d'homeomorphismes du cercle et cohomologie
bornee][ghys87:groupes], Proposition 2.1 and 5.4 respectively. In the paper they are formulated for
homeomorphisms of the circle, so in order to apply results from this file one has to lift these
homeomorphisms to the real line first.
-/

variables {α : Type*} {β : Type*}

open set

/-- We say that `g : β → α` is an order right adjoint function for `f : α → β` if it sends each `y`
to a least upper bound for `{x | f x ≤ y}`. If `α` is a partial order, and `f : α → β` has
a right adjoint, then this right adjoint is unique. -/
def is_order_right_adjoint [preorder α] [preorder β] (f : α → β) (g : β → α) :=
∀ y, is_lub {x | f x ≤ y} (g y)

lemma is_order_right_adjoint_Sup [complete_lattice α] [preorder β] (f : α → β) :
  is_order_right_adjoint f (λ y, Sup {x | f x ≤ y}) :=
λ y, is_lub_Sup _

lemma is_order_right_adjoint_cSup [conditionally_complete_lattice α] [preorder β] (f : α → β)
  (hne : ∀ y, ∃ x, f x ≤ y) (hbdd : ∀ y, ∃ b, ∀ x, f x ≤ y → x ≤ b) :
  is_order_right_adjoint f (λ y, Sup {x | f x ≤ y}) :=
λ y, is_lub_cSup (hne y) (hbdd y)

lemma is_order_right_adjoint.unique [partial_order α] [preorder β] {f : α → β} {g₁ g₂ : β → α}
  (h₁ : is_order_right_adjoint f g₁) (h₂ : is_order_right_adjoint f g₂) :
  g₁ = g₂ :=
funext $ λ y, (h₁ y).unique (h₂ y)

lemma is_order_right_adjoint.right_mono [preorder α] [preorder β] {f : α → β} {g : β → α}
  (h : is_order_right_adjoint f g) :
  monotone g :=
λ y₁ y₂ hy, (h y₁).mono (h y₂) $ λ x hx, le_trans hx hy

namespace function

/-- If an order automorphism `fa` is semiconjugate to an order embedding `fb` by a function `g`
and `g'` is an order right adjoint of `g` (i.e. `g' y = Sup {x | f x ≤ y}`), then `fb` is
semiconjugate to `fa` by `g'`.

This is a version of Proposition 2.1 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
cohomologie bornee][ghys87:groupes]. -/
lemma semiconj.symm_adjoint [partial_order α] [preorder β]
  {fa : α ≃o α}
  {fb : β ↪o β} {g : α → β}
  (h : function.semiconj g fa fb) {g' : β → α} (hg' : is_order_right_adjoint g g') :
  function.semiconj g' fb fa :=
begin
  refine λ y, (hg' _).unique _,
  rw [← fa.surjective.image_preimage {x | g x ≤ fb y}, preimage_set_of_eq],
  simp only [h.eq, fb.le_iff_le, fa.left_ord_continuous (hg' _)]
end

variable {G : Type*}

lemma semiconj_of_is_lub [partial_order α] [group G]
  (f₁ f₂ : G →* (α ≃o α)) {h : α → α}
  (H : ∀ x, is_lub (range (λ g', (f₁ g')⁻¹ (f₂ g' x))) (h x)) (g : G) :
  function.semiconj h (f₂ g) (f₁ g) :=
begin
  refine λ y, (H _).unique _,
  have := (f₁ g).left_ord_continuous (H y),
  rw [← range_comp, ← (equiv.mul_right g).surjective.range_comp _] at this,
  simpa [(∘)] using this
end

/-- Consider two actions `f₁ f₂ : G → α → α` of a group on a complete lattice by order
isomorphisms. Then the map `x ↦ ⨆ g : G, (f₁ g)⁻¹ (f₂ g x)` semiconjugates each `f₁ g'` to `f₂ g'`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
cohomologie bornee][ghys87:groupes]. -/
lemma Sup_div_semiconj [complete_lattice α] [group G]
  (f₁ f₂ : G →* (α ≃o α)) (g : G) :
  function.semiconj (λ x, ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g) :=
semiconj_of_is_lub f₁ f₂ (λ x, is_lub_supr) _

/-- Consider two actions `f₁ f₂ : G → α → α` of a group on a conditionally complete lattice by order
isomorphisms. Suppose that each set $s(x)=\{f_1(g)^{-1} (f_2(g)(x)) | g \in G\}$ is bounded above.
Then the map `x ↦ Sup s(x)` semiconjugates each `f₁ g'` to `f₂ g'`.

This is a version of Proposition 5.4 from [Étienne Ghys, Groupes d'homeomorphismes du cercle et
cohomologie bornee][ghys87:groupes]. -/
lemma cSup_div_semiconj [conditionally_complete_lattice α] [group G]
  (f₁ f₂ : G →* (α ≃o α))
  (hbdd : ∀ x, bdd_above (range $ λ g, (f₁ g)⁻¹ (f₂ g x))) (g : G) :
  function.semiconj (λ x, ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g) :=
semiconj_of_is_lub f₁ f₂ (λ x, is_lub_cSup (range_nonempty _) (hbdd x)) _

end function
