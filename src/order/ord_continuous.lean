/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Johannes Hölzl
-/
import order.conditionally_complete_lattice
import logic.function.iterate

/-!
# Order continuity

We say that a function is *left order continuous* if it sends all least upper bounds
to least upper bounds. The order dual notion is called *right order continuity*.

For monotone functions `ℝ → ℝ` these notions correspond to the usual left and right continuity.

We prove some basic lemmas (`map_sup`, `map_Sup` etc) and prove that an `rel_iso` is both left
and right order continuous.
-/

universes u v w x

variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

open set function

/-!
### Definitions
-/

/-- A function `f` between preorders is left order continuous if it preserves all suprema.  We
define it using `is_lub` instead of `Sup` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def left_ord_continuous [preorder α] [preorder β] (f : α → β) :=
∀ ⦃s : set α⦄ ⦃x⦄, is_lub s x → is_lub (f '' s) (f x)

/-- A function `f` between preorders is right order continuous if it preserves all infima.  We
define it using `is_glb` instead of `Inf` so that the proof works both for complete lattices and
conditionally complete lattices. -/
def right_ord_continuous [preorder α] [preorder β] (f : α → β) :=
∀ ⦃s : set α⦄ ⦃x⦄, is_glb s x → is_glb (f '' s) (f x)

namespace left_ord_continuous

section preorder

variables (α) [preorder α] [preorder β] [preorder γ] {g : β → γ} {f : α → β}

protected lemma id : left_ord_continuous (id : α → α) := λ s x h, by simpa only [image_id] using h

variable {α}

protected lemma order_dual (hf : left_ord_continuous f) :
  @right_ord_continuous (order_dual α) (order_dual β) _ _ f := hf

lemma map_is_greatest (hf : left_ord_continuous f) {s : set α} {x : α} (h : is_greatest s x):
  is_greatest (f '' s) (f x) :=
⟨mem_image_of_mem f h.1, (hf h.is_lub).1⟩

lemma mono (hf : left_ord_continuous f) : monotone f :=
λ a₁ a₂ h,
have is_greatest {a₁, a₂} a₂ := ⟨or.inr rfl, by simp [*]⟩,
(hf.map_is_greatest this).2 $ mem_image_of_mem _ (or.inl rfl)

lemma comp (hg : left_ord_continuous g) (hf : left_ord_continuous f) :
  left_ord_continuous (g ∘ f) :=
λ s x h, by simpa only [image_image] using hg (hf h)

protected lemma iterate {f : α → α} (hf : left_ord_continuous f) (n : ℕ) :
  left_ord_continuous (f^[n]) :=
nat.rec_on n (left_ord_continuous.id α) $ λ n ihn, ihn.comp hf

end preorder

section semilattice_sup

variables [semilattice_sup α] [semilattice_sup β] {f : α → β}

lemma map_sup (hf : left_ord_continuous f) (x y : α) :
  f (x ⊔ y) = f x ⊔ f y :=
(hf is_lub_pair).unique $ by simp only [image_pair, is_lub_pair]

lemma le_iff (hf : left_ord_continuous f) (h : injective f) {x y} :
  f x ≤ f y ↔ x ≤ y :=
by simp only [← sup_eq_right, ← hf.map_sup, h.eq_iff]

lemma lt_iff (hf : left_ord_continuous f) (h : injective f) {x y} :
  f x < f y ↔ x < y :=
by simp only [lt_iff_le_not_le, hf.le_iff h]

variable (f)

/-- Convert an injective left order continuous function to an order embedding. -/
def to_order_embedding (hf : left_ord_continuous f) (h : injective f) :
  α ↪o β :=
⟨⟨f, h⟩, λ x y, hf.le_iff h⟩

variable {f}

@[simp] lemma coe_to_order_embedding (hf : left_ord_continuous f) (h : injective f) :
  ⇑(hf.to_order_embedding f h) = f := rfl

end semilattice_sup

section complete_lattice

variables [complete_lattice α] [complete_lattice β] {f : α → β}

lemma map_Sup' (hf : left_ord_continuous f) (s : set α) :
  f (Sup s) = Sup (f '' s) :=
(hf $ is_lub_Sup s).Sup_eq.symm

lemma map_Sup (hf : left_ord_continuous f) (s : set α) :
  f (Sup s) = ⨆ x ∈ s, f x :=
by rw [hf.map_Sup', Sup_image]

lemma map_supr (hf : left_ord_continuous f) (g : ι → α) :
  f (⨆ i, g i) = ⨆ i, f (g i) :=
by simp only [supr, hf.map_Sup', ← range_comp]

end complete_lattice

section conditionally_complete_lattice

variables [conditionally_complete_lattice α] [conditionally_complete_lattice β] [nonempty ι]
  {f : α → β}

lemma map_cSup (hf : left_ord_continuous f) {s : set α} (sne : s.nonempty) (sbdd : bdd_above s) :
  f (Sup s) = Sup (f '' s) :=
((hf $ is_lub_cSup sne sbdd).cSup_eq $ sne.image f).symm

lemma map_csupr (hf : left_ord_continuous f) {g : ι → α} (hg : bdd_above (range g)) :
  f (⨆ i, g i) = ⨆ i, f (g i) :=
by simp only [supr, hf.map_cSup (range_nonempty _) hg, ← range_comp]

end conditionally_complete_lattice

end left_ord_continuous

namespace right_ord_continuous

section preorder

variables (α) [preorder α] [preorder β] [preorder γ] {g : β → γ} {f : α → β}

protected lemma id : right_ord_continuous (id : α → α) := λ s x h, by simpa only [image_id] using h

variable {α}

protected lemma order_dual (hf : right_ord_continuous f) :
  @left_ord_continuous (order_dual α) (order_dual β) _ _ f := hf

lemma map_is_least (hf : right_ord_continuous f) {s : set α} {x : α} (h : is_least s x):
  is_least (f '' s) (f x) :=
hf.order_dual.map_is_greatest h

lemma mono (hf : right_ord_continuous f) : monotone f :=
hf.order_dual.mono.order_dual

lemma comp (hg : right_ord_continuous g) (hf : right_ord_continuous f) :
  right_ord_continuous (g ∘ f) :=
hg.order_dual.comp hf.order_dual

protected lemma iterate {f : α → α} (hf : right_ord_continuous f) (n : ℕ) :
  right_ord_continuous (f^[n]) :=
hf.order_dual.iterate n

end preorder

section semilattice_inf

variables [semilattice_inf α] [semilattice_inf β] {f : α → β}

lemma map_inf (hf : right_ord_continuous f) (x y : α) :
  f (x ⊓ y) = f x ⊓ f y :=
hf.order_dual.map_sup x y

lemma le_iff (hf : right_ord_continuous f) (h : injective f) {x y} :
  f x ≤ f y ↔ x ≤ y :=
hf.order_dual.le_iff h

lemma lt_iff (hf : right_ord_continuous f) (h : injective f) {x y} :
  f x < f y ↔ x < y :=
hf.order_dual.lt_iff h

variable (f)

/-- Convert an injective left order continuous function to a `order_embedding`. -/
def to_order_embedding (hf : right_ord_continuous f) (h : injective f) : α ↪o β :=
⟨⟨f, h⟩, λ x y, hf.le_iff h⟩

variable {f}

@[simp] lemma coe_to_order_embedding (hf : right_ord_continuous f) (h : injective f) :
  ⇑(hf.to_order_embedding f h) = f := rfl

end semilattice_inf

section complete_lattice

variables [complete_lattice α] [complete_lattice β] {f : α → β}

lemma map_Inf' (hf : right_ord_continuous f) (s : set α) :
  f (Inf s) = Inf (f '' s) :=
hf.order_dual.map_Sup' s

lemma map_Inf (hf : right_ord_continuous f) (s : set α) :
  f (Inf s) = ⨅ x ∈ s, f x :=
hf.order_dual.map_Sup s

lemma map_infi (hf : right_ord_continuous f) (g : ι → α) :
  f (⨅ i, g i) = ⨅ i, f (g i) :=
hf.order_dual.map_supr g

end complete_lattice

section conditionally_complete_lattice

variables [conditionally_complete_lattice α] [conditionally_complete_lattice β] [nonempty ι]
  {f : α → β}

lemma map_cInf (hf : right_ord_continuous f) {s : set α} (sne : s.nonempty) (sbdd : bdd_below s) :
  f (Inf s) = Inf (f '' s) :=
hf.order_dual.map_cSup sne sbdd

lemma map_cinfi (hf : right_ord_continuous f) {g : ι → α} (hg : bdd_below (range g)) :
  f (⨅ i, g i) = ⨅ i, f (g i) :=
hf.order_dual.map_csupr hg

end conditionally_complete_lattice

end right_ord_continuous

namespace order_iso

section preorder

variables [preorder α] [preorder β] (e : α ≃o β)
  {s : set α} {x : α}

protected lemma left_ord_continuous : left_ord_continuous e :=
λ s x hx,
⟨monotone.mem_upper_bounds_image (λ x y, e.map_rel_iff.2) hx.1,
  λ y hy, e.rel_symm_apply.1 $ (is_lub_le_iff hx).2 $ λ x' hx', e.rel_symm_apply.2 $ hy $
    mem_image_of_mem _ hx'⟩

protected lemma right_ord_continuous : right_ord_continuous e := order_iso.left_ord_continuous e.dual

end preorder

end order_iso
