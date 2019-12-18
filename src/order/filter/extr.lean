/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import order.filter.basic logic.relator tactic.alias

/-! # Minimum and maximum w.r.t. a filter and on a set

This file defines six predicates of the form `is_A_B`, where `A` is `min`, `max`, or `extr`,
and `B` is `filter` or `on`.

* `is_min_filter f a l` means that `f a ≤ f x` in some `l`-neighborhood of `a`;
* `is_max_filter f a l` means that `f x ≤ f a` in some `l`-neighborhood of `a`;
* `is_extr_filter f a l` means `is_min_filter f a l` or `is_max_filter f a l`.

Similar predicates with `_on` suffix are particular cases for `l = principal s`.

We also define various operations on these statements.
-/

universes u v w x

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

open set lattice filter

section preorder

variables [preorder β] [preorder γ]

variables (f : α → β) (a : α) (s : set α) (l : filter α)

/-! ### Definitions -/

def is_min_filter (f : α → β) (a : α) (l : filter α) : Prop := {x | f a ≤ f x} ∈ l

def is_max_filter (f : α → β) (a : α) (l : filter α) : Prop := {x | f x ≤ f a} ∈ l

def is_extr_filter (f : α → β) (a : α) (l : filter α) : Prop :=
is_min_filter f a l ∨ is_max_filter f a l

def is_min_on := is_min_filter f a (principal s)

def is_max_on := is_max_filter f a (principal s)

def is_extr_on : Prop := is_extr_filter f a (principal s)

variables {f a s l} {t : set α} {l' : filter α}

lemma is_extr_on.elim {p : Prop} :
  is_extr_on f a s → (is_min_on f a s → p) → (is_max_on f a s → p) → p :=
or.elim

lemma is_min_on_iff : is_min_on f a s ↔ ∀ x ∈ s, f a ≤ f x := iff.rfl

lemma is_max_on_iff : is_max_on f a s ↔ ∀ x ∈ s, f x ≤ f a := iff.rfl

lemma is_min_on_univ_iff : is_min_on f a univ ↔ ∀ x, f a ≤ f x :=
univ_subset_iff.trans eq_univ_iff_forall

lemma is_max_on_univ_iff : is_max_on f a univ ↔ ∀ x, f x ≤ f a :=
univ_subset_iff.trans eq_univ_iff_forall

/-! ### Conversion to `is_extr_*` -/

lemma is_min_filter.is_extr : is_min_filter f a l → is_extr_filter f a l := or.inl

lemma is_max_filter.is_extr : is_max_filter f a l → is_extr_filter f a l := or.inr

lemma is_min_on.is_extr (h : is_min_on f a s) : is_extr_on f a s := h.is_extr

lemma is_max_on.is_extr (h : is_max_on f a s) : is_extr_on f a s := h.is_extr

/-! ### Constant function -/

lemma is_min_filter_const {b : β} : is_min_filter (λ _, b) a l :=
univ_mem_sets' $ λ _, le_refl _

lemma is_max_filter_const {b : β} : is_max_filter (λ _, b) a l :=
univ_mem_sets' $ λ _, le_refl _

lemma is_extr_filter_const {b : β} : is_extr_filter (λ _, b) a l := is_min_filter_const.is_extr

lemma is_min_on_const {b : β} : is_min_on (λ _, b) a s := is_min_filter_const

lemma is_max_on_const {b : β} : is_max_on (λ _, b) a s := is_max_filter_const

lemma is_extr_on_const {b : β} : is_extr_on (λ _, b) a s := is_extr_filter_const

/-! ### Order dual -/

lemma is_min_filter_dual_iff : @is_min_filter α (order_dual β) _ f a l ↔ is_max_filter f a l :=
iff.rfl

lemma is_max_filter_dual_iff : @is_max_filter α (order_dual β) _ f a l ↔ is_min_filter f a l :=
iff.rfl

lemma is_extr_filter_dual_iff : @is_extr_filter α (order_dual β) _ f a l ↔ is_extr_filter f a l :=
or_comm _ _

alias is_min_filter_dual_iff ↔ is_min_filter.undual is_max_filter.dual
alias is_max_filter_dual_iff ↔ is_max_filter.undual is_min_filter.dual
alias is_extr_filter_dual_iff ↔ is_extr_filter.undual is_extr_filter.dual

lemma is_min_on_dual_iff : @is_min_on α (order_dual β) _ f a s ↔ is_max_on f a s := iff.rfl
lemma is_max_on_dual_iff : @is_max_on α (order_dual β) _ f a s ↔ is_min_on f a s := iff.rfl
lemma is_extr_on_dual_iff : @is_extr_on α (order_dual β) _ f a s ↔ is_extr_on f a s := or_comm _ _

alias is_min_on_dual_iff ↔ is_min_on.undual is_max_on.dual
alias is_max_on_dual_iff ↔ is_max_on.undual is_min_on.dual
alias is_extr_on_dual_iff ↔ is_extr_on.undual is_extr_on.dual

/-! ### Operations on the filter/set -/

lemma is_min_filter.filter_mono (h : is_min_filter f a l) (hl : l' ≤ l) :
  is_min_filter f a l' := hl h

lemma is_max_filter.filter_mono (h : is_max_filter f a l) (hl : l' ≤ l) :
  is_max_filter f a l' := hl h

lemma is_extr_filter.filter_mono (h : is_extr_filter f a l) (hl : l' ≤ l) :
  is_extr_filter f a l' :=
h.elim (λ h, (h.filter_mono hl).is_extr) (λ h, (h.filter_mono hl).is_extr)

lemma is_min_filter.filter_inf (h : is_min_filter f a l) (l') : is_min_filter f a (l ⊓ l') :=
h.filter_mono inf_le_left

lemma is_max_filter.filter_inf (h : is_max_filter f a l) (l') : is_max_filter f a (l ⊓ l') :=
h.filter_mono inf_le_left

lemma is_extr_filter.filter_inf (h : is_extr_filter f a l) (l') : is_extr_filter f a (l ⊓ l') :=
h.filter_mono inf_le_left

lemma is_min_on.on_subset (hf : is_min_on f a t) (h : s ⊆ t) : is_min_on f a s :=
hf.filter_mono $ principal_mono.2 h

lemma is_max_on.on_subset (hf : is_max_on f a t) (h : s ⊆ t) : is_max_on f a s :=
hf.filter_mono $ principal_mono.2 h

lemma is_extr_on.on_subset (hf : is_extr_on f a t) (h : s ⊆ t) : is_extr_on f a s :=
hf.filter_mono $ principal_mono.2 h

lemma is_min_on.inter (hf : is_min_on f a s) (t) : is_min_on f a (s ∩ t) :=
hf.on_subset (inter_subset_left s t)

lemma is_max_on.inter (hf : is_max_on f a s) (t) : is_max_on f a (s ∩ t) :=
hf.on_subset (inter_subset_left s t)

lemma is_extr_on.inter (hf : is_extr_on f a s) (t) : is_extr_on f a (s ∩ t) :=
hf.on_subset (inter_subset_left s t)

/-! ### Composition with (anti)monotone functions -/

lemma is_min_filter.comp_mono (hf : is_min_filter f a l) {g : β → γ} (hg : monotone g) :
  is_min_filter (g ∘ f) a l :=
mem_sets_of_superset hf $ λ x hx, hg hx

lemma is_max_filter.comp_mono (hf : is_max_filter f a l) {g : β → γ} (hg : monotone g) :
  is_max_filter (g ∘ f) a l :=
mem_sets_of_superset hf $ λ x hx, hg hx

lemma is_extr_filter.comp_mono (hf : is_extr_filter f a l) {g : β → γ} (hg : monotone g) :
  is_extr_filter (g ∘ f) a l :=
hf.elim (λ hf, (hf.comp_mono hg).is_extr)  (λ hf, (hf.comp_mono hg).is_extr)

lemma is_min_filter.comp_antimono (hf : is_min_filter f a l) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_max_filter (g ∘ f) a l :=
hf.dual.comp_mono (λ x y h, hg h)

lemma is_max_filter.comp_antimono (hf : is_max_filter f a l) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_min_filter (g ∘ f) a l :=
hf.dual.comp_mono (λ x y h, hg h)

lemma is_extr_filter.comp_antimono (hf : is_extr_filter f a l) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_extr_filter (g ∘ f) a l :=
hf.dual.comp_mono (λ x y h, hg h)

lemma is_min_on.comp_mono (hf : is_min_on f a s) {g : β → γ} (hg : monotone g) :
  is_min_on (g ∘ f) a s :=
hf.comp_mono hg

lemma is_max_on.comp_mono (hf : is_max_on f a s) {g : β → γ} (hg : monotone g) :
  is_max_on (g ∘ f) a s :=
hf.comp_mono hg

lemma is_extr_on.comp_mono (hf : is_extr_on f a s) {g : β → γ} (hg : monotone g) :
  is_extr_on (g ∘ f) a s :=
hf.comp_mono hg

lemma is_min_on.comp_antimono (hf : is_min_on f a s) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_max_on (g ∘ f) a s :=
hf.comp_antimono hg

lemma is_max_on.comp_antimono (hf : is_max_on f a s) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_min_on (g ∘ f) a s :=
hf.comp_antimono hg

lemma is_extr_on.comp_antimono (hf : is_extr_on f a s) {g : β → γ}
  (hg : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x) :
  is_extr_on (g ∘ f) a s :=
hf.comp_antimono hg

lemma is_min_filter.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_min_filter f a l) {g : α → γ} (hg : is_min_filter g a l) :
  is_min_filter (λ x, op (f x) (g x)) a l :=
mem_sets_of_superset (inter_mem_sets hf hg) $ λ x ⟨hfx, hgx⟩, hop hfx hgx

lemma is_max_filter.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_max_filter f a l) {g : α → γ} (hg : is_max_filter g a l) :
  is_max_filter (λ x, op (f x) (g x)) a l :=
mem_sets_of_superset (inter_mem_sets hf hg) $ λ x ⟨hfx, hgx⟩, hop hfx hgx

-- No `extr` version because we need `hf` and `hg` to be of the same kind

lemma is_min_on.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_min_on f a s) {g : α → γ} (hg : is_min_on g a s) :
  is_min_on (λ x, op (f x) (g x)) a s :=
hf.bicomp_mono hop hg

lemma is_max_on.bicomp_mono [preorder δ] {op : β → γ → δ} (hop : ((≤) ⇒ (≤) ⇒ (≤)) op op)
  (hf : is_max_on f a s) {g : α → γ} (hg : is_max_on g a s) :
  is_max_on (λ x, op (f x) (g x)) a s :=
hf.bicomp_mono hop hg

/-! ### Composition with `tendsto` -/

lemma is_min_filter.comp_tendsto {g : δ → α} {l' : filter δ} {b : δ} (hf : is_min_filter f (g b) l)
  (hg : tendsto g l' l) :
  is_min_filter (f ∘ g) b l' :=
hg hf

lemma is_max_filter.comp_tendsto {g : δ → α} {l' : filter δ} {b : δ} (hf : is_max_filter f (g b) l)
  (hg : tendsto g l' l) :
  is_max_filter (f ∘ g) b l' :=
hg hf

lemma is_extr_filter.comp_tendsto {g : δ → α} {l' : filter δ} {b : δ} (hf : is_extr_filter f (g b) l)
  (hg : tendsto g l' l) :
  is_extr_filter (f ∘ g) b l' :=
hf.elim (λ hf, (hf.comp_tendsto hg).is_extr) (λ hf, (hf.comp_tendsto hg).is_extr)

lemma is_min_on.on_preimage (g : δ → α) {b : δ} (hf : is_min_on f (g b) s) :
  is_min_on (f ∘ g) b (g ⁻¹' s) :=
hf.comp_tendsto (tendsto_principal_principal.mpr $ subset.refl _)

lemma is_max_on.on_preimage (g : δ → α) {b : δ} (hf : is_max_on f (g b) s) :
  is_max_on (f ∘ g) b (g ⁻¹' s) :=
hf.comp_tendsto (tendsto_principal_principal.mpr $ subset.refl _)

lemma is_extr_on.on_preimage (g : δ → α) {b : δ} (hf : is_extr_on f (g b) s) :
  is_extr_on (f ∘ g) b (g ⁻¹' s) :=
hf.elim (λ hf, (hf.on_preimage g).is_extr) (λ hf, (hf.on_preimage g).is_extr)

end preorder

/-! ### Pointwise addition -/
section ordered_comm_monoid

variables [ordered_comm_monoid β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.add (hf : is_min_filter f a l) (hg : is_min_filter g a l) :
  is_min_filter (λ x, f x + g x) a l :=
show is_min_filter (λ x, f x + g x) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, add_le_add' hx hy) hg

lemma is_max_filter.add (hf : is_max_filter f a l) (hg : is_max_filter g a l) :
  is_max_filter (λ x, f x + g x) a l :=
show is_max_filter (λ x, f x + g x) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, add_le_add' hx hy) hg

lemma is_min_on.add (hf : is_min_on f a s) (hg : is_min_on g a s) :
  is_min_on (λ x, f x + g x) a s :=
hf.add hg

lemma is_max_on.add (hf : is_max_on f a s) (hg : is_max_on g a s) :
  is_max_on (λ x, f x + g x) a s :=
hf.add hg

end ordered_comm_monoid

/-! ### Pointwise negation and subtraction -/

section ordered_comm_group

variables [ordered_comm_group β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.neg (hf : is_min_filter f a l) : is_max_filter (λ x, -f x) a l :=
hf.comp_antimono (λ x y hx, neg_le_neg hx)

lemma is_max_filter.neg (hf : is_max_filter f a l) : is_min_filter (λ x, -f x) a l :=
hf.comp_antimono (λ x y hx, neg_le_neg hx)

lemma is_extr_filter.neg (hf : is_extr_filter f a l) : is_extr_filter (λ x, -f x) a l :=
hf.elim (λ hf, hf.neg.is_extr) (λ hf, hf.neg.is_extr)

lemma is_min_on.neg (hf : is_min_on f a s) : is_max_on (λ x, -f x) a s :=
hf.comp_antimono (λ x y hx, neg_le_neg hx)

lemma is_max_on.neg (hf : is_max_on f a s) : is_min_on (λ x, -f x) a s :=
hf.comp_antimono (λ x y hx, neg_le_neg hx)

lemma is_extr_on.neg (hf : is_extr_on f a s) : is_extr_on (λ x, -f x) a s :=
hf.elim (λ hf, hf.neg.is_extr) (λ hf, hf.neg.is_extr)

lemma is_min_filter.sub (hf : is_min_filter f a l) (hg : is_max_filter g a l) :
  is_min_filter (λ x, f x - g x) a l :=
hf.add hg.neg

lemma is_max_filter.sub (hf : is_max_filter f a l) (hg : is_min_filter g a l) :
  is_max_filter (λ x, f x - g x) a l :=
hf.add hg.neg

lemma is_min_on.sub (hf : is_min_on f a s) (hg : is_max_on g a s) :
  is_min_on (λ x, f x - g x) a s :=
hf.add hg.neg

lemma is_max_on.sub (hf : is_max_on f a s) (hg : is_min_on g a s) :
  is_max_on (λ x, f x - g x) a s :=
hf.add hg.neg

end ordered_comm_group

/-! ### Pointwise `sup`/`inf` -/

section semilattice_sup

variables [semilattice_sup β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.sup (hf : is_min_filter f a l) (hg : is_min_filter g a l) :
  is_min_filter (λ x, f x ⊔ g x) a l :=
show is_min_filter (λ x, f x ⊔ g x) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, sup_le_sup hx hy) hg

lemma is_max_filter.sup (hf : is_max_filter f a l) (hg : is_max_filter g a l) :
  is_max_filter (λ x, f x ⊔ g x) a l :=
show is_max_filter (λ x, f x ⊔ g x) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, sup_le_sup hx hy) hg

lemma is_min_on.sup (hf : is_min_on f a s) (hg : is_min_on g a s) :
  is_min_on (λ x, f x ⊔ g x) a s :=
hf.sup hg

lemma is_max_on.sup (hf : is_max_on f a s) (hg : is_max_on g a s) :
  is_max_on (λ x, f x ⊔ g x) a s :=
hf.sup hg

end semilattice_sup

section semilattice_inf

variables [semilattice_inf β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.inf (hf : is_min_filter f a l) (hg : is_min_filter g a l) :
  is_min_filter (λ x, f x ⊓ g x) a l :=
show is_min_filter (λ x, f x ⊓ g x) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, inf_le_inf hx hy) hg

lemma is_max_filter.inf (hf : is_max_filter f a l) (hg : is_max_filter g a l) :
  is_max_filter (λ x, f x ⊓ g x) a l :=
show is_max_filter (λ x, f x ⊓ g x) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, inf_le_inf hx hy) hg

lemma is_min_on.inf (hf : is_min_on f a s) (hg : is_min_on g a s) :
  is_min_on (λ x, f x ⊓ g x) a s :=
hf.inf hg

lemma is_max_on.inf (hf : is_max_on f a s) (hg : is_max_on g a s) :
  is_max_on (λ x, f x ⊓ g x) a s :=
hf.inf hg

end semilattice_inf

/-! ### Pointwise `min`/`max` -/

section decidable_linear_order

variables [decidable_linear_order β] {f g : α → β} {a : α} {s : set α} {l : filter α}

lemma is_min_filter.min (hf : is_min_filter f a l) (hg : is_min_filter g a l) :
  is_min_filter (λ x, min (f x) (g x)) a l :=
show is_min_filter (λ x, min (f x) (g x)) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, min_le_min hx hy) hg

lemma is_max_filter.min (hf : is_max_filter f a l) (hg : is_max_filter g a l) :
  is_max_filter (λ x, min (f x) (g x)) a l :=
show is_max_filter (λ x, min (f x) (g x)) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, min_le_min hx hy) hg

lemma is_min_on.min (hf : is_min_on f a s) (hg : is_min_on g a s) :
  is_min_on (λ x, min (f x) (g x)) a s :=
hf.min hg

lemma is_max_on.min (hf : is_max_on f a s) (hg : is_max_on g a s) :
  is_max_on (λ x, min (f x) (g x)) a s :=
hf.min hg

lemma is_min_filter.max (hf : is_min_filter f a l) (hg : is_min_filter g a l) :
  is_min_filter (λ x, max (f x) (g x)) a l :=
show is_min_filter (λ x, max (f x) (g x)) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, max_le_max hx hy) hg

lemma is_max_filter.max (hf : is_max_filter f a l) (hg : is_max_filter g a l) :
  is_max_filter (λ x, max (f x) (g x)) a l :=
show is_max_filter (λ x, max (f x) (g x)) a l,
from hf.bicomp_mono (λ x x' hx y y' hy, max_le_max hx hy) hg

lemma is_min_on.max (hf : is_min_on f a s) (hg : is_min_on g a s) :
  is_min_on (λ x, max (f x) (g x)) a s :=
hf.max hg

lemma is_max_on.max (hf : is_max_on f a s) (hg : is_max_on g a s) :
  is_max_on (λ x, max (f x) (g x)) a s :=
hf.max hg

end decidable_linear_order
