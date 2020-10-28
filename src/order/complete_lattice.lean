/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.bounds

/-!
# Theory of complete lattices

## Main definitions

* `Sup` and `Inf` are the supremum and the infimum of a set;
* `supr (f : ι → α)` and `infi (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `Sup` and `Inf` of the range of this function;
* `class complete_lattice`: a bounded lattice such that `Sup s` is always the least upper boundary
  of `s` and `Inf s` is always the greatest lower boundary of `s`;
* `class complete_linear_order`: a linear ordered complete lattice.

## Naming conventions

We use `Sup`/`Inf`/`supr`/`infi` for the corresponding functions in the statement. Sometimes we
also use `bsupr`/`binfi` for "bounded` supremum or infimum, i.e. one of `⨆ i ∈ s, f i`,
`⨆ i (hi : p i), f i`, or more generally `⨆ i (hi : p i), f i hi`.

## Notation

* `⨆ i, f i` : `supr f`, the supremum of the range of `f`;
* `⨅ i, f i` : `infi f`, the infimum of the range of `f`.
-/

set_option old_structure_cmd true
open set

variables {α β β₂ : Type*} {ι ι₂ : Sort*}

/-- class for the `Sup` operator -/
class has_Sup (α : Type*) := (Sup : set α → α)
/-- class for the `Inf` operator -/
class has_Inf (α : Type*) := (Inf : set α → α)

export has_Sup (Sup) has_Inf (Inf)

/-- Supremum of a set -/
add_decl_doc has_Sup.Sup
/-- Infimum of a set -/
add_decl_doc has_Inf.Inf

/-- Indexed supremum -/
def supr [has_Sup α] {ι} (s : ι → α) : α := Sup (range s)
/-- Indexed infimum -/
def infi [has_Inf α] {ι} (s : ι → α) : α := Inf (range s)

@[priority 50] instance has_Inf_to_nonempty (α) [has_Inf α] : nonempty α := ⟨Inf ∅⟩
@[priority 50] instance has_Sup_to_nonempty (α) [has_Sup α] : nonempty α := ⟨Sup ∅⟩

notation `⨆` binders `, ` r:(scoped f, supr f) := r
notation `⨅` binders `, ` r:(scoped f, infi f) := r

instance (α) [has_Inf α] : has_Sup (order_dual α) := ⟨(Inf : set α → α)⟩
instance (α) [has_Sup α] : has_Inf (order_dual α) := ⟨(Sup : set α → α)⟩

/-- A complete lattice is a bounded lattice which
  has suprema and infima for every subset. -/
class complete_lattice (α : Type*) extends bounded_lattice α, has_Sup α, has_Inf α :=
(le_Sup : ∀s, ∀a∈s, a ≤ Sup s)
(Sup_le : ∀s a, (∀b∈s, b ≤ a) → Sup s ≤ a)
(Inf_le : ∀s, ∀a∈s, Inf s ≤ a)
(le_Inf : ∀s a, (∀b∈s, a ≤ b) → a ≤ Inf s)

/-- Create a `complete_lattice` from a `partial_order` and `Inf` function
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities, so it should be used with
`.. complete_lattice_of_Inf α _`. -/
def complete_lattice_of_Inf (α : Type*) [H1 : partial_order α]
  [H2 : has_Inf α] (is_glb_Inf : ∀ s : set α, is_glb s (Inf s)) :
  complete_lattice α :=
{ bot := Inf univ,
  bot_le := λ x, (is_glb_Inf univ).1 trivial,
  top := Inf ∅,
  le_top := λ a, (is_glb_Inf ∅).2 $ by simp,
  sup := λ a b, Inf {x | a ≤ x ∧ b ≤ x},
  inf := λ a b, Inf {a, b},
  le_inf := λ a b c hab hac, by { apply (is_glb_Inf _).2, simp [*] },
  inf_le_right := λ a b, (is_glb_Inf _).1 $ mem_insert_of_mem _ $ mem_singleton _,
  inf_le_left := λ a b, (is_glb_Inf _).1 $ mem_insert _ _,
  sup_le := λ a b c hac hbc, (is_glb_Inf _).1 $ by simp [*],
  le_sup_left := λ a b, (is_glb_Inf _).2 $ λ x, and.left,
  le_sup_right := λ a b, (is_glb_Inf _).2 $ λ x, and.right,
  le_Inf := λ s a ha, (is_glb_Inf s).2 ha,
  Inf_le := λ s a ha, (is_glb_Inf s).1 ha,
  Sup := λ s, Inf (upper_bounds s),
  le_Sup := λ s a ha, (is_glb_Inf (upper_bounds s)).2 $ λ b hb, hb ha,
  Sup_le := λ s a ha, (is_glb_Inf (upper_bounds s)).1 ha,
  .. H1, .. H2 }

/-- Create a `complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities, so it should be used with
`.. complete_lattice_of_Sup α _`. -/
def complete_lattice_of_Sup (α : Type*) [H1 : partial_order α]
  [H2 : has_Sup α] (is_lub_Sup : ∀ s : set α, is_lub s (Sup s)) :
  complete_lattice α :=
{ top := Sup univ,
  le_top := λ x, (is_lub_Sup univ).1 trivial,
  bot := Sup ∅,
  bot_le := λ x, (is_lub_Sup ∅).2 $ by simp,
  sup := λ a b, Sup {a, b},
  sup_le := λ a b c hac hbc, (is_lub_Sup _).2 (by simp [*]),
  le_sup_left := λ a b, (is_lub_Sup _).1 $ mem_insert _ _,
  le_sup_right := λ a b, (is_lub_Sup _).1 $ mem_insert_of_mem _ $ mem_singleton _,
  inf := λ a b, Sup {x | x ≤ a ∧ x ≤ b},
  le_inf := λ a b c hab hac, (is_lub_Sup _).1 $ by simp [*],
  inf_le_left := λ a b, (is_lub_Sup _).2 (λ x, and.left),
  inf_le_right := λ a b, (is_lub_Sup _).2 (λ x, and.right),
  Inf := λ s, Sup (lower_bounds s),
  Sup_le := λ s a ha, (is_lub_Sup s).2 ha,
  le_Sup := λ s a ha, (is_lub_Sup s).1 ha,
  Inf_le := λ s a ha, (is_lub_Sup (lower_bounds s)).2 (λ b hb, hb ha),
  le_Inf := λ s a ha, (is_lub_Sup (lower_bounds s)).1 ha,
  .. H1, .. H2 }

/-- A complete linear order is a linear order whose lattice structure is complete. -/
class complete_linear_order (α : Type*) extends complete_lattice α, linear_order α

namespace order_dual
variable (α)

instance [complete_lattice α] : complete_lattice (order_dual α) :=
{ le_Sup := @complete_lattice.Inf_le α _,
  Sup_le := @complete_lattice.le_Inf α _,
  Inf_le := @complete_lattice.le_Sup α _,
  le_Inf := @complete_lattice.Sup_le α _,
  .. order_dual.bounded_lattice α, ..order_dual.has_Sup α, ..order_dual.has_Inf α }

instance [complete_linear_order α] : complete_linear_order (order_dual α) :=
{ .. order_dual.complete_lattice α, .. order_dual.linear_order α }

end order_dual

section
variables [complete_lattice α] {s t : set α} {a b : α}

@[ematch] theorem le_Sup : a ∈ s → a ≤ Sup s := complete_lattice.le_Sup s a

theorem Sup_le : (∀b∈s, b ≤ a) → Sup s ≤ a := complete_lattice.Sup_le s a

@[ematch] theorem Inf_le : a ∈ s → Inf s ≤ a := complete_lattice.Inf_le s a

theorem le_Inf : (∀b∈s, a ≤ b) → a ≤ Inf s := complete_lattice.le_Inf s a

lemma is_lub_Sup (s : set α) : is_lub s (Sup s) := ⟨assume x, le_Sup, assume x, Sup_le⟩

lemma is_lub.Sup_eq (h : is_lub s a) : Sup s = a := (is_lub_Sup s).unique h

lemma is_glb_Inf (s : set α) : is_glb s (Inf s) := ⟨assume a, Inf_le, assume a, le_Inf⟩

lemma is_glb.Inf_eq (h : is_glb s a) : Inf s = a := (is_glb_Inf s).unique h

theorem le_Sup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ Sup s :=
le_trans h (le_Sup hb)

theorem Inf_le_of_le (hb : b ∈ s) (h : b ≤ a) : Inf s ≤ a :=
le_trans (Inf_le hb) h

theorem Sup_le_Sup (h : s ⊆ t) : Sup s ≤ Sup t :=
(is_lub_Sup s).mono (is_lub_Sup t) h

theorem Inf_le_Inf (h : s ⊆ t) : Inf t ≤ Inf s :=
(is_glb_Inf s).mono (is_glb_Inf t) h

@[simp] theorem Sup_le_iff : Sup s ≤ a ↔ (∀b ∈ s, b ≤ a) :=
is_lub_le_iff (is_lub_Sup s)

@[simp] theorem le_Inf_iff : a ≤ Inf s ↔ (∀b ∈ s, a ≤ b) :=
le_is_glb_iff (is_glb_Inf s)

theorem Sup_le_Sup_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : Sup s ≤ Sup t :=
le_of_forall_le' (by simp only [Sup_le_iff]; introv h₀ h₁; rcases h _ h₁ with ⟨y,hy,hy'⟩; solve_by_elim [le_trans hy'])

theorem Inf_le_Inf_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : Inf t ≤ Inf s :=
le_of_forall_le (by simp only [le_Inf_iff]; introv h₀ h₁; rcases h _ h₁ with ⟨y,hy,hy'⟩; solve_by_elim [le_trans _ hy'])

theorem Inf_le_Sup (hs : s.nonempty) : Inf s ≤ Sup s :=
is_glb_le_is_lub (is_glb_Inf s) (is_lub_Sup s) hs

-- TODO: it is weird that we have to add union_def
theorem Sup_union {s t : set α} : Sup (s ∪ t) = Sup s ⊔ Sup t :=
((is_lub_Sup s).union (is_lub_Sup t)).Sup_eq

theorem Sup_inter_le {s t : set α} : Sup (s ∩ t) ≤ Sup s ⊓ Sup t :=
by finish
/-
  Sup_le (assume a ⟨a_s, a_t⟩, le_inf (le_Sup a_s) (le_Sup a_t))
-/

theorem Inf_union {s t : set α} : Inf (s ∪ t) = Inf s ⊓ Inf t :=
((is_glb_Inf s).union (is_glb_Inf t)).Inf_eq

theorem le_Inf_inter {s t : set α} : Inf s ⊔ Inf t ≤ Inf (s ∩ t) :=
@Sup_inter_le (order_dual α) _ _ _

@[simp] theorem Sup_empty : Sup ∅ = (⊥ : α) :=
is_lub_empty.Sup_eq

@[simp] theorem Inf_empty : Inf ∅ = (⊤ : α) :=
(@is_glb_empty α _).Inf_eq

@[simp] theorem Sup_univ : Sup univ = (⊤ : α) :=
(@is_lub_univ α _).Sup_eq

@[simp] theorem Inf_univ : Inf univ = (⊥ : α) :=
is_glb_univ.Inf_eq

-- TODO(Jeremy): get this automatically
@[simp] theorem Sup_insert {a : α} {s : set α} : Sup (insert a s) = a ⊔ Sup s :=
((is_lub_Sup s).insert a).Sup_eq

@[simp] theorem Inf_insert {a : α} {s : set α} : Inf (insert a s) = a ⊓ Inf s :=
((is_glb_Inf s).insert a).Inf_eq

theorem Sup_le_Sup_of_subset_instert_bot (h : s ⊆ insert ⊥ t) : Sup s ≤ Sup t :=
le_trans (Sup_le_Sup h) (le_of_eq (trans Sup_insert bot_sup_eq))

theorem Inf_le_Inf_of_subset_insert_top (h : s ⊆ insert ⊤ t) : Inf t ≤ Inf s :=
le_trans (le_of_eq (trans top_inf_eq.symm Inf_insert.symm)) (Inf_le_Inf h)

-- We will generalize this to conditionally complete lattices in `cSup_singleton`.
theorem Sup_singleton {a : α} : Sup {a} = a :=
is_lub_singleton.Sup_eq

-- We will generalize this to conditionally complete lattices in `cInf_singleton`.
theorem Inf_singleton {a : α} : Inf {a} = a :=
is_glb_singleton.Inf_eq

theorem Sup_pair {a b : α} : Sup {a, b} = a ⊔ b :=
(@is_lub_pair α _ a b).Sup_eq

theorem Inf_pair {a b : α} : Inf {a, b} = a ⊓ b :=
(@is_glb_pair α _ a b).Inf_eq

@[simp] theorem Inf_eq_top : Inf s = ⊤ ↔ (∀a∈s, a = ⊤) :=
iff.intro
  (assume h a ha, top_unique $ h ▸ Inf_le ha)
  (assume h, top_unique $ le_Inf $ assume a ha, top_le_iff.2 $ h a ha)

@[simp] theorem Sup_eq_bot : Sup s = ⊥ ↔ (∀a∈s, a = ⊥) :=
@Inf_eq_top (order_dual α) _ _

end

section complete_linear_order
variables [complete_linear_order α] {s t : set α} {a b : α}

lemma Inf_lt_iff : Inf s < b ↔ (∃a∈s, a < b) :=
is_glb_lt_iff (is_glb_Inf s)

lemma lt_Sup_iff : b < Sup s ↔ (∃a∈s, b < a) :=
lt_is_lub_iff (is_lub_Sup s)

lemma Sup_eq_top : Sup s = ⊤ ↔ (∀b<⊤, ∃a∈s, b < a) :=
iff.intro
  (assume (h : Sup s = ⊤) b hb, by rwa [←h, lt_Sup_iff] at hb)
  (assume h, top_unique $ le_of_not_gt $ assume h',
    let ⟨a, ha, h⟩ := h _ h' in
    lt_irrefl a $ lt_of_le_of_lt (le_Sup ha) h)

lemma Inf_eq_bot : Inf s = ⊥ ↔ (∀b>⊥, ∃a∈s, a < b) :=
@Sup_eq_top (order_dual α) _ _

lemma lt_supr_iff {f : ι → α} : a < supr f ↔ (∃i, a < f i) :=
lt_Sup_iff.trans exists_range_iff

lemma infi_lt_iff {f : ι → α} : infi f < a ↔ (∃i, f i < a) :=
Inf_lt_iff.trans exists_range_iff

end complete_linear_order

/-
### supr & infi
-/

section
variables [complete_lattice α] {s t : ι → α} {a b : α}

-- TODO: this declaration gives error when starting smt state
--@[ematch]
theorem le_supr (s : ι → α) (i : ι) : s i ≤ supr s :=
le_Sup ⟨i, rfl⟩

@[ematch] theorem le_supr' (s : ι → α) (i : ι) : (: s i ≤ supr s :) :=
le_Sup ⟨i, rfl⟩

/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
@[ematch] theorem le_supr' (s : ι → α) (i : ι) : (: s i :) ≤ (: supr s :) :=
le_Sup ⟨i, rfl⟩
-/

lemma is_lub_supr : is_lub (range s) (⨆j, s j) := is_lub_Sup _

lemma is_lub.supr_eq (h : is_lub (range s) a) : (⨆j, s j) = a := h.Sup_eq

lemma is_glb_infi : is_glb (range s) (⨅j, s j) := is_glb_Inf _

lemma is_glb.infi_eq (h : is_glb (range s) a) : (⨅j, s j) = a := h.Inf_eq

theorem le_supr_of_le (i : ι) (h : a ≤ s i) : a ≤ supr s :=
le_trans h (le_supr _ i)

theorem le_bsupr {p : ι → Prop} {f : Π i (h : p i), α} (i : ι) (hi : p i) :
  f i hi ≤ ⨆ i hi, f i hi :=
le_supr_of_le i $ le_supr (f i) hi

theorem supr_le (h : ∀i, s i ≤ a) : supr s ≤ a :=
Sup_le $ assume b ⟨i, eq⟩, eq ▸ h i

theorem bsupr_le {p : ι → Prop} {f : Π i (h : p i), α} (h : ∀ i hi, f i hi ≤ a) :
  (⨆ i (hi : p i), f i hi) ≤ a :=
supr_le $ λ i, supr_le $ h i

theorem bsupr_le_supr (p : ι → Prop) (f : ι → α) : (⨆ i (H : p i), f i) ≤ ⨆ i, f i :=
bsupr_le (λ i hi, le_supr f i)

theorem supr_le_supr (h : ∀i, s i ≤ t i) : supr s ≤ supr t :=
supr_le $ assume i, le_supr_of_le i (h i)

theorem supr_le_supr2 {t : ι₂ → α} (h : ∀i, ∃j, s i ≤ t j) : supr s ≤ supr t :=
supr_le $ assume j, exists.elim (h j) le_supr_of_le

theorem bsupr_le_bsupr {p : ι → Prop} {f g : Π i (hi : p i), α} (h : ∀ i hi, f i hi ≤ g i hi) :
  (⨆ i hi, f i hi) ≤ ⨆ i hi, g i hi :=
bsupr_le $ λ i hi, le_trans (h i hi) (le_bsupr i hi)

theorem supr_le_supr_const (h : ι → ι₂) : (⨆ i:ι, a) ≤ (⨆ j:ι₂, a) :=
supr_le $ le_supr _ ∘ h

@[simp] theorem supr_le_iff : supr s ≤ a ↔ (∀i, s i ≤ a) :=
(is_lub_le_iff is_lub_supr).trans forall_range_iff

theorem Sup_eq_supr {s : set α} : Sup s = (⨆a ∈ s, a) :=
le_antisymm
  (Sup_le $ assume b h, le_supr_of_le b $ le_supr _ h)
  (supr_le $ assume b, supr_le $ assume h, le_Sup h)

lemma le_supr_iff : (a ≤ supr s) ↔ (∀ b, (∀ i, s i ≤ b) → a ≤ b) :=
⟨λ h b hb, le_trans h (supr_le hb), λ h, h _ $ λ i, le_supr s i⟩

lemma monotone.le_map_supr [complete_lattice β] {f : α → β} (hf : monotone f) :
  (⨆ i, f (s i)) ≤ f (supr s) :=
supr_le $ λ i, hf $ le_supr _ _

lemma monotone.le_map_supr2 [complete_lattice β] {f : α → β} (hf : monotone f)
  {ι' : ι → Sort*} (s : Π i, ι' i → α) :
  (⨆ i (h : ι' i), f (s i h)) ≤ f (⨆ i (h : ι' i), s i h) :=
calc (⨆ i h, f (s i h)) ≤ (⨆ i, f (⨆ h, s i h)) :
  supr_le_supr $ λ i, hf.le_map_supr
... ≤ f (⨆ i (h : ι' i), s i h) : hf.le_map_supr

lemma monotone.le_map_Sup [complete_lattice β] {s : set α} {f : α → β} (hf : monotone f) :
  (⨆a∈s, f a) ≤ f (Sup s) :=
by rw [Sup_eq_supr]; exact hf.le_map_supr2 _

lemma supr_comp_le {ι' : Sort*} (f : ι' → α) (g : ι → ι') :
  (⨆ x, f (g x)) ≤ ⨆ y, f y :=
supr_le_supr2 $ λ x, ⟨_, le_refl _⟩

lemma monotone.supr_comp_eq [preorder β] {f : β → α} (hf : monotone f)
  {s : ι → β} (hs : ∀ x, ∃ i, x ≤ s i) :
  (⨆ x, f (s x)) = ⨆ y, f y :=
le_antisymm (supr_comp_le _ _) (supr_le_supr2 $ λ x, (hs x).imp $ λ i hi, hf hi)

lemma function.surjective.supr_comp {α : Type*} [has_Sup α] {f : ι → ι₂}
  (hf : function.surjective f) (g : ι₂ → α) :
  (⨆ x, g (f x)) = ⨆ y, g y :=
by simp only [supr, hf.range_comp]

lemma supr_congr {α : Type*} [has_Sup α] {f : ι → α} {g : ι₂ → α} (h : ι → ι₂)
  (h1 : function.surjective h) (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y :=
by { convert h1.supr_comp g, exact (funext h2).symm }

-- TODO: finish doesn't do well here.
@[congr] theorem supr_congr_Prop {α : Type*} [has_Sup α] {p q : Prop} {f₁ : p → α} {f₂ : q → α}
  (pq : p ↔ q) (f : ∀x, f₁ (pq.mpr x) = f₂ x) : supr f₁ = supr f₂ :=
begin
  have : f₁ ∘ pq.mpr = f₂ := funext f,
  rw [← this],
  refine (function.surjective.supr_comp (λ h, ⟨pq.1 h, _⟩) f₁).symm,
  refl
end

theorem infi_le (s : ι → α) (i : ι) : infi s ≤ s i :=
Inf_le ⟨i, rfl⟩

@[ematch] theorem infi_le' (s : ι → α) (i : ι) : (: infi s ≤ s i :) :=
Inf_le ⟨i, rfl⟩

theorem infi_le_of_le (i : ι) (h : s i ≤ a) : infi s ≤ a :=
le_trans (infi_le _ i) h

theorem binfi_le {p : ι → Prop} {f : Π i (hi : p i), α} (i : ι) (hi : p i) :
  (⨅ i hi, f i hi) ≤ f i hi :=
infi_le_of_le i $ infi_le (f i) hi

theorem le_infi (h : ∀i, a ≤ s i) : a ≤ infi s :=
le_Inf $ assume b ⟨i, eq⟩, eq ▸ h i

theorem le_binfi {p : ι → Prop} {f : Π i (h : p i), α} (h : ∀ i hi, a ≤ f i hi) :
  a ≤ ⨅ i hi, f i hi :=
le_infi $ λ i, le_infi $ h i

theorem infi_le_binfi (p : ι → Prop) (f : ι → α) : (⨅ i, f i) ≤ ⨅ i (H : p i), f i :=
le_binfi (λ i hi, infi_le f i)

theorem infi_le_infi (h : ∀i, s i ≤ t i) : infi s ≤ infi t :=
le_infi $ assume i, infi_le_of_le i (h i)

theorem infi_le_infi2 {t : ι₂ → α} (h : ∀j, ∃i, s i ≤ t j) : infi s ≤ infi t :=
le_infi $ assume j, exists.elim (h j) infi_le_of_le

theorem binfi_le_binfi {p : ι → Prop} {f g : Π i (h : p i), α} (h : ∀ i hi, f i hi ≤ g i hi) :
  (⨅ i hi, f i hi) ≤ ⨅ i hi, g i hi :=
le_binfi $ λ i hi, le_trans (binfi_le i hi) (h i hi)

theorem infi_le_infi_const (h : ι₂ → ι) : (⨅ i:ι, a) ≤ (⨅ j:ι₂, a) :=
le_infi $ infi_le _ ∘ h

@[simp] theorem le_infi_iff : a ≤ infi s ↔ (∀i, a ≤ s i) :=
⟨assume : a ≤ infi s, assume i, le_trans this (infi_le _ _), le_infi⟩

theorem Inf_eq_infi {s : set α} : Inf s = (⨅a ∈ s, a) :=
@Sup_eq_supr (order_dual α) _ _

lemma monotone.map_infi_le [complete_lattice β] {f : α → β} (hf : monotone f) :
  f (infi s) ≤ (⨅ i, f (s i)) :=
le_infi $ λ i, hf $ infi_le _ _

lemma monotone.map_infi2_le [complete_lattice β] {f : α → β} (hf : monotone f)
  {ι' : ι → Sort*} (s : Π i, ι' i → α) :
  f (⨅ i (h : ι' i), s i h) ≤ (⨅ i (h : ι' i), f (s i h)) :=
@monotone.le_map_supr2 (order_dual α) (order_dual β) _ _ _ f hf.order_dual _ _

lemma monotone.map_Inf_le [complete_lattice β] {s : set α} {f : α → β} (hf : monotone f) :
  f (Inf s) ≤ ⨅ a∈s, f a :=
by rw [Inf_eq_infi]; exact hf.map_infi2_le _

lemma le_infi_comp {ι' : Sort*} (f : ι' → α) (g : ι → ι') :
  (⨅ y, f y) ≤ ⨅ x, f (g x) :=
infi_le_infi2 $ λ x, ⟨_, le_refl _⟩

lemma monotone.infi_comp_eq [preorder β] {f : β → α} (hf : monotone f)
  {s : ι → β} (hs : ∀ x, ∃ i, s i ≤ x) :
  (⨅ x, f (s x)) = ⨅ y, f y :=
le_antisymm (infi_le_infi2 $ λ x, (hs x).imp $ λ i hi, hf hi) (le_infi_comp _ _)

lemma function.surjective.infi_comp {α : Type*} [has_Inf α] {f : ι → ι₂}
  (hf : function.surjective f) (g : ι₂ → α) :
  (⨅ x, g (f x)) = ⨅ y, g y :=
@function.surjective.supr_comp _ _ (order_dual α) _ f hf g

lemma infi_congr {α : Type*} [has_Inf α] {f : ι → α} {g : ι₂ → α} (h : ι → ι₂)
  (h1 : function.surjective h) (h2 : ∀ x, g (h x) = f x) : (⨅ x, f x) = ⨅ y, g y :=
@supr_congr _ _ (order_dual α) _ _ _ h h1 h2

@[congr] theorem infi_congr_Prop {α : Type*} [has_Inf α] {p q : Prop} {f₁ : p → α} {f₂ : q → α}
  (pq : p ↔ q) (f : ∀x, f₁ (pq.mpr x) = f₂ x) : infi f₁ = infi f₂ :=
@supr_congr_Prop (order_dual α) _ p q f₁ f₂ pq f

-- We will generalize this to conditionally complete lattices in `cinfi_const`.
theorem infi_const [nonempty ι] {a : α} : (⨅ b:ι, a) = a :=
by rw [infi, range_const, Inf_singleton]

-- We will generalize this to conditionally complete lattices in `csupr_const`.
theorem supr_const [nonempty ι] {a : α} : (⨆ b:ι, a) = a :=
@infi_const (order_dual α) _ _ _ _

@[simp] lemma infi_top : (⨅i:ι, ⊤ : α) = ⊤ :=
top_unique $ le_infi $ assume i, le_refl _

@[simp] lemma supr_bot : (⨆i:ι, ⊥ : α) = ⊥ :=
@infi_top (order_dual α) _ _

@[simp] lemma infi_eq_top : infi s = ⊤ ↔ (∀i, s i = ⊤) :=
Inf_eq_top.trans forall_range_iff

@[simp] lemma supr_eq_bot : supr s = ⊥ ↔ (∀i, s i = ⊥) :=
Sup_eq_bot.trans forall_range_iff

@[simp] lemma infi_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
le_antisymm (infi_le _ _) (le_infi $ assume h, le_refl _)

@[simp] lemma infi_neg {p : Prop} {f : p → α} (hp : ¬ p) : (⨅ h : p, f h) = ⊤ :=
le_antisymm le_top $ le_infi $ assume h, (hp h).elim

@[simp] lemma supr_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
le_antisymm (supr_le $ assume h, le_refl _) (le_supr _ _)

@[simp] lemma supr_neg {p : Prop} {f : p → α} (hp : ¬ p) : (⨆ h : p, f h) = ⊥ :=
le_antisymm (supr_le $ assume h, (hp h).elim) bot_le

lemma supr_eq_dif {p : Prop} [decidable p] (a : p → α) :
  (⨆h:p, a h) = (if h : p then a h else ⊥) :=
by by_cases p; simp [h]

lemma supr_eq_if {p : Prop} [decidable p] (a : α) :
  (⨆h:p, a) = (if p then a else ⊥) :=
supr_eq_dif (λ _, a)

lemma infi_eq_dif {p : Prop} [decidable p] (a : p → α) :
  (⨅h:p, a h) = (if h : p then a h else ⊤) :=
@supr_eq_dif (order_dual α) _ _ _ _

lemma infi_eq_if {p : Prop} [decidable p] (a : α) :
  (⨅h:p, a) = (if p then a else ⊤) :=
infi_eq_dif (λ _, a)

-- TODO: should this be @[simp]?
theorem infi_comm {f : ι → ι₂ → α} : (⨅i, ⨅j, f i j) = (⨅j, ⨅i, f i j) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume j, infi_le_of_le j $ infi_le _ i)
  (le_infi $ assume j, le_infi $ assume i, infi_le_of_le i $ infi_le _ j)

/- TODO: this is strange. In the proof below, we get exactly the desired
   among the equalities, but close does not get it.
begin
  apply @le_antisymm,
    simp, intros,
    begin [smt]
      ematch, ematch, ematch, trace_state, have := le_refl (f i_1 i),
      trace_state, close
    end
end
-/

-- TODO: should this be @[simp]?
theorem supr_comm {f : ι → ι₂ → α} : (⨆i, ⨆j, f i j) = (⨆j, ⨆i, f i j) :=
@infi_comm (order_dual α) _ _ _ _

@[simp] theorem infi_infi_eq_left {b : β} {f : Πx:β, x = b → α} :
  (⨅x, ⨅h:x = b, f x h) = f b rfl :=
le_antisymm
  (infi_le_of_le b $ infi_le _ rfl)
  (le_infi $ assume b', le_infi $ assume eq, match b', eq with ._, rfl := le_refl _ end)

@[simp] theorem infi_infi_eq_right {b : β} {f : Πx:β, b = x → α} :
  (⨅x, ⨅h:b = x, f x h) = f b rfl :=
le_antisymm
  (infi_le_of_le b $ infi_le _ rfl)
  (le_infi $ assume b', le_infi $ assume eq, match b', eq with ._, rfl := le_refl _ end)

@[simp] theorem supr_supr_eq_left {b : β} {f : Πx:β, x = b → α} :
  (⨆x, ⨆h : x = b, f x h) = f b rfl :=
@infi_infi_eq_left (order_dual α) _ _ _ _

@[simp] theorem supr_supr_eq_right {b : β} {f : Πx:β, b = x → α} :
  (⨆x, ⨆h : b = x, f x h) = f b rfl :=
@infi_infi_eq_right (order_dual α) _ _ _ _

attribute [ematch] le_refl

theorem infi_subtype {p : ι → Prop} {f : subtype p → α} : (⨅ x, f x) = (⨅ i (h:p i), f ⟨i, h⟩) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume : p i, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

lemma infi_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
  (⨅ i (h : p i), f i h) = (⨅ x : subtype p, f x x.property) :=
(@infi_subtype _ _ _ p (λ x, f x.val x.property)).symm

lemma infi_subtype'' {ι} (s : set ι) (f : ι → α) :
  (⨅ i : s, f i) = ⨅ (t : ι) (H : t ∈ s), f t :=
infi_subtype

theorem infi_inf_eq {f g : ι → α} : (⨅ x, f x ⊓ g x) = (⨅ x, f x) ⊓ (⨅ x, g x) :=
le_antisymm
  (le_inf
    (le_infi $ assume i, infi_le_of_le i inf_le_left)
    (le_infi $ assume i, infi_le_of_le i inf_le_right))
  (le_infi $ assume i, le_inf
    (inf_le_left_of_le $ infi_le _ _)
    (inf_le_right_of_le $ infi_le _ _))

/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/

lemma infi_inf [h : nonempty ι] {f : ι → α} {a : α} : (⨅x, f x) ⊓ a = (⨅ x, f x ⊓ a) :=
by rw [infi_inf_eq, infi_const]

lemma inf_infi [nonempty ι] {f : ι → α} {a : α} : a ⊓ (⨅x, f x) = (⨅ x, a ⊓ f x) :=
by rw [inf_comm, infi_inf]; simp [inf_comm]

lemma binfi_inf {p : ι → Prop} {f : Π i (hi : p i), α} {a : α} (h : ∃ i, p i) :
  (⨅i (h : p i), f i h) ⊓ a = (⨅ i (h : p i), f i h ⊓ a) :=
by haveI : nonempty {i // p i} := (let ⟨i, hi⟩ := h in ⟨⟨i, hi⟩⟩);
  rw [infi_subtype', infi_subtype', infi_inf]

theorem supr_sup_eq {f g : β → α} : (⨆ x, f x ⊔ g x) = (⨆ x, f x) ⊔ (⨆ x, g x) :=
@infi_inf_eq (order_dual α) β _ _ _

/- supr and infi under Prop -/

@[simp] theorem infi_false {s : false → α} : infi s = ⊤ :=
le_antisymm le_top (le_infi $ assume i, false.elim i)

@[simp] theorem supr_false {s : false → α} : supr s = ⊥ :=
le_antisymm (supr_le $ assume i, false.elim i) bot_le

@[simp] theorem infi_true {s : true → α} : infi s = s trivial :=
le_antisymm (infi_le _ _) (le_infi $ assume ⟨⟩, le_refl _)

@[simp] theorem supr_true {s : true → α} : supr s = s trivial :=
le_antisymm (supr_le $ assume ⟨⟩, le_refl _) (le_supr _ _)

@[simp] theorem infi_exists {p : ι → Prop} {f : Exists p → α} :
  (⨅ x, f x) = (⨅ i, ⨅ h:p i, f ⟨i, h⟩) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume : p i, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

@[simp] theorem supr_exists {p : ι → Prop} {f : Exists p → α} :
  (⨆ x, f x) = (⨆ i, ⨆ h:p i, f ⟨i, h⟩) :=
@infi_exists (order_dual α) _ _ _ _

theorem infi_and {p q : Prop} {s : p ∧ q → α} : infi s = (⨅ h₁ h₂, s ⟨h₁, h₂⟩) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume j, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

/-- The symmetric case of `infi_and`, useful for rewriting into a infimum over a conjunction -/
lemma infi_and' {p q : Prop} {s : p → q → α} :
  (⨅ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨅ (h : p ∧ q), s h.1 h.2 :=
by { symmetry, exact infi_and }

theorem supr_and {p q : Prop} {s : p ∧ q → α} : supr s = (⨆ h₁ h₂, s ⟨h₁, h₂⟩) :=
@infi_and (order_dual α) _ _ _ _

/-- The symmetric case of `supr_and`, useful for rewriting into a supremum over a conjunction -/
lemma supr_and' {p q : Prop} {s : p → q → α} :
  (⨆ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨆ (h : p ∧ q), s h.1 h.2 :=
by { symmetry, exact supr_and }

theorem infi_or {p q : Prop} {s : p ∨ q → α} :
  infi s = (⨅ h : p, s (or.inl h)) ⊓ (⨅ h : q, s (or.inr h)) :=
le_antisymm
  (le_inf
    (infi_le_infi2 $ assume j, ⟨_, le_refl _⟩)
    (infi_le_infi2 $ assume j, ⟨_, le_refl _⟩))
  (le_infi $ assume i, match i with
  | or.inl i := inf_le_left_of_le $ infi_le _ _
  | or.inr j := inf_le_right_of_le $ infi_le _ _
  end)

theorem supr_or {p q : Prop} {s : p ∨ q → α} :
  (⨆ x, s x) = (⨆ i, s (or.inl i)) ⊔ (⨆ j, s (or.inr j)) :=
@infi_or (order_dual α) _ _ _ _

lemma Sup_range {α : Type*} [has_Sup α] {f : ι → α} : Sup (range f) = supr f := rfl

lemma Inf_range {α : Type*} [has_Inf α] {f : ι → α} : Inf (range f) = infi f := rfl

lemma supr_range {g : β → α} {f : ι → β} : (⨆b∈range f, g b) = (⨆i, g (f i)) :=
le_antisymm
  (supr_le $ assume b, supr_le $ assume ⟨i, (h : f i = b)⟩, h ▸ le_supr _ i)
  (supr_le $ assume i, le_supr_of_le (f i) $ le_supr (λp, g (f i)) (mem_range_self _))

lemma infi_range {g : β → α} {f : ι → β} : (⨅b∈range f, g b) = (⨅i, g (f i)) :=
@supr_range (order_dual α) _ _ _ _ _

theorem Inf_image {s : set β} {f : β → α} : Inf (f '' s) = (⨅ a ∈ s, f a) :=
by rw [← infi_subtype'', infi, range_comp, subtype.range_coe]

theorem Sup_image {s : set β} {f : β → α} : Sup (f '' s) = (⨆ a ∈ s, f a) :=
@Inf_image (order_dual α) _ _ _ _

/-
### supr and infi under set constructions
-/

theorem infi_emptyset {f : β → α} : (⨅ x ∈ (∅ : set β), f x) = ⊤ :=
by simp

theorem supr_emptyset {f : β → α} : (⨆ x ∈ (∅ : set β), f x) = ⊥ :=
by simp

theorem infi_univ {f : β → α} : (⨅ x ∈ (univ : set β), f x) = (⨅ x, f x) :=
by simp

theorem supr_univ {f : β → α} : (⨆ x ∈ (univ : set β), f x) = (⨆ x, f x) :=
by simp

theorem infi_union {f : β → α} {s t : set β} : (⨅ x ∈ s ∪ t, f x) = (⨅x∈s, f x) ⊓ (⨅x∈t, f x) :=
by simp only [← infi_inf_eq, infi_or]

lemma infi_split (f : β → α) (p : β → Prop) :
  (⨅ i, f i) = (⨅ i (h : p i), f i) ⊓ (⨅ i (h : ¬ p i), f i) :=
by simpa [classical.em] using @infi_union _ _ _ f {i | p i} {i | ¬ p i}

lemma infi_split_single (f : β → α) (i₀ : β) :
  (⨅ i, f i) = f i₀ ⊓ (⨅ i (h : i ≠ i₀), f i) :=
by convert infi_split _ _; simp

theorem infi_le_infi_of_subset {f : β → α} {s t : set β} (h : s ⊆ t) :
  (⨅ x ∈ t, f x) ≤ (⨅ x ∈ s, f x) :=
by rw [(union_eq_self_of_subset_left h).symm, infi_union]; exact inf_le_left

theorem supr_union {f : β → α} {s t : set β} : (⨆ x ∈ s ∪ t, f x) = (⨆x∈s, f x) ⊔ (⨆x∈t, f x) :=
@infi_union (order_dual α) _ _ _ _ _

lemma supr_split (f : β → α) (p : β → Prop) :
  (⨆ i, f i) = (⨆ i (h : p i), f i) ⊔ (⨆ i (h : ¬ p i), f i) :=
@infi_split (order_dual α) _ _ _ _

lemma supr_split_single (f : β → α) (i₀ : β) :
  (⨆ i, f i) = f i₀ ⊔ (⨆ i (h : i ≠ i₀), f i) :=
@infi_split_single (order_dual α) _ _ _ _

theorem supr_le_supr_of_subset {f : β → α} {s t : set β} (h : s ⊆ t) :
  (⨆ x ∈ s, f x) ≤ (⨆ x ∈ t, f x) :=
@infi_le_infi_of_subset (order_dual α) _ _ _ _ _ h

theorem infi_insert {f : β → α} {s : set β} {b : β} :
  (⨅ x ∈ insert b s, f x) = f b ⊓ (⨅x∈s, f x) :=
eq.trans infi_union $ congr_arg (λx:α, x ⊓ (⨅x∈s, f x)) infi_infi_eq_left

theorem supr_insert {f : β → α} {s : set β} {b : β} :
  (⨆ x ∈ insert b s, f x) = f b ⊔ (⨆x∈s, f x) :=
eq.trans supr_union $ congr_arg (λx:α, x ⊔ (⨆x∈s, f x)) supr_supr_eq_left

theorem infi_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : set β), f x) = f b :=
by simp

theorem infi_pair {f : β → α} {a b : β} : (⨅ x ∈ ({a, b} : set β), f x) = f a ⊓ f b :=
by rw [infi_insert, infi_singleton]

theorem supr_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : set β), f x) = f b :=
@infi_singleton (order_dual α) _ _ _ _

theorem supr_pair {f : β → α} {a b : β} : (⨆ x ∈ ({a, b} : set β), f x) = f a ⊔ f b :=
by rw [supr_insert, supr_singleton]

lemma infi_image {γ} {f : β → γ} {g : γ → α} {t : set β} :
  (⨅ c ∈ f '' t, g c) = (⨅ b ∈ t, g (f b)) :=
by rw [← Inf_image, ← Inf_image, ← image_comp]

lemma supr_image {γ} {f : β → γ} {g : γ → α} {t : set β} :
  (⨆ c ∈ f '' t, g c) = (⨆ b ∈ t, g (f b)) :=
@infi_image (order_dual α) _ _ _ _ _ _

/-!
### `supr` and `infi` under `Type`
-/

theorem infi_of_empty' (h : ι → false) {s : ι → α} : infi s = ⊤ :=
top_unique (le_infi $ assume i, (h i).elim)

theorem supr_of_empty' (h : ι → false) {s : ι → α} : supr s = ⊥ :=
bot_unique (supr_le $ assume i, (h i).elim)

theorem infi_of_empty (h : ¬nonempty ι) {s : ι → α} : infi s = ⊤ :=
infi_of_empty' (λ i, h ⟨i⟩)

theorem supr_of_empty (h : ¬nonempty ι) {s : ι → α} : supr s = ⊥ :=
supr_of_empty' (λ i, h ⟨i⟩)

@[simp] theorem infi_empty {s : empty → α} : infi s = ⊤ :=
infi_of_empty nonempty_empty

@[simp] theorem supr_empty {s : empty → α} : supr s = ⊥ :=
supr_of_empty nonempty_empty

@[simp] theorem infi_unit {f : unit → α} : (⨅ x, f x) = f () :=
le_antisymm (infi_le _ _) (le_infi $ assume ⟨⟩, le_refl _)

@[simp] theorem supr_unit {f : unit → α} : (⨆ x, f x) = f () :=
le_antisymm (supr_le $ assume ⟨⟩, le_refl _) (le_supr _ _)

lemma supr_bool_eq {f : bool → α} : (⨆b:bool, f b) = f tt ⊔ f ff :=
le_antisymm
  (supr_le $ assume b, match b with tt := le_sup_left | ff := le_sup_right end)
  (sup_le (le_supr _ _) (le_supr _ _))

lemma infi_bool_eq {f : bool → α} : (⨅b:bool, f b) = f tt ⊓ f ff :=
@supr_bool_eq (order_dual α) _ _

lemma is_glb_binfi {s : set β} {f : β → α} : is_glb (f '' s) (⨅ x ∈ s, f x) :=
by simpa only [range_comp, subtype.range_coe, infi_subtype'] using @is_glb_infi α s _ (f ∘ coe)

theorem supr_subtype {p : ι → Prop} {f : subtype p → α} : (⨆ x, f x) = (⨆ i (h:p i), f ⟨i, h⟩) :=
@infi_subtype (order_dual α) _ _ _ _

lemma supr_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
  (⨆ i (h : p i), f i h) = (⨆ x : subtype p, f x x.property) :=
(@supr_subtype _ _ _ p (λ x, f x.val x.property)).symm

lemma Sup_eq_supr' {s : set α} : Sup s = ⨆ x : s, (x : α) :=
by rw [Sup_eq_supr, supr_subtype']; refl

lemma is_lub_bsupr {s : set β} {f : β → α} : is_lub (f '' s) (⨆ x ∈ s, f x) :=
by simpa only [range_comp, subtype.range_coe, supr_subtype'] using @is_lub_supr α s _ (f ∘ coe)

theorem infi_sigma {p : β → Type*} {f : sigma p → α} : (⨅ x, f x) = (⨅ i (h:p i), f ⟨i, h⟩) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume : p i, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

theorem supr_sigma {p : β → Type*} {f : sigma p → α} : (⨆ x, f x) = (⨆ i (h:p i), f ⟨i, h⟩) :=
@infi_sigma (order_dual α) _ _ _ _

theorem infi_prod {γ : Type*} {f : β × γ → α} : (⨅ x, f x) = (⨅ i j, f (i, j)) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume j, infi_le _ _)
  (le_infi $ assume ⟨i, h⟩, infi_le_of_le i $ infi_le _ _)

theorem supr_prod {γ : Type*} {f : β × γ → α} : (⨆ x, f x) = (⨆ i j, f (i, j)) :=
@infi_prod (order_dual α) _ _ _ _

theorem infi_sum {γ : Type*} {f : β ⊕ γ → α} :
  (⨅ x, f x) = (⨅ i, f (sum.inl i)) ⊓ (⨅ j, f (sum.inr j)) :=
le_antisymm
  (le_inf
    (infi_le_infi2 $ assume i, ⟨_, le_refl _⟩)
    (infi_le_infi2 $ assume j, ⟨_, le_refl _⟩))
  (le_infi $ assume s, match s with
  | sum.inl i := inf_le_left_of_le $ infi_le _ _
  | sum.inr j := inf_le_right_of_le $ infi_le _ _
  end)

theorem supr_sum {γ : Type*} {f : β ⊕ γ → α} :
  (⨆ x, f x) = (⨆ i, f (sum.inl i)) ⊔ (⨆ j, f (sum.inr j)) :=
@infi_sum (order_dual α) _ _ _ _

/-!
### `supr` and `infi` under `ℕ`
-/

lemma supr_ge_eq_supr_nat_add {u : ℕ → α} (n : ℕ) : (⨆ i ≥ n, u i) = ⨆ i, u (i + n) :=
begin
  apply le_antisymm;
  simp only [supr_le_iff],
  { exact λ i hi, le_Sup ⟨i - n, by { dsimp only, rw nat.sub_add_cancel hi }⟩ },
  { exact λ i, le_Sup ⟨i + n, supr_pos (nat.le_add_left _ _)⟩ }
end

lemma infi_ge_eq_infi_nat_add {u : ℕ → α} (n : ℕ) : (⨅ i ≥ n, u i) = ⨅ i, u (i + n) :=
@supr_ge_eq_supr_nat_add (order_dual α) _ _ _

end

section complete_linear_order
variables [complete_linear_order α]

lemma supr_eq_top (f : ι → α) : supr f = ⊤ ↔ (∀b<⊤, ∃i, b < f i) :=
by simp only [← Sup_range, Sup_eq_top, set.exists_range_iff]

lemma infi_eq_bot (f : ι → α) : infi f = ⊥ ↔ (∀b>⊥, ∃i, f i < b) :=
by simp only [← Inf_range, Inf_eq_bot, set.exists_range_iff]

end complete_linear_order

/-!
### Instances
-/

instance complete_lattice_Prop : complete_lattice Prop :=
{ Sup    := λs, ∃a∈s, a,
  le_Sup := assume s a h p, ⟨a, h, p⟩,
  Sup_le := assume s a h ⟨b, h', p⟩, h b h' p,
  Inf    := λs, ∀a:Prop, a∈s → a,
  Inf_le := assume s a h p, p a h,
  le_Inf := assume s a h p b hb, h b hb p,
  .. bounded_distrib_lattice_Prop }

lemma Inf_Prop_eq {s : set Prop} : Inf s = (∀p ∈ s, p) := rfl

lemma Sup_Prop_eq {s : set Prop} : Sup s = (∃p ∈ s, p) := rfl

lemma infi_Prop_eq {ι : Sort*} {p : ι → Prop} : (⨅i, p i) = (∀i, p i) :=
le_antisymm (assume h i, h _ ⟨i, rfl⟩ ) (assume h p ⟨i, eq⟩, eq ▸ h i)

lemma supr_Prop_eq {ι : Sort*} {p : ι → Prop} : (⨆i, p i) = (∃i, p i) :=
le_antisymm (λ ⟨q, ⟨i, (eq : p i = q)⟩, hq⟩, ⟨i, eq.symm ▸ hq⟩) (λ ⟨i, hi⟩, ⟨p i, ⟨i, rfl⟩, hi⟩)

instance pi.has_Sup {α : Type*} {β : α → Type*} [Π i, has_Sup (β i)] : has_Sup (Π i, β i) :=
⟨λ s i, ⨆ f : s, (f : Π i, β i) i⟩

instance pi.has_Inf {α : Type*} {β : α → Type*} [Π i, has_Inf (β i)] : has_Inf (Π i, β i) :=
⟨λ s i, ⨅ f : s, (f : Π i, β i) i⟩

instance pi.complete_lattice {α : Type*} {β : α → Type*} [∀ i, complete_lattice (β i)] :
  complete_lattice (Π i, β i) :=
{ Sup := Sup,
  Inf := Inf,
  le_Sup := λ s f hf i, le_supr (λ f : s, (f : Π i, β i) i) ⟨f, hf⟩,
  Inf_le := λ s f hf i, infi_le (λ f : s, (f : Π i, β i) i) ⟨f, hf⟩,
  Sup_le := λ s f hf i, supr_le $ λ g, hf g g.2 i,
  le_Inf := λ s f hf i, le_infi $ λ g, hf g g.2 i,
  .. pi.bounded_lattice }

lemma Inf_apply {α : Type*} {β : α → Type*} [Π i, has_Inf (β i)]
  {s : set (Πa, β a)} {a : α} :
  (Inf s) a = (⨅ f : s, (f : Πa, β a) a) :=
rfl

lemma infi_apply {α : Type*} {β : α → Type*} {ι : Sort*} [Π i, has_Inf (β i)]
  {f : ι → Πa, β a} {a : α} :
  (⨅i, f i) a = (⨅i, f i a) :=
by rw [infi, Inf_apply, infi, infi, ← image_eq_range (λ f : Π i, β i, f a) (range f), ← range_comp]

lemma Sup_apply {α : Type*} {β : α → Type*} [Π i, has_Sup (β i)] {s : set (Πa, β a)} {a : α} :
  (Sup s) a = (⨆f:s, (f : Πa, β a) a) :=
rfl

lemma supr_apply {α : Type*} {β : α → Type*} {ι : Sort*} [Π i, has_Sup (β i)] {f : ι → Πa, β a}
  {a : α} :
  (⨆i, f i) a = (⨆i, f i a) :=
@infi_apply α (λ i, order_dual (β i)) _ _ f a

section complete_lattice
variables [preorder α] [complete_lattice β]

theorem monotone_Sup_of_monotone {s : set (α → β)} (m_s : ∀f∈s, monotone f) : monotone (Sup s) :=
assume x y h, supr_le $ λ f, le_supr_of_le f $ m_s f f.2 h

theorem monotone_Inf_of_monotone {s : set (α → β)} (m_s : ∀f∈s, monotone f) : monotone (Inf s) :=
assume x y h, le_infi $ λ f, infi_le_of_le f $ m_s f f.2 h

end complete_lattice

namespace prod
variables (α β)

instance [has_Inf α] [has_Inf β] : has_Inf (α × β) :=
⟨λs, (Inf (prod.fst '' s), Inf (prod.snd '' s))⟩

instance [has_Sup α] [has_Sup β] : has_Sup (α × β) :=
⟨λs, (Sup (prod.fst '' s), Sup (prod.snd '' s))⟩

instance [complete_lattice α] [complete_lattice β] : complete_lattice (α × β) :=
{ le_Sup := assume s p hab, ⟨le_Sup $ mem_image_of_mem _ hab, le_Sup $ mem_image_of_mem _ hab⟩,
  Sup_le := assume s p h,
    ⟨ Sup_le $ ball_image_of_ball $ assume p hp, (h p hp).1,
      Sup_le $ ball_image_of_ball $ assume p hp, (h p hp).2⟩,
  Inf_le := assume s p hab, ⟨Inf_le $ mem_image_of_mem _ hab, Inf_le $ mem_image_of_mem _ hab⟩,
  le_Inf := assume s p h,
    ⟨ le_Inf $ ball_image_of_ball $ assume p hp, (h p hp).1,
      le_Inf $ ball_image_of_ball $ assume p hp, (h p hp).2⟩,
  .. prod.bounded_lattice α β,
  .. prod.has_Sup α β,
  .. prod.has_Inf α β }

end prod
