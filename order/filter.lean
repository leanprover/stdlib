/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

Theory of filters on sets.
-/
import order.galois_connection data.set data.finset order.zorn
open lattice set

universes u v w x y

local attribute [instance] classical.prop_decidable

namespace lattice
variables {α : Type u} {ι : Sort v}

section
variable [complete_lattice α]

lemma Inf_eq_finite_sets {s : set α} :
  Inf s = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t) :=
le_antisymm
  (le_infi $ assume t, le_infi $ assume ⟨_, h⟩, Inf_le_Inf h)
  (le_Inf $ assume b h, infi_le_of_le {b} $ infi_le_of_le (by simp [h]) $ Inf_le $ by simp)

lemma infi_insert_finset {ι : Type v} {s : finset ι} {f : ι → α} {i : ι} :
  (⨅j∈insert i s, f j) = f i ⊓ (⨅j∈s, f j) :=
by simp [infi_or, infi_inf_eq]

lemma infi_empty_finset {ι : Type v} {f : ι → α} : (⨅j∈(∅ : finset ι), f j) = ⊤ :=
by simp

end

-- TODO: move
lemma inf_left_comm [semilattice_inf α] (a b c : α) : a ⊓ (b ⊓ c) = b ⊓ (a ⊓ c) :=
by rw [← inf_assoc, ← inf_assoc, @inf_comm α _ a]

def complete_lattice.copy (c : complete_lattice α)
  (le : α → α → Prop) (eq_le : le = @complete_lattice.le α c)
  (top : α) (eq_top : top = @complete_lattice.top α c)
  (bot : α) (eq_bot : bot = @complete_lattice.bot α c)
  (sup : α → α → α) (eq_sup : sup = @complete_lattice.sup α c)
  (inf : α → α → α) (eq_inf : inf = @complete_lattice.inf α c)
  (Sup : set α → α) (eq_Sup : Sup = @complete_lattice.Sup α c)
  (Inf : set α → α) (eq_Inf : Inf = @complete_lattice.Inf α c) :
  complete_lattice α :=
begin
  refine { le := le, top := top, bot := bot, sup := sup, inf := inf, Sup := Sup, Inf := Inf, ..};
    subst_vars,
  exact @complete_lattice.le_refl α c,
  exact @complete_lattice.le_trans α c,
  exact @complete_lattice.le_antisymm α c,
  exact @complete_lattice.le_sup_left α c,
  exact @complete_lattice.le_sup_right α c,
  exact @complete_lattice.sup_le α c,
  exact @complete_lattice.inf_le_left α c,
  exact @complete_lattice.inf_le_right α c,
  exact @complete_lattice.le_inf α c,
  exact @complete_lattice.le_top α c,
  exact @complete_lattice.bot_le α c,
  exact @complete_lattice.le_Sup α c,
  exact @complete_lattice.Sup_le α c,
  exact @complete_lattice.Inf_le α c,
  exact @complete_lattice.le_Inf α c
end

end lattice

namespace set

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} {ι : Sort y}

theorem monotone_inter [preorder β] {f g : β → set α}
  (hf : monotone f) (hg : monotone g) : monotone (λx, (f x) ∩ (g x)) :=
assume a b h x ⟨h₁, h₂⟩, ⟨hf h h₁, hg h h₂⟩

theorem monotone_set_of [preorder α] {p : α → β → Prop}
  (hp : ∀b, monotone (λa, p a b)) : monotone (λa, {b | p a b}) :=
assume a a' h b, hp b h

end set

open set lattice

section order
variables {α : Type u} (r : α → α → Prop)
local infix `≼` : 50 := r

/-- A family of elements of α is directed (with respect to a relation `≼` on α)
  if there is a member of the family `≼`-above any pair in the family.  -/
def directed {ι : Sort v} (f : ι → α) := ∀x y, ∃z, f z ≼ f x ∧ f z ≼ f y
/-- A subset of α is directed if there is an element of the set `≼`-above any
  pair of elements in the set. -/
def directed_on (s : set α) := ∀ (x ∈ s) (y ∈ s), ∃z ∈ s, z ≼ x ∧ z ≼ y

lemma directed_on_Union {r} {ι : Sort v} {f : ι → set α} (hd : directed (⊇) f)
  (h : ∀x, directed_on r (f x)) : directed_on r (⋃x, f x) :=
by simp [directed_on]; exact
assume a₁ b₁ fb₁ a₂ b₂ fb₂,
let ⟨z, zb₁, zb₂⟩ := hd b₁ b₂,
    ⟨x, xf, xa₁, xa₂⟩ := h z a₁ (zb₁ fb₁) a₂ (zb₂ fb₂) in
⟨x, ⟨z, xf⟩, xa₁, xa₂⟩

end order

theorem directed_of_chain {α : Type u} {β : Type v} [preorder β] {f : α → β} {c : set α}
  (h : zorn.chain (λa b, f b ≤ f a) c) :
  directed (≤) (λx:{a:α // a ∈ c}, f (x.val)) :=
assume ⟨a, ha⟩ ⟨b, hb⟩, classical.by_cases
  (assume : a = b, by simp [this]; exact ⟨b, hb, le_refl _⟩)
  (assume : a ≠ b,
    have f b ≤ f a ∨ f a ≤ f b, from h a ha b hb this,
    or.elim this
      (assume : f b ≤ f a, ⟨⟨b, hb⟩, this, le_refl _⟩)
      (assume : f a ≤ f b, ⟨⟨a, ha⟩, le_refl _, this⟩))

structure filter (α : Type*) :=
(sets                   : set (set α))
(univ_sets              : set.univ ∈ sets)
(sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → x ∩ y ∈ sets)

namespace filter
variables {α : Type u} {f g : filter α} {s t : set α}

lemma filter_eq : ∀{f g : filter α}, f.sets = g.sets → f = g
| ⟨a, _, _, _⟩ ⟨._, _, _, _⟩ rfl := rfl

lemma filter_eq_iff : f = g ↔ f.sets = g.sets :=
⟨congr_arg _, filter_eq⟩

protected lemma ext_iff : f = g ↔ ∀ s, s ∈ f.sets ↔ s ∈ g.sets :=
by rw [filter_eq_iff, ext_iff]

@[extensionality]
protected lemma ext : (∀ s, s ∈ f.sets ↔ s ∈ g.sets) → f = g :=
filter.ext_iff.2

lemma univ_mem_sets : univ ∈ f.sets :=
f.univ_sets

lemma mem_sets_of_superset : ∀{x y : set α}, x ∈ f.sets → x ⊆ y → y ∈ f.sets :=
f.sets_of_superset

lemma inter_mem_sets : ∀{s t}, s ∈ f.sets → t ∈ f.sets → s ∩ t ∈ f.sets :=
f.inter_sets

lemma univ_mem_sets' (h : ∀ a, a ∈ s): s ∈ f.sets :=
mem_sets_of_superset univ_mem_sets (assume x _, h x)

lemma mp_sets (hs : s ∈ f.sets) (h : {x | x ∈ s → x ∈ t} ∈ f.sets) : t ∈ f.sets :=
mem_sets_of_superset (inter_mem_sets hs h) $ assume x ⟨h₁, h₂⟩, h₂ h₁

lemma Inter_mem_sets {β : Type v} {s : β → set α} {is : set β} (hf : finite is) :
  (∀i∈is, s i ∈ f.sets) → (⋂i∈is, s i) ∈ f.sets :=
finite.induction_on hf
  (assume hs, by simp [univ_mem_sets])
  (assume i is _ hf hi hs,
    have h₁ : s i ∈ f.sets, from hs i (by simp),
    have h₂ : (⋂x∈is, s x) ∈ f.sets, from hi $ assume a ha, hs _ $ by simp [ha],
    by simp [inter_mem_sets h₁ h₂])

lemma exists_sets_subset_iff : (∃t∈f.sets, t ⊆ s) ↔ s ∈ f.sets :=
⟨assume ⟨t, ht, ts⟩, mem_sets_of_superset ht ts, assume hs, ⟨s, hs, subset.refl _⟩⟩

lemma monotone_mem_sets {f : filter α} : monotone (λs, s ∈ f.sets) :=
assume s t hst h, mem_sets_of_superset h hst

end filter

namespace tactic.interactive
open tactic interactive

/-- `filter [t1, ⋯, tn]` replaces a goal of the form `s ∈ f.sets`
and terms `h1 : t1 ∈ f.sets, ⋯, tn ∈ f.sets` with `∀x, x ∈ t1 → ⋯ → x ∈ tn → x ∈ s`.

`filter [t1, ⋯, tn] e` is a short form for `{ filter [t1, ⋯, tn], exact e }`.
-/
meta def filter_upwards
  (s : parse types.pexpr_list)
  (e' : parse $ optional types.texpr) : tactic unit :=
do
  s.reverse.mmap (λ e, eapplyc `filter.mp_sets >> eapply e),
  eapplyc `filter.univ_mem_sets',
  match e' with
  | some e := interactive.exact e
  | none := skip
  end

end tactic.interactive

namespace filter
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

section principal

/-- The principal filter of `s` is the collection of all supersets of `s`. -/
def principal (s : set α) : filter α :=
{ sets             := {t | s ⊆ t},
  univ_sets        := subset_univ s,
  sets_of_superset := assume x y hx hy, subset.trans hx hy,
  inter_sets       := assume x y, subset_inter }

instance : inhabited (filter α) :=
⟨principal ∅⟩

@[simp] lemma mem_principal_sets {s t : set α} : s ∈ (principal t).sets ↔ t ⊆ s := iff.rfl

lemma mem_principal_self (s : set α) : s ∈ (principal s).sets := subset.refl _

end principal

section join

/-- The join of a filter of filters is defined by the relation `s ∈ join f ↔ {t | s ∈ t} ∈ f`. -/
def join (f : filter (filter α)) : filter α :=
{ sets             := {s | {t : filter α | s ∈ t.sets} ∈ f.sets},
  univ_sets        := by simp [univ_mem_sets]; exact univ_mem_sets,
  sets_of_superset := assume x y hx xy,
    mem_sets_of_superset hx $ assume f h, mem_sets_of_superset h xy,
  inter_sets       := assume x y hx hy,
    mem_sets_of_superset (inter_mem_sets hx hy) $ assume f ⟨h₁, h₂⟩, inter_mem_sets h₁ h₂ }

@[simp] lemma mem_join_sets {s : set α} {f : filter (filter α)} :
  s ∈ (join f).sets ↔ {t | s ∈ filter.sets t} ∈ f.sets := iff.rfl

end join

section lattice

instance : partial_order (filter α) :=
{ le            := λf g, g.sets ⊆ f.sets,
  le_antisymm   := assume a b h₁ h₂, filter_eq $ subset.antisymm h₂ h₁,
  le_refl       := assume a, subset.refl _,
  le_trans      := assume a b c h₁ h₂, subset.trans h₂ h₁ }

theorem le_def {f g : filter α} : f ≤ g ↔ ∀ x ∈ g.sets, x ∈ f.sets := iff.rfl

/-- `generate_sets g s`: `s` is in the filter closure of `g`. -/
inductive generate_sets (g : set (set α)) : set α → Prop
| basic {s : set α}      : s ∈ g → generate_sets s
| univ {}                : generate_sets univ
| superset {s t : set α} : generate_sets s → s ⊆ t → generate_sets t
| inter {s t : set α}    : generate_sets s → generate_sets t → generate_sets (s ∩ t)

/-- `generate g` is the smallest filter containing the sets `g`. -/
def generate (g : set (set α)) : filter α :=
{ sets             := {s | generate_sets g s},
  univ_sets        := generate_sets.univ,
  sets_of_superset := assume x y, generate_sets.superset,
  inter_sets       := assume s t, generate_sets.inter }

lemma sets_iff_generate {s : set (set α)} {f : filter α} : f ≤ filter.generate s ↔ s ⊆ f.sets :=
iff.intro
  (assume h u hu, h $ generate_sets.basic $ hu)
  (assume h u hu, hu.rec_on h univ_mem_sets
    (assume x y _ hxy hx, mem_sets_of_superset hx hxy)
    (assume x y _ _ hx hy, inter_mem_sets hx hy))

protected def mk_of_closure (s : set (set α)) (hs : (generate s).sets = s) : filter α :=
{ sets             := s,
  univ_sets        := hs ▸ univ_mem_sets,
  sets_of_superset := assume x y, hs ▸ mem_sets_of_superset,
  inter_sets       := assume x y, hs ▸ inter_mem_sets }

lemma mk_of_closure_sets {s : set (set α)} {hs : (generate s).sets = s} :
  filter.mk_of_closure s hs = generate s :=
filter.ext $ assume u, hs.symm ▸ iff.refl _

/- Galois insertion from sets of sets into a filters. -/
def gi_generate (α : Type*) :
  @galois_insertion (set (set α)) (order_dual (filter α)) _ _ filter.generate filter.sets :=
{ gc        := assume s f, sets_iff_generate,
  le_l_u    := assume f u, generate_sets.basic,
  choice    := λs hs, filter.mk_of_closure s (le_antisymm hs $ sets_iff_generate.1 $ le_refl _),
  choice_eq := assume s hs, mk_of_closure_sets }

/-- The infimum of filters is the filter generated by intersections
  of elements of the two filters. -/
instance : has_inf (filter α) := ⟨λf g : filter α,
{ sets             := {s | ∃ (a ∈ f.sets) (b ∈ g.sets), a ∩ b ⊆ s },
  univ_sets        := ⟨_, univ_mem_sets, _, univ_mem_sets, inter_subset_left _ _⟩,
  sets_of_superset := assume x y ⟨a, ha, b, hb, h⟩ xy, ⟨a, ha, b, hb, subset.trans h xy⟩,
  inter_sets       := assume x y ⟨a, ha, b, hb, hx⟩ ⟨c, hc, d, hd, hy⟩,
    ⟨_, inter_mem_sets ha hc, _, inter_mem_sets hb hd,
      calc a ∩ c ∩ (b ∩ d) = (a ∩ b) ∩ (c ∩ d) : by ac_refl
        ... ⊆ x ∩ y : inter_subset_inter hx hy⟩ }⟩

@[simp] lemma mem_inf_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊓ g).sets ↔ ∃t₁∈f.sets, ∃t₂∈g.sets, t₁ ∩ t₂ ⊆ s := iff.rfl

lemma mem_inf_sets_of_left {f g : filter α} {s : set α} (h : s ∈ f.sets) : s ∈ (f ⊓ g).sets :=
⟨s, h, univ, univ_mem_sets, inter_subset_left _ _⟩

lemma mem_inf_sets_of_right {f g : filter α} {s : set α} (h : s ∈ g.sets) : s ∈ (f ⊓ g).sets :=
⟨univ, univ_mem_sets, s, h, inter_subset_right _ _⟩

lemma inter_mem_inf_sets {α : Type u} {f g : filter α} {s t : set α}
  (hs : s ∈ f.sets) (ht : t ∈ g.sets) : s ∩ t ∈ (f ⊓ g).sets :=
inter_mem_sets (mem_inf_sets_of_left hs) (mem_inf_sets_of_right ht)

instance : has_top (filter α) :=
⟨{ sets            := {s | ∀x, x ∈ s},
  univ_sets        := assume x, mem_univ x,
  sets_of_superset := assume x y hx hxy a, hxy (hx a),
  inter_sets       := assume x y hx hy a, mem_inter (hx _) (hy _) }⟩

lemma mem_top_sets_iff_forall {s : set α} : s ∈ (⊤ : filter α).sets ↔ (∀x, x ∈ s) :=
iff.refl _

@[simp] lemma mem_top_sets {s : set α} : s ∈ (⊤ : filter α).sets ↔ s = univ :=
by rw [mem_top_sets_iff_forall, eq_univ_iff_forall]

section complete_lattice

/- We lift the complete lattice along the Galois connection `generate` / `sets`. Unfortunately,
  we want to have different definitional equalities for the lattice operations. So we define them
  upfront and change the lattice operations for the complete lattice instance. -/

private def original_complete_lattice : complete_lattice (filter α) :=
@order_dual.lattice.complete_lattice _ (gi_generate α).lift_complete_lattice

local attribute [instance] original_complete_lattice

instance : complete_lattice (filter α) := original_complete_lattice.copy
  /- le  -/ filter.partial_order.le rfl
  /- top -/ (filter.lattice.has_top).1
  (top_unique $ assume s hs, (eq_univ_of_forall hs).symm ▸ univ_mem_sets)
  /- bot -/ _ rfl
  /- sup -/ _ rfl
  /- inf -/ (filter.lattice.has_inf).1
  begin
    ext f g : 2,
    exact le_antisymm
      (le_inf (assume s, mem_inf_sets_of_left) (assume s, mem_inf_sets_of_right))
      (assume s ⟨a, ha, b, hb, hs⟩, mem_sets_of_superset (inter_mem_sets
        (@inf_le_left (filter α) _ _ _ _ ha)
        (@inf_le_right (filter α) _ _ _ _ hb)) hs)
  end
  /- Sup -/ (join ∘ principal) (by ext s x; exact (@mem_bInter_iff _ _ s filter.sets x).symm)
  /- Inf -/ _ rfl

end complete_lattice

lemma bot_sets_eq : (⊥ : filter α).sets = univ := rfl

lemma sup_sets_eq {f g : filter α} : (f ⊔ g).sets = f.sets ∩ g.sets :=
(gi_generate α).gc.u_inf

lemma Sup_sets_eq {s : set (filter α)} : (Sup s).sets = (⋂f∈s, (f:filter α).sets) :=
(gi_generate α).gc.u_Inf

lemma supr_sets_eq {f : ι → filter α} : (supr f).sets = (⋂i, (f i).sets) :=
(gi_generate α).gc.u_infi

lemma generate_empty : filter.generate ∅ = (⊤ : filter α) :=
(gi_generate α).gc.l_bot

lemma generate_univ : filter.generate univ = (⊥ : filter α) :=
mk_of_closure_sets.symm

lemma generate_union {s t : set (set α)} :
  filter.generate (s ∪ t) = filter.generate s ⊓ filter.generate t :=
(gi_generate α).gc.l_sup

lemma generate_Union {s : ι → set (set α)} :
  filter.generate (⋃ i, s i) = (⨅ i, filter.generate (s i)) :=
(gi_generate α).gc.l_supr

@[simp] lemma mem_bot_sets {s : set α} : s ∈ (⊥ : filter α).sets :=
trivial

@[simp] lemma mem_sup_sets {f g : filter α} {s : set α} :
  s ∈ (f ⊔ g).sets ↔ s ∈ f.sets ∧ s ∈ g.sets :=
iff.rfl

@[simp] lemma mem_Sup_sets {x : set α} {s : set (filter α)} :
  x ∈ (Sup s).sets ↔ (∀f∈s, x ∈ (f:filter α).sets) :=
iff.rfl

@[simp] lemma mem_supr_sets {x : set α} {f : ι → filter α} :
  x ∈ (supr f).sets ↔ (∀i, x ∈ (f i).sets) :=
by simp [supr_sets_eq]

@[simp] lemma le_principal_iff {s : set α} {f : filter α} : f ≤ principal s ↔ s ∈ f.sets :=
show (∀{t}, s ⊆ t → t ∈ f.sets) ↔ s ∈ f.sets,
  from ⟨assume h, h (subset.refl s), assume hs t ht, mem_sets_of_superset hs ht⟩

lemma principal_mono {s t : set α} : principal s ≤ principal t ↔ s ⊆ t :=
by simp

lemma monotone_principal : monotone (principal : set α → filter α) :=
by simp [monotone, principal_mono]; exact assume a b h, h

@[simp] lemma principal_eq_iff_eq {s t : set α} : principal s = principal t ↔ s = t :=
by simp [le_antisymm_iff]; refl

@[simp] lemma join_principal_eq_Sup {s : set (filter α)} : join (principal s) = Sup s := rfl

/- lattice equations -/

lemma empty_in_sets_eq_bot {f : filter α} : ∅ ∈ f.sets ↔ f = ⊥ :=
⟨assume h, bot_unique $ assume s _, mem_sets_of_superset h (empty_subset s),
  assume : f = ⊥, this.symm ▸ mem_bot_sets⟩

lemma inhabited_of_mem_sets {f : filter α} {s : set α} (hf : f ≠ ⊥) (hs : s ∈ f.sets) :
  ∃x, x ∈ s :=
have ∅ ∉ f.sets, from assume h, hf $ empty_in_sets_eq_bot.mp h,
have s ≠ ∅, from assume h, this (h ▸ hs),
exists_mem_of_ne_empty this

lemma filter_eq_bot_of_not_nonempty {f : filter α} (ne : ¬ nonempty α) : f = ⊥ :=
empty_in_sets_eq_bot.mp $ univ_mem_sets' $ assume x, false.elim (ne ⟨x⟩)

lemma forall_sets_neq_empty_iff_neq_bot {f : filter α} :
  (∀ (s : set α), s ∈ f.sets → s ≠ ∅) ↔ f ≠ ⊥ :=
by
  simp [(@empty_in_sets_eq_bot α f).symm];
  exact ⟨assume h hs, h _ hs rfl, assume h s hs eq, h $ eq ▸ hs⟩

lemma mem_sets_of_neq_bot {f : filter α} {s : set α} (h : f ⊓ principal (-s) = ⊥) : s ∈ f.sets :=
have ∅ ∈ (f ⊓ principal (- s)).sets, from h.symm ▸ mem_bot_sets,
let ⟨s₁, hs₁, s₂, (hs₂ : -s ⊆ s₂), (hs : s₁ ∩ s₂ ⊆ ∅)⟩ := this in
by filter_upwards [hs₁] assume a ha, classical.by_contradiction $ assume ha', hs ⟨ha, hs₂ ha'⟩

lemma infi_sets_eq {f : ι → filter α} (h : directed (≤) f) (ne : nonempty ι) :
  (infi f).sets = (⋃ i, (f i).sets) :=
let ⟨i⟩ := ne, u := { filter .
    sets             := (⋃ i, (f i).sets),
    univ_sets        := begin simp, exact ⟨i, univ_mem_sets⟩ end,
    sets_of_superset := begin simp, assume x y i hx hxy, exact ⟨i, mem_sets_of_superset hx hxy⟩ end,
    inter_sets       :=
    begin
      simp,
      assume x y a hx b hy,
      rcases h a b with ⟨c, ha, hb⟩,
      exact ⟨c, inter_mem_sets (ha hx) (hb hy)⟩
    end } in
subset.antisymm
  (show u ≤ infi f, from le_infi $ assume i, le_supr (λi, (f i).sets) i)
  (Union_subset $ assume i, infi_le f i)

lemma infi_sets_eq' {f : β → filter α} {s : set β} (h : directed_on (λx y, f x ≤ f y) s) (ne : ∃i, i ∈ s) :
  (⨅ i∈s, f i).sets = (⋃ i ∈ s, (f i).sets) :=
let ⟨i, hi⟩ := ne in
calc (⨅ i ∈ s, f i).sets  = (⨅ t : {t // t ∈ s}, (f t.val)).sets : by rw [infi_subtype]; refl
  ... = (⨆ t : {t // t ∈ s}, (f t.val).sets) : infi_sets_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨆ t ∈ {t | t ∈ s}, (f t).sets) : by rw [supr_subtype]; refl

lemma Inf_sets_eq_finite {s : set (filter α)} :
  (Inf s).sets = (⋃ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t).sets) :=
calc (Inf s).sets = (⨅ t ∈ { t | finite t ∧ t ⊆ s}, Inf t).sets : by rw [lattice.Inf_eq_finite_sets]
  ... = (⨆ t ∈ {t | finite t ∧ t ⊆ s}, (Inf t).sets) : infi_sets_eq'
    (assume x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩, ⟨x ∪ y, ⟨finite_union hx₁ hy₁, union_subset hx₂ hy₂⟩,
      Inf_le_Inf $ subset_union_left _ _, Inf_le_Inf $ subset_union_right _ _⟩)
    ⟨∅, by simp⟩

@[simp] lemma sup_join {f₁ f₂ : filter (filter α)} : (join f₁ ⊔ join f₂) = join (f₁ ⊔ f₂) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq, join]

@[simp] lemma supr_join {ι : Sort w} {f : ι → filter (filter α)} : (⨆x, join (f x)) = join (⨆x, f x) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq, join]

instance : bounded_distrib_lattice (filter α) :=
{ le_sup_inf :=
  begin
    assume x y z s,
    simp only [and_assoc, mem_inf_sets, mem_sup_sets, exists_prop, exists_imp_distrib, and_imp],
    intros hs t₁ ht₁ t₂ ht₂ hts,
    exact ⟨s ∪ t₁,
      x.sets_of_superset hs $ subset_union_left _ _,
      y.sets_of_superset ht₁ $ subset_union_right _ _,
      s ∪ t₂,
      x.sets_of_superset hs $ subset_union_left _ _,
      z.sets_of_superset ht₂ $ subset_union_right _ _,
      subset.trans (@le_sup_inf (set α) _ _ _ _) (union_subset (subset.refl _) hts)⟩
  end,
  ..filter.lattice.complete_lattice }

private lemma infi_finite_distrib {s : set (filter α)} {f : filter α} (h : finite s) :
  (⨅ a ∈ s, f ⊔ a) = f ⊔ (Inf s) :=
finite.induction_on h
  (by simp only [mem_empty_eq, infi_false, infi_top, Inf_empty, sup_top_eq])
  (by intros a s hn hs hi; rw [infi_insert, hi, ← sup_inf_left, Inf_insert])

/- the complementary version with ⨆ g∈s, f ⊓ g does not hold! -/
lemma binfi_sup_eq { f : filter α } {s : set (filter α)} : (⨅ g∈s, f ⊔ g) = f ⊔ Inf s :=
le_antisymm
  begin
    intros t h,
    cases h with h₁ h₂,
    rw [Inf_sets_eq_finite] at h₂,
    simp [and_assoc] at h₂,
    rcases h₂ with ⟨s', hs', hs's, ht'⟩,
    have ht : t ∈ (⨅ a ∈ s', f ⊔ a).sets,
    { rw [infi_finite_distrib], exact ⟨h₁, ht'⟩, exact hs' },
    clear h₁ ht',
    revert ht t,
    change (⨅ a ∈ s, f ⊔ a) ≤ (⨅ a ∈ s', f ⊔ a),
    apply infi_le_infi2 _,
    exact assume i, ⟨i, infi_le_infi2 $ assume h, ⟨hs's h, le_refl _⟩⟩
  end
  (le_infi $ assume g, le_infi $ assume h, sup_le_sup (le_refl f) $ Inf_le h)

lemma infi_sup_eq { f : filter α } {g : ι → filter α} : (⨅ x, f ⊔ g x) = f ⊔ infi g :=
calc (⨅ x, f ⊔ g x) = (⨅ x (h : ∃i, g i = x), f ⊔ x) : by simp; rw [infi_comm]; simp
  ... = f ⊔ Inf {x | ∃i, g i = x} : binfi_sup_eq
  ... = f ⊔ infi g : by rw [Inf_eq_infi]; dsimp; simp; rw [infi_comm]; simp

lemma mem_infi_sets_finset {s : finset α} {f : α → filter β} :
  ∀t, t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⋂a∈s, p a) ⊆ t) :=
show ∀t, t ∈ (⨅a∈s, f a).sets ↔ (∃p:α → set β, (∀a∈s, p a ∈ (f a).sets) ∧ (⨅a∈s, p a) ≤ t),
begin
  refine finset.induction_on s _ _,
  { simp only [finset.not_mem_empty, false_implies_iff, lattice.infi_empty_finset, top_le_iff,
      imp_true_iff, mem_top_sets, true_and, exists_const],
    intros; refl },
  { intros a s has ih t,
    simp only [ih, finset.forall_mem_insert, lattice.infi_insert_finset, mem_inf_sets,
      exists_prop, iff_iff_implies_and_implies, exists_imp_distrib, and_imp, and_assoc] {contextual := tt},
    split,
    { intros t₁ ht₁ t₂ p hp ht₂ ht,
      existsi function.update p a t₁,
      have : ∀a'∈s, function.update p a t₁ a' = p a',
        from assume a' ha',
        have a' ≠ a, from assume h, has $ h ▸ ha',
        function.update_noteq this,
      have eq : (⨅j ∈ s, function.update p a t₁ j) = (⨅j ∈ s, p j),
        begin congr, funext b, congr, funext h, apply this, assumption end,
      simp only [this, ht₁, hp, function.update_same, true_and, imp_true_iff, eq] {contextual := tt},
      exact subset.trans (inter_subset_inter (subset.refl _) ht₂) ht },
    from assume p hpa hp ht, ⟨p a, hpa, (⨅j∈s, p j), ⟨⟨p, hp, le_refl _⟩, ht⟩⟩ }
end

/- principal equations -/

@[simp] lemma inf_principal {s t : set α} : principal s ⊓ principal t = principal (s ∩ t) :=
le_antisymm
  (by simp; exact ⟨s, subset.refl s, t, subset.refl t, by simp⟩)
  (by simp [le_inf_iff, inter_subset_left, inter_subset_right])

@[simp] lemma sup_principal {s t : set α} : principal s ⊔ principal t = principal (s ∪ t) :=
filter_eq $ set.ext $ by simp [union_subset_iff]

@[simp] lemma supr_principal {ι : Sort w} {s : ι → set α} : (⨆x, principal (s x)) = principal (⋃i, s i) :=
filter_eq $ set.ext $ assume x, by simp [supr_sets_eq]; exact (@supr_le_iff (set α) _ _ _ _).symm

lemma principal_univ : principal (univ : set α) = ⊤ :=
top_unique $ by simp

lemma principal_empty : principal (∅ : set α) = ⊥ :=
bot_unique $ assume s _, empty_subset _

@[simp] lemma principal_eq_bot_iff {s : set α} : principal s = ⊥ ↔ s = ∅ :=
⟨assume h, principal_eq_iff_eq.mp $ by simp [principal_empty, h], assume h, by simp [*, principal_empty]⟩

lemma inf_principal_eq_bot {f : filter α} {s : set α} (hs : -s ∈ f.sets) : f ⊓ principal s = ⊥ :=
empty_in_sets_eq_bot.mp ⟨_, hs, s, mem_principal_self s, assume x ⟨h₁, h₂⟩, h₁ h₂⟩

end lattice

section map

/-- The forward map of a filter -/
def map (m : α → β) (f : filter α) : filter β :=
{ sets             := preimage m ⁻¹' f.sets,
  univ_sets        := univ_mem_sets,
  sets_of_superset := assume s t hs st, mem_sets_of_superset hs $ preimage_mono st,
  inter_sets       := assume s t hs ht, inter_mem_sets hs ht }

@[simp] lemma map_principal {s : set α} {f : α → β} :
  map f (principal s) = principal (set.image f s) :=
filter_eq $ set.ext $ assume a, image_subset_iff.symm

variables {f : filter α} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] lemma mem_map : t ∈ (map m f).sets ↔ {x | m x ∈ t} ∈ f.sets := iff.rfl

lemma image_mem_map (hs : s ∈ f.sets) : m '' s ∈ (map m f).sets :=
f.sets_of_superset hs $ subset_preimage_image m s

@[simp] lemma map_id : filter.map id f = f :=
filter_eq $ rfl

@[simp] lemma map_compose : filter.map m' ∘ filter.map m = filter.map (m' ∘ m) :=
funext $ assume _, filter_eq $ rfl

@[simp] lemma map_map : filter.map m' (filter.map m f) = filter.map (m' ∘ m) f :=
congr_fun (@@filter.map_compose m m') f

end map

section vmap

/-- The inverse map of a filter -/
def vmap (m : α → β) (f : filter β) : filter α :=
{ sets             := { s | ∃t∈f.sets, m ⁻¹' t ⊆ s },
  univ_sets        := ⟨univ, univ_mem_sets, by simp⟩,
  sets_of_superset := assume a b ⟨a', ha', ma'a⟩ ab,
    ⟨a', ha', subset.trans ma'a ab⟩,
  inter_sets       := assume a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩,
    ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, inter_subset_inter ha₂ hb₂⟩ }

end vmap

/-- The cofinite filter is the filter of subsets whose complements are finite. -/
def cofinite : filter α :=
{ sets             := {s | finite (- s)},
  univ_sets        := by simp,
  sets_of_superset := assume s t (hs : finite (-s)) (st: s ⊆ t),
    finite_subset hs $ @lattice.neg_le_neg (set α) _ _ _ st,
  inter_sets       := assume s t (hs : finite (-s)) (ht : finite (-t)),
    by simp [compl_inter, finite_union, ht, hs] }

/-- The monadic bind operation on filter is defined the usual way in terms of `map` and `join`. -/
def bind (f : filter α) (m : α → filter β) : filter β := join (map m f)

instance : monad filter :=
{ bind       := @bind,
  pure       := λ(α : Type u) x, principal {x},
  map        := @filter.map }

instance : is_lawful_monad filter :=
{ id_map     := assume α f, filter_eq rfl,
  pure_bind  := assume α β a f, by simp [bind, Sup_image],
  bind_assoc := assume α β γ f m₁ m₂, filter_eq rfl,
  bind_pure_comp_eq_map := assume α β f x, filter_eq $ by simp [bind, join, map, preimage, principal] }

@[simp] lemma pure_def (x : α) : pure x = principal {x} := rfl

@[simp] lemma mem_pure {a : α} {s : set α} : a ∈ s → s ∈ (pure a : filter α).sets :=
by simp; exact id

@[simp] lemma map_def {α β} (m : α → β) (f : filter α) : m <$> f = map m f := rfl

@[simp] lemma bind_def {α β} (f : filter α) (m : α → filter β) : f >>= m = bind f m := rfl

instance : alternative filter :=
{ failure := λα, ⊥,
  orelse  := λα x y, x ⊔ y }

/- map and vmap equations -/
section map
variables {f f₁ f₂ : filter α} {g g₁ g₂ : filter β} {m : α → β} {m' : β → γ} {s : set α} {t : set β}

@[simp] theorem mem_vmap_sets : s ∈ (vmap m g).sets ↔ ∃t∈g.sets, m ⁻¹' t ⊆ s := iff.rfl
theorem preimage_mem_vmap (ht : t ∈ g.sets) : m ⁻¹' t ∈ (vmap m g).sets :=
⟨t, ht, subset.refl _⟩

lemma vmap_id : vmap id f = f :=
le_antisymm (assume s, preimage_mem_vmap) (assume s ⟨t, ht, hst⟩, mem_sets_of_superset ht hst)

lemma vmap_vmap_comp {m : γ → β} {n : β → α} : vmap m (vmap n f) = vmap (n ∘ m) f :=
le_antisymm
  (assume c ⟨b, hb, (h : preimage (n ∘ m) b ⊆ c)⟩, ⟨preimage n b, preimage_mem_vmap hb, h⟩)
  (assume c ⟨b, ⟨a, ha, (h₁ : preimage n a ⊆ b)⟩, (h₂ : preimage m b ⊆ c)⟩,
    ⟨a, ha, show preimage m (preimage n a) ⊆ c, from subset.trans (preimage_mono h₁) h₂⟩)

@[simp] theorem vmap_principal {t : set β} : vmap m (principal t) = principal (m ⁻¹' t) :=
filter_eq $ set.ext $ assume s,
  ⟨assume ⟨u, (hu : t ⊆ u), (b : preimage m u ⊆ s)⟩, subset.trans (preimage_mono hu) b,
    assume : preimage m t ⊆ s, ⟨t, subset.refl t, this⟩⟩

lemma map_le_iff_le_vmap : map m f ≤ g ↔ f ≤ vmap m g :=
⟨assume h s ⟨t, ht, hts⟩, mem_sets_of_superset (h ht) hts, assume h s ht, h ⟨_, ht, subset.refl _⟩⟩

lemma gc_map_vmap (m : α → β) : galois_connection (map m) (vmap m) :=
assume f g, map_le_iff_le_vmap

lemma map_mono (h : f₁ ≤ f₂) : map m f₁ ≤ map m f₂ := (gc_map_vmap m).monotone_l h
lemma monotone_map : monotone (map m) | a b := map_mono
lemma vmap_mono (h : g₁ ≤ g₂) : vmap m g₁ ≤ vmap m g₂ := (gc_map_vmap m).monotone_u h
lemma monotone_vmap : monotone (vmap m) | a b := vmap_mono

@[simp] lemma map_bot : map m ⊥ = ⊥ := (gc_map_vmap m).l_bot
@[simp] lemma map_sup : map m (f₁ ⊔ f₂) = map m f₁ ⊔ map m f₂ := (gc_map_vmap m).l_sup
@[simp] lemma map_supr {f : ι → filter α} : map m (⨆i, f i) = (⨆i, map m (f i)) :=
(gc_map_vmap m).l_supr

@[simp] lemma vmap_top : vmap m ⊤ = ⊤ := (gc_map_vmap m).u_top
@[simp] lemma vmap_inf : vmap m (g₁ ⊓ g₂) = vmap m g₁ ⊓ vmap m g₂ := (gc_map_vmap m).u_inf
@[simp] lemma vmap_infi {f : ι → filter β} : vmap m (⨅i, f i) = (⨅i, vmap m (f i)) :=
(gc_map_vmap m).u_infi

lemma map_vmap_le : map m (vmap m g) ≤ g := (gc_map_vmap m).l_u_le _
lemma le_vmap_map : f ≤ vmap m (map m f) := (gc_map_vmap m).le_u_l _

@[simp] lemma vmap_bot : vmap m ⊥ = ⊥ :=
bot_unique $ assume s _, ⟨∅, by simp, by simp⟩

lemma vmap_sup : vmap m (g₁ ⊔ g₂) = vmap m g₁ ⊔ vmap m g₂ :=
le_antisymm
  (assume s ⟨⟨t₁, ht₁, hs₁⟩, ⟨t₂, ht₂, hs₂⟩⟩,
    ⟨t₁ ∪ t₂,
      ⟨g₁.sets_of_superset ht₁ (subset_union_left _ _), g₂.sets_of_superset ht₂ (subset_union_right _ _)⟩,
      union_subset hs₁ hs₂⟩)
  (sup_le (vmap_mono le_sup_left) (vmap_mono le_sup_right))

lemma le_map_vmap' {f : filter β} {m : α → β} {s : set β}
  (hs : s ∈ f.sets) (hm : ∀b∈s, ∃a, m a = b) : f ≤ map m (vmap m f) :=
assume t' ⟨t, ht, (sub : m ⁻¹' t ⊆ m ⁻¹' t')⟩,
by filter_upwards [ht, hs] assume x hxt hxs,
  let ⟨y, hy⟩ := hm x hxs in
  hy ▸ sub (show m y ∈ t, from hy.symm ▸ hxt)

lemma le_map_vmap {f : filter β} {m : α → β} (hm : ∀x, ∃y, m y = x) : f ≤ map m (vmap m f) :=
le_map_vmap' univ_mem_sets (assume b _, hm b)

lemma vmap_map {f : filter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  vmap m (map m f) = f :=
have ∀s, preimage m (image m s) = s,
  from assume s, preimage_image_eq s h,
le_antisymm
  (assume s hs, ⟨
    image m s,
    f.sets_of_superset hs $ by simp [this, subset.refl],
    by simp [this, subset.refl]⟩)
  le_vmap_map

lemma le_of_map_le_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f.sets) (hsg : s ∈ g.sets) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f ≤ map m g) : f ≤ g :=
assume t ht, by filter_upwards [hsf, h $ image_mem_map (inter_mem_sets hsg ht)]
assume a has ⟨b, ⟨hbs, hb⟩, h⟩,
have b = a, from hm _ hbs _ has h,
this ▸ hb

lemma le_of_map_le_map_inj_iff {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f.sets) (hsg : s ∈ g.sets) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y) :
  map m f ≤ map m g ↔ f ≤ g :=
iff.intro (le_of_map_le_map_inj' hsf hsg hm) map_mono

lemma eq_of_map_eq_map_inj' {f g : filter α} {m : α → β} {s : set α}
  (hsf : s ∈ f.sets) (hsg : s ∈ g.sets) (hm : ∀x∈s, ∀y∈s, m x = m y → x = y)
  (h : map m f = map m g) : f = g :=
le_antisymm
  (le_of_map_le_map_inj' hsf hsg hm $ le_of_eq h)
  (le_of_map_le_map_inj' hsg hsf hm $ le_of_eq h.symm)

lemma map_inj {f g : filter α} {m : α → β} (hm : ∀ x y, m x = m y → x = y) (h : map m f = map m g) :
  f = g :=
have vmap m (map m f) = vmap m (map m g), by rw h,
by rwa [vmap_map hm, vmap_map hm] at this

lemma vmap_neq_bot {f : filter β} {m : α → β}
  (hm : ∀t∈f.sets, ∃a, m a ∈ t) : vmap m f ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $ assume s ⟨t, ht, t_s⟩,
  let ⟨a, (ha : a ∈ preimage m t)⟩ := hm t ht in
  neq_bot_of_le_neq_bot (ne_empty_of_mem ha) t_s

lemma vmap_neq_bot_of_surj {f : filter β} {m : α → β}
  (hf : f ≠ ⊥) (hm : ∀b, ∃a, m a = b) : vmap m f ≠ ⊥ :=
vmap_neq_bot $ assume t ht,
  let
    ⟨b, (hx : b ∈ t)⟩ := inhabited_of_mem_sets hf ht,
    ⟨a, (ha : m a = b)⟩ := hm b
  in ⟨a, ha.symm ▸ hx⟩

@[simp] lemma map_eq_bot_iff : map m f = ⊥ ↔ f = ⊥ :=
⟨by rw [←empty_in_sets_eq_bot, ←empty_in_sets_eq_bot]; exact id,
  assume h, by simp [*]⟩

lemma map_ne_bot (hf : f ≠ ⊥) : map m f ≠ ⊥ :=
assume h, hf $ by rwa [map_eq_bot_iff] at h

lemma sInter_vmap_sets (f : α → β) (F : filter β) :
  ⋂₀(vmap f F).sets = ⋂ U ∈ F.sets, f ⁻¹' U :=
begin
  ext x,
  suffices : (∀ (A : set α) (B : set β), B ∈ F.sets → f ⁻¹' B ⊆ A → x ∈ A) ↔
    ∀ (B : set β), B ∈ F.sets → f x ∈ B,
  by simp [set.mem_sInter, set.mem_Inter, mem_vmap_sets, this],
  split,
  { intros h U U_in,
    simpa [set.subset.refl] using h (f ⁻¹' U) U U_in },
  { intros h V U U_in f_U_V,
    exact f_U_V (h U U_in) },
end
end map

lemma map_cong {m₁ m₂ : α → β} {f : filter α} (h : {x | m₁ x = m₂ x} ∈ f.sets) :
  map m₁ f = map m₂ f :=
have ∀(m₁ m₂ : α → β) (h : {x | m₁ x = m₂ x} ∈ f.sets), map m₁ f ≤ map m₂ f,
begin
  intros  m₁ m₂ h s hs,
  show {x | m₁ x ∈ s} ∈ f.sets,
  filter_upwards [h, hs],
  simp [subset_def] {contextual := tt}
end,
le_antisymm (this m₁ m₂ h) (this m₂ m₁ $ mem_sets_of_superset h $ assume x, eq.symm)

-- this is a generic rule for monotone functions:
lemma map_infi_le {f : ι → filter α} {m : α → β} :
  map m (infi f) ≤ (⨅ i, map m (f i)) :=
le_infi $ assume i, map_mono $ infi_le _ _

lemma map_infi_eq {f : ι → filter α} {m : α → β} (hf : directed (≤) f) (hι : nonempty ι) :
  map m (infi f) = (⨅ i, map m (f i)) :=
le_antisymm
  map_infi_le
  (assume s (hs : preimage m s ∈ (infi f).sets),
    have ∃i, preimage m s ∈ (f i).sets,
      by simp [infi_sets_eq hf hι] at hs; assumption,
    let ⟨i, hi⟩ := this in
    have (⨅ i, map m (f i)) ≤ principal s,
      from infi_le_of_le i $ by simp; assumption,
    by simp at this; assumption)

lemma map_binfi_eq {ι : Type w} {f : ι → filter α} {m : α → β} {p : ι → Prop}
  (h : directed_on (λx y, f x ≤ f y) {x | p x}) (ne : ∃i, p i) :
  map m (⨅i (h : p i), f i) = (⨅i (h: p i), map m (f i)) :=
let ⟨i, hi⟩ := ne in
calc map m (⨅i (h : p i), f i) = map m (⨅i:subtype p, f i.val) : by simp [infi_subtype]
  ... = (⨅i:subtype p, map m (f i.val)) : map_infi_eq
    (assume ⟨x, hx⟩ ⟨y, hy⟩, match h x hx y hy with ⟨z, h₁, h₂, h₃⟩ := ⟨⟨z, h₁⟩, h₂, h₃⟩ end)
    ⟨⟨i, hi⟩⟩
  ... = (⨅i (h : p i), map m (f i)) : by simp [infi_subtype]

lemma map_inf' {f g : filter α} {m : α → β} {t : set α} (htf : t ∈ f.sets) (htg : t ∈ g.sets)
  (h : ∀x∈t, ∀y∈t, m x = m y → x = y) : map m (f ⊓ g) = map m f ⊓ map m g :=
begin
  refine le_antisymm
    (le_inf (map_mono inf_le_left) (map_mono inf_le_right))
    (assume s hs, _),
  simp [map, mem_inf_sets] at hs ⊢,
  rcases hs with ⟨t₁, h₁, t₂, h₂, hs⟩,
  refine ⟨m '' (t₁ ∩ t), _, m '' (t₂ ∩ t), _, _⟩,
  { filter_upwards [h₁, htf] assume a h₁ h₂, mem_image_of_mem _ ⟨h₁, h₂⟩ },
  { filter_upwards [h₂, htg] assume a h₁ h₂, mem_image_of_mem _ ⟨h₁, h₂⟩ },
  { rw [image_inter_on],
    { refine image_subset_iff.2 _,
      exact λ x ⟨⟨h₁, _⟩, h₂, _⟩, hs ⟨h₁, h₂⟩ },
    { exact λ x ⟨_, hx⟩ y ⟨_, hy⟩, h x hx y hy } }
end

lemma map_inf {f g : filter α} {m : α → β} (h : ∀ x y, m x = m y → x = y) :
  map m (f ⊓ g) = map m f ⊓ map m g :=
map_inf' univ_mem_sets univ_mem_sets (assume x _ y _, h x y)

lemma map_eq_vmap_of_inverse {f : filter α} {m : α → β} {n : β → α}
  (h₁ : m ∘ n = id) (h₂ : n ∘ m = id) : map m f = vmap n f :=
le_antisymm
  (assume b ⟨a, ha, (h : preimage n a ⊆ b)⟩, f.sets_of_superset ha $
    calc a = preimage (n ∘ m) a : by simp [h₂, preimage_id]
      ... ⊆ preimage m b : preimage_mono h)
  (assume b (hb : preimage m b ∈ f.sets),
    ⟨preimage m b, hb, show preimage (m ∘ n) b ⊆ b, by simp [h₁]; apply subset.refl⟩)

lemma map_swap_eq_vmap_swap {f : filter (α × β)} : prod.swap <$> f = vmap prod.swap f :=
map_eq_vmap_of_inverse prod.swap_swap_eq prod.swap_swap_eq

/- bind equations -/

@[simp] lemma mem_bind_sets {s : set β} {f : filter α} {m : α → filter β} :
  s ∈ (bind f m).sets ↔ ∃t ∈ f.sets, ∀x ∈ t, s ∈ (m x).sets :=
calc s ∈ (bind f m).sets ↔ {a | s ∈ (m a).sets} ∈ f.sets : by simp [bind]
                     ... ↔ (∃t ∈ f.sets, t ⊆ {a | s ∈ (m a).sets}) : exists_sets_subset_iff.symm
                     ... ↔ (∃t ∈ f.sets, ∀x ∈ t, s ∈ (m x).sets) : iff.refl _

lemma bind_mono {f : filter α} {g h : α → filter β} (h₁ : {a | g a ≤ h a} ∈ f.sets) :
  bind f g ≤ bind f h :=
assume x h₂, show (_ ∈ f.sets), by filter_upwards [h₁, h₂] assume s gh' h', gh' h'

lemma bind_sup {f g : filter α} {h : α → filter β} :
  bind (f ⊔ g) h = bind f h ⊔ bind g h :=
by simp [bind]

lemma bind_mono2 {f g : filter α} {h : α → filter β} (h₁ : f ≤ g) :
  bind f h ≤ bind g h :=
assume s h', h₁ h'

lemma principal_bind {s : set α} {f : α → filter β} :
  (bind (principal s) f) = (⨆x ∈ s, f x) :=
show join (map f (principal s)) = (⨆x ∈ s, f x),
  by simp [Sup_image]

lemma seq_mono {β : Type u} {f₁ f₂ : filter (α → β)} {g₁ g₂ : filter α}
  (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁ <*> g₁ ≤ f₂ <*> g₂ :=
le_trans (bind_mono2 hf) (bind_mono $ univ_mem_sets' $ assume f, map_mono hg)

@[simp] lemma mem_pure_sets {a : α} {s : set α} :
  s ∈ (pure a : filter α).sets ↔ a ∈ s := by simp

@[simp] lemma mem_return_sets {a : α} {s : set α} :
  s ∈ (return a : filter α).sets ↔ a ∈ s := mem_pure_sets

lemma infi_neq_bot_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≤) f) (hb : ∀i, f i ≠ ⊥): (infi f) ≠ ⊥ :=
let ⟨x⟩ := hn in
assume h, have he: ∅ ∈ (infi f).sets, from h.symm ▸ mem_bot_sets,
classical.by_cases
  (assume : nonempty ι,
    have ∃i, ∅ ∈ (f i).sets,
      by rw [infi_sets_eq hd this] at he; simp at he; assumption,
    let ⟨i, hi⟩ := this in
    hb i $ bot_unique $
    assume s _, (f i).sets_of_superset hi $ empty_subset _)
  (assume : ¬ nonempty ι,
    have univ ⊆ (∅ : set α),
    begin
      rw [←principal_mono, principal_univ, principal_empty, ←h],
      exact (le_infi $ assume i, false.elim $ this ⟨i⟩)
    end,
    this $ mem_univ x)

lemma infi_neq_bot_iff_of_directed {f : ι → filter α}
  (hn : nonempty α) (hd : directed (≤) f) : (infi f) ≠ ⊥ ↔ (∀i, f i ≠ ⊥) :=
⟨assume neq_bot i eq_bot, neq_bot $ bot_unique $ infi_le_of_le i $ eq_bot ▸ le_refl _,
  infi_neq_bot_of_directed hn hd⟩

lemma mem_infi_sets {f : ι → filter α} (i : ι) : ∀{s}, s ∈ (f i).sets → s ∈ (⨅i, f i).sets :=
show (⨅i, f i) ≤ f i, from infi_le _ _

@[elab_as_eliminator]
lemma infi_sets_induct {f : ι → filter α} {s : set α} (hs : s ∈ (infi f).sets) {p : set α → Prop}
  (uni : p univ)
  (ins : ∀{i s₁ s₂}, s₁ ∈ (f i).sets → p s₂ → p (s₁ ∩ s₂))
  (upw : ∀{s₁ s₂}, s₁ ⊆ s₂ → p s₁ → p s₂) : p s :=
begin
  have hs' : s ∈ (Inf {a : filter α | ∃ (i : ι), a = f i}).sets := hs,
  rw [Inf_sets_eq_finite] at hs',
  simp only [mem_Union] at hs',
  rcases hs' with ⟨is, ⟨fin_is, his⟩, hs⟩, revert his s,
  refine finite.induction_on fin_is _ (λ fi is fi_ne_is fin_is ih, _); intros his s hs' hs,
  { rw [Inf_empty, mem_top_sets] at hs, simpa [hs] },
  { rw [Inf_insert] at hs,
    rcases hs with ⟨s₁, hs₁, s₂, hs₂, hs⟩,
    rcases (his (mem_insert _ _) : ∃i, fi = f i) with ⟨i, rfl⟩,
    have hs₂ : p s₂, from
      have his : is ⊆ {x | ∃i, x = f i}, from assume i hi, his $ mem_insert_of_mem _ hi,
      have infi f ≤ Inf is, from Inf_le_Inf his,
      ih his (this hs₂) hs₂,
    exact upw hs (ins hs₁ hs₂) }
end

@[simp] lemma pure_neq_bot {α : Type u} {a : α} : pure a ≠ (⊥ : filter α) :=
by simp [pure, has_pure.pure]

/- tendsto -/

/-- `tendsto` is the generic "limit of a function" predicate.
  `tendsto f l₁ l₂` asserts that for every `l₂` neighborhood `a`,
  the `f`-preimage of `a` is an `l₁` neighborhood. -/
def tendsto (f : α → β) (l₁ : filter α) (l₂ : filter β) := l₁.map f ≤ l₂

lemma tendsto_def {f : α → β} {l₁ : filter α} {l₂ : filter β} :
  tendsto f l₁ l₂ ↔ ∀ s ∈ l₂.sets, f ⁻¹' s ∈ l₁.sets := iff.rfl

lemma tendsto_iff_vmap {f : α → β} {l₁ : filter α} {l₂ : filter β} :
  tendsto f l₁ l₂ ↔ l₁ ≤ l₂.vmap f :=
map_le_iff_le_vmap

lemma tendsto_cong {f₁ f₂ : α → β} {l₁ : filter α} {l₂ : filter β}
  (h : tendsto f₁ l₁ l₂) (hl : {x | f₁ x = f₂ x} ∈ l₁.sets) : tendsto f₂ l₁ l₂ :=
by rwa [tendsto, ←map_cong hl]

lemma tendsto_id' {x y : filter α} : x ≤ y → tendsto id x y :=
by simp [tendsto] { contextual := tt }

lemma tendsto_id {x : filter α} : tendsto id x x := tendsto_id' $ le_refl x

lemma tendsto.comp {f : α → β} {g : β → γ} {x : filter α} {y : filter β} {z : filter γ}
  (hf : tendsto f x y) (hg : tendsto g y z) : tendsto (g ∘ f) x z :=
calc map (g ∘ f) x = map g (map f x) : by rw [map_map]
  ... ≤ map g y : map_mono hf
  ... ≤ z : hg

lemma tendsto_le_left {f : α → β} {x y : filter α} {z : filter β}
  (h : y ≤ x) : tendsto f x z → tendsto f y z :=
le_trans (map_mono h)

lemma tendsto_le_right {f : α → β} {x : filter α} {y z : filter β}
  (h₁ : y ≤ z) (h₂ : tendsto f x y) : tendsto f x z :=
le_trans h₂ h₁

lemma tendsto_map {f : α → β} {x : filter α} : tendsto f x (map f x) := le_refl (map f x)

lemma tendsto_map' {f : β → γ} {g : α → β} {x : filter α} {y : filter γ}
  (h : tendsto (f ∘ g) x y) : tendsto f (map g x) y :=
by rwa [tendsto, map_map]

lemma tendsto_map'_iff {f : β → γ} {g : α → β} {x : filter α} {y : filter γ} :
  tendsto f (map g x) y ↔ tendsto (f ∘ g) x y :=
by rw [tendsto, map_map]; refl

lemma tendsto_vmap {f : α → β} {x : filter β} : tendsto f (vmap f x) x :=
map_vmap_le

lemma tendsto_vmap_iff {f : α → β} {g : β → γ} {a : filter α} {c : filter γ} :
  tendsto f a (c.vmap g) ↔ tendsto (g ∘ f) a c :=
⟨assume h, h.comp tendsto_vmap, assume h, map_le_iff_le_vmap.mp $ by rwa [map_map]⟩

lemma tendsto_vmap'' {m : α → β} {f : filter α} {g : filter β} (s : set α)
  {i : γ → α} (hs : s ∈ f.sets) (hi : ∀a∈s, ∃c, i c = a)
  (h : tendsto (m ∘ i) (vmap i f) g) : tendsto m f g :=
have tendsto m (map i $ vmap i $ f) g,
  by rwa [tendsto, ←map_compose] at h,
le_trans (map_mono $ le_map_vmap' hs hi) this

lemma vmap_eq_of_inverse {f : filter α} {g : filter β}
  {φ : α → β} {ψ : β → α} (inv₁ : φ ∘ ψ = id) (inv₂ : ψ ∘ φ = id)
  (lim₁ : tendsto φ f g) (lim₂ : tendsto ψ g f) : vmap φ g = f :=
begin
  have ineq₁ := calc
    vmap φ g = map ψ g : eq.symm (map_eq_vmap_of_inverse inv₂ inv₁)
         ... ≤ f : lim₂,
  have ineq₂ : f ≤ vmap φ g := map_le_iff_le_vmap.1 lim₁,
  exact le_antisymm ineq₁ ineq₂
end

lemma tendsto_inf {f : α → β} {x : filter α} {y₁ y₂ : filter β} :
  tendsto f x (y₁ ⊓ y₂) ↔ tendsto f x y₁ ∧ tendsto f x y₂ :=
by simp [tendsto]

lemma tendsto_inf_left {f : α → β} {x₁ x₂ : filter α} {y : filter β}
  (h : tendsto f x₁ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_left) h

lemma tendsto_inf_right {f : α → β} {x₁ x₂ : filter α} {y : filter β}
  (h : tendsto f x₂ y) : tendsto f (x₁ ⊓ x₂) y  :=
le_trans (map_mono inf_le_right) h

lemma tendsto_infi {f : α → β} {x : filter α} {y : ι → filter β} :
  tendsto f x (⨅i, y i) ↔ ∀i, tendsto f x (y i) :=
by simp [tendsto]

lemma tendsto_infi' {f : α → β} {x : ι → filter α} {y : filter β} (i : ι) :
  tendsto f (x i) y → tendsto f (⨅i, x i) y :=
tendsto_le_left (infi_le _ _)

lemma tendsto_principal {f : α → β} {a : filter α} {s : set β} :
  tendsto f a (principal s) ↔ {a | f a ∈ s} ∈ a.sets :=
by simp [tendsto]

lemma tendsto_principal_principal {f : α → β} {s : set α} {t : set β} :
  tendsto f (principal s) (principal t) ↔ ∀a∈s, f a ∈ t :=
by simp [tendsto, image_subset_iff]; refl

section lift

/-- A variant on `bind` using a function `g` taking a set
  instead of a member of `α`. -/
protected def lift (f : filter α) (g : set α → filter β) :=
⨅s ∈ f.sets, g s

variables {f f₁ f₂ : filter α} {g g₁ g₂ : set α → filter β}

lemma lift_sets_eq (hg : monotone g) : (f.lift g).sets = (⋃t∈f.sets, (g t).sets) :=
infi_sets_eq'
  (assume s hs t ht, ⟨s ∩ t, inter_mem_sets hs ht,
    hg $ inter_subset_left s t, hg $ inter_subset_right s t⟩)
  ⟨univ, univ_mem_sets⟩

lemma mem_lift {s : set β} {t : set α} (ht : t ∈ f.sets) (hs : s ∈ (g t).sets) :
  s ∈ (f.lift g).sets :=
le_principal_iff.mp $ show f.lift g ≤ principal s,
  from infi_le_of_le t $ infi_le_of_le ht $ le_principal_iff.mpr hs

lemma mem_lift_sets (hg : monotone g) {s : set β} :
  s ∈ (f.lift g).sets ↔ (∃t∈f.sets, s ∈ (g t).sets) :=
by rw [lift_sets_eq hg]; simp only [mem_Union]

lemma lift_le {f : filter α} {g : set α → filter β} {h : filter β} {s : set α}
  (hs : s ∈ f.sets) (hg : g s ≤ h) : f.lift g ≤ h :=
infi_le_of_le s $ infi_le_of_le hs $ hg

lemma le_lift {f : filter α} {g : set α → filter β} {h : filter β}
  (hh : ∀s∈f.sets, h ≤ g s) : h ≤ f.lift g :=
le_infi $ assume s, le_infi $ assume hs, hh s hs

lemma lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi2 $ assume hs, ⟨hf hs, hg s⟩

lemma lift_mono' (hg : ∀s∈f.sets, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, hg s hs

lemma map_lift_eq {m : β → γ} (hg : monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
have monotone (map m ∘ g),
  from monotone_comp hg monotone_map,
filter_eq $ set.ext $
  by simp [mem_lift_sets, hg, @mem_lift_sets _ _ f _ this]

lemma vmap_lift_eq {m : γ → β} (hg : monotone g) : vmap m (f.lift g) = f.lift (vmap m ∘ g) :=
have monotone (vmap m ∘ g),
  from monotone_comp hg monotone_vmap,
filter_eq $ set.ext begin
  simp only [hg, @mem_lift_sets _ _ f _ this, vmap, mem_lift_sets, mem_set_of_eq, exists_prop,
    function.comp_apply],
  exact λ s,
   ⟨λ ⟨b, ⟨a, ha, hb⟩, hs⟩, ⟨a, ha, b, hb, hs⟩,
    λ ⟨a, ha, b, hb, hs⟩, ⟨b, ⟨a, ha, hb⟩, hs⟩⟩
end

theorem vmap_lift_eq2 {m : β → α} {g : set β → filter γ} (hg : monotone g) :
  (vmap m f).lift g = f.lift (g ∘ preimage m) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs,
    infi_le_of_le (preimage m s) $ infi_le _ ⟨s, hs, subset.refl _⟩)
  (le_infi $ assume s, le_infi $ assume ⟨s', hs', (h_sub : preimage m s' ⊆ s)⟩,
    infi_le_of_le s' $ infi_le_of_le hs' $ hg h_sub)

lemma map_lift_eq2 {g : set β → filter γ} {m : α → β} (hg : monotone g) :
  (map m f).lift g = f.lift (g ∘ image m) :=
le_antisymm
  (infi_le_infi2 $ assume s, ⟨image m s,
    infi_le_infi2 $ assume hs, ⟨
      f.sets_of_superset hs $ assume a h, mem_image_of_mem _ h,
      le_refl _⟩⟩)
  (infi_le_infi2 $ assume t, ⟨preimage m t,
    infi_le_infi2 $ assume ht, ⟨ht,
      hg $ assume x, assume h : x ∈ m '' preimage m t,
        let ⟨y, hy, h_eq⟩ := h in
        show x ∈ t, from h_eq ▸ hy⟩⟩)

lemma lift_comm {g : filter β} {h : set α → set β → filter γ} :
  f.lift (λs, g.lift (h s)) = g.lift (λt, f.lift (λs, h s t)) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)

lemma lift_assoc {h : set β → filter γ} (hg : monotone g)  :
  (f.lift g).lift h = f.lift (λs, (g s).lift h) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le t $ infi_le _ $ (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
  (le_infi $ assume t, le_infi $ assume ht,
    let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht in
    infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le t $ infi_le _ h')

lemma lift_lift_same_le_lift {g : set α → set α → filter β} :
  f.lift (λs, f.lift (g s)) ≤ f.lift (λs, g s s) :=
le_infi $ assume s, le_infi $ assume hs, infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le s $ infi_le _ hs

lemma lift_lift_same_eq_lift {g : set α → set α → filter β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)):
  f.lift (λs, f.lift (g s)) = f.lift (λs, g s s) :=
le_antisymm
  lift_lift_same_le_lift
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le (s ∩ t) $
    infi_le_of_le (inter_mem_sets hs ht) $
    calc g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) : hg₂ (s ∩ t) (inter_subset_left _ _)
      ... ≤ g s t                        : hg₁ s (inter_subset_right _ _))

lemma lift_principal {s : set α} (hg : monotone g) :
  (principal s).lift g = g s :=
le_antisymm
  (infi_le_of_le s $ infi_le _ $ subset.refl _)
  (le_infi $ assume t, le_infi $ assume hi, hg hi)

theorem monotone_lift [preorder γ] {f : γ → filter α} {g : γ → set α → filter β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift (g c)) :=
assume a b h, lift_mono (hf h) (hg h)

lemma lift_neq_bot_iff (hm : monotone g) : (f.lift g ≠ ⊥) ↔ (∀s∈f.sets, g s ≠ ⊥) :=
classical.by_cases
  (assume hn : nonempty β,
    calc f.lift g ≠ ⊥ ↔ (⨅s : { s // s ∈ f.sets}, g s.val) ≠ ⊥ : by simp [filter.lift, infi_subtype]
      ... ↔ (∀s:{ s // s ∈ f.sets}, g s.val ≠ ⊥) :
        infi_neq_bot_iff_of_directed hn
          (assume ⟨a, ha⟩ ⟨b, hb⟩, ⟨⟨a ∩ b, inter_mem_sets ha hb⟩,
            hm $ inter_subset_left _ _, hm $ inter_subset_right _ _⟩)
      ... ↔ (∀s∈f.sets, g s ≠ ⊥) : ⟨assume h s hs, h ⟨s, hs⟩, assume h ⟨s, hs⟩, h s hs⟩)
  (assume hn : ¬ nonempty β,
    have h₁ : f.lift g = ⊥, from filter_eq_bot_of_not_nonempty hn,
    have h₂ : ∀s, g s = ⊥, from assume s, filter_eq_bot_of_not_nonempty hn,
    calc (f.lift g ≠ ⊥) ↔ false : by simp [h₁]
      ... ↔ (∀s∈f.sets, false) : ⟨false.elim, assume h, h univ univ_mem_sets⟩
      ... ↔ (∀s∈f.sets, g s ≠ ⊥) : by simp [h₂])

@[simp] lemma lift_const {f : filter α} {g : filter β} : f.lift (λx, g) = g :=
le_antisymm (lift_le univ_mem_sets $ le_refl g) (le_lift $ assume s hs, le_refl g)

@[simp] lemma lift_inf {f : filter α} {g h : set α → filter β} :
  f.lift (λx, g x ⊓ h x) = f.lift g ⊓ f.lift h :=
by simp [filter.lift, infi_inf_eq]

@[simp] lemma lift_principal2 {f : filter α} : f.lift principal = f :=
le_antisymm
  (assume s hs, mem_lift hs (mem_principal_self s))
  (le_infi $ assume s, le_infi $ assume hs, by simp [hs])

lemma lift_infi {f : ι → filter α} {g : set α → filter β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ⊓ g t = g (s ∩ t)) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
    have g_mono : monotone g,
      from assume s t h, le_of_inf_eq $ eq.trans hg $ congr_arg g $ inter_eq_self_of_subset_left h,
    have ∀t∈(infi f).sets, (⨅ (i : ι), filter.lift (f i) g) ≤ g t,
      from assume t ht, infi_sets_induct ht
        (let ⟨i⟩ := hι in infi_le_of_le i $ infi_le_of_le univ $ infi_le _ univ_mem_sets)
        (assume i s₁ s₂ hs₁ hs₂,
          @hg s₁ s₂ ▸ le_inf (infi_le_of_le i $ infi_le_of_le s₁ $ infi_le _ hs₁) hs₂)
        (assume s₁ s₂ hs₁ hs₂, le_trans hs₂ $ g_mono hs₁),
    begin
      rw [lift_sets_eq g_mono],
      simp only [mem_Union, exists_imp_distrib],
      exact assume t ht hs, this t ht hs
    end)

end lift

section lift'
/-- Specialize `lift` to functions `set α → set β`. This can be viewed as
  a generalization of `vmap`. -/
protected def lift' (f : filter α) (h : set α → set β) :=
f.lift (principal ∘ h)

variables {f f₁ f₂ : filter α} {h h₁ h₂ : set α → set β}

lemma mem_lift' {t : set α} (ht : t ∈ f.sets) : h t ∈ (f.lift' h).sets :=
le_principal_iff.mp $ show f.lift' h ≤ principal (h t),
  from infi_le_of_le t $ infi_le_of_le ht $ le_refl _

lemma mem_lift'_sets (hh : monotone h) {s : set β} : s ∈ (f.lift' h).sets ↔ (∃t∈f.sets, h t ⊆ s) :=
have monotone (principal ∘ h),
  from assume a b h, principal_mono.mpr $ hh h,
by simp [filter.lift', @mem_lift_sets α β f _ this]

lemma lift'_le {f : filter α} {g : set α → set β} {h : filter β} {s : set α}
  (hs : s ∈ f.sets) (hg : principal (g s) ≤ h) : f.lift' g ≤ h :=
lift_le hs hg

lemma lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
lift_mono hf $ assume s, principal_mono.mpr $ hh s

lemma lift'_mono' (hh : ∀s∈f.sets, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, principal_mono.mpr $ hh s hs

lemma lift'_cong (hh : ∀s∈f.sets, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
le_antisymm (lift'_mono' $ assume s hs, le_of_eq $ hh s hs) (lift'_mono' $ assume s hs, le_of_eq $ (hh s hs).symm)

lemma map_lift'_eq {m : β → γ} (hh : monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
calc map m (f.lift' h) = f.lift (map m ∘ principal ∘ h) :
    map_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (image m ∘ h) : by simp [function.comp, filter.lift']

lemma map_lift'_eq2 {g : set β → set γ} {m : α → β} (hg : monotone g) :
  (map m f).lift' g = f.lift' (g ∘ image m) :=
map_lift_eq2 $ monotone_comp hg monotone_principal

theorem vmap_lift'_eq {m : γ → β} (hh : monotone h) :
  vmap m (f.lift' h) = f.lift' (preimage m ∘ h) :=
calc vmap m (f.lift' h) = f.lift (vmap m ∘ principal ∘ h) :
    vmap_lift_eq $ monotone_comp hh monotone_principal
  ... = f.lift' (preimage m ∘ h) : by simp [function.comp, filter.lift']

theorem vmap_lift'_eq2 {m : β → α} {g : set β → set γ} (hg : monotone g) :
  (vmap m f).lift' g = f.lift' (g ∘ preimage m) :=
vmap_lift_eq2 $ monotone_comp hg monotone_principal

lemma lift'_principal {s : set α} (hh : monotone h) :
  (principal s).lift' h = principal (h s) :=
lift_principal $ monotone_comp hh monotone_principal

lemma principal_le_lift' {t : set β} (hh : ∀s∈f.sets, t ⊆ h s) :
  principal t ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, principal_mono.mpr (hh s hs)

theorem monotone_lift' [preorder γ] {f : γ → filter α} {g : γ → set α → set β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift' (g c)) :=
assume a b h, lift'_mono (hf h) (hg h)

lemma lift_lift'_assoc {g : set α → set β} {h : set β → filter γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift h = f.lift (λs, h (g s)) :=
calc (f.lift' g).lift h = f.lift (λs, (principal (g s)).lift h) :
    lift_assoc (monotone_comp hg monotone_principal)
  ... = f.lift (λs, h (g s)) : by simp [lift_principal, hh]

lemma lift'_lift'_assoc {g : set α → set β} {h : set β → set γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift' h = f.lift' (λs, h (g s)) :=
lift_lift'_assoc hg (monotone_comp hh monotone_principal)

lemma lift'_lift_assoc {g : set α → filter β} {h : set β → set γ}
  (hg : monotone g) : (f.lift g).lift' h = f.lift (λs, (g s).lift' h) :=
lift_assoc hg

lemma lift_lift'_same_le_lift' {g : set α → set α → set β} :
  f.lift (λs, f.lift' (g s)) ≤ f.lift' (λs, g s s) :=
lift_lift_same_le_lift

lemma lift_lift'_same_eq_lift' {g : set α → set α → set β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)):
  f.lift (λs, f.lift' (g s)) = f.lift' (λs, g s s) :=
lift_lift_same_eq_lift
  (assume s, monotone_comp monotone_id $ monotone_comp (hg₁ s) monotone_principal)
  (assume t, monotone_comp (hg₂ t) monotone_principal)

lemma lift'_inf_principal_eq {h : set α → set β} {s : set β} :
  f.lift' h ⊓ principal s = f.lift' (λt, h t ∩ s) :=
le_antisymm
  (le_infi $ assume t, le_infi $ assume ht,
    calc filter.lift' f h ⊓ principal s ≤ principal (h t) ⊓ principal s :
        inf_le_inf (infi_le_of_le t $ infi_le _ ht) (le_refl _)
      ... = _ : by simp)
  (le_inf
    (le_infi $ assume t, le_infi $ assume ht,
      infi_le_of_le t $ infi_le_of_le ht $ by simp; exact inter_subset_right _ _)
    (infi_le_of_le univ $ infi_le_of_le univ_mem_sets $ by simp; exact inter_subset_left _ _))

lemma lift'_neq_bot_iff (hh : monotone h) : (f.lift' h ≠ ⊥) ↔ (∀s∈f.sets, h s ≠ ∅) :=
calc (f.lift' h ≠ ⊥) ↔ (∀s∈f.sets, principal (h s) ≠ ⊥) :
    lift_neq_bot_iff (monotone_comp hh monotone_principal)
  ... ↔ (∀s∈f.sets, h s ≠ ∅) : by simp [principal_eq_bot_iff]

@[simp] lemma lift'_id {f : filter α} : f.lift' id = f :=
lift_principal2

lemma le_lift' {f : filter α} {h : set α → set β} {g : filter β}
  (h_le : ∀s∈f.sets, h s ∈ g.sets) : g ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, by simp [h_le]; exact h_le s hs

lemma lift_infi' {f : ι → filter α} {g : set α → filter β}
  (hι : nonempty ι) (hf : directed (≤) f) (hg : monotone g) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
  begin
    rw [lift_sets_eq hg],
    simp only [mem_Union, exists_imp_distrib, infi_sets_eq hf hι],
    exact assume t i ht hs, mem_infi_sets i $ mem_lift ht hs
  end)

lemma lift'_infi {f : ι → filter α} {g : set α → set β}
  (hι : nonempty ι) (hg : ∀{s t}, g s ∩ g t = g (s ∩ t)) : (infi f).lift' g = (⨅i, (f i).lift' g) :=
lift_infi hι $ by simp; apply assume s t, hg

theorem vmap_eq_lift' {f : filter β} {m : α → β} :
  vmap m f = f.lift' (preimage m) :=
filter_eq $ set.ext $ by simp [mem_lift'_sets, monotone_preimage, vmap]

end lift'

section prod
variables {s : set α} {t : set β} {f : filter α} {g : filter β}
/- The product filter cannot be defined using the monad structure on filters. For example:

  F := do {x <- seq, y <- top, return (x, y)}
  hence:
    s ∈ F  <->  ∃n, [n..∞] × univ ⊆ s

  G := do {y <- top, x <- seq, return (x, y)}
  hence:
    s ∈ G  <->  ∀i:ℕ, ∃n, [n..∞] × {i} ⊆ s

  Now ⋃i, [i..∞] × {i}  is in G but not in F.

  As product filter we want to have F as result.
-/

/-- Product of filters. This is the filter generated by cartesian products
  of elements of the component filters. -/
protected def prod (f : filter α) (g : filter β) : filter (α × β) :=
f.vmap prod.fst ⊓ g.vmap prod.snd

lemma prod_mem_prod {s : set α} {t : set β} {f : filter α} {g : filter β}
  (hs : s ∈ f.sets) (ht : t ∈ g.sets) : set.prod s t ∈ (filter.prod f g).sets :=
inter_mem_inf_sets (preimage_mem_vmap hs) (preimage_mem_vmap ht)

lemma mem_prod_iff {s : set (α×β)} {f : filter α} {g : filter β} :
  s ∈ (filter.prod f g).sets ↔ (∃t₁∈f.sets, ∃t₂∈g.sets, set.prod t₁ t₂ ⊆ s) :=
begin
  simp [filter.prod],
  split,
  exact assume ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, h⟩,
    ⟨s₁, hs₁, s₂, hs₂, subset.trans (inter_subset_inter hts₁ hts₂) h⟩,
  exact assume ⟨t₁, ht₁, t₂, ht₂, h⟩,
    ⟨prod.fst ⁻¹' t₁, ⟨t₁, ht₁, subset.refl _⟩, prod.snd ⁻¹' t₂, ⟨t₂, ht₂, subset.refl _⟩, h⟩
end

lemma tendsto_fst {f : filter α} {g : filter β} : tendsto prod.fst (filter.prod f g) f :=
tendsto_inf_left tendsto_vmap

lemma tendsto_snd {f : filter α} {g : filter β} : tendsto prod.snd (filter.prod f g) g :=
tendsto_inf_right tendsto_vmap

lemma tendsto.prod_mk {f : filter α} {g : filter β} {h : filter γ} {m₁ : α → β} {m₂ : α → γ}
  (h₁ : tendsto m₁ f g) (h₂ : tendsto m₂ f h) : tendsto (λx, (m₁ x, m₂ x)) f (filter.prod g h) :=
tendsto_inf.2 ⟨tendsto_vmap_iff.2 h₁, tendsto_vmap_iff.2 h₂⟩

lemma prod_infi_left {f : ι → filter α} {g : filter β} (i : ι) :
  filter.prod (⨅i, f i) g = (⨅i, filter.prod (f i) g) :=
by rw [filter.prod, vmap_infi, infi_inf i]; simp [filter.prod]

lemma prod_infi_right {f : filter α} {g : ι → filter β} (i : ι) :
  filter.prod f (⨅i, g i) = (⨅i, filter.prod f (g i)) :=
by rw [filter.prod, vmap_infi, inf_infi i]; simp [filter.prod]

lemma prod_mono {f₁ f₂ : filter α} {g₁ g₂ : filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
  filter.prod f₁ g₁ ≤ filter.prod f₂ g₂ :=
inf_le_inf (vmap_mono hf) (vmap_mono hg)

lemma prod_vmap_vmap_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
  filter.prod (vmap m₁ f₁) (vmap m₂ f₂) = vmap (λp:β₁×β₂, (m₁ p.1, m₂ p.2)) (filter.prod f₁ f₂) :=
by simp [filter.prod, vmap_vmap_comp]

lemma prod_comm' : filter.prod f g = vmap (prod.swap) (filter.prod g f) :=
by simp [filter.prod, vmap_vmap_comp, function.comp, inf_comm]

lemma prod_comm : filter.prod f g = map (λp:β×α, (p.2, p.1)) (filter.prod g f) :=
by rw [prod_comm', ← map_swap_eq_vmap_swap]; refl

lemma prod_map_map_eq {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
  filter.prod (map m₁ f₁) (map m₂ f₂) = map (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) (filter.prod f₁ f₂) :=
le_antisymm
  (assume s hs,
    let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs in
    filter.sets_of_superset _ (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) $
      calc set.prod (m₁ '' s₁) (m₂ '' s₂) = (λp:α₁×α₂, (m₁ p.1, m₂ p.2)) '' set.prod s₁ s₂ :
          set.prod_image_image_eq
        ... ⊆ _ : by rwa [image_subset_iff])
  ((tendsto_fst.comp (le_refl _)).prod_mk (tendsto_snd.comp (le_refl _)))

lemma prod_inf_prod {f₁ f₂ : filter α} {g₁ g₂ : filter β} :
  filter.prod f₁ g₁ ⊓ filter.prod f₂ g₂ = filter.prod (f₁ ⊓ f₂) (g₁ ⊓ g₂) :=
by simp only [filter.prod, vmap_inf, inf_comm, inf_assoc, lattice.inf_left_comm]

@[simp] lemma prod_bot1 {f : filter α} : filter.prod f (⊥ : filter β) = ⊥ := by simp [filter.prod]
@[simp] lemma prod_bot2 {g : filter β} : filter.prod (⊥ : filter α) g = ⊥ := by simp [filter.prod]

@[simp] lemma prod_principal_principal {s : set α} {t : set β} :
  filter.prod (principal s) (principal t) = principal (set.prod s t) :=
by simp [filter.prod, vmap_principal]; refl

lemma prod_def {f : filter α} {g : filter β} : f.prod g = (f.lift $ λs, g.lift' $ set.prod s) :=
have ∀(s:set α) (t : set β),
    principal (set.prod s t) = (principal s).vmap prod.fst ⊓ (principal t).vmap prod.snd,
  by simp; intros; refl,
begin
  simp [filter.lift', function.comp, this, -vmap_principal, lift_inf],
  rw [← vmap_lift_eq monotone_principal, ← vmap_lift_eq monotone_principal],
  simp [filter.prod]
end

lemma prod_same_eq : filter.prod f f = f.lift' (λt, set.prod t t) :=
by rw [prod_def];
from lift_lift'_same_eq_lift'
  (assume s, set.monotone_prod monotone_const monotone_id)
  (assume t, set.monotone_prod monotone_id monotone_const)

lemma mem_prod_same_iff {s : set (α×α)} :
  s ∈ (filter.prod f f).sets ↔ (∃t∈f.sets, set.prod t t ⊆ s) :=
by rw [prod_same_eq, mem_lift'_sets]; exact set.monotone_prod monotone_id monotone_id

lemma prod_lift_lift {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → filter β₁} {g₂ : set α₂ → filter β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  filter.prod (f₁.lift g₁) (f₂.lift g₂) = f₁.lift (λs, f₂.lift (λt, filter.prod (g₁ s) (g₂ t))) :=
begin
  simp only [prod_def],
  rw [lift_assoc],
  apply congr_arg, funext x,
  rw [lift_comm],
  apply congr_arg, funext y,
  rw [lift'_lift_assoc],
  exact hg₂,
  exact hg₁
end

lemma prod_lift'_lift' {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → set β₁} {g₂ : set α₂ → set β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  filter.prod (f₁.lift' g₁) (f₂.lift' g₂) = f₁.lift (λs, f₂.lift' (λt, set.prod (g₁ s) (g₂ t))) :=
begin
  rw [prod_def, lift_lift'_assoc],
  apply congr_arg, funext x,
  rw [lift'_lift'_assoc],
  exact hg₂,
  exact set.monotone_prod monotone_const monotone_id,
  exact hg₁,
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume x, set.monotone_prod monotone_id monotone_const)
end

lemma prod_neq_bot {f : filter α} {g : filter β} : filter.prod f g ≠ ⊥ ↔ (f ≠ ⊥ ∧ g ≠ ⊥) :=
calc filter.prod f g ≠ ⊥ ↔ (∀s∈f.sets, g.lift' (set.prod s) ≠ ⊥) :
  begin
    rw [prod_def, lift_neq_bot_iff],
    exact (monotone_lift' monotone_const $ monotone_lam $ assume s, set.monotone_prod monotone_id monotone_const)
  end
  ... ↔ (∀s∈f.sets, ∀t∈g.sets, s ≠ ∅ ∧ t ≠ ∅) :
  begin
    apply forall_congr, intro s,
    apply forall_congr, intro hs,
    rw [lift'_neq_bot_iff],
    apply forall_congr, intro t,
    apply forall_congr, intro ht,
    rw [set.prod_neq_empty_iff],
    exact set.monotone_prod monotone_const monotone_id
  end
  ... ↔ (∀s∈f.sets, s ≠ ∅) ∧ (∀t∈g.sets, t ≠ ∅) :
    ⟨assume h, ⟨assume s hs, (h s hs univ univ_mem_sets).left,
        assume t ht, (h univ univ_mem_sets t ht).right⟩,
      assume ⟨h₁, h₂⟩ s hs t ht, ⟨h₁ s hs, h₂ t ht⟩⟩
  ... ↔ _ : by simp only  [forall_sets_neq_empty_iff_neq_bot]

lemma tendsto_prod_iff {f : α × β → γ} {x : filter α} {y : filter β} {z : filter γ} :
  filter.tendsto f (filter.prod x y) z ↔
  ∀ W ∈ z.sets, ∃ U ∈ x.sets,  ∃ V ∈ y.sets, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W :=
by simp [tendsto_def, mem_prod_iff, set.prod_sub_preimage_iff]

lemma tendsto_prod_self_iff {f : α × α → β} {x : filter α} {y : filter β} :
  filter.tendsto f (filter.prod x x) y ↔
  ∀ W ∈ y.sets, ∃ U ∈ x.sets, ∀ (x x' : α), x ∈ U → x' ∈ U → f (x, x') ∈ W :=
by simp [tendsto_def, mem_prod_same_iff, set.prod_sub_preimage_iff]

end prod

/- at_top and at_bot -/

/-- `at_top` is the filter representing the limit `→ ∞` on an ordered set.
  It is generated by the collection of up-sets `{b | a ≤ b}`.
  (The preorder need not have a top element for this to be well defined,
  and indeed is trivial when a top element exists.) -/
def at_top [preorder α] : filter α := ⨅ a, principal {b | a ≤ b}

/-- `at_bot` is the filter representing the limit `→ -∞` on an ordered set.
  It is generated by the collection of down-sets `{b | b ≤ a}`.
  (The preorder need not have a bottom element for this to be well defined,
  and indeed is trivial when a bottom element exists.) -/
def at_bot [preorder α] : filter α := ⨅ a, principal {b | b ≤ a}

lemma mem_at_top [preorder α] (a : α) : {b : α | a ≤ b} ∈ (@at_top α _).sets :=
mem_infi_sets a $ subset.refl _

@[simp] lemma at_top_ne_bot [inhabited α] [semilattice_sup α] : (at_top : filter α) ≠ ⊥ :=
infi_neq_bot_of_directed (by apply_instance)
  (assume a b, ⟨a ⊔ b, by simp {contextual := tt}⟩)
  (assume a, by simp [principal_eq_bot_iff]; exact ne_empty_of_mem (le_refl a))

@[simp] lemma mem_at_top_sets [inhabited α] [semilattice_sup α] {s : set α} :
  s ∈ (at_top : filter α).sets ↔ ∃a:α, ∀b≥a, b ∈ s :=
iff.intro
  (assume h, infi_sets_induct h ⟨default α, by simp⟩
    (assume a s₁ s₂ ha ⟨b, hb⟩, ⟨a ⊔ b,
      assume c hc, ⟨ha $ le_trans le_sup_left hc, hb _ $ le_trans le_sup_right hc⟩⟩)
    (assume s₁ s₂ h ⟨a, ha⟩, ⟨a, assume b hb, h $ ha _ hb⟩))
  (assume ⟨a, h⟩, mem_infi_sets a $ assume x, h x)

lemma map_at_top_eq [inhabited α] [semilattice_sup α] {f : α → β} :
  at_top.map f = (⨅a, principal $ f '' {a' | a ≤ a'}) :=
calc map f (⨅a, principal {a' | a ≤ a'}) = (⨅a, map f $ principal {a' | a ≤ a'}) :
    map_infi_eq (assume a b, ⟨a ⊔ b, by simp {contextual := tt}⟩) ⟨default α⟩
  ... = (⨅a, principal $ f '' {a' | a ≤ a'}) : by simp

lemma tendsto_finset_image_at_top_at_top {i : β → γ} {j : γ → β} (h : ∀x, j (i x) = x) :
  tendsto (λs:finset γ, s.image j) at_top at_top :=
tendsto_infi.2 $ assume s, tendsto_infi' (s.image i) $ tendsto_principal_principal.2 $
  assume t (ht : s.image i ⊆ t),
  calc s = (s.image i).image j :
      by simp [finset.image_image, (∘), h]; exact finset.image_id.symm
    ... ⊆  t.image j : finset.image_subset_image ht


/- ultrafilter -/

section ultrafilter
open zorn

variables {f g : filter α}

/-- An ultrafilter is a minimal (maximal in the set order) proper filter. -/
def ultrafilter (f : filter α) := f ≠ ⊥ ∧ ∀g, g ≠ ⊥ → g ≤ f → f ≤ g

lemma ultrafilter_pure {a : α} : ultrafilter (pure a) :=
⟨pure_neq_bot,
  assume g hg ha,
  have {a} ∈ g.sets, begin simp at ha, assumption end,
  show ∀s∈g.sets, {a} ⊆ s, from classical.by_contradiction $
  begin
    simp only [classical.not_forall, not_imp, exists_imp_distrib, singleton_subset_iff],
    exact assume s ⟨hs, hna⟩,
      have {a} ∩ s ∈ g.sets, from inter_mem_sets ‹{a} ∈ g.sets› hs,
      have ∅ ∈ g.sets, from mem_sets_of_superset this $
        assume x ⟨hxa, hxs⟩, begin simp at hxa; simp [hxa] at hxs, exact hna hxs end,
      have g = ⊥, from empty_in_sets_eq_bot.mp this,
      hg this
  end⟩

lemma ultrafilter_unique (hg : ultrafilter g) (hf : f ≠ ⊥) (h : f ≤ g) : f = g :=
le_antisymm h (hg.right _ hf h)

lemma exists_ultrafilter (h : f ≠ ⊥) : ∃u, u ≤ f ∧ ultrafilter u :=
let
  τ                := {f' // f' ≠ ⊥ ∧ f' ≤ f},
  r : τ → τ → Prop := λt₁ t₂, t₂.val ≤ t₁.val,
  ⟨a, ha⟩          := inhabited_of_mem_sets h univ_mem_sets,
  top : τ          := ⟨f, h, le_refl f⟩,
  sup : Π(c:set τ), chain r c → τ :=
    λc hc, ⟨⨅a:{a:τ // a ∈ insert top c}, a.val.val,
      infi_neq_bot_of_directed ⟨a⟩
        (directed_of_chain $ chain_insert hc $ assume ⟨b, _, hb⟩ _ _, or.inl hb)
        (assume ⟨⟨a, ha, _⟩, _⟩, ha),
      infi_le_of_le ⟨top, mem_insert _ _⟩ (le_refl _)⟩
in
have ∀c (hc: chain r c) a (ha : a ∈ c), r a (sup c hc),
  from assume c hc a ha, infi_le_of_le ⟨a, mem_insert_of_mem _ ha⟩ (le_refl _),
have (∃ (u : τ), ∀ (a : τ), r u a → r a u),
  from zorn (assume c hc, ⟨sup c hc, this c hc⟩) (assume f₁ f₂ f₃ h₁ h₂, le_trans h₂ h₁),
let ⟨uτ, hmin⟩ := this in
⟨uτ.val, uτ.property.right, uτ.property.left, assume g hg₁ hg₂,
  hmin ⟨g, hg₁, le_trans hg₂ uτ.property.right⟩ hg₂⟩

lemma le_of_ultrafilter {g : filter α} (hf : ultrafilter f) (h : f ⊓ g ≠ ⊥) :
  f ≤ g :=
le_of_inf_eq $ ultrafilter_unique hf h inf_le_left

lemma mem_or_compl_mem_of_ultrafilter (hf : ultrafilter f) (s : set α) :
  s ∈ f.sets ∨ - s ∈ f.sets :=
classical.or_iff_not_imp_right.2 $ assume : - s ∉ f.sets,
  have f ≤ principal s,
    from le_of_ultrafilter hf $ assume h, this $ mem_sets_of_neq_bot $ by simp [*],
  by simp at this; assumption

lemma mem_or_mem_of_ultrafilter {s t : set α} (hf : ultrafilter f) (h : s ∪ t ∈ f.sets) :
  s ∈ f.sets ∨ t ∈ f.sets :=
(mem_or_compl_mem_of_ultrafilter hf s).imp_right
  (assume : -s ∈ f.sets, by filter_upwards [this, h] assume x hnx hx, hx.resolve_left hnx)

lemma mem_of_finite_sUnion_ultrafilter {s : set (set α)} (hf : ultrafilter f) (hs : finite s)
  : ⋃₀ s ∈ f.sets → ∃t∈s, t ∈ f.sets :=
finite.induction_on hs (by simp [empty_in_sets_eq_bot, hf.left]) $
λ t s' ht' hs' ih, by simp; exact
assume h, (mem_or_mem_of_ultrafilter hf h).elim
  (assume : t ∈ f.sets, ⟨t, or.inl rfl, this⟩)
  (assume h, let ⟨t, hts', ht⟩ := ih h in ⟨t, or.inr hts', ht⟩)

lemma mem_of_finite_Union_ultrafilter {is : set β} {s : β → set α}
  (hf : ultrafilter f) (his : finite is) (h : (⋃i∈is, s i) ∈ f.sets) : ∃i∈is, s i ∈ f.sets :=
have his : finite (image s is), from finite_image s his,
have h : (⋃₀ image s is) ∈ f.sets, from by simp [sUnion_image]; assumption,
let ⟨t, ⟨i, hi, h_eq⟩, (ht : t ∈ f.sets)⟩ := mem_of_finite_sUnion_ultrafilter hf his h in
⟨i, hi, h_eq.symm ▸ ht⟩

lemma ultrafilter_of_split {f : filter α} (hf : f ≠ ⊥) (h : ∀s, s ∈ f.sets ∨ - s ∈ f.sets) :
  ultrafilter f :=
⟨hf, assume g hg g_le s hs, (h s).elim id $
  assume : - s ∈ f.sets,
  have s ∩ -s ∈ g.sets, from inter_mem_sets hs (g_le this),
  by simp [empty_in_sets_eq_bot, hg] at this; contradiction⟩

lemma ultrafilter_map {f : filter α} {m : α → β} (h : ultrafilter f) : ultrafilter (map m f) :=
ultrafilter_of_split (by simp [map_eq_bot_iff, h.left]) $
  assume s, show preimage m s ∈ f.sets ∨ - preimage m s ∈ f.sets,
    from mem_or_compl_mem_of_ultrafilter h (preimage m s)

/-- Construct an ultrafilter extending a given filter.
  The ultrafilter lemma is the assertion that such a filter exists;
  we use the axiom of choice to pick one. -/
noncomputable def ultrafilter_of (f : filter α) : filter α :=
if h : f = ⊥ then ⊥ else classical.epsilon (λu, u ≤ f ∧ ultrafilter u)

lemma ultrafilter_of_spec (h : f ≠ ⊥) : ultrafilter_of f ≤ f ∧ ultrafilter (ultrafilter_of f) :=
begin
  have h' := classical.epsilon_spec (exists_ultrafilter h),
  simp [ultrafilter_of, dif_neg, h],
  simp at h',
  assumption
end

lemma ultrafilter_of_le : ultrafilter_of f ≤ f :=
if h : f = ⊥ then by simp [ultrafilter_of, dif_pos, h]; exact le_refl _
  else (ultrafilter_of_spec h).left

lemma ultrafilter_ultrafilter_of (h : f ≠ ⊥) : ultrafilter (ultrafilter_of f) :=
(ultrafilter_of_spec h).right

lemma ultrafilter_of_ultrafilter (h : ultrafilter f) : ultrafilter_of f = f :=
ultrafilter_unique h (ultrafilter_ultrafilter_of h.left).left ultrafilter_of_le

end ultrafilter

end filter
