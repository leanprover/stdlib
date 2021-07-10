/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import set_theory.cardinal

/-!
# Ordinals

Ordinals are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an ordinal is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.

## Main definitions

* `initial_seg r s`: type of order embeddings of `r` into `s` for which the range is an initial
  segment (i.e., if `b` belongs to the range, then any `b' < b` also belongs to the range).
  It is denoted by `r ≼i s`.
* `principal_seg r s`: Type of order embeddings of `r` into `s` for which the range is a principal
  segment, i.e., an interval of the form `(-∞, top)` for some element `top`. It is denoted by
  `r ≺i s`.

* `ordinal`: the type of ordinals (in a given universe)
* `ordinal.type r`: given a well-founded order `r`, this is the corresponding ordinal
* `ordinal.typein r a`: given a well-founded order `r` on a type `α`, and `a : α`, the ordinal
  corresponding to all elements smaller than `a`.
* `enum r o h`: given a well-order `r` on a type `α`, and an ordinal `o` strictly smaller than
  the ordinal corresponding to `r` (this is the assumption `h`), returns the `o`-th element of `α`.
  In other words, the elements of `α` can be enumerated using ordinals up to `type r`.
* `ordinal.card o`: the cardinality of an ordinal `o`.
* `ordinal.lift` lifts an ordinal in universe `u` to an ordinal in universe `max u v`.
  For a version registering additionally that this is an initial segment embedding, see
  `ordinal.lift.initial_seg`.
  For a version regiserting that it is a principal segment embedding if `u < v`, see
  `ordinal.lift.principal_seg`.
* `ordinal.omega` is the first infinite ordinal. It is the order type of `ℕ`.

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. The main properties of addition
  (and the other operations on ordinals) are stated and proved in `ordinal_arithmetic.lean`. Here,
  we only introduce it and prove its basic properties to deduce the fact that the order on ordinals
  is total (and well founded).
* `succ o` is the successor of the ordinal `o`.

* `ordinal.min`: the minimal element of a nonempty indexed family of ordinals
* `ordinal.omin` : the minimal element of a nonempty set of ordinals

* `cardinal.ord c`: when `c` is a cardinal, `ord c` is the smallest ordinal with this cardinality.
  It is the canonical way to represent a cardinal with an ordinal.

## Notations
* `r ≼i s`: the type of initial segment embeddings of `r` into `s`.
* `r ≺i s`: the type of principal segment embeddings of `r` into `s`.
* `ω` is a notation for the first infinite ordinal in the locale `ordinal`.
-/

noncomputable theory

open function cardinal set equiv
open_locale classical cardinal

universes u v w
variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-!
### Initial segments

Order embeddings whose range is an initial segment of `s` (i.e., if `b` belongs to the range, then
any `b' < b` also belongs to the range). The type of these embeddings from `r` to `s` is called
`initial_seg r s`, and denoted by `r ≼i s`.
-/

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≼i s` is an order
embedding whose range is an initial segment. That is, whenever `b < f a` in `β` then `b` is in the
range of `f`. -/
@[nolint has_inhabited_instance]
structure initial_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s :=
(init : ∀ a b, s b (to_rel_embedding a) → ∃ a', to_rel_embedding a' = b)

local infix ` ≼i `:25 := initial_seg

namespace initial_seg

instance : has_coe (r ≼i s) (r ↪r s) := ⟨initial_seg.to_rel_embedding⟩
instance : has_coe_to_fun (r ≼i s) := ⟨λ _, α → β, λ f x, (f : r ↪r s) x⟩

@[simp] theorem coe_fn_mk (f : r ↪r s) (o) :
  (@initial_seg.mk _ _ r s f o : α → β) = f := rfl

@[simp] theorem coe_fn_to_rel_embedding (f : r ≼i s) : (f.to_rel_embedding : α → β) = f := rfl

@[simp] theorem coe_coe_fn (f : r ≼i s) : ((f : r ↪r s) : α → β) = f := rfl

theorem init' (f : r ≼i s) {a : α} {b : β} : s b (f a) → ∃ a', f a' = b :=
f.init _ _

theorem init_iff (f : r ≼i s) {a : α} {b : β} : s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
⟨λ h, let ⟨a', e⟩ := f.init' h in ⟨a', e, (f : r ↪r s).map_rel_iff.1 (e.symm ▸ h)⟩,
 λ ⟨a', e, h⟩, e ▸ (f : r ↪r s).map_rel_iff.2 h⟩

/-- An order isomorphism is an initial segment -/
def of_iso (f : r ≃r s) : r ≼i s :=
⟨f, λ a b h, ⟨f.symm b, rel_iso.apply_symm_apply f _⟩⟩

/-- The identity function shows that `≼i` is reflexive -/
@[refl] protected def refl (r : α → α → Prop) : r ≼i r :=
⟨rel_embedding.refl _, λ a b h, ⟨_, rfl⟩⟩

/-- Composition of functions shows that `≼i` is transitive -/
@[trans] protected def trans (f : r ≼i s) (g : s ≼i t) : r ≼i t :=
⟨f.1.trans g.1, λ a c h, begin
  simp at h ⊢,
  rcases g.2 _ _ h with ⟨b, rfl⟩, have h := g.1.map_rel_iff.1 h,
  rcases f.2 _ _ h with ⟨a', rfl⟩, exact ⟨a', rfl⟩
end⟩

@[simp] theorem refl_apply (x : α) : initial_seg.refl r x = x := rfl

@[simp] theorem trans_apply (f : r ≼i s) (g : s ≼i t) (a : α) : (f.trans g) a = g (f a) := rfl

theorem unique_of_extensional [is_extensional β s] :
  well_founded r → subsingleton (r ≼i s) | ⟨h⟩ :=
⟨λ f g, begin
  suffices : (f : α → β) = g, { cases f, cases g,
    congr, exact rel_embedding.coe_fn_inj this },
  funext a, have := h a, induction this with a H IH,
  refine @is_extensional.ext _ s _ _ _ (λ x, ⟨λ h, _, λ h, _⟩),
  { rcases f.init_iff.1 h with ⟨y, rfl, h'⟩,
    rw IH _ h', exact (g : r ↪r s).map_rel_iff.2 h' },
  { rcases g.init_iff.1 h with ⟨y, rfl, h'⟩,
    rw ← IH _ h', exact (f : r ↪r s).map_rel_iff.2 h' }
end⟩

instance [is_well_order β s] : subsingleton (r ≼i s) :=
⟨λ a, @subsingleton.elim _ (unique_of_extensional
  (@rel_embedding.well_founded _ _ r s a is_well_order.wf)) a⟩

protected theorem eq [is_well_order β s] (f g : r ≼i s) (a) : f a = g a :=
by rw subsingleton.elim f g

theorem antisymm.aux [is_well_order α r] (f : r ≼i s) (g : s ≼i r) : left_inverse g f :=
initial_seg.eq (f.trans g) (initial_seg.refl _)

/-- If we have order embeddings between `α` and `β` whose images are initial segments, and `β`
is a well-order then `α` and `β` are order-isomorphic. -/
def antisymm [is_well_order β s] (f : r ≼i s) (g : s ≼i r) : r ≃r s :=
by haveI := f.to_rel_embedding.is_well_order; exact
⟨⟨f, g, antisymm.aux f g, antisymm.aux g f⟩, f.map_rel_iff'⟩

@[simp] theorem antisymm_to_fun [is_well_order β s]
  (f : r ≼i s) (g : s ≼i r) : (antisymm f g : α → β) = f := rfl

@[simp] theorem antisymm_symm [is_well_order α r] [is_well_order β s]
  (f : r ≼i s) (g : s ≼i r) : (antisymm f g).symm = antisymm g f :=
rel_iso.coe_fn_injective rfl

theorem eq_or_principal [is_well_order β s] (f : r ≼i s) :
  surjective f ∨ ∃ b, ∀ x, s x b ↔ ∃ y, f y = x :=
or_iff_not_imp_right.2 $ λ h b,
acc.rec_on (is_well_order.wf.apply b : acc s b) $ λ x H IH,
not_forall_not.1 $ λ hn,
h ⟨x, λ y, ⟨(IH _), λ ⟨a, e⟩, by rw ← e; exact
  (trichotomous _ _).resolve_right
  (not_or (hn a) (λ hl, not_exists.2 hn (f.init' hl)))⟩⟩

/-- Restrict the codomain of an initial segment -/
def cod_restrict (p : set β) (f : r ≼i s) (H : ∀ a, f a ∈ p) : r ≼i subrel s p :=
⟨rel_embedding.cod_restrict p f H, λ a ⟨b, m⟩ (h : s b (f a)),
  let ⟨a', e⟩ := f.init' h in ⟨a', by clear _let_match; subst e; refl⟩⟩

@[simp] theorem cod_restrict_apply (p) (f : r ≼i s) (H a) : cod_restrict p f H a = ⟨f a, H a⟩ := rfl

/-- Initial segment embedding of an order `r` into the disjoint union of `r` and `s`. -/
def le_add (r : α → α → Prop) (s : β → β → Prop) : r ≼i sum.lex r s :=
⟨⟨⟨sum.inl, λ _ _, sum.inl.inj⟩, λ a b, sum.lex_inl_inl⟩,
  λ a b, by cases b; [exact λ _, ⟨_, rfl⟩, exact false.elim ∘ sum.lex_inr_inl]⟩

@[simp] theorem le_add_apply (r : α → α → Prop) (s : β → β → Prop)
  (a) : le_add r s a = sum.inl a := rfl

end initial_seg

/-!
### Principal segments

Order embeddings whose range is a principal segment of `s` (i.e., an interval of the form
`(-∞, top)` for some element `top` of `β`). The type of these embeddings from `r` to `s` is called
`principal_seg r s`, and denoted by `r ≺i s`. Principal segments are in particular initial
segments.
-/

/-- If `r` is a relation on `α` and `s` in a relation on `β`, then `f : r ≺i s` is an order
embedding whose range is an open interval `(-∞, top)` for some element `top` of `β`. Such order
embeddings are called principal segments -/
@[nolint has_inhabited_instance]
structure principal_seg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s :=
(top : β)
(down : ∀ b, s b top ↔ ∃ a, to_rel_embedding a = b)

local infix ` ≺i `:25 := principal_seg

namespace principal_seg

instance : has_coe (r ≺i s) (r ↪r s) := ⟨principal_seg.to_rel_embedding⟩
instance : has_coe_to_fun (r ≺i s) := ⟨λ _, α → β, λ f, f⟩

@[simp] theorem coe_fn_mk (f : r ↪r s) (t o) :
  (@principal_seg.mk _ _ r s f t o : α → β) = f := rfl

@[simp] theorem coe_fn_to_rel_embedding (f : r ≺i s) : (f.to_rel_embedding : α → β) = f := rfl

@[simp] theorem coe_coe_fn (f : r ≺i s) : ((f : r ↪r s) : α → β) = f := rfl

theorem down' (f : r ≺i s) {b : β} : s b f.top ↔ ∃ a, f a = b :=
f.down _

theorem lt_top (f : r ≺i s) (a : α) : s (f a) f.top :=
f.down'.2 ⟨_, rfl⟩

theorem init [is_trans β s] (f : r ≺i s) {a : α} {b : β} (h : s b (f a)) : ∃ a', f a' = b :=
f.down'.1 $ trans h $ f.lt_top _

/-- A principal segment is in particular an initial segment. -/
instance has_coe_initial_seg [is_trans β s] : has_coe (r ≺i s) (r ≼i s) :=
⟨λ f, ⟨f.to_rel_embedding, λ a b, f.init⟩⟩

theorem coe_coe_fn' [is_trans β s] (f : r ≺i s) : ((f : r ≼i s) : α → β) = f := rfl

theorem init_iff [is_trans β s] (f : r ≺i s) {a : α} {b : β} :
  s b (f a) ↔ ∃ a', f a' = b ∧ r a' a :=
@initial_seg.init_iff α β r s f a b

theorem irrefl (r : α → α → Prop) [is_well_order α r] (f : r ≺i r) : false :=
begin
  have := f.lt_top f.top,
  rw [show f f.top = f.top, from
      initial_seg.eq ↑f (initial_seg.refl r) f.top] at this,
  exact irrefl _ this
end

/-- Composition of a principal segment with an initial segment, as a principal segment -/
def lt_le (f : r ≺i s) (g : s ≼i t) : r ≺i t :=
⟨@rel_embedding.trans _ _ _ r s t f g, g f.top, λ a,
 by simp only [g.init_iff, f.down', exists_and_distrib_left.symm,
   exists_swap, rel_embedding.trans_apply, exists_eq_right']; refl⟩

@[simp] theorem lt_le_apply (f : r ≺i s) (g : s ≼i t) (a : α) : (f.lt_le g) a = g (f a) :=
rel_embedding.trans_apply _ _ _

@[simp] theorem lt_le_top (f : r ≺i s) (g : s ≼i t) : (f.lt_le g).top = g f.top := rfl

/-- Composition of two principal segments as a principal segment -/
@[trans] protected def trans [is_trans γ t] (f : r ≺i s) (g : s ≺i t) : r ≺i t :=
lt_le f g

@[simp] theorem trans_apply [is_trans γ t] (f : r ≺i s) (g : s ≺i t) (a : α) :
  (f.trans g) a = g (f a) :=
lt_le_apply _ _ _

@[simp] theorem trans_top [is_trans γ t] (f : r ≺i s) (g : s ≺i t) :
  (f.trans g).top = g f.top := rfl

/-- Composition of an order isomorphism with a principal segment, as a principal segment -/
def equiv_lt (f : r ≃r s) (g : s ≺i t) : r ≺i t :=
⟨@rel_embedding.trans _ _ _ r s t f g, g.top, λ c,
 suffices (∃ (a : β), g a = c) ↔ ∃ (a : α), g (f a) = c, by simpa [g.down],
 ⟨λ ⟨b, h⟩, ⟨f.symm b, by simp only [h, rel_iso.apply_symm_apply, rel_iso.coe_coe_fn]⟩,
  λ ⟨a, h⟩, ⟨f a, h⟩⟩⟩

/-- Composition of a principal segment with an order isomorphism, as a principal segment -/
def lt_equiv {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  (f : principal_seg r s) (g : s ≃r t) : principal_seg r t :=
⟨@rel_embedding.trans _ _ _ r s t f g, g f.top,
  begin
    intro x,
    rw [← g.apply_symm_apply x, g.map_rel_iff, f.down', exists_congr],
    intro y, exact ⟨congr_arg g, λ h, g.to_equiv.bijective.1 h⟩
  end⟩

@[simp] theorem equiv_lt_apply (f : r ≃r s) (g : s ≺i t) (a : α) : (equiv_lt f g) a = g (f a) :=
rel_embedding.trans_apply _ _ _

@[simp] theorem equiv_lt_top (f : r ≃r s) (g : s ≺i t) : (equiv_lt f g).top = g.top := rfl

/-- Given a well order `s`, there is a most one principal segment embedding of `r` into `s`. -/
instance [is_well_order β s] : subsingleton (r ≺i s) :=
⟨λ f g, begin
  have ef : (f : α → β) = g,
  { show ((f : r ≼i s) : α → β) = g,
    rw @subsingleton.elim _ _ (f : r ≼i s) g, refl },
  have et : f.top = g.top,
  { refine @is_extensional.ext _ s _ _ _ (λ x, _),
    simp only [f.down, g.down, ef, coe_fn_to_rel_embedding] },
  cases f, cases g,
  have := rel_embedding.coe_fn_inj ef; congr'
end⟩

theorem top_eq [is_well_order γ t]
  (e : r ≃r s) (f : r ≺i t) (g : s ≺i t) : f.top = g.top :=
by rw subsingleton.elim f (principal_seg.equiv_lt e g); refl

lemma top_lt_top {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}
  [is_well_order γ t]
  (f : principal_seg r s) (g : principal_seg s t) (h : principal_seg r t) : t h.top g.top :=
by { rw [subsingleton.elim h (f.trans g)], apply principal_seg.lt_top }

/-- Any element of a well order yields a principal segment -/
def of_element {α : Type*} (r : α → α → Prop) (a : α) : subrel r {b | r b a} ≺i r :=
⟨subrel.rel_embedding _ _, a, λ b,
  ⟨λ h, ⟨⟨_, h⟩, rfl⟩, λ ⟨⟨_, h⟩, rfl⟩, h⟩⟩

@[simp] theorem of_element_apply {α : Type*} (r : α → α → Prop) (a : α) (b) :
  of_element r a b = b.1 := rfl

@[simp] theorem of_element_top {α : Type*} (r : α → α → Prop) (a : α) :
  (of_element r a).top = a := rfl

/-- Restrict the codomain of a principal segment -/
def cod_restrict (p : set β) (f : r ≺i s)
  (H : ∀ a, f a ∈ p) (H₂ : f.top ∈ p) : r ≺i subrel s p :=
⟨rel_embedding.cod_restrict p f H, ⟨f.top, H₂⟩, λ ⟨b, h⟩,
  f.down'.trans $ exists_congr $ λ a,
  show (⟨f a, H a⟩ : p).1 = _ ↔ _, from ⟨subtype.eq, congr_arg _⟩⟩

@[simp]
theorem cod_restrict_apply (p) (f : r ≺i s) (H H₂ a) : cod_restrict p f H H₂ a = ⟨f a, H a⟩ := rfl

@[simp]
theorem cod_restrict_top (p) (f : r ≺i s) (H H₂) : (cod_restrict p f H H₂).top = ⟨f.top, H₂⟩ := rfl

end principal_seg

/-! ### Properties of initial and principal segments -/

/-- To an initial segment taking values in a well order, one can associate either a principal
segment (if the range is not everything, hence one can take as top the minimum of the complement
of the range) or an order isomorphism (if the range is everything). -/
def initial_seg.lt_or_eq [is_well_order β s] (f : r ≼i s) :
  (r ≺i s) ⊕ (r ≃r s) :=
if h : surjective f then sum.inr (rel_iso.of_surjective f h) else
have h' : _, from (initial_seg.eq_or_principal f).resolve_left h,
sum.inl ⟨f, classical.some h', classical.some_spec h'⟩

theorem initial_seg.lt_or_eq_apply_left [is_well_order β s]
  (f : r ≼i s) (g : r ≺i s) (a : α) : g a = f a :=
@initial_seg.eq α β r s _ g f a

theorem initial_seg.lt_or_eq_apply_right [is_well_order β s]
  (f : r ≼i s) (g : r ≃r s) (a : α) : g a = f a :=
initial_seg.eq (initial_seg.of_iso g) f a

/-- Composition of an initial segment taking values in a well order and a principal segment. -/
def initial_seg.le_lt [is_well_order β s] [is_trans γ t] (f : r ≼i s) (g : s ≺i t) : r ≺i t :=
match f.lt_or_eq with
| sum.inl f' := f'.trans g
| sum.inr f' := principal_seg.equiv_lt f' g
end

@[simp] theorem initial_seg.le_lt_apply [is_well_order β s] [is_trans γ t]
  (f : r ≼i s) (g : s ≺i t) (a : α) : (f.le_lt g) a = g (f a) :=
begin
  delta initial_seg.le_lt, cases h : f.lt_or_eq with f' f',
  { simp only [principal_seg.trans_apply, f.lt_or_eq_apply_left] },
  { simp only [principal_seg.equiv_lt_apply, f.lt_or_eq_apply_right] }
end

namespace rel_embedding

/-- Given an order embedding into a well order, collapse the order embedding by filling the
gaps, to obtain an initial segment. Here, we construct the collapsed order embedding pointwise,
but the proof of the fact that it is an initial segment will be given in `collapse`. -/
def collapse_F [is_well_order β s] (f : r ↪r s) : Π a, {b // ¬ s (f a) b} :=
(rel_embedding.well_founded f $ is_well_order.wf).fix $ λ a IH, begin
  let S := {b | ∀ a h, s (IH a h).1 b},
  have : f a ∈ S, from λ a' h, ((trichotomous _ _)
    .resolve_left $ λ h', (IH a' h).2 $ trans (f.map_rel_iff.2 h) h')
    .resolve_left $ λ h', (IH a' h).2 $ h' ▸ f.map_rel_iff.2 h,
  exact ⟨is_well_order.wf.min S ⟨_, this⟩,
   is_well_order.wf.not_lt_min _ _ this⟩
end

theorem collapse_F.lt [is_well_order β s] (f : r ↪r s) {a : α}
   : ∀ {a'}, r a' a → s (collapse_F f a').1 (collapse_F f a).1 :=
show (collapse_F f a).1 ∈ {b | ∀ a' (h : r a' a), s (collapse_F f a').1 b}, begin
  unfold collapse_F, rw well_founded.fix_eq,
  apply well_founded.min_mem _ _
end

theorem collapse_F.not_lt [is_well_order β s] (f : r ↪r s) (a : α)
   {b} (h : ∀ a' (h : r a' a), s (collapse_F f a').1 b) : ¬ s b (collapse_F f a).1 :=
begin
  unfold collapse_F, rw well_founded.fix_eq,
  exact well_founded.not_lt_min _ _ _
    (show b ∈ {b | ∀ a' (h : r a' a), s (collapse_F f a').1 b}, from h)
end

/-- Construct an initial segment from an order embedding into a well order, by collapsing it
to fill the gaps. -/
def collapse [is_well_order β s] (f : r ↪r s) : r ≼i s :=
by haveI := rel_embedding.is_well_order f; exact
⟨rel_embedding.of_monotone
  (λ a, (collapse_F f a).1) (λ a b, collapse_F.lt f),
λ a b, acc.rec_on (is_well_order.wf.apply b : acc s b) (λ b H IH a h, begin
  let S := {a | ¬ s (collapse_F f a).1 b},
  have : S.nonempty := ⟨_, asymm h⟩,
  existsi (is_well_order.wf : well_founded r).min S this,
  refine ((@trichotomous _ s _ _ _).resolve_left _).resolve_right _,
  { exact (is_well_order.wf : well_founded r).min_mem S this },
  { refine collapse_F.not_lt f _ (λ a' h', _),
    by_contradiction hn,
    exact is_well_order.wf.not_lt_min S this hn h' }
end) a⟩

theorem collapse_apply [is_well_order β s] (f : r ↪r s)
  (a) : collapse f a = (collapse_F f a).1 := rfl

end rel_embedding

/-! ### Well order on an arbitrary type -/

section well_ordering_thm
parameter {σ : Type u}
open function

theorem nonempty_embedding_to_cardinal : nonempty (σ ↪ cardinal.{u}) :=
embedding.total.resolve_left $ λ ⟨⟨f, hf⟩⟩,
  let g : σ → cardinal.{u} := inv_fun f in
  let ⟨x, (hx : g x = 2 ^ sum g)⟩ := inv_fun_surjective hf (2 ^ sum g) in
  have g x ≤ sum g, from le_sum.{u u} g x,
  not_le_of_gt (by rw hx; exact cantor _) this

/-- An embedding of any type to the set of cardinals. -/
def embedding_to_cardinal : σ ↪ cardinal.{u} := classical.choice nonempty_embedding_to_cardinal

/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
def well_ordering_rel : σ → σ → Prop := embedding_to_cardinal ⁻¹'o (<)

instance well_ordering_rel.is_well_order : is_well_order σ well_ordering_rel :=
(rel_embedding.preimage _ _).is_well_order

end well_ordering_thm

/-! ### Definition of ordinals -/

/-- Bundled structure registering a well order on a type. Ordinals will be defined as a quotient
of this type. -/
structure Well_order : Type (u+1) :=
(α : Type u)
(r : α → α → Prop)
(wo : is_well_order α r)

attribute [instance] Well_order.wo

namespace Well_order

instance : inhabited Well_order := ⟨⟨pempty, _, empty_relation.is_well_order⟩⟩

end Well_order

/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. -/
instance ordinal.is_equivalent : setoid Well_order :=
{ r     := λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, nonempty (r ≃r s),
  iseqv := ⟨λ⟨α, r, _⟩, ⟨rel_iso.refl _⟩,
    λ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩, ⟨e.symm⟩,
    λ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

/-- `ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
def ordinal : Type (u + 1) := quotient ordinal.is_equivalent

namespace ordinal

/-- The order type of a well order is an ordinal. -/
def type (r : α → α → Prop) [wo : is_well_order α r] : ordinal :=
⟦⟨α, r, wo⟩⟧

/-- The order type of an element inside a well order. For the embedding as a principal segment, see
`typein.principal_seg`. -/
def typein (r : α → α → Prop) [is_well_order α r] (a : α) : ordinal :=
type (subrel r {b | r b a})

theorem type_def (r : α → α → Prop) [wo : is_well_order α r] :
  @eq ordinal ⟦⟨α, r, wo⟩⟧ (type r) := rfl

@[simp] theorem type_def' (r : α → α → Prop) [is_well_order α r] {wo} :
  @eq ordinal ⟦⟨α, r, wo⟩⟧ (type r) := rfl

theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r = type s ↔ nonempty (r ≃r s) := quotient.eq

@[simp] lemma type_out (o : ordinal) : type o.out.r = o :=
by { refine eq.trans _ (by rw [←quotient.out_eq o]), cases quotient.out o, refl }

@[elab_as_eliminator] theorem induction_on {C : ordinal → Prop}
  (o : ordinal) (H : ∀ α r [is_well_order α r], by exactI C (type r)) : C o :=
quot.induction_on o $ λ ⟨α, r, wo⟩, @H α r wo

/-! ### The order on ordinals -/

/-- Ordinal less-equal is defined such that
  well orders `r` and `s` satisfy `type r ≤ type s` if there exists
  a function embedding `r` as an initial segment of `s`. -/
protected def le (a b : ordinal) : Prop :=
quotient.lift_on₂ a b (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, nonempty (r ≼i s)) $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
propext ⟨
  λ ⟨h⟩, ⟨(initial_seg.of_iso f.symm).trans $
    h.trans (initial_seg.of_iso g)⟩,
  λ ⟨h⟩, ⟨(initial_seg.of_iso f).trans $
    h.trans (initial_seg.of_iso g.symm)⟩⟩

instance : has_le ordinal := ⟨ordinal.le⟩

theorem type_le {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r ≤ type s ↔ nonempty (r ≼i s) := iff.rfl

theorem type_le' {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] : type r ≤ type s ↔ nonempty (r ↪r s) :=
⟨λ ⟨f⟩, ⟨f⟩, λ ⟨f⟩, ⟨f.collapse⟩⟩

/-- Ordinal less-than is defined such that
  well orders `r` and `s` satisfy `type r < type s` if there exists
  a function embedding `r` as a principal segment of `s`. -/
def lt (a b : ordinal) : Prop :=
quotient.lift_on₂ a b (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, nonempty (r ≺i s)) $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
by exactI propext ⟨
  λ ⟨h⟩, ⟨principal_seg.equiv_lt f.symm $
    h.lt_le (initial_seg.of_iso g)⟩,
  λ ⟨h⟩, ⟨principal_seg.equiv_lt f $
    h.lt_le (initial_seg.of_iso g.symm)⟩⟩

instance : has_lt ordinal := ⟨ordinal.lt⟩

@[simp] theorem type_lt {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] :
  type r < type s ↔ nonempty (r ≺i s) := iff.rfl

instance : partial_order ordinal :=
{ le := (≤),
  lt := (<),
  le_refl := quot.ind $ by exact λ ⟨α, r, wo⟩, ⟨initial_seg.refl _⟩,
  le_trans := λ a b c, quotient.induction_on₃ a b c $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ ⟨g⟩, ⟨f.trans g⟩,
  lt_iff_le_not_le := λ a b, quotient.induction_on₂ a b $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩, by exactI
      ⟨λ ⟨f⟩, ⟨⟨f⟩, λ ⟨g⟩, (f.lt_le g).irrefl _⟩,
      λ ⟨⟨f⟩, h⟩, sum.rec_on f.lt_or_eq (λ g, ⟨g⟩)
       (λ g, (h ⟨initial_seg.of_iso g.symm⟩).elim)⟩,
  le_antisymm := λ x b, show x ≤ b → b ≤ x → x = b, from
    quotient.induction_on₂ x b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨h₁⟩ ⟨h₂⟩,
    by exactI quot.sound ⟨initial_seg.antisymm h₁ h₂⟩ }

/-- Given two ordinals `α ≤ β`, then `initial_seg_out α β` is the initial segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def initial_seg_out {α β : ordinal} (h : α ≤ β) : initial_seg α.out.r β.out.r :=
begin
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice
end

/-- Given two ordinals `α < β`, then `principal_seg_out α β` is the principal segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def principal_seg_out {α β : ordinal} (h : α < β) : principal_seg α.out.r β.out.r :=
begin
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice
end

/-- Given two ordinals `α = β`, then `rel_iso_out α β` is the order isomorphism between two
model types for `α` and `β`. -/
def rel_iso_out {α β : ordinal} (h : α = β) : α.out.r ≃r β.out.r :=
begin
  rw [←quotient.out_eq α, ←quotient.out_eq β] at h, revert h,
  cases quotient.out α, cases quotient.out β, exact classical.choice ∘ quotient.exact
end

theorem typein_lt_type (r : α → α → Prop) [is_well_order α r]
  (a : α) : typein r a < type r :=
⟨principal_seg.of_element _ _⟩

@[simp] theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : r ≺i s) :
  typein s f.top = type r :=
eq.symm $ quot.sound ⟨rel_iso.of_surjective
  (rel_embedding.cod_restrict _ f f.lt_top)
  (λ ⟨a, h⟩, by rcases f.down'.1 h with ⟨b, rfl⟩; exact ⟨b, rfl⟩)⟩

@[simp] theorem typein_apply {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : r ≼i s) (a : α) :
  ordinal.typein s (f a) = ordinal.typein r a :=
eq.symm $ quotient.sound ⟨rel_iso.of_surjective
  (rel_embedding.cod_restrict _
    ((subrel.rel_embedding _ _).trans f)
    (λ ⟨x, h⟩, by rw [rel_embedding.trans_apply]; exact f.to_rel_embedding.map_rel_iff.2 h))
  (λ ⟨y, h⟩, by rcases f.init' h with ⟨a, rfl⟩;
    exact ⟨⟨a, f.to_rel_embedding.map_rel_iff.1 h⟩, subtype.eq $ rel_embedding.trans_apply _ _ _⟩)⟩

@[simp] theorem typein_lt_typein (r : α → α → Prop) [is_well_order α r]
  {a b : α} : typein r a < typein r b ↔ r a b :=
⟨λ ⟨f⟩, begin
  have : f.top.1 = a,
  { let f' := principal_seg.of_element r a,
    let g' := f.trans (principal_seg.of_element r b),
    have : g'.top = f'.top, {rw subsingleton.elim f' g'},
    exact this },
  rw ← this, exact f.top.2
end, λ h, ⟨principal_seg.cod_restrict _
  (principal_seg.of_element r a)
  (λ x, @trans _ r _ _ _ _ x.2 h) h⟩⟩

theorem typein_surj (r : α → α → Prop) [is_well_order α r]
  {o} (h : o < type r) : ∃ a, typein r a = o :=
induction_on o (λ β s _ ⟨f⟩, by exactI ⟨f.top, typein_top _⟩) h

lemma typein_injective (r : α → α → Prop) [is_well_order α r] : injective (typein r) :=
injective_of_increasing r (<) (typein r) (λ x y, (typein_lt_typein r).2)

theorem typein_inj (r : α → α → Prop) [is_well_order α r]
  {a b} : typein r a = typein r b ↔ a = b :=
injective.eq_iff (typein_injective r)

/-! ### Enumerating elements in a well-order with ordinals. -/

/-- `enum r o h` is the `o`-th element of `α` ordered by `r`.
  That is, `enum` maps an initial segment of the ordinals, those
  less than the order type of `r`, to the elements of `α`. -/
def enum (r : α → α → Prop) [is_well_order α r] (o) : o < type r → α :=
quot.rec_on o (λ ⟨β, s, _⟩ h, (classical.choice h).top) $
λ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨h⟩, begin
  resetI, refine funext (λ (H₂ : type t < type r), _),
  have H₁ : type s < type r, {rwa type_eq.2 ⟨h⟩},
  have : ∀ {o e} (H : o < type r), @@eq.rec
   (λ (o : ordinal), o < type r → α)
   (λ (h : type s < type r), (classical.choice h).top)
     e H = (classical.choice H₁).top, {intros, subst e},
  exact (this H₂).trans (principal_seg.top_eq h
    (classical.choice H₁) (classical.choice H₂))
end

theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s] (f : s ≺i r)
  {h : type s < type r} : enum r (type s) h = f.top :=
principal_seg.top_eq (rel_iso.refl _) _ _

@[simp] theorem enum_typein (r : α → α → Prop) [is_well_order α r] (a : α)
  {h : typein r a < type r} : enum r (typein r a) h = a :=
enum_type (principal_seg.of_element r a)

@[simp] theorem typein_enum (r : α → α → Prop) [is_well_order α r]
  {o} (h : o < type r) : typein r (enum r o h) = o :=
let ⟨a, e⟩ := typein_surj r h in
by clear _let_match; subst e; rw enum_typein

/-- A well order `r` is order isomorphic to the set of ordinals strictly smaller than the
ordinal version of `r`. -/
def typein_iso (r : α → α → Prop) [is_well_order α r] : r ≃r subrel (<) (< type r) :=
⟨⟨λ x, ⟨typein r x, typein_lt_type r x⟩, λ x, enum r x.1 x.2, λ y, enum_typein r y,
 λ ⟨y, hy⟩, subtype.eq (typein_enum r hy)⟩,
  λ a b, (typein_lt_typein r)⟩

theorem enum_lt {r : α → α → Prop} [is_well_order α r]
  {o₁ o₂ : ordinal} (h₁ : o₁ < type r) (h₂ : o₂ < type r) :
  r (enum r o₁ h₁) (enum r o₂ h₂) ↔ o₁ < o₂ :=
by rw [← typein_lt_typein r, typein_enum, typein_enum]

lemma rel_iso_enum' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s]
  (f : r ≃r s) (o : ordinal) : ∀(hr : o < type r) (hs : o < type s),
  f (enum r o hr) = enum s o hs :=
begin
  refine induction_on o _, rintros γ t wo ⟨g⟩ ⟨h⟩,
  resetI, rw [enum_type g, enum_type (principal_seg.lt_equiv g f)], refl
end

lemma rel_iso_enum {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
  [is_well_order α r] [is_well_order β s]
  (f : r ≃r s) (o : ordinal) (hr : o < type r) :
  f (enum r o hr) =
  enum s o (by {convert hr using 1, apply quotient.sound, exact ⟨f.symm⟩ }) :=
rel_iso_enum' _ _ _ _

theorem wf : @well_founded ordinal (<) :=
⟨λ a, induction_on a $ λ α r wo, by exactI
suffices ∀ a, acc (<) (typein r a), from
⟨_, λ o h, let ⟨a, e⟩ := typein_surj r h in e ▸ this a⟩,
λ a, acc.rec_on (wo.wf.apply a) $ λ x H IH, ⟨_, λ o h, begin
  rcases typein_surj r (lt_trans h (typein_lt_type r _)) with ⟨b, rfl⟩,
  exact IH _ ((typein_lt_typein r).1 h)
end⟩⟩

instance : has_well_founded ordinal := ⟨(<), wf⟩

/-- Principal segment version of the `typein` function, embedding a well order into
  ordinals as a principal segment. -/
def typein.principal_seg {α : Type u} (r : α → α → Prop) [is_well_order α r] :
  @principal_seg α ordinal.{u} r (<) :=
⟨rel_embedding.of_monotone (typein r)
  (λ a b, (typein_lt_typein r).2), type r, λ b,
    ⟨λ h, ⟨enum r _ h, typein_enum r h⟩,
    λ ⟨a, e⟩, e ▸ typein_lt_type _ _⟩⟩

@[simp] theorem typein.principal_seg_coe (r : α → α → Prop) [is_well_order α r] :
  (typein.principal_seg r : α → ordinal) = typein r := rfl

/-! ### Cardinality of ordinals -/

/-- The cardinal of an ordinal is the cardinal of any
  set with that order type. -/
def card (o : ordinal) : cardinal :=
quot.lift_on o (λ ⟨α, r, _⟩, mk α) $
λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩, quotient.sound ⟨e.to_equiv⟩

@[simp] theorem card_type (r : α → α → Prop) [is_well_order α r] :
  card (type r) = mk α := rfl

lemma card_typein {r : α → α → Prop} [wo : is_well_order α r] (x : α) :
  mk {y // r y x} = (typein r x).card := rfl

theorem card_le_card {o₁ o₂ : ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
induction_on o₁ $ λ α r _, induction_on o₂ $ λ β s _ ⟨⟨⟨f, _⟩, _⟩⟩, ⟨f⟩

instance : has_zero ordinal :=
⟨⟦⟨pempty, empty_relation, by apply_instance⟩⟧⟩

instance : inhabited ordinal := ⟨0⟩

theorem zero_eq_type_empty : 0 = @type empty empty_relation _ :=
quotient.sound ⟨⟨empty_equiv_pempty.symm, λ _ _, iff.rfl⟩⟩

@[simp] theorem card_zero : card 0 = 0 := rfl

protected theorem zero_le (o : ordinal) : 0 ≤ o :=
induction_on o $ λ α r _, ⟨⟨⟨embedding.of_is_empty, is_empty_elim⟩, is_empty_elim⟩⟩

@[simp] protected theorem le_zero {o : ordinal} : o ≤ 0 ↔ o = 0 :=
by simp only [le_antisymm_iff, ordinal.zero_le, and_true]

protected theorem pos_iff_ne_zero {o : ordinal} : 0 < o ↔ o ≠ 0 :=
by simp only [lt_iff_le_and_ne, ordinal.zero_le, true_and, ne.def, eq_comm]

instance : has_one ordinal :=
⟨⟦⟨punit, empty_relation, by apply_instance⟩⟧⟩

theorem one_eq_type_unit : 1 = @type unit empty_relation _ :=
quotient.sound ⟨⟨punit_equiv_punit, λ _ _, iff.rfl⟩⟩

@[simp] theorem card_one : card 1 = 1 := rfl

/-! ### Lifting ordinals to a higher universe -/

/-- The universe lift operation for ordinals, which embeds `ordinal.{u}` as
  a proper initial segment of `ordinal.{v}` for `v > u`. For the initial segment version,
  see `lift.initial_seg`. -/
def lift (o : ordinal.{u}) : ordinal.{max u v} :=
quotient.lift_on o (λ ⟨α, r, wo⟩,
  @type _ _ (@rel_embedding.is_well_order _ _ (@equiv.ulift.{v} α ⁻¹'o r) r
    (rel_iso.preimage equiv.ulift.{v} r) wo)) $
λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨f⟩,
quot.sound ⟨(rel_iso.preimage equiv.ulift r).trans $
  f.trans (rel_iso.preimage equiv.ulift s).symm⟩

theorem lift_type {α} (r : α → α → Prop) [is_well_order α r] :
  ∃ wo', lift (type r) = @type _ (@equiv.ulift.{v} α ⁻¹'o r) wo' :=
⟨_, rfl⟩

theorem lift_umax : lift.{u (max u v)} = lift.{u v} :=
funext $ λ a, induction_on a $ λ α r _,
quotient.sound ⟨(rel_iso.preimage equiv.ulift r).trans (rel_iso.preimage equiv.ulift r).symm⟩

theorem lift_id' (a : ordinal) : lift a = a :=
induction_on a $ λ α r _,
quotient.sound ⟨rel_iso.preimage equiv.ulift r⟩

@[simp] theorem lift_id : ∀ a, lift.{u u} a = a := lift_id'.{u u}

@[simp]
theorem lift_lift (a : ordinal) : lift.{(max u v) w} (lift.{u v} a) = lift.{u (max v w)} a :=
induction_on a $ λ α r _,
quotient.sound ⟨(rel_iso.preimage equiv.ulift _).trans $
  (rel_iso.preimage equiv.ulift _).trans (rel_iso.preimage equiv.ulift _).symm⟩

theorem lift_type_le {α : Type u} {β : Type v} {r s} [is_well_order α r] [is_well_order β s] :
  lift.{u (max v w)} (type r) ≤ lift.{v (max u w)} (type s) ↔ nonempty (r ≼i s) :=
⟨λ ⟨f⟩, ⟨(initial_seg.of_iso (rel_iso.preimage equiv.ulift r).symm).trans $
    f.trans (initial_seg.of_iso (rel_iso.preimage equiv.ulift s))⟩,
 λ ⟨f⟩, ⟨(initial_seg.of_iso (rel_iso.preimage equiv.ulift r)).trans $
    f.trans (initial_seg.of_iso (rel_iso.preimage equiv.ulift s).symm)⟩⟩

theorem lift_type_eq {α : Type u} {β : Type v} {r s} [is_well_order α r] [is_well_order β s] :
  lift.{u (max v w)} (type r) = lift.{v (max u w)} (type s) ↔ nonempty (r ≃r s) :=
quotient.eq.trans
⟨λ ⟨f⟩, ⟨(rel_iso.preimage equiv.ulift r).symm.trans $
    f.trans (rel_iso.preimage equiv.ulift s)⟩,
 λ ⟨f⟩, ⟨(rel_iso.preimage equiv.ulift r).trans $
    f.trans (rel_iso.preimage equiv.ulift s).symm⟩⟩

theorem lift_type_lt {α : Type u} {β : Type v} {r s} [is_well_order α r] [is_well_order β s] :
  lift.{u (max v w)} (type r) < lift.{v (max u w)} (type s) ↔ nonempty (r ≺i s) :=
by haveI := @rel_embedding.is_well_order _ _ (@equiv.ulift.{(max v w)} α ⁻¹'o r)
     r (rel_iso.preimage equiv.ulift.{(max v w)} r) _;
   haveI := @rel_embedding.is_well_order _ _ (@equiv.ulift.{(max u w)} β ⁻¹'o s)
     s (rel_iso.preimage equiv.ulift.{(max u w)} s) _; exact
⟨λ ⟨f⟩, ⟨(f.equiv_lt (rel_iso.preimage equiv.ulift r).symm).lt_le
    (initial_seg.of_iso (rel_iso.preimage equiv.ulift s))⟩,
 λ ⟨f⟩, ⟨(f.equiv_lt (rel_iso.preimage equiv.ulift r)).lt_le
    (initial_seg.of_iso (rel_iso.preimage equiv.ulift s).symm)⟩⟩

@[simp] theorem lift_le {a b : ordinal} : lift.{u v} a ≤ lift b ↔ a ≤ b :=
induction_on a $ λ α r _, induction_on b $ λ β s _,
by rw ← lift_umax; exactI lift_type_le

@[simp] theorem lift_inj {a b : ordinal} : lift a = lift b ↔ a = b :=
by simp only [le_antisymm_iff, lift_le]

@[simp] theorem lift_lt {a b : ordinal} : lift a < lift b ↔ a < b :=
by simp only [lt_iff_le_not_le, lift_le]

@[simp] theorem lift_zero : lift 0 = 0 :=
quotient.sound ⟨(rel_iso.preimage equiv.ulift _).trans
 ⟨pempty_equiv_pempty, λ a b, iff.rfl⟩⟩

theorem zero_eq_lift_type_empty : 0 = lift.{0 u} (@type empty empty_relation _) :=
by rw [← zero_eq_type_empty, lift_zero]

@[simp] theorem lift_one : lift 1 = 1 :=
quotient.sound ⟨(rel_iso.preimage equiv.ulift _).trans
 ⟨punit_equiv_punit, λ a b, iff.rfl⟩⟩

theorem one_eq_lift_type_unit : 1 = lift.{0 u} (@type unit empty_relation _) :=
by rw [← one_eq_type_unit, lift_one]

@[simp] theorem lift_card (a) : (card a).lift = card (lift a) :=
induction_on a $ λ α r _, rfl

theorem lift_down' {a : cardinal.{u}} {b : ordinal.{max u v}}
  (h : card b ≤ a.lift) : ∃ a', lift a' = b :=
let ⟨c, e⟩ := cardinal.lift_down h in
quotient.induction_on c (λ α, induction_on b $ λ β s _ e', begin
  resetI,
  rw [mk_def, card_type, ← cardinal.lift_id'.{(max u v) u} (mk β),
      ← cardinal.lift_umax.{u v}, lift_mk_eq.{u (max u v) (max u v)}] at e',
  cases e' with f,
  have g := rel_iso.preimage f s,
  haveI := (g : ⇑f ⁻¹'o s ↪r s).is_well_order,
  have := lift_type_eq.{u (max u v) (max u v)}.2 ⟨g⟩,
  rw [lift_id, lift_umax.{u v}] at this,
  exact ⟨_, this⟩
end) e

theorem lift_down {a : ordinal.{u}} {b : ordinal.{max u v}}
  (h : b ≤ lift a) : ∃ a', lift a' = b :=
@lift_down' (card a) _ (by rw lift_card; exact card_le_card h)

theorem le_lift_iff {a : ordinal.{u}} {b : ordinal.{max u v}} :
  b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
⟨λ h, let ⟨a', e⟩ := lift_down h in ⟨a', e, lift_le.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : ordinal.{u}} {b : ordinal.{max u v}} :
  b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
⟨λ h, let ⟨a', e⟩ := lift_down (le_of_lt h) in
      ⟨a', e, lift_lt.1 $ e.symm ▸ h⟩,
 λ ⟨a', e, h⟩, e ▸ lift_lt.2 h⟩

/-- Initial segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as an initial segment when `u ≤ v`. -/
def lift.initial_seg : @initial_seg ordinal.{u} ordinal.{max u v} (<) (<) :=
⟨⟨⟨lift.{u v}, λ a b, lift_inj.1⟩, λ a b, lift_lt⟩,
  λ a b h, lift_down (le_of_lt h)⟩

@[simp] theorem lift.initial_seg_coe : (lift.initial_seg : ordinal → ordinal) = lift := rfl

/-! ### The first infinite ordinal `omega` -/

/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega : ordinal.{u} := lift $ @type ℕ (<) _

localized "notation `ω` := ordinal.omega.{0}" in ordinal

theorem card_omega : card omega = cardinal.omega := rfl

@[simp] theorem lift_omega : lift omega = omega := lift_lift _

/-!
### Definition and first properties of addition on ordinals

In this paragraph, we introduce the addition on ordinals, and prove just enough properties to
deduce that the order on ordinals is total (and therefore well-founded). Further properties of
the addition, together with properties of the other operations, are proved in
`ordinal_arithmetic.lean`.
-/

/-- `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. -/
instance : has_add ordinal.{u} :=
⟨λo₁ o₂, quotient.lift_on₂ o₁ o₂
  (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, ⟦⟨α ⊕ β, sum.lex r s, by exactI sum.lex.is_well_order⟩⟧
    : Well_order → Well_order → ordinal) $
λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
quot.sound ⟨rel_iso.sum_lex_congr f g⟩⟩

@[simp] theorem card_add (o₁ o₂ : ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
induction_on o₁ $ λ α r _, induction_on o₂ $ λ β s _, rfl

@[simp] theorem card_nat (n : ℕ) : card.{u} n = n :=
by induction n; [refl, simp only [card_add, card_one, nat.cast_succ, *]]

@[simp] theorem type_add {α β : Type u} (r : α → α → Prop) (s : β → β → Prop)
  [is_well_order α r] [is_well_order β s] : type r + type s = type (sum.lex r s) := rfl

/-- The ordinal successor is the smallest ordinal larger than `o`.
  It is defined as `o + 1`. -/
def succ (o : ordinal) : ordinal := o + 1

theorem succ_eq_add_one (o) : succ o = o + 1 := rfl

instance : add_monoid ordinal.{u} :=
{ add       := (+),
  zero      := 0,
  zero_add  := λ o, induction_on o $ λ α r _, eq.symm $ quotient.sound
    ⟨⟨(empty_sum pempty α).symm, λ a b, sum.lex_inr_inr⟩⟩,
  add_zero  := λ o, induction_on o $ λ α r _, eq.symm $ quotient.sound
    ⟨⟨(sum_empty α pempty).symm, λ a b, sum.lex_inl_inl⟩⟩,
  add_assoc := λ o₁ o₂ o₃, quotient.induction_on₃ o₁ o₂ o₃ $
    λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩, quot.sound
    ⟨⟨sum_assoc _ _ _, λ a b,
    begin rcases a with ⟨a|a⟩|a; rcases b with ⟨b|b⟩|b;
      simp only [sum_assoc_apply_in1, sum_assoc_apply_in2, sum_assoc_apply_in3,
        sum.lex_inl_inl, sum.lex_inr_inr, sum.lex.sep, sum.lex_inr_inl] end⟩⟩ }

theorem add_le_add_left {a b : ordinal} : a ≤ b → ∀ c, c + a ≤ c + b :=
induction_on a $ λ α₁ r₁ _, induction_on b $ λ α₂ r₂ _ ⟨⟨⟨f, fo⟩, fi⟩⟩ c,
induction_on c $ λ β s _,
⟨⟨⟨(embedding.refl _).sum_map f,
  λ a b, match a, b with
    | sum.inl a, sum.inl b := sum.lex_inl_inl.trans sum.lex_inl_inl.symm
    | sum.inl a, sum.inr b := by apply iff_of_true; apply sum.lex.sep
    | sum.inr a, sum.inl b := by apply iff_of_false; exact sum.lex_inr_inl
    | sum.inr a, sum.inr b := sum.lex_inr_inr.trans $ fo.trans sum.lex_inr_inr.symm
    end⟩,
  λ a b H, match a, b, H with
    | _,         sum.inl b, _ := ⟨sum.inl b, rfl⟩
    | sum.inl a, sum.inr b, H := (sum.lex_inr_inl H).elim
    | sum.inr a, sum.inr b, H := let ⟨w, h⟩ := fi _ _ (sum.lex_inr_inr.1 H) in
        ⟨sum.inr w, congr_arg sum.inr h⟩
  end⟩⟩

theorem le_add_right (a b : ordinal) : a ≤ a + b :=
by simpa only [add_zero] using add_le_add_left (ordinal.zero_le b) a

theorem add_le_add_right {a b : ordinal} : a ≤ b → ∀ c, a + c ≤ b + c :=
induction_on a $ λ α₁ r₁ hr₁, induction_on b $ λ α₂ r₂ hr₂ ⟨⟨⟨f, fo⟩, fi⟩⟩ c,
induction_on c $ λ β s hs, (@type_le' _ _ _ _
  (@sum.lex.is_well_order _ _ _ _ hr₁ hs)
  (@sum.lex.is_well_order _ _ _ _ hr₂ hs)).2
⟨⟨f.sum_map (embedding.refl _), λ a b, begin
  split; intro H,
  { cases a with a a; cases b with b b; cases H; constructor; [rwa ← fo, assumption] },
  { cases H; constructor; [rwa fo, assumption] }
end⟩⟩

theorem le_add_left (a b : ordinal) : a ≤ b + a :=
by simpa only [zero_add] using add_le_add_right (ordinal.zero_le b) a

theorem lt_succ_self (o : ordinal.{u}) : o < succ o :=
induction_on o $ λ α r _, ⟨⟨⟨⟨λ x, sum.inl x, λ _ _, sum.inl.inj⟩,
  λ _ _, sum.lex_inl_inl⟩,
sum.inr punit.star, λ b, sum.rec_on b
  (λ x, ⟨λ _, ⟨x, rfl⟩, λ _, sum.lex.sep _ _⟩)
  (λ x, sum.lex_inr_inr.trans ⟨false.elim, λ ⟨x, H⟩, sum.inl_ne_inr H⟩)⟩⟩

theorem succ_le {a b : ordinal} : succ a ≤ b ↔ a < b :=
⟨lt_of_lt_of_le (lt_succ_self _),
induction_on a $ λ α r hr, induction_on b $ λ β s hs ⟨⟨f, t, hf⟩⟩, begin
  refine ⟨⟨@rel_embedding.of_monotone (α ⊕ punit) β _ _
    (@sum.lex.is_well_order _ _ _ _ hr _).1.1
    (@is_asymm_of_is_trans_of_is_irrefl _ _ hs.1.2.2 hs.1.2.1)
    (sum.rec _ _) (λ a b, _), λ a b, _⟩⟩,
  { exact f }, { exact λ _, t },
  { rcases a with a|_; rcases b with b|_,
    { simpa only [sum.lex_inl_inl] using f.map_rel_iff.2 },
    { intro _, rw hf, exact ⟨_, rfl⟩ },
    { exact false.elim ∘ sum.lex_inr_inl },
    { exact false.elim ∘ sum.lex_inr_inr.1 } },
  { rcases a with a|_,
    { intro h, have := @principal_seg.init _ _ _ _ hs.1.2.2 ⟨f, t, hf⟩ _ _ h,
      cases this with w h, exact ⟨sum.inl w, h⟩ },
    { intro h, cases (hf b).1 h with w h, exact ⟨sum.inl w, h⟩ } }
end⟩

theorem le_total (a b : ordinal) : a ≤ b ∨ b ≤ a :=
match lt_or_eq_of_le (le_add_left b a), lt_or_eq_of_le (le_add_right a b) with
| or.inr h, _ := by rw h; exact or.inl (le_add_right _ _)
| _, or.inr h := by rw h; exact or.inr (le_add_left _ _)
| or.inl h₁, or.inl h₂ := induction_on a (λ α₁ r₁ _,
  induction_on b $ λ α₂ r₂ _ ⟨f⟩ ⟨g⟩, begin
    resetI,
    rw [← typein_top f, ← typein_top g, le_iff_lt_or_eq,
        le_iff_lt_or_eq, typein_lt_typein, typein_lt_typein],
    rcases trichotomous_of (sum.lex r₁ r₂) g.top f.top with h|h|h;
    [exact or.inl (or.inl h), {left, right, rw h}, exact or.inr (or.inl h)]
  end) h₁ h₂
end

instance : linear_order ordinal :=
{ le_total     := le_total,
  decidable_le := classical.dec_rel _,
  ..ordinal.partial_order }

instance : is_well_order ordinal (<) := ⟨wf⟩

@[simp] lemma typein_le_typein (r : α → α → Prop) [is_well_order α r] {x x' : α} :
  typein r x ≤ typein r x' ↔ ¬r x' x :=
by rw [←not_lt, typein_lt_typein]

lemma enum_le_enum (r : α → α → Prop) [is_well_order α r] {o o' : ordinal}
  (ho : o < type r) (ho' : o' < type r) : ¬r (enum r o' ho') (enum r o ho) ↔ o ≤ o' :=
by rw [←@not_lt _ _ o' o, enum_lt ho']

/-- `univ.{u v}` is the order type of the ordinals of `Type u` as a member
  of `ordinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
def univ := lift.{(u+1) v} (@type ordinal.{u} (<) _)

theorem univ_id : univ.{u (u+1)} = @type ordinal.{u} (<) _ := lift_id _

@[simp] theorem lift_univ : lift.{_ w} univ.{u v} = univ.{u (max v w)} := lift_lift _

theorem univ_umax : univ.{u (max (u+1) v)} = univ.{u v} := congr_fun lift_umax _

/-- Principal segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as a principal segment when `u < v`. -/
def lift.principal_seg : @principal_seg ordinal.{u} ordinal.{max (u+1) v} (<) (<) :=
⟨↑lift.initial_seg.{u (max (u+1) v)}, univ.{u v}, begin
  refine λ b, induction_on b _, introsI β s _,
  rw [univ, ← lift_umax], split; intro h,
  { rw ← lift_id (type s) at h ⊢,
    cases lift_type_lt.1 h with f, cases f with f a hf,
    existsi a, revert hf,
    apply induction_on a, introsI α r _ hf,
    refine lift_type_eq.{u (max (u+1) v) (max (u+1) v)}.2
      ⟨(rel_iso.of_surjective (rel_embedding.of_monotone _ _) _).symm⟩,
    { exact λ b, enum r (f b) ((hf _).2 ⟨_, rfl⟩) },
    { refine λ a b h, (typein_lt_typein r).1 _,
      rw [typein_enum, typein_enum],
      exact f.map_rel_iff.2 h },
    { intro a', cases (hf _).1 (typein_lt_type _ a') with b e,
      existsi b, simp, simp [e] } },
  { cases h with a e, rw [← e],
    apply induction_on a, introsI α r _,
    exact lift_type_lt.{u (u+1) (max (u+1) v)}.2
      ⟨typein.principal_seg r⟩ }
end⟩

@[simp] theorem lift.principal_seg_coe :
  (lift.principal_seg.{u v} : ordinal → ordinal) = lift.{u (max (u+1) v)} := rfl

@[simp] theorem lift.principal_seg_top : lift.principal_seg.top = univ := rfl

theorem lift.principal_seg_top' :
  lift.principal_seg.{u (u+1)}.top = @type ordinal.{u} (<) _ :=
by simp only [lift.principal_seg_top, univ_id]

/-! ### Minimum -/

/-- The minimal element of a nonempty family of ordinals -/
def min {ι} (I : nonempty ι) (f : ι → ordinal) : ordinal :=
wf.min (set.range f) (let ⟨i⟩ := I in ⟨_, set.mem_range_self i⟩)

theorem min_eq {ι} (I) (f : ι → ordinal) : ∃ i, min I f = f i :=
let ⟨i, e⟩ := wf.min_mem (set.range f) _ in ⟨i, e.symm⟩

theorem min_le {ι I} (f : ι → ordinal) (i) : min I f ≤ f i :=
le_of_not_gt $ wf.not_lt_min (set.range f) _ (set.mem_range_self i)

theorem le_min {ι I} {f : ι → ordinal} {a} : a ≤ min I f ↔ ∀ i, a ≤ f i :=
⟨λ h i, le_trans h (min_le _ _),
 λ h, let ⟨i, e⟩ := min_eq I f in e.symm ▸ h i⟩

/-- The minimal element of a nonempty set of ordinals -/
def omin (S : set ordinal.{u}) (H : ∃ x, x ∈ S) : ordinal.{u} :=
@min.{(u+2) u} S (let ⟨x, px⟩ := H in ⟨⟨x, px⟩⟩) subtype.val

theorem omin_mem (S H) : omin S H ∈ S :=
let ⟨⟨i, h⟩, e⟩ := @min_eq S _ _ in
(show omin S H = i, from e).symm ▸ h

theorem le_omin {S H a} : a ≤ omin S H ↔ ∀ i ∈ S, a ≤ i :=
le_min.trans set_coe.forall

theorem omin_le {S H i} (h : i ∈ S) : omin S H ≤ i :=
le_omin.1 (le_refl _) _ h

@[simp] theorem lift_min {ι} (I) (f : ι → ordinal) : lift (min I f) = min I (lift ∘ f) :=
le_antisymm (le_min.2 $ λ a, lift_le.2 $ min_le _ a) $
let ⟨i, e⟩ := min_eq I (lift ∘ f) in
by rw e; exact lift_le.2 (le_min.2 $ λ j, lift_le.1 $
by have := min_le (lift ∘ f) j; rwa e at this)

end ordinal

/-! ### Representing a cardinal with an ordinal -/

namespace cardinal
open ordinal

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. For the order-embedding version, see `ord.order_embedding`. -/
def ord (c : cardinal) : ordinal :=
begin
  let ι := λ α, {r // is_well_order α r},
  have : Π α, ι α := λ α, ⟨well_ordering_rel, by apply_instance⟩,
  let F := λ α, ordinal.min ⟨this _⟩ (λ i:ι α, ⟦⟨α, i.1, i.2⟩⟧),
  refine quot.lift_on c F _,
  suffices : ∀ {α β}, α ≈ β → F α ≤ F β,
  from λ α β h, le_antisymm (this h) (this (setoid.symm h)),
  intros α β h, cases h with f, refine ordinal.le_min.2 (λ i, _),
  haveI := @rel_embedding.is_well_order _ _
    (f ⁻¹'o i.1) _ ↑(rel_iso.preimage f i.1) i.2,
  rw ← show type (f ⁻¹'o i.1) = ⟦⟨β, i.1, i.2⟩⟧, from
    quot.sound ⟨rel_iso.preimage f i.1⟩,
  exact ordinal.min_le (λ i:ι α, ⟦⟨α, i.1, i.2⟩⟧) ⟨_, _⟩
end

lemma ord_eq_min (α : Type u) : ord (mk α) =
  @ordinal.min {r // is_well_order α r} ⟨⟨well_ordering_rel, by apply_instance⟩⟩
    (λ i, ⟦⟨α, i.1, i.2⟩⟧) := rfl

theorem ord_eq (α) : ∃ (r : α → α → Prop) [wo : is_well_order α r],
  ord (mk α) = @type α r wo :=
let ⟨⟨r, wo⟩, h⟩ := @ordinal.min_eq {r // is_well_order α r}
  ⟨⟨well_ordering_rel, by apply_instance⟩⟩
  (λ i:{r // is_well_order α r}, ⟦⟨α, i.1, i.2⟩⟧) in
⟨r, wo, h⟩

theorem ord_le_type (r : α → α → Prop) [is_well_order α r] : ord (mk α) ≤ ordinal.type r :=
@ordinal.min_le {r // is_well_order α r}
  ⟨⟨well_ordering_rel, by apply_instance⟩⟩
  (λ i:{r // is_well_order α r}, ⟦⟨α, i.1, i.2⟩⟧) ⟨r, _⟩

theorem ord_le {c o} : ord c ≤ o ↔ c ≤ o.card :=
quotient.induction_on c $ λ α, induction_on o $ λ β s _,
let ⟨r, _, e⟩ := ord_eq α in begin
  resetI, simp only [mk_def, card_type], split; intro h,
  { rw e at h, exact let ⟨f⟩ := h in ⟨f.to_embedding⟩ },
  { cases h with f,
    have g := rel_embedding.preimage f s,
    haveI := rel_embedding.is_well_order g,
    exact le_trans (ord_le_type _) (type_le'.2 ⟨g⟩) }
end

theorem lt_ord {c o} : o < ord c ↔ o.card < c :=
by rw [← not_le, ← not_le, ord_le]

@[simp] theorem card_ord (c) : (ord c).card = c :=
quotient.induction_on c $ λ α,
let ⟨r, _, e⟩ := ord_eq α in by simp only [mk_def, e, card_type]

theorem ord_card_le (o : ordinal) : o.card.ord ≤ o :=
ord_le.2 (le_refl _)

lemma lt_ord_succ_card (o : ordinal) : o < o.card.succ.ord :=
by { rw [lt_ord], apply cardinal.lt_succ_self }

@[simp] theorem ord_le_ord {c₁ c₂} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ :=
by simp only [ord_le, card_ord]

@[simp] theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ :=
by simp only [lt_ord, card_ord]

@[simp] theorem ord_zero : ord 0 = 0 :=
le_antisymm (ord_le.2 $ zero_le _) (ordinal.zero_le _)

@[simp] theorem ord_nat (n : ℕ) : ord n = n :=
le_antisymm (ord_le.2 $ by simp only [card_nat]) $ begin
  induction n with n IH,
  { apply ordinal.zero_le },
  { exact (@ordinal.succ_le n _).2 (lt_of_le_of_lt IH $
    ord_lt_ord.2 $ nat_cast_lt.2 (nat.lt_succ_self n)) }
end

@[simp] theorem lift_ord (c) : (ord c).lift = ord (lift c) :=
eq_of_forall_ge_iff $ λ o, le_iff_le_iff_lt_iff_lt.2 $ begin
  split; intro h,
  { rcases ordinal.lt_lift_iff.1 h with ⟨a, e, h⟩,
    rwa [← e, lt_ord, ← lift_card, lift_lt, ← lt_ord] },
  { rw lt_ord at h,
    rcases lift_down' (le_of_lt h) with ⟨o, rfl⟩,
    rw [← lift_card, lift_lt] at h,
    rwa [ordinal.lift_lt, lt_ord] }
end

lemma mk_ord_out (c : cardinal) : mk c.ord.out.α = c :=
by rw [←card_type c.ord.out.r, type_out, card_ord]

lemma card_typein_lt (r : α → α → Prop) [is_well_order α r] (x : α)
  (h : ord (mk α) = type r) : card (typein r x) < mk α :=
by { rw [←ord_lt_ord, h], refine lt_of_le_of_lt (ord_card_le _) (typein_lt_type r x) }

lemma card_typein_out_lt (c : cardinal) (x : c.ord.out.α) : card (typein c.ord.out.r x) < c :=
by { convert card_typein_lt c.ord.out.r x _, rw [mk_ord_out], rw [type_out, mk_ord_out] }

lemma ord_injective : injective ord :=
by { intros c c' h, rw [←card_ord c, ←card_ord c', h] }

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular function, see `ord`.
-/
def ord.order_embedding : cardinal ↪o ordinal :=
rel_embedding.order_embedding_of_lt_embedding
  (rel_embedding.of_monotone cardinal.ord $ λ a b, cardinal.ord_lt_ord.2)

@[simp] theorem ord.order_embedding_coe :
  (ord.order_embedding : cardinal → ordinal) = ord := rfl

/-- The cardinal `univ` is the cardinality of ordinal `univ`, or
  equivalently the cardinal of `ordinal.{u}`, or `cardinal.{u}`,
  as an element of `cardinal.{v}` (when `u < v`). -/
def univ := lift.{(u+1) v} (mk ordinal)

theorem univ_id : univ.{u (u+1)} = mk ordinal := lift_id _

@[simp] theorem lift_univ : lift.{_ w} univ.{u v} = univ.{u (max v w)} := lift_lift _

theorem univ_umax : univ.{u (max (u+1) v)} = univ.{u v} := congr_fun lift_umax _

theorem lift_lt_univ (c : cardinal) : lift.{u (u+1)} c < univ.{u (u+1)} :=
by simpa only [lift.principal_seg_coe, lift_ord, lift_succ, ord_le, succ_le] using le_of_lt
  (lift.principal_seg.{u (u+1)}.lt_top (succ c).ord)

theorem lift_lt_univ' (c : cardinal) : lift.{u (max (u+1) v)} c < univ.{u v} :=
by simpa only [lift_lift, lift_univ, univ_umax] using
  lift_lt.{_ (max (u+1) v)}.2 (lift_lt_univ c)

@[simp] theorem ord_univ : ord univ.{u v} = ordinal.univ.{u v} :=
le_antisymm (ord_card_le _) $ le_of_forall_lt $ λ o h,
lt_ord.2 begin
  rcases lift.principal_seg.{u v}.down'.1
    (by simpa only [lift.principal_seg_coe] using h) with ⟨o', rfl⟩,
  simp only [lift.principal_seg_coe], rw [← lift_card],
  apply lift_lt_univ'
end

theorem lt_univ {c} : c < univ.{u (u+1)} ↔ ∃ c', c = lift.{u (u+1)} c' :=
⟨λ h, begin
  have := ord_lt_ord.2 h,
  rw ord_univ at this,
  cases lift.principal_seg.{u (u+1)}.down'.1
    (by simpa only [lift.principal_seg_top]) with o e,
  have := card_ord c,
  rw [← e, lift.principal_seg_coe, ← lift_card] at this,
  exact ⟨_, this.symm⟩
end, λ ⟨c', e⟩, e.symm ▸ lift_lt_univ _⟩

theorem lt_univ' {c} : c < univ.{u v} ↔ ∃ c', c = lift.{u (max (u+1) v)} c' :=
⟨λ h, let ⟨a, e, h'⟩ := lt_lift_iff.1 h in begin
  rw [← univ_id] at h',
  rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩,
  exact ⟨c', by simp only [e.symm, lift_lift]⟩
end, λ ⟨c', e⟩, e.symm ▸ lift_lt_univ' _⟩

end cardinal

namespace ordinal

@[simp] theorem card_univ : card univ = cardinal.univ := rfl

end ordinal
