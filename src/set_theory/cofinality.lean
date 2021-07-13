/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import set_theory.cardinal_ordinal
/-!
# Cofinality

This file contains the definition of cofinality of a ordinal number and regular cardinals

## Main Definitions

* `ordinal.cof o` is the cofinality of the ordinal `o`.
  If `o` is the order type of the relation `<` on `α`, then `o.cof` is the smallest cardinality of a
  subset `s` of α that is *cofinal* in `α`, i.e. `∀ x : α, ∃ y ∈ s, ¬ y < x`.
* `cardinal.is_limit c` means that `c` is a (weak) limit cardinal: `c ≠ 0 ∧ ∀ x < c, succ x < c`.
* `cardinal.is_strong_limit c` means that `c` is a strong limit cardinal:
  `c ≠ 0 ∧ ∀ x < c, 2 ^ x < c`.
* `cardinal.is_regular c` means that `c` is a regular cardinal: `omega ≤ c ∧ c.ord.cof = c`.
* `cardinal.is_inaccessible c` means that `c` is strongly inaccessible:
  `omega < c ∧ is_regular c ∧ is_strong_limit c`.

## Main Statements

* `ordinal.infinite_pigeonhole_card`: the infinite pigeonhole principle
* `cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ cardinal.omega`
* `cardinal.univ_inaccessible`: The type of ordinals in `Type u` form an inaccessible cardinal
  (in `Type v` with `v > u`). This shows (externally) that in `Type u` there are at least `u`
  inaccessible cardinals.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.

## Tags

cofinality, regular cardinals, limits cardinals, inaccessible cardinals,
infinite pigeonhole principle


-/
noncomputable theory

open function cardinal set
open_locale classical

universes u v w
variables {α : Type*} {r : α → α → Prop}

namespace order
/-- Cofinality of a reflexive order `≼`. This is the smallest cardinality
  of a subset `S : set α` such that `∀ a, ∃ b ∈ S, a ≼ b`. -/
def cof (r : α → α → Prop) [is_refl α r] : cardinal :=
@cardinal.min {S : set α // ∀ a, ∃ b ∈ S, r a b}
  ⟨⟨set.univ, λ a, ⟨a, ⟨⟩, refl _⟩⟩⟩
  (λ S, mk S)

lemma cof_le (r : α → α → Prop) [is_refl α r] {S : set α} (h : ∀a, ∃(b ∈ S), r a b) :
  order.cof r ≤ mk S :=
le_trans (cardinal.min_le _ ⟨S, h⟩) (le_refl _)

lemma le_cof {r : α → α → Prop} [is_refl α r] (c : cardinal) :
  c ≤ order.cof r ↔ ∀ {S : set α} (h : ∀a, ∃(b ∈ S), r a b) , c ≤ mk S :=
by { rw [order.cof, cardinal.le_min], exact ⟨λ H S h, H ⟨S, h⟩, λ H ⟨S, h⟩, H h ⟩ }

end order

theorem rel_iso.cof.aux {α : Type u} {β : Type v} {r s}
  [is_refl α r] [is_refl β s] (f : r ≃r s) :
  cardinal.lift.{u (max u v)} (order.cof r) ≤
  cardinal.lift.{v (max u v)} (order.cof s) :=
begin
  rw [order.cof, order.cof, lift_min, lift_min, cardinal.le_min],
  intro S, cases S with S H, simp [(∘)],
  refine le_trans (min_le _ _) _,
  { exact ⟨f ⁻¹' S, λ a,
    let ⟨b, bS, h⟩ := H (f a) in ⟨f.symm b, by simp [bS, ← f.map_rel_iff, h,
      -coe_fn_coe_base, -coe_fn_coe_trans, principal_seg.coe_coe_fn', initial_seg.coe_coe_fn]⟩⟩ },
  { exact lift_mk_le.{u v (max u v)}.2
    ⟨⟨λ ⟨x, h⟩, ⟨f x, h⟩, λ ⟨x, h₁⟩ ⟨y, h₂⟩ h₃,
      by congr; injection h₃ with h'; exact f.to_equiv.injective h'⟩⟩ }
end

theorem rel_iso.cof {α : Type u} {β : Type v} {r s}
  [is_refl α r] [is_refl β s] (f : r ≃r s) :
  cardinal.lift.{u (max u v)} (order.cof r) =
  cardinal.lift.{v (max u v)} (order.cof s) :=
le_antisymm (rel_iso.cof.aux f) (rel_iso.cof.aux f.symm)

def strict_order.cof (r : α → α → Prop) [h : is_irrefl α r] : cardinal :=
@order.cof α (λ x y, ¬ r y x) ⟨h.1⟩

namespace ordinal

/-- Cofinality of an ordinal. This is the smallest cardinal of a
  subset `S` of the ordinal which is unbounded, in the sense
  `∀ a, ∃ b ∈ S, ¬(b > a)`. It is defined for all ordinals, but
  `cof 0 = 0` and `cof (succ o) = 1`, so it is only really
  interesting on limit ordinals (when it is an infinite cardinal). -/
def cof (o : ordinal.{u}) : cardinal.{u} :=
quot.lift_on o (λ ⟨α, r, _⟩, by exactI strict_order.cof r)
begin
  rintros ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨⟨f, hf⟩⟩,
  rw ← cardinal.lift_inj,
  apply rel_iso.cof ⟨f, _⟩,
  simp [hf]
end

lemma cof_type (r : α → α → Prop) [is_well_order α r] : (type r).cof = strict_order.cof r := rfl

theorem le_cof_type [is_well_order α r] {c} : c ≤ cof (type r) ↔
  ∀ S : set α, (∀ a, ∃ b ∈ S, ¬ r b a) → c ≤ mk S :=
by dsimp [cof, strict_order.cof, order.cof, type, quotient.mk, quot.lift_on];
   rw [cardinal.le_min, subtype.forall]; refl

theorem cof_type_le [is_well_order α r] (S : set α) (h : ∀ a, ∃ b ∈ S, ¬ r b a) :
  cof (type r) ≤ mk S :=
le_cof_type.1 (le_refl _) S h

theorem lt_cof_type [is_well_order α r] (S : set α) (hl : mk S < cof (type r)) :
  ∃ a, ∀ b ∈ S, r b a :=
not_forall_not.1 $ λ h, not_le_of_lt hl $ cof_type_le S (λ a, not_ball.1 (h a))

theorem cof_eq (r : α → α → Prop) [is_well_order α r] :
  ∃ S : set α, (∀ a, ∃ b ∈ S, ¬ r b a) ∧ mk S = cof (type r) :=
begin
  have : ∃ i, cof (type r) = _,
  { dsimp [cof, order.cof, type, quotient.mk, quot.lift_on],
    apply cardinal.min_eq },
  exact let ⟨⟨S, hl⟩, e⟩ := this in ⟨S, hl, e.symm⟩,
end

theorem ord_cof_eq (r : α → α → Prop) [is_well_order α r] :
  ∃ S : set α, (∀ a, ∃ b ∈ S, ¬ r b a) ∧ type (subrel r S) = (cof (type r)).ord :=
let ⟨S, hS, e⟩ := cof_eq r, ⟨s, _, e'⟩ := cardinal.ord_eq S,
    T : set α := {a | ∃ aS : a ∈ S, ∀ b : S, s b ⟨_, aS⟩ → r b a} in
begin
  resetI, suffices,
  { refine ⟨T, this,
      le_antisymm _ (cardinal.ord_le.2 $ cof_type_le T this)⟩,
    rw [← e, e'],
    refine type_le'.2 ⟨rel_embedding.of_monotone
      (λ a, ⟨a, let ⟨aS, _⟩ := a.2 in aS⟩) (λ a b h, _)⟩,
    rcases a with ⟨a, aS, ha⟩, rcases b with ⟨b, bS, hb⟩,
    change s ⟨a, _⟩ ⟨b, _⟩,
    refine ((trichotomous_of s _ _).resolve_left (λ hn, _)).resolve_left _,
    { exact asymm h (ha _ hn) },
    { intro e, injection e with e, subst b,
      exact irrefl _ h } },
  { intro a,
    have : {b : S | ¬ r b a}.nonempty := let ⟨b, bS, ba⟩ := hS a in ⟨⟨b, bS⟩, ba⟩,
    let b := (is_well_order.wf).min _ this,
    have ba : ¬r b a := (is_well_order.wf).min_mem _ this,
    refine ⟨b, ⟨b.2, λ c, not_imp_not.1 $ λ h, _⟩, ba⟩,
    rw [show ∀b:S, (⟨b, b.2⟩:S) = b, by intro b; cases b; refl],
    exact (is_well_order.wf).not_lt_min _ this
      (is_order_connected.neg_trans h ba) }
end

theorem lift_cof (o) : (cof o).lift = cof o.lift :=
induction_on o $ begin introsI α r _,
  cases lift_type r with _ e, rw e,
  apply le_antisymm,
  { unfreezingI { refine le_cof_type.2 (λ S H, _) },
    have : (mk (ulift.up ⁻¹' S)).lift ≤ mk S :=
     ⟨⟨λ ⟨⟨x, h⟩⟩, ⟨⟨x⟩, h⟩,
       λ ⟨⟨x, h₁⟩⟩ ⟨⟨y, h₂⟩⟩ e, by simp at e; congr; injection e⟩⟩,
    refine le_trans (cardinal.lift_le.2 $ cof_type_le _ _) this,
    exact λ a, let ⟨⟨b⟩, bs, br⟩ := H ⟨a⟩ in ⟨b, bs, br⟩ },
  { rcases cof_eq r with ⟨S, H, e'⟩,
    have : mk (ulift.down ⁻¹' S) ≤ (mk S).lift :=
     ⟨⟨λ ⟨⟨x⟩, h⟩, ⟨⟨x, h⟩⟩,
       λ ⟨⟨x⟩, h₁⟩ ⟨⟨y⟩, h₂⟩ e, by simp at e; congr; injections⟩⟩,
    rw e' at this,
    unfreezingI { refine le_trans (cof_type_le _ _) this },
    exact λ ⟨a⟩, let ⟨b, bs, br⟩ := H a in ⟨⟨b⟩, bs, br⟩ }
end

theorem cof_le_card (o) : cof o ≤ card o :=
induction_on o $ λ α r _, begin
  resetI,
  have : mk (@set.univ α) = card (type r) :=
    quotient.sound ⟨equiv.set.univ _⟩,
  rw ← this, exact cof_type_le set.univ (λ a, ⟨a, ⟨⟩, irrefl a⟩)
end

theorem cof_ord_le (c : cardinal) : cof c.ord ≤ c :=
by simpa using cof_le_card c.ord

@[simp] theorem cof_zero : cof 0 = 0 :=
le_antisymm (by simpa using cof_le_card 0) (cardinal.zero_le _)

@[simp] theorem cof_eq_zero {o} : cof o = 0 ↔ o = 0 :=
⟨induction_on o $ λ α r _ z, by exactI
  let ⟨S, hl, e⟩ := cof_eq r in type_eq_zero_iff_empty.2 $
  λ ⟨a⟩, let ⟨b, h, _⟩ := hl a in
  ne_zero_iff_nonempty.2 (by exact ⟨⟨_, h⟩⟩) (e.trans z),
λ e, by simp [e]⟩

@[simp] theorem cof_succ (o) : cof (succ o) = 1 :=
begin
  apply le_antisymm,
  { refine induction_on o (λ α r _, _),
    change cof (type _) ≤ _,
    rw [← (_ : mk _ = 1)], apply cof_type_le,
    { refine λ a, ⟨sum.inr punit.star, set.mem_singleton _, _⟩,
      rcases a with a|⟨⟨⟨⟩⟩⟩; simp [empty_relation] },
    { rw [cardinal.fintype_card, set.card_singleton], simp } },
  { rw [← cardinal.succ_zero, cardinal.succ_le],
    simpa [lt_iff_le_and_ne, cardinal.zero_le] using
      λ h, succ_ne_zero o (cof_eq_zero.1 (eq.symm h)) }
end

@[simp] theorem cof_eq_one_iff_is_succ {o} : cof.{u} o = 1 ↔ ∃ a, o = succ a :=
⟨induction_on o $ λ α r _ z, begin
  resetI,
  rcases cof_eq r with ⟨S, hl, e⟩, rw z at e,
  cases ne_zero_iff_nonempty.1 (by rw e; exact one_ne_zero) with a,
  refine ⟨typein r a, eq.symm $ quotient.sound
    ⟨rel_iso.of_surjective (rel_embedding.of_monotone _
      (λ x y, _)) (λ x, _)⟩⟩,
  { apply sum.rec; [exact subtype.val, exact λ _, a] },
  { rcases x with x|⟨⟨⟨⟩⟩⟩; rcases y with y|⟨⟨⟨⟩⟩⟩;
      simp [subrel, order.preimage, empty_relation],
    exact x.2 },
  { suffices : r x a ∨ ∃ (b : punit), ↑a = x, {simpa},
    rcases trichotomous_of r x a with h|h|h,
    { exact or.inl h },
    { exact or.inr ⟨punit.star, h.symm⟩ },
    { rcases hl x with ⟨a', aS, hn⟩,
      rw (_ : ↑a = a') at h, {exact absurd h hn},
      refine congr_arg subtype.val (_ : a = ⟨a', aS⟩),
      haveI := le_one_iff_subsingleton.1 (le_of_eq e),
      apply subsingleton.elim } }
end, λ ⟨a, e⟩, by simp [e]⟩

@[simp] theorem cof_add (a b : ordinal) : b ≠ 0 → cof (a + b) = cof b :=
induction_on a $ λ α r _, induction_on b $ λ β s _ b0, begin
  resetI,
  change cof (type _) = _,
  refine eq_of_forall_le_iff (λ c, _),
  rw [le_cof_type, le_cof_type],
  split; intros H S hS,
  { refine le_trans (H {a | sum.rec_on a (∅:set α) S} (λ a, _)) ⟨⟨_, _⟩⟩,
    { cases a with a b,
      { cases type_ne_zero_iff_nonempty.1 b0 with b,
        rcases hS b with ⟨b', bs, _⟩,
        exact ⟨sum.inr b', bs, by simp⟩ },
      { rcases hS b with ⟨b', bs, h⟩,
        exact ⟨sum.inr b', bs, by simp [h]⟩ } },
    { exact λ a, match a with ⟨sum.inr b, h⟩ := ⟨b, h⟩ end },
    { exact λ a b, match a, b with
        ⟨sum.inr a, h₁⟩, ⟨sum.inr b, h₂⟩, h := by congr; injection h
      end } },
  { refine le_trans (H (sum.inr ⁻¹' S) (λ a, _)) ⟨⟨_, _⟩⟩,
    { rcases hS (sum.inr a) with ⟨a'|b', bs, h⟩; simp at h,
      { cases h }, { exact ⟨b', bs, h⟩ } },
    { exact λ ⟨a, h⟩, ⟨_, h⟩ },
    { exact λ ⟨a, h₁⟩ ⟨b, h₂⟩ h,
        by injection h with h; congr; injection h } }
end

@[simp] theorem cof_cof (o : ordinal) : cof (cof o).ord= cof o :=
le_antisymm (le_trans (cof_le_card _) (by simp)) $
induction_on o $ λ α r _, by exactI
let ⟨S, hS, e₁⟩ := ord_cof_eq r,
    ⟨T, hT, e₂⟩ := cof_eq (subrel r S) in begin
  rw e₁ at e₂, rw ← e₂,
  refine le_trans (cof_type_le {a | ∃ h, (subtype.mk a h : S) ∈ T} (λ a, _)) ⟨⟨_, _⟩⟩,
  { rcases hS a with ⟨b, bS, br⟩,
    rcases hT ⟨b, bS⟩ with ⟨⟨c, cS⟩, cT, cs⟩,
    exact ⟨c, ⟨cS, cT⟩, is_order_connected.neg_trans cs br⟩ },
  { exact λ ⟨a, h⟩, ⟨⟨a, h.fst⟩, h.snd⟩ },
  { exact λ ⟨a, ha⟩ ⟨b, hb⟩ h,
      by injection h with h; congr; injection h },
end

theorem omega_le_cof {o} : cardinal.omega ≤ cof o ↔ is_limit o :=
begin
  rcases zero_or_succ_or_limit o with rfl|⟨o,rfl⟩|l,
  { simp [not_zero_is_limit, cardinal.omega_ne_zero] },
  { simp [not_succ_is_limit, cardinal.one_lt_omega] },
  { simp [l], refine le_of_not_lt (λ h, _),
    cases cardinal.lt_omega.1 h with n e,
    have := cof_cof o,
    rw [e, ord_nat] at this,
    cases n,
    { simp at e, simpa [e, not_zero_is_limit] using l },
    { rw [← nat_cast_succ, cof_succ] at this,
      rw [← this, cof_eq_one_iff_is_succ] at e,
      rcases e with ⟨a, rfl⟩,
      exact not_succ_is_limit _ l } }
end

@[simp] theorem cof_omega : cof omega = cardinal.omega :=
le_antisymm
  (by rw ← card_omega; apply cof_le_card)
  (omega_le_cof.2 omega_is_limit)

theorem cof_eq' (r : α → α → Prop) [is_well_order α r] (h : is_limit (type r)) :
  ∃ S : set α, (∀ a, ∃ b ∈ S, r a b) ∧ mk S = cof (type r) :=
let ⟨S, H, e⟩ := cof_eq r in
⟨S, λ a,
  let a' := enum r _ (h.2 _ (typein_lt_type r a)) in
  let ⟨b, h, ab⟩ := H a' in
  ⟨b, h, (is_order_connected.conn a b a' $ (typein_lt_typein r).1
    (by rw typein_enum; apply ordinal.lt_succ_self)).resolve_right ab⟩,
e⟩

theorem cof_sup_le_lift {ι} (f : ι → ordinal) (H : ∀ i, f i < sup f) :
  cof (sup f) ≤ (mk ι).lift :=
begin
  generalize e : sup f = o,
  refine ordinal.induction_on o _ e, introsI α r _ e',
  rw e' at H,
  refine le_trans (cof_type_le (set.range (λ i, enum r _ (H i))) _)
    ⟨embedding.of_surjective _ _⟩,
  { intro a, by_contra h,
    apply not_le_of_lt (typein_lt_type r a),
    rw [← e', sup_le],
    intro i,
    have h : ∀ (x : ι), r (enum r (f x) _) a, { simpa using h },
    simpa only [typein_enum] using le_of_lt ((typein_lt_typein r).2 (h i)) },
  { exact λ i, ⟨_, set.mem_range_self i.1⟩ },
  { intro a, rcases a with ⟨_, i, rfl⟩, exact ⟨⟨i⟩, by simp⟩ }
end

theorem cof_sup_le {ι} (f : ι → ordinal) (H : ∀ i, f i < sup.{u u} f) :
  cof (sup.{u u} f) ≤ mk ι :=
by simpa using cof_sup_le_lift.{u u} f H

theorem cof_bsup_le_lift {o : ordinal} : ∀ (f : Π a < o, ordinal), (∀ i h, f i h < bsup o f) →
  cof (bsup o f) ≤ o.card.lift :=
induction_on o $ λ α r _ f H,
by rw bsup_type; refine cof_sup_le_lift _ _;
   rw ← bsup_type; intro a; apply H

theorem cof_bsup_le {o : ordinal} : ∀ (f : Π a < o, ordinal), (∀ i h, f i h < bsup.{u u} o f) →
  cof (bsup.{u u} o f) ≤ o.card :=
induction_on o $ λ α r _ f H,
by simpa using cof_bsup_le_lift.{u u} f H

@[simp] theorem cof_univ : cof univ.{u v} = cardinal.univ :=
le_antisymm (cof_le_card _) begin
  refine le_of_forall_lt (λ c h, _),
  rcases lt_univ'.1 h with ⟨c, rfl⟩,
  rcases @cof_eq ordinal.{u} (<) _ with ⟨S, H, Se⟩,
  rw [univ, ← lift_cof, ← cardinal.lift_lift, cardinal.lift_lt, ← Se],
  refine lt_of_not_ge (λ h, _),
  cases cardinal.lift_down h with a e,
  refine quotient.induction_on a (λ α e, _) e,
  cases quotient.exact e with f,
  have f := equiv.ulift.symm.trans f,
  let g := λ a, (f a).1,
  let o := succ (sup.{u u} g),
  rcases H o with ⟨b, h, l⟩,
  refine l (lt_succ.2 _),
  rw ← show g (f.symm ⟨b, h⟩) = b, by dsimp [g]; simp,
  apply le_sup
end

theorem sup_lt_ord {ι} (f : ι → ordinal) {c : ordinal} (H1 : cardinal.mk ι < c.cof)
  (H2 : ∀ i, f i < c) : sup.{u u} f < c :=
begin
  apply lt_of_le_of_ne,
  { rw [sup_le], exact λ i, le_of_lt (H2 i) },
  rintro h, apply not_le_of_lt H1,
  simpa [sup_ord, H2, h] using cof_sup_le.{u} f
end

theorem sup_lt {ι} (f : ι → cardinal) {c : cardinal} (H1 : cardinal.mk ι < c.ord.cof)
  (H2 : ∀ i, f i < c) : cardinal.sup.{u u} f < c :=
by { rw [←ord_lt_ord, ←sup_ord], apply sup_lt_ord _ H1, intro i, rw ord_lt_ord, apply H2 }

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_sUnion (r : α → α → Prop) [wo : is_well_order α r] {s : set (set α)}
  (h₁ : unbounded r $ ⋃₀ s) (h₂ : mk s < strict_order.cof r) : ∃(x ∈ s), unbounded r x :=
begin
  by_contra h, simp only [not_exists, exists_prop, not_and, not_unbounded_iff] at h,
  apply not_le_of_lt h₂,
  let f : s → α := λ x : s, wo.wf.sup x (h x.1 x.2),
  let t : set α := range f,
  have : mk t ≤ mk s, exact mk_range_le, refine le_trans _ this,
  have : unbounded r t,
  { intro x, rcases h₁ x with ⟨y, ⟨c, hc, hy⟩, hxy⟩,
    refine ⟨f ⟨c, hc⟩, mem_range_self _, _⟩, intro hxz, apply hxy,
    refine trans (wo.wf.lt_sup _ hy) hxz },
  exact cardinal.min_le _ (subtype.mk t this)
end

/-- If the union of s is unbounded and s is smaller than the cofinality,
  then s has an unbounded member -/
theorem unbounded_of_unbounded_Union {α β : Type u} (r : α → α → Prop) [wo : is_well_order α r]
  (s : β → set α)
  (h₁ : unbounded r $ ⋃x, s x) (h₂ : mk β < strict_order.cof r) : ∃x : β, unbounded r (s x) :=
begin
  rw [← sUnion_range] at h₁,
  have : mk ↥(range (λ (i : β), s i)) < strict_order.cof r := lt_of_le_of_lt mk_range_le h₂,
  rcases unbounded_of_unbounded_sUnion r h₁ this with ⟨_, ⟨x, rfl⟩, u⟩, exact ⟨x, u⟩
end

/-- The infinite pigeonhole principle -/
theorem infinite_pigeonhole {β α : Type u} (f : β → α) (h₁ : cardinal.omega ≤ mk β)
  (h₂ : mk α < (mk β).ord.cof) : ∃a : α, mk (f ⁻¹' {a}) = mk β :=
begin
  have : ¬∀a, mk (f ⁻¹' {a}) < mk β,
  { intro h,
    apply not_lt_of_ge (ge_of_eq $ mk_univ),
    rw [←@preimage_univ _ _ f, ←Union_of_singleton, preimage_Union],
    apply lt_of_le_of_lt mk_Union_le_sum_mk,
    apply lt_of_le_of_lt (sum_le_sup _),
    apply mul_lt_of_lt h₁ (lt_of_lt_of_le h₂ $ cof_ord_le _),
    exact sup_lt _ h₂ h },
  rw [not_forall] at this, cases this with x h,
  use x, apply le_antisymm _ (le_of_not_gt h),
  rw [le_mk_iff_exists_set], exact ⟨_, rfl⟩
end

/-- pigeonhole principle for a cardinality below the cardinality of the domain -/
theorem infinite_pigeonhole_card {β α : Type u} (f : β → α) (θ : cardinal) (hθ : θ ≤ mk β)
  (h₁ : cardinal.omega ≤ θ) (h₂ : mk α < θ.ord.cof) : ∃a : α, θ ≤ mk (f ⁻¹' {a}) :=
begin
  rcases le_mk_iff_exists_set.1 hθ with ⟨s, rfl⟩,
  cases infinite_pigeonhole (f ∘ subtype.val : s → α) h₁ h₂ with a ha,
  use a, rw [←ha, @preimage_comp _ _ _ subtype.val f],
  apply mk_preimage_of_injective _ _ subtype.val_injective
end

theorem infinite_pigeonhole_set {β α : Type u} {s : set β} (f : s → α) (θ : cardinal)
  (hθ : θ ≤ mk s) (h₁ : cardinal.omega ≤ θ) (h₂ : mk α < θ.ord.cof) :
    ∃(a : α) (t : set β) (h : t ⊆ s), θ ≤ mk t ∧ ∀{{x}} (hx : x ∈ t), f ⟨x, h hx⟩ = a :=
begin
  cases infinite_pigeonhole_card f θ hθ h₁ h₂ with a ha,
  refine ⟨a, {x | ∃(h : x ∈ s), f ⟨x, h⟩ = a}, _, _, _⟩,
  { rintro x ⟨hx, hx'⟩, exact hx },
  { refine le_trans ha _, apply ge_of_eq, apply quotient.sound, constructor,
    refine equiv.trans _ (equiv.subtype_subtype_equiv_subtype_exists _ _).symm,
    simp only [set_coe_eq_subtype, mem_singleton_iff, mem_preimage, mem_set_of_eq] },
  rintro x ⟨hx, hx'⟩, exact hx'
end

end ordinal

namespace cardinal
open ordinal

local infixr ^ := @pow cardinal.{u} cardinal cardinal.has_pow

/-- A cardinal is a limit if it is not zero or a successor
  cardinal. Note that `ω` is a limit cardinal by this definition. -/
def is_limit (c : cardinal) : Prop :=
c ≠ 0 ∧ ∀ x < c, succ x < c

/-- A cardinal is a strong limit if it is not zero and it is
  closed under powersets. Note that `ω` is a strong limit by this definition. -/
def is_strong_limit (c : cardinal) : Prop :=
c ≠ 0 ∧ ∀ x < c, 2 ^ x < c

theorem is_strong_limit.is_limit {c} (H : is_strong_limit c) : is_limit c :=
⟨H.1, λ x h, lt_of_le_of_lt (succ_le.2 $ cantor _) (H.2 _ h)⟩

/-- A cardinal is regular if it is infinite and it equals its own cofinality. -/
def is_regular (c : cardinal) : Prop :=
omega ≤ c ∧ c.ord.cof = c

theorem cof_is_regular {o : ordinal} (h : o.is_limit) : is_regular o.cof :=
⟨omega_le_cof.2 h, cof_cof _⟩

theorem omega_is_regular : is_regular omega :=
⟨le_refl _, by simp⟩

theorem succ_is_regular {c : cardinal.{u}} (h : omega ≤ c) : is_regular (succ c) :=
⟨le_trans h (le_of_lt $ lt_succ_self _), begin
  refine le_antisymm (cof_ord_le _) (succ_le.2 _),
  cases quotient.exists_rep (succ c) with α αe, simp at αe,
  rcases ord_eq α with ⟨r, wo, re⟩, resetI,
  have := ord_is_limit (le_trans h $ le_of_lt $ lt_succ_self _),
  rw [← αe, re] at this ⊢,
  rcases cof_eq' r this with ⟨S, H, Se⟩,
  rw [← Se],
  apply lt_imp_lt_of_le_imp_le
    (λ (h : mk S ≤ c), canonically_ordered_semiring.mul_le_mul_right' h c),
  rw [mul_eq_self h, ← succ_le, ← αe, ← sum_const],
  refine le_trans _ (sum_le_sum (λ x:S, card (typein r x)) _ _),
  { simp [typein, sum_mk (λ x:S, {a//r a x})],
    refine ⟨embedding.of_surjective _ _⟩,
    { exact λ x, x.2.1 },
    { exact λ a, let ⟨b, h, ab⟩ := H a in ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩ } },
  { intro i,
    rw [← lt_succ, ← lt_ord, ← αe, re],
    apply typein_lt_type }
end⟩

/--
A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has a fiber with cardinality strictly great than the codomain.
-/
theorem infinite_pigeonhole_card_lt {β α : Type u} (f : β → α)
  (w : mk α < mk β) (w' : omega ≤ mk α) :
  ∃ a : α, mk α < mk (f ⁻¹' {a}) :=
begin
  simp_rw [← succ_le],
  exact ordinal.infinite_pigeonhole_card f (mk α).succ (succ_le.mpr w)
    (w'.trans (lt_succ_self _).le)
    ((lt_succ_self _).trans_le (succ_is_regular w').2.ge),
end

/--
A function whose codomain's cardinality is infinite but strictly smaller than its domain's
has an infinite fiber.
-/
theorem exists_infinite_fiber {β α : Type*} (f : β → α)
  (w : mk α < mk β) (w' : _root_.infinite α) :
  ∃ a : α, _root_.infinite (f ⁻¹' {a}) :=
begin
  simp_rw [cardinal.infinite_iff] at ⊢ w',
  cases infinite_pigeonhole_card_lt f w w' with a ha,
  exact ⟨a, w'.trans ha.le⟩,
end

/--
If an infinite type `β` can be expressed as a union of finite sets,
then the cardinality of the collection of those finite sets
must be at least the cardinality of `β`.
-/
lemma le_range_of_union_finset_eq_top
  {α β : Type*} [infinite β] (f : α → finset β) (w : (⋃ a, (f a : set β)) = ⊤) :
  mk β ≤ mk (range f) :=
begin
  have k : _root_.infinite (range f),
  { rw infinite_coe_iff,
    apply mt (union_finset_finite_of_range_finite f),
    rw w,
    exact infinite_univ, },
  by_contradiction h,
  simp only [not_le] at h,
  let u : Π b, ∃ a, b ∈ f a := λ b, by simpa using (w.ge : _) (set.mem_univ b),
  let u' : β → range f := λ b, ⟨f (u b).some, by simp⟩,
  have v' : ∀ a, u' ⁻¹' {⟨f a, by simp⟩} ≤ f a, begin rintros a p m,
    simp at m,
    rw ←m,
    apply (λ b, (u b).some_spec),
  end,
  obtain ⟨⟨-, ⟨a, rfl⟩⟩, p⟩ := exists_infinite_fiber u' h k,
  exact (@infinite.of_injective _ _ p (inclusion (v' a)) (inclusion_injective _)).false,
end

theorem sup_lt_ord_of_is_regular {ι} (f : ι → ordinal)
  {c} (hc : is_regular c) (H1 : cardinal.mk ι < c)
  (H2 : ∀ i, f i < c.ord) : ordinal.sup.{u u} f < c.ord :=
by { apply sup_lt_ord _ _ H2, rw [hc.2], exact H1 }

theorem sup_lt_of_is_regular {ι} (f : ι → cardinal)
  {c} (hc : is_regular c) (H1 : cardinal.mk ι < c)
  (H2 : ∀ i, f i < c) : sup.{u u} f < c :=
by { apply sup_lt _ _ H2, rwa [hc.2] }

theorem sum_lt_of_is_regular {ι} (f : ι → cardinal)
  {c} (hc : is_regular c) (H1 : cardinal.mk ι < c)
  (H2 : ∀ i, f i < c) : sum.{u u} f < c :=
lt_of_le_of_lt (sum_le_sup _) $ mul_lt_of_lt hc.1 H1 $
sup_lt_of_is_regular f hc H1 H2

/-- A cardinal is inaccessible if it is an uncountable regular strong limit cardinal. -/
def is_inaccessible (c : cardinal) :=
omega < c ∧ is_regular c ∧ is_strong_limit c

theorem is_inaccessible.mk {c}
 (h₁ : omega < c) (h₂ : c ≤ c.ord.cof) (h₃ : ∀ x < c, 2 ^ x < c) :
 is_inaccessible c :=
⟨h₁, ⟨le_of_lt h₁, le_antisymm (cof_ord_le _) h₂⟩,
  ne_of_gt (lt_trans omega_pos h₁), h₃⟩

/- Lean's foundations prove the existence of ω many inaccessible cardinals -/
theorem univ_inaccessible : is_inaccessible (univ.{u v}) :=
is_inaccessible.mk
  (by simpa using lift_lt_univ' omega)
  (by simp)
  (λ c h, begin
    rcases lt_univ'.1 h with ⟨c, rfl⟩,
    rw ← lift_two_power.{u (max (u+1) v)},
    apply lift_lt_univ'
  end)

theorem lt_power_cof {c : cardinal.{u}} : omega ≤ c → c < c ^ cof c.ord :=
quotient.induction_on c $ λ α h, begin
  rcases ord_eq α with ⟨r, wo, re⟩, resetI,
  have := ord_is_limit h,
  rw [mk_def, re] at this ⊢,
  rcases cof_eq' r this with ⟨S, H, Se⟩,
  have := sum_lt_prod (λ a:S, mk {x // r x a}) (λ _, mk α) (λ i, _),
  { simp [Se.symm] at this ⊢,
    refine lt_of_le_of_lt _ this,
    refine ⟨embedding.of_surjective _ _⟩,
    { exact λ x, x.2.1 },
    { exact λ a, let ⟨b, h, ab⟩ := H a in ⟨⟨⟨_, h⟩, _, ab⟩, rfl⟩ } },
  { have := typein_lt_type r i,
    rwa [← re, lt_ord] at this }
end

theorem lt_cof_power {a b : cardinal} (ha : omega ≤ a) (b1 : 1 < b) :
  a < cof (b ^ a).ord :=
begin
  have b0 : b ≠ 0 := ne_of_gt (lt_trans zero_lt_one b1),
  apply lt_imp_lt_of_le_imp_le (power_le_power_left $ power_ne_zero a b0),
  rw [← power_mul, mul_eq_self ha],
  exact lt_power_cof (le_trans ha $ le_of_lt $ cantor' _ b1),
end

end cardinal
