/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import set_theory.ordinal

/-!
# Ordinal arithmetic

Ordinals have an addition (corresponding to disjoint union) that turns them into an additive
monoid, and a multiplication (corresponding to the lexicographic order on the product) that turns
them into a monoid. One can also define correspondingly a subtraction, a division, a successor
function, a power function and a logarithm function.

We also define limit ordinals and prove the basic induction principle on ordinals separating
successor ordinals and limit ordinals, in `limit_rec_on`.

## Main definitions and results

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`.
* `o₁ - o₂` is the unique ordinal `o` such that `o₂ + o = o₁`, when `o₂ ≤ o₁`.
* `o₁ * o₂` is the lexicographic order on `o₂ × o₁`.
* `o₁ / o₂` is the ordinal `o` such that `o₁ = o₂ * o + o'` with `o' < o₂`. We also define the
  divisibility predicate, and a modulo operation.
* `succ o = o + 1` is the successor of `o`.
* `pred o` if the predecessor of `o`. If `o` is not a successor, we set `pred o = o`.

We also define the power function and the logarithm function on ordinals, and discuss the properties
of casts of natural numbers of and of `omega` with respect to these operations.

Some properties of the operations are also used to discuss general tools on ordinals:

* `is_limit o`: an ordinal is a limit ordinal if it is neither `0` nor a successor.
* `limit_rec_on` is the main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals.

* `is_normal`: a function `f : ordinal → ordinal` satisfies `is_normal` if it is strictly increasing
  and order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.
* `nfp f a`: the next fixed point of a function `f` on ordinals, above `a`. It behaves well
  for normal functions.

* `CNF b o` is the Cantor normal form of the ordinal `o` in base `b`.

* `sup`: the supremum of an indexed family of ordinals in `Type u`, as an ordinal in `Type u`.
* `bsup`: the supremum of a set of ordinals indexed by ordinals less than a given ordinal `o`.
-/

noncomputable theory

open function cardinal set equiv
open_locale classical cardinal

universes u v w
variables {α : Type*} {β : Type*} {γ : Type*}
  {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

namespace ordinal

/-! ### Further properties of addition on ordinals -/

@[simp] theorem lift_add (a b) : lift (a + b) = lift a + lift b :=
quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩,
quotient.sound ⟨(rel_iso.preimage equiv.ulift _).trans
 (rel_iso.sum_lex_congr (rel_iso.preimage equiv.ulift _)
   (rel_iso.preimage equiv.ulift _)).symm⟩

@[simp] theorem lift_succ (a) : lift (succ a) = succ (lift a) :=
by unfold succ; simp only [lift_add, lift_one]

theorem add_le_add_iff_left (a) {b c : ordinal} : a + b ≤ a + c ↔ b ≤ c :=
⟨induction_on a $ λ α r hr, induction_on b $ λ β₁ s₁ hs₁, induction_on c $ λ β₂ s₂ hs₂ ⟨f⟩, ⟨
  have fl : ∀ a, f (sum.inl a) = sum.inl a := λ a,
    by simpa only [initial_seg.trans_apply, initial_seg.le_add_apply]
      using @initial_seg.eq _ _ _ _ (@sum.lex.is_well_order _ _ _ _ hr hs₂)
        ((initial_seg.le_add r s₁).trans f) (initial_seg.le_add r s₂) a,
  have ∀ b, {b' // f (sum.inr b) = sum.inr b'}, begin
    intro b, cases e : f (sum.inr b),
    { rw ← fl at e, have := f.inj' e, contradiction },
    { exact ⟨_, rfl⟩ }
  end,
  let g (b) := (this b).1 in
  have fr : ∀ b, f (sum.inr b) = sum.inr (g b), from λ b, (this b).2,
  ⟨⟨⟨g, λ x y h, by injection f.inj'
    (by rw [fr, fr, h] : f (sum.inr x) = f (sum.inr y))⟩,
    λ a b, by simpa only [sum.lex_inr_inr, fr, rel_embedding.coe_fn_to_embedding,
        initial_seg.coe_fn_to_rel_embedding, function.embedding.coe_fn_mk]
      using @rel_embedding.map_rel_iff _ _ _ _ f.to_rel_embedding (sum.inr a) (sum.inr b)⟩,
    λ a b H, begin
      rcases f.init' (by rw fr; exact sum.lex_inr_inr.2 H) with ⟨a'|a', h⟩,
      { rw fl at h, cases h },
      { rw fr at h, exact ⟨a', sum.inr.inj h⟩ }
    end⟩⟩,
λ h, add_le_add_left h _⟩

theorem add_succ (o₁ o₂ : ordinal) : o₁ + succ o₂ = succ (o₁ + o₂) :=
(add_assoc _ _ _).symm

@[simp] theorem succ_zero : succ 0 = 1 := zero_add _

theorem one_le_iff_pos {o : ordinal} : 1 ≤ o ↔ 0 < o :=
by rw [← succ_zero, succ_le]

theorem one_le_iff_ne_zero {o : ordinal} : 1 ≤ o ↔ o ≠ 0 :=
by rw [one_le_iff_pos, ordinal.pos_iff_ne_zero]

theorem succ_pos (o : ordinal) : 0 < succ o :=
lt_of_le_of_lt (ordinal.zero_le _) (lt_succ_self _)

theorem succ_ne_zero (o : ordinal) : succ o ≠ 0 :=
ne_of_gt $ succ_pos o

@[simp] theorem card_succ (o : ordinal) : card (succ o) = card o + 1 :=
by simp only [succ, card_add, card_one]

theorem nat_cast_succ (n : ℕ) : (succ n : ordinal) = n.succ := rfl

theorem add_left_cancel (a) {b c : ordinal} : a + b = a + c ↔ b = c :=
by simp only [le_antisymm_iff, add_le_add_iff_left]

theorem lt_succ {a b : ordinal} : a < succ b ↔ a ≤ b :=
by rw [← not_le, succ_le, not_lt]

theorem add_lt_add_iff_left (a) {b c : ordinal} : a + b < a + c ↔ b < c :=
by rw [← not_le, ← not_le, add_le_add_iff_left]

theorem lt_of_add_lt_add_right {a b c : ordinal} : a + b < c + b → a < c :=
lt_imp_lt_of_le_imp_le (λ h, add_le_add_right h _)

@[simp] theorem succ_lt_succ {a b : ordinal} : succ a < succ b ↔ a < b :=
by rw [lt_succ, succ_le]

@[simp] theorem succ_le_succ {a b : ordinal} : succ a ≤ succ b ↔ a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 succ_lt_succ

theorem succ_inj {a b : ordinal} : succ a = succ b ↔ a = b :=
by simp only [le_antisymm_iff, succ_le_succ]

theorem add_le_add_iff_right {a b : ordinal} (n : ℕ) : a + n ≤ b + n ↔ a ≤ b :=
by induction n with n ih; [rw [nat.cast_zero, add_zero, add_zero],
  rw [← nat_cast_succ, add_succ, add_succ, succ_le_succ, ih]]

theorem add_right_cancel {a b : ordinal} (n : ℕ) : a + n = b + n ↔ a = b :=
by simp only [le_antisymm_iff, add_le_add_iff_right]

/-! ### The zero ordinal -/

@[simp] theorem card_eq_zero {o} : card o = 0 ↔ o = 0 :=
⟨induction_on o $ λ α r _ h, begin
  refine le_antisymm (le_of_not_lt $
    λ hn, ne_zero_iff_nonempty.2 _ h) (ordinal.zero_le _),
  rw [← succ_le, succ_zero] at hn, cases hn with f,
  exact ⟨f punit.star⟩
end, λ e, by simp only [e, card_zero]⟩

@[simp] theorem type_eq_zero_of_empty [is_well_order α r] [is_empty α] : type r = 0 :=
card_eq_zero.symm.mpr eq_zero_of_is_empty

@[simp] theorem type_eq_zero_iff_is_empty [is_well_order α r] : type r = 0 ↔ is_empty α :=
(@card_eq_zero (type r)).symm.trans eq_zero_iff_is_empty

theorem type_ne_zero_iff_nonempty [is_well_order α r] : type r ≠ 0 ↔ nonempty α :=
(not_congr (@card_eq_zero (type r))).symm.trans ne_zero_iff_nonempty

protected lemma one_ne_zero : (1 : ordinal) ≠ 0 :=
type_ne_zero_iff_nonempty.2 ⟨punit.star⟩

instance : nontrivial ordinal.{u} :=
⟨⟨1, 0, ordinal.one_ne_zero⟩⟩

theorem zero_lt_one : (0 : ordinal) < 1 :=
lt_iff_le_and_ne.2 ⟨ordinal.zero_le _, ne.symm $ ordinal.one_ne_zero⟩

/-! ### The predecessor of an ordinal -/

/-- The ordinal predecessor of `o` is `o'` if `o = succ o'`,
  and `o` otherwise. -/
def pred (o : ordinal.{u}) : ordinal.{u} :=
if h : ∃ a, o = succ a then classical.some h else o

@[simp] theorem pred_succ (o) : pred (succ o) = o :=
by have h : ∃ a, succ o = succ a := ⟨_, rfl⟩;
   simpa only [pred, dif_pos h] using (succ_inj.1 $ classical.some_spec h).symm

theorem pred_le_self (o) : pred o ≤ o :=
if h : ∃ a, o = succ a then let ⟨a, e⟩ := h in
by rw [e, pred_succ]; exact le_of_lt (lt_succ_self _)
else by rw [pred, dif_neg h]

theorem pred_eq_iff_not_succ {o} : pred o = o ↔ ¬ ∃ a, o = succ a :=
⟨λ e ⟨a, e'⟩, by rw [e', pred_succ] at e; exact ne_of_lt (lt_succ_self _) e,
 λ h, dif_neg h⟩

theorem pred_lt_iff_is_succ {o} : pred o < o ↔ ∃ a, o = succ a :=
iff.trans (by simp only [le_antisymm_iff, pred_le_self, true_and, not_le])
  (iff_not_comm.1 pred_eq_iff_not_succ).symm

theorem succ_pred_iff_is_succ {o} : succ (pred o) = o ↔ ∃ a, o = succ a :=
⟨λ e, ⟨_, e.symm⟩, λ ⟨a, e⟩, by simp only [e, pred_succ]⟩

theorem succ_lt_of_not_succ {o} (h : ¬ ∃ a, o = succ a) {b} : succ b < o ↔ b < o :=
⟨lt_trans (lt_succ_self _), λ l,
  lt_of_le_of_ne (succ_le.2 l) (λ e, h ⟨_, e.symm⟩)⟩

theorem lt_pred {a b} : a < pred b ↔ succ a < b :=
if h : ∃ a, b = succ a then let ⟨c, e⟩ := h in
by rw [e, pred_succ, succ_lt_succ]
else by simp only [pred, dif_neg h, succ_lt_of_not_succ h]

theorem pred_le {a b} : pred a ≤ b ↔ a ≤ succ b :=
le_iff_le_iff_lt_iff_lt.2 lt_pred

@[simp] theorem lift_is_succ {o} : (∃ a, lift o = succ a) ↔ (∃ a, o = succ a) :=
⟨λ ⟨a, h⟩,
  let ⟨b, e⟩ := lift_down $ show a ≤ lift o, from le_of_lt $
    h.symm ▸ lt_succ_self _ in
  ⟨b, lift_inj.1 $ by rw [h, ← e, lift_succ]⟩,
 λ ⟨a, h⟩, ⟨lift a, by simp only [h, lift_succ]⟩⟩

@[simp] theorem lift_pred (o) : lift (pred o) = pred (lift o) :=
if h : ∃ a, o = succ a then
by cases h with a e; simp only [e, pred_succ, lift_succ]
else by rw [pred_eq_iff_not_succ.2 h,
            pred_eq_iff_not_succ.2 (mt lift_is_succ.1 h)]

/-! ### Limit ordinals -/

/-- A limit ordinal is an ordinal which is not zero and not a successor. -/
def is_limit (o : ordinal) : Prop := o ≠ 0 ∧ ∀ a < o, succ a < o

theorem not_zero_is_limit : ¬ is_limit 0
| ⟨h, _⟩ := h rfl

theorem not_succ_is_limit (o) : ¬ is_limit (succ o)
| ⟨_, h⟩ := lt_irrefl _ (h _ (lt_succ_self _))

theorem not_succ_of_is_limit {o} (h : is_limit o) : ¬ ∃ a, o = succ a
| ⟨a, e⟩ := not_succ_is_limit a (e ▸ h)

theorem succ_lt_of_is_limit {o} (h : is_limit o) {a} : succ a < o ↔ a < o :=
⟨lt_trans (lt_succ_self _), h.2 _⟩

theorem le_succ_of_is_limit {o} (h : is_limit o) {a} : o ≤ succ a ↔ o ≤ a :=
le_iff_le_iff_lt_iff_lt.2 $ succ_lt_of_is_limit h

theorem limit_le {o} (h : is_limit o) {a} : o ≤ a ↔ ∀ x < o, x ≤ a :=
⟨λ h x l, le_trans (le_of_lt l) h,
 λ H, (le_succ_of_is_limit h).1 $ le_of_not_lt $ λ hn,
  not_lt_of_le (H _ hn) (lt_succ_self _)⟩

theorem lt_limit {o} (h : is_limit o) {a} : a < o ↔ ∃ x < o, a < x :=
by simpa only [not_ball, not_le] using not_congr (@limit_le _ h a)

@[simp] theorem lift_is_limit (o) : is_limit (lift o) ↔ is_limit o :=
and_congr (not_congr $ by simpa only [lift_zero] using @lift_inj o 0)
⟨λ H a h, lift_lt.1 $ by simpa only [lift_succ] using H _ (lift_lt.2 h),
 λ H a h, let ⟨a', e⟩ := lift_down (le_of_lt h) in
   by rw [← e, ← lift_succ, lift_lt];
      rw [← e, lift_lt] at h; exact H a' h⟩

theorem is_limit.pos {o : ordinal} (h : is_limit o) : 0 < o :=
lt_of_le_of_ne (ordinal.zero_le _) h.1.symm

theorem is_limit.one_lt {o : ordinal} (h : is_limit o) : 1 < o :=
by simpa only [succ_zero] using h.2 _ h.pos

theorem is_limit.nat_lt {o : ordinal} (h : is_limit o) : ∀ n : ℕ, (n : ordinal) < o
| 0     := h.pos
| (n+1) := h.2 _ (is_limit.nat_lt n)

theorem zero_or_succ_or_limit (o : ordinal) :
  o = 0 ∨ (∃ a, o = succ a) ∨ is_limit o :=
if o0 : o = 0 then or.inl o0 else
if h : ∃ a, o = succ a then or.inr (or.inl h) else
or.inr $ or.inr ⟨o0, λ a, (succ_lt_of_not_succ h).2⟩

/-- Main induction principle of ordinals: if one can prove a property by
  induction at successor ordinals and at limit ordinals, then it holds for all ordinals. -/
@[elab_as_eliminator] def limit_rec_on {C : ordinal → Sort*}
  (o : ordinal) (H₁ : C 0) (H₂ : ∀ o, C o → C (succ o))
  (H₃ : ∀ o, is_limit o → (∀ o' < o, C o') → C o) : C o :=
wf.fix (λ o IH,
  if o0 : o = 0 then by rw o0; exact H₁ else
  if h : ∃ a, o = succ a then
    by rw ← succ_pred_iff_is_succ.2 h; exact
    H₂ _ (IH _ $ pred_lt_iff_is_succ.2 h)
  else H₃ _ ⟨o0, λ a, (succ_lt_of_not_succ h).2⟩ IH) o

@[simp] theorem limit_rec_on_zero {C} (H₁ H₂ H₃) : @limit_rec_on C 0 H₁ H₂ H₃ = H₁ :=
by rw [limit_rec_on, well_founded.fix_eq, dif_pos rfl]; refl

@[simp] theorem limit_rec_on_succ {C} (o H₁ H₂ H₃) :
  @limit_rec_on C (succ o) H₁ H₂ H₃ = H₂ o (@limit_rec_on C o H₁ H₂ H₃) :=
begin
  have h : ∃ a, succ o = succ a := ⟨_, rfl⟩,
  rw [limit_rec_on, well_founded.fix_eq,
      dif_neg (succ_ne_zero o), dif_pos h],
  generalize : limit_rec_on._proof_2 (succ o) h = h₂,
  generalize : limit_rec_on._proof_3 (succ o) h = h₃,
  revert h₂ h₃, generalize e : pred (succ o) = o', intros,
  rw pred_succ at e, subst o', refl
end

@[simp] theorem limit_rec_on_limit {C} (o H₁ H₂ H₃ h) :
  @limit_rec_on C o H₁ H₂ H₃ = H₃ o h (λ x h, @limit_rec_on C x H₁ H₂ H₃) :=
by rw [limit_rec_on, well_founded.fix_eq,
       dif_neg h.1, dif_neg (not_succ_of_is_limit h)]; refl

lemma has_succ_of_is_limit {α} {r : α → α → Prop} [wo : is_well_order α r]
  (h : (type r).is_limit) (x : α) : ∃y, r x y :=
begin
  use enum r (typein r x).succ (h.2 _ (typein_lt_type r x)),
  convert (enum_lt (typein_lt_type r x) _).mpr (lt_succ_self _), rw [enum_typein]
end

lemma type_subrel_lt (o : ordinal.{u}) :
  type (subrel (<) {o' : ordinal | o' < o}) = ordinal.lift.{u u+1} o :=
begin
  refine quotient.induction_on o _,
  rintro ⟨α, r, wo⟩, resetI, apply quotient.sound,
  constructor, symmetry, refine (rel_iso.preimage equiv.ulift r).trans (typein_iso r)
end

lemma mk_initial_seg (o : ordinal.{u}) :
  #{o' : ordinal | o' < o} = cardinal.lift.{u u+1} o.card :=
by rw [lift_card, ←type_subrel_lt, card_type]

/-! ### Normal ordinal functions -/

/-- A normal ordinal function is a strictly increasing function which is
  order-continuous, i.e., the image `f o` of a limit ordinal `o` is the sup of `f a` for
  `a < o`.  -/
def is_normal (f : ordinal → ordinal) : Prop :=
(∀ o, f o < f (succ o)) ∧ ∀ o, is_limit o → ∀ a, f o ≤ a ↔ ∀ b < o, f b ≤ a

theorem is_normal.limit_le {f} (H : is_normal f) : ∀ {o}, is_limit o →
  ∀ {a}, f o ≤ a ↔ ∀ b < o, f b ≤ a := H.2

theorem is_normal.limit_lt {f} (H : is_normal f) {o} (h : is_limit o) {a} :
  a < f o ↔ ∃ b < o, a < f b :=
not_iff_not.1 $ by simpa only [exists_prop, not_exists, not_and, not_lt] using H.2 _ h a

theorem is_normal.lt_iff {f} (H : is_normal f) {a b} : f a < f b ↔ a < b :=
strict_mono.lt_iff_lt $ λ a b,
limit_rec_on b (not.elim (not_lt_of_le $ ordinal.zero_le _))
  (λ b IH h, (lt_or_eq_of_le (lt_succ.1 h)).elim
    (λ h, lt_trans (IH h) (H.1 _))
    (λ e, e ▸ H.1 _))
  (λ b l IH h, lt_of_lt_of_le (H.1 a)
    ((H.2 _ l _).1 (le_refl _) _ (l.2 _ h)))

theorem is_normal.le_iff {f} (H : is_normal f) {a b} : f a ≤ f b ↔ a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 H.lt_iff

theorem is_normal.inj {f} (H : is_normal f) {a b} : f a = f b ↔ a = b :=
by simp only [le_antisymm_iff, H.le_iff]

theorem is_normal.le_self {f} (H : is_normal f) (a) : a ≤ f a :=
limit_rec_on a (ordinal.zero_le _)
  (λ a IH, succ_le.2 $ lt_of_le_of_lt IH (H.1 _))
  (λ a l IH, (limit_le l).2 $ λ b h,
    le_trans (IH b h) $ H.le_iff.2 $ le_of_lt h)

theorem is_normal.le_set {f} (H : is_normal f) (p : ordinal → Prop)
  (p0 : ∃ x, p x) (S)
  (H₂ : ∀ o, S ≤ o ↔ ∀ a, p a → a ≤ o) {o} :
  f S ≤ o ↔ ∀ a, p a → f a ≤ o :=
⟨λ h a pa, le_trans (H.le_iff.2 ((H₂ _).1 (le_refl _) _ pa)) h,
λ h, begin
  revert H₂, apply limit_rec_on S,
  { intro H₂,
     cases p0 with x px,
     have := ordinal.le_zero.1 ((H₂ _).1 (ordinal.zero_le _) _ px),
     rw this at px, exact h _ px },
  { intros S _ H₂,
    rcases not_ball.1 (mt (H₂ S).2 $ not_le_of_lt $ lt_succ_self _) with ⟨a, h₁, h₂⟩,
    exact le_trans (H.le_iff.2 $ succ_le.2 $ not_le.1 h₂) (h _ h₁) },
  { intros S L _ H₂, apply (H.2 _ L _).2, intros a h',
    rcases not_ball.1 (mt (H₂ a).2 (not_le.2 h')) with ⟨b, h₁, h₂⟩,
    exact le_trans (H.le_iff.2 $ le_of_lt $ not_le.1 h₂) (h _ h₁) }
end⟩

theorem is_normal.le_set' {f} (H : is_normal f) (p : α → Prop) (g : α → ordinal)
  (p0 : ∃ x, p x) (S)
  (H₂ : ∀ o, S ≤ o ↔ ∀ a, p a → g a ≤ o) {o} :
  f S ≤ o ↔ ∀ a, p a → f (g a) ≤ o :=
(H.le_set (λ x, ∃ y, p y ∧ x = g y)
  (let ⟨x, px⟩ := p0 in ⟨_, _, px, rfl⟩) _
  (λ o, (H₂ o).trans ⟨λ H a ⟨y, h1, h2⟩, h2.symm ▸ H y h1,
    λ H a h1, H (g a) ⟨a, h1, rfl⟩⟩)).trans
⟨λ H a h, H (g a) ⟨a, h, rfl⟩, λ H a ⟨y, h1, h2⟩, h2.symm ▸ H y h1⟩

theorem is_normal.refl : is_normal id :=
⟨λ x, lt_succ_self _, λ o l a, limit_le l⟩

theorem is_normal.trans {f g} (H₁ : is_normal f) (H₂ : is_normal g) :
  is_normal (λ x, f (g x)) :=
⟨λ x, H₁.lt_iff.2 (H₂.1 _),
 λ o l a, H₁.le_set' (< o) g ⟨_, l.pos⟩ _ (λ c, H₂.2 _ l _)⟩

theorem is_normal.is_limit {f} (H : is_normal f) {o} (l : is_limit o) :
  is_limit (f o) :=
⟨ne_of_gt $ lt_of_le_of_lt (ordinal.zero_le _) $ H.lt_iff.2 l.pos,
λ a h, let ⟨b, h₁, h₂⟩ := (H.limit_lt l).1 h in
  lt_of_le_of_lt (succ_le.2 h₂) (H.lt_iff.2 h₁)⟩

theorem add_le_of_limit {a b c : ordinal.{u}}
  (h : is_limit b) : a + b ≤ c ↔ ∀ b' < b, a + b' ≤ c :=
⟨λ h b' l, le_trans (add_le_add_left (le_of_lt l) _) h,
λ H, le_of_not_lt $
induction_on a (λ α r _, induction_on b $ λ β s _ h H l, begin
  resetI,
  suffices : ∀ x : β, sum.lex r s (sum.inr x) (enum _ _ l),
  { cases enum _ _ l with x x,
    { cases this (enum s 0 h.pos) },
    { exact irrefl _ (this _) } },
  intros x,
  rw [← typein_lt_typein (sum.lex r s), typein_enum],
  have := H _ (h.2 _ (typein_lt_type s x)),
  rw [add_succ, succ_le] at this,
  refine lt_of_le_of_lt (type_le'.2
    ⟨rel_embedding.of_monotone (λ a, _) (λ a b, _)⟩) this,
  { rcases a with ⟨a | b, h⟩,
    { exact sum.inl a },
    { exact sum.inr ⟨b, by cases h; assumption⟩ } },
  { rcases a with ⟨a | a, h₁⟩; rcases b with ⟨b | b, h₂⟩; cases h₁; cases h₂;
      rintro ⟨⟩; constructor; assumption }
end) h H⟩

theorem add_is_normal (a : ordinal) : is_normal ((+) a) :=
⟨λ b, (add_lt_add_iff_left a).2 (lt_succ_self _),
 λ b l c, add_le_of_limit l⟩

theorem add_is_limit (a) {b} : is_limit b → is_limit (a + b) :=
(add_is_normal a).is_limit

/-! ### Subtraction on ordinals-/

/-- `a - b` is the unique ordinal satisfying
  `b + (a - b) = a` when `b ≤ a`. -/
def sub (a b : ordinal.{u}) : ordinal.{u} :=
omin {o | a ≤ b+o} ⟨a, le_add_left _ _⟩

instance : has_sub ordinal := ⟨sub⟩

theorem le_add_sub (a b : ordinal) : a ≤ b + (a - b) :=
omin_mem {o | a ≤ b+o} _

theorem sub_le {a b c : ordinal} : a - b ≤ c ↔ a ≤ b + c :=
⟨λ h, le_trans (le_add_sub a b) (add_le_add_left h _),
 λ h, omin_le h⟩

theorem lt_sub {a b c : ordinal} : a < b - c ↔ c + a < b :=
lt_iff_lt_of_le_iff_le sub_le

theorem add_sub_cancel (a b : ordinal) : a + b - a = b :=
le_antisymm (sub_le.2 $ le_refl _)
  ((add_le_add_iff_left a).1 $ le_add_sub _ _)

theorem sub_eq_of_add_eq {a b c : ordinal} (h : a + b = c) : c - a = b :=
h ▸ add_sub_cancel _ _

theorem sub_le_self (a b : ordinal) : a - b ≤ a :=
sub_le.2 $ le_add_left _ _

theorem add_sub_cancel_of_le {a b : ordinal} (h : b ≤ a) : b + (a - b) = a :=
le_antisymm begin
  rcases zero_or_succ_or_limit (a-b) with e|⟨c,e⟩|l,
  { simp only [e, add_zero, h] },
  { rw [e, add_succ, succ_le, ← lt_sub, e], apply lt_succ_self },
  { exact (add_le_of_limit l).2 (λ c l, le_of_lt (lt_sub.1 l)) }
end (le_add_sub _ _)

@[simp] theorem sub_zero (a : ordinal) : a - 0 = a :=
by simpa only [zero_add] using add_sub_cancel 0 a

@[simp] theorem zero_sub (a : ordinal) : 0 - a = 0 :=
by rw ← ordinal.le_zero; apply sub_le_self

@[simp] theorem sub_self (a : ordinal) : a - a = 0 :=
by simpa only [add_zero] using add_sub_cancel a 0

theorem sub_eq_zero_iff_le {a b : ordinal} : a - b = 0 ↔ a ≤ b :=
⟨λ h, by simpa only [h, add_zero] using le_add_sub a b,
 λ h, by rwa [← ordinal.le_zero, sub_le, add_zero]⟩

theorem sub_sub (a b c : ordinal) : a - b - c = a - (b + c) :=
eq_of_forall_ge_iff $ λ d, by rw [sub_le, sub_le, sub_le, add_assoc]

theorem add_sub_add_cancel (a b c : ordinal) : a + b - (a + c) = b - c :=
by rw [← sub_sub, add_sub_cancel]

theorem sub_is_limit {a b} (l : is_limit a) (h : b < a) : is_limit (a - b) :=
⟨ne_of_gt $ lt_sub.2 $ by rwa add_zero,
 λ c h, by rw [lt_sub, add_succ]; exact l.2 _ (lt_sub.1 h)⟩

@[simp] theorem one_add_omega : 1 + omega.{u} = omega :=
begin
  refine le_antisymm _ (le_add_left _ _),
  rw [omega, one_eq_lift_type_unit, ← lift_add, lift_le, type_add],
  have : is_well_order unit empty_relation := by apply_instance,
  refine ⟨rel_embedding.collapse (rel_embedding.of_monotone _ _)⟩,
  { apply sum.rec, exact λ _, 0, exact nat.succ },
  { intros a b, cases a; cases b; intro H; cases H with _ _ H _ _ H;
    [cases H, exact nat.succ_pos _, exact nat.succ_lt_succ H] }
end

@[simp, priority 990]
theorem one_add_of_omega_le {o} (h : omega ≤ o) : 1 + o = o :=
by rw [← add_sub_cancel_of_le h, ← add_assoc, one_add_omega]

/-! ### Multiplication of ordinals-/

/-- The multiplication of ordinals `o₁` and `o₂` is the (well founded) lexicographic order on
`o₂ × o₁`. -/
instance : monoid ordinal.{u} :=
{ mul := λ a b, quotient.lift_on₂ a b
      (λ ⟨α, r, wo⟩ ⟨β, s, wo'⟩, ⟦⟨β × α, prod.lex s r, by exactI prod.lex.is_well_order⟩⟧
        : Well_order → Well_order → ordinal) $
    λ ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩,
    quot.sound ⟨rel_iso.prod_lex_congr g f⟩,
  one := 1,
  mul_assoc := λ a b c, quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩,
    eq.symm $ quotient.sound ⟨⟨prod_assoc _ _ _, λ a b, begin
      rcases a with ⟨⟨a₁, a₂⟩, a₃⟩,
      rcases b with ⟨⟨b₁, b₂⟩, b₃⟩,
      simp [prod.lex_def, and_or_distrib_left, or_assoc, and_assoc]
    end⟩⟩,
  mul_one := λ a, induction_on a $ λ α r _, quotient.sound
    ⟨⟨punit_prod _, λ a b, by rcases a with ⟨⟨⟨⟩⟩, a⟩; rcases b with ⟨⟨⟨⟩⟩, b⟩;
    simp only [prod.lex_def, empty_relation, false_or];
    simp only [eq_self_iff_true, true_and]; refl⟩⟩,
  one_mul := λ a, induction_on a $ λ α r _, quotient.sound
    ⟨⟨prod_punit _, λ a b, by rcases a with ⟨a, ⟨⟨⟩⟩⟩; rcases b with ⟨b, ⟨⟨⟩⟩⟩;
    simp only [prod.lex_def, empty_relation, and_false, or_false]; refl⟩⟩ }

@[simp] theorem type_mul {α β : Type u} (r : α → α → Prop) (s : β → β → Prop)
  [is_well_order α r] [is_well_order β s] : type r * type s = type (prod.lex s r) := rfl

@[simp] theorem lift_mul (a b) : lift (a * b) = lift a * lift b :=
quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩,
quotient.sound ⟨(rel_iso.preimage equiv.ulift _).trans
 (rel_iso.prod_lex_congr (rel_iso.preimage equiv.ulift _)
   (rel_iso.preimage equiv.ulift _)).symm⟩

@[simp] theorem card_mul (a b) : card (a * b) = card a * card b :=
quotient.induction_on₂ a b $ λ ⟨α, r, _⟩ ⟨β, s, _⟩,
mul_comm (mk β) (mk α)

@[simp] theorem mul_zero (a : ordinal) : a * 0 = 0 :=
induction_on a $ λ α _ _, by exactI type_eq_zero_of_empty

@[simp] theorem zero_mul (a : ordinal) : 0 * a = 0 :=
induction_on a $ λ α _ _, by exactI type_eq_zero_of_empty

theorem mul_add (a b c : ordinal) : a * (b + c) = a * b + a * c :=
quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩,
quotient.sound ⟨⟨sum_prod_distrib _ _ _, begin
  rintro ⟨a₁|a₁, a₂⟩ ⟨b₁|b₁, b₂⟩; simp only [prod.lex_def,
    sum.lex_inl_inl, sum.lex.sep, sum.lex_inr_inl, sum.lex_inr_inr,
    sum_prod_distrib_apply_left, sum_prod_distrib_apply_right];
  simp only [sum.inl.inj_iff, true_or, false_and, false_or]
end⟩⟩

@[simp] theorem mul_add_one (a b : ordinal) : a * (b + 1) = a * b + a :=
by simp only [mul_add, mul_one]

@[simp] theorem mul_succ (a b : ordinal) : a * succ b = a * b + a := mul_add_one _ _

theorem mul_le_mul_left {a b} (c : ordinal) : a ≤ b → c * a ≤ c * b :=
quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩, begin
  resetI,
  refine type_le'.2 ⟨rel_embedding.of_monotone
    (λ a, (f a.1, a.2))
    (λ a b h, _)⟩, clear_,
  cases h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h',
  { exact prod.lex.left _ _ (f.to_rel_embedding.map_rel_iff.2 h') },
  { exact prod.lex.right _ h' }
end

theorem mul_le_mul_right {a b} (c : ordinal) : a ≤ b → a * c ≤ b * c :=
quotient.induction_on₃ a b c $ λ ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩, begin
  resetI,
  refine type_le'.2 ⟨rel_embedding.of_monotone
    (λ a, (a.1, f a.2))
    (λ a b h, _)⟩,
  cases h with a₁ b₁ a₂ b₂ h' a b₁ b₂ h',
  { exact prod.lex.left _ _ h' },
  { exact prod.lex.right _ (f.to_rel_embedding.map_rel_iff.2 h') }
end

theorem mul_le_mul {a b c d : ordinal} (h₁ : a ≤ c) (h₂ : b ≤ d) : a * b ≤ c * d :=
le_trans (mul_le_mul_left _ h₂) (mul_le_mul_right _ h₁)

private lemma mul_le_of_limit_aux {α β r s} [is_well_order α r] [is_well_order β s]
  {c} (h : is_limit (type s)) (H : ∀ b' < type s, type r * b' ≤ c)
  (l : c < type r * type s) : false :=
begin
  suffices : ∀ a b, prod.lex s r (b, a) (enum _ _ l),
  { cases enum _ _ l with b a, exact irrefl _ (this _ _) },
  intros a b,
  rw [← typein_lt_typein (prod.lex s r), typein_enum],
  have := H _ (h.2 _ (typein_lt_type s b)),
  rw [mul_succ] at this,
  have := lt_of_lt_of_le ((add_lt_add_iff_left _).2
    (typein_lt_type _ a)) this,
  refine lt_of_le_of_lt _ this,
  refine (type_le'.2 _),
  constructor,
  refine rel_embedding.of_monotone (λ a, _) (λ a b, _),
  { rcases a with ⟨⟨b', a'⟩, h⟩,
    by_cases e : b = b',
    { refine sum.inr ⟨a', _⟩,
      subst e, cases h with _ _ _ _ h _ _ _ h,
      { exact (irrefl _ h).elim },
      { exact h } },
    { refine sum.inl (⟨b', _⟩, a'),
      cases h with _ _ _ _ h _ _ _ h,
      { exact h }, { exact (e rfl).elim } } },
  { rcases a with ⟨⟨b₁, a₁⟩, h₁⟩,
    rcases b with ⟨⟨b₂, a₂⟩, h₂⟩,
    intro h, by_cases e₁ : b = b₁; by_cases e₂ : b = b₂,
    { substs b₁ b₂,
      simpa only [subrel_val, prod.lex_def, @irrefl _ s _ b, true_and, false_or, eq_self_iff_true,
        dif_pos, sum.lex_inr_inr] using h },
    { subst b₁,
      simp only [subrel_val, prod.lex_def, e₂, prod.lex_def, dif_pos, subrel_val, eq_self_iff_true,
        or_false, dif_neg, not_false_iff, sum.lex_inr_inl, false_and] at h ⊢,
      cases h₂; [exact asymm h h₂_h, exact e₂ rfl] },
    { simp only [e₂, dif_pos, eq_self_iff_true, dif_neg e₁, not_false_iff, sum.lex.sep] },
    { simpa only [dif_neg e₁, dif_neg e₂, prod.lex_def, subrel_val, subtype.mk_eq_mk,
        sum.lex_inl_inl] using h } }
end

theorem mul_le_of_limit {a b c : ordinal.{u}}
  (h : is_limit b) : a * b ≤ c ↔ ∀ b' < b, a * b' ≤ c :=
⟨λ h b' l, le_trans (mul_le_mul_left _ (le_of_lt l)) h,
λ H, le_of_not_lt $ induction_on a (λ α r _, induction_on b $ λ β s _,
  by exactI mul_le_of_limit_aux) h H⟩

theorem mul_is_normal {a : ordinal} (h : 0 < a) : is_normal ((*) a) :=
⟨λ b, by rw mul_succ; simpa only [add_zero] using (add_lt_add_iff_left (a*b)).2 h,
 λ b l c, mul_le_of_limit l⟩

theorem lt_mul_of_limit {a b c : ordinal.{u}}
  (h : is_limit c) : a < b * c ↔ ∃ c' < c, a < b * c' :=
by simpa only [not_ball, not_le] using not_congr (@mul_le_of_limit b c a h)

theorem mul_lt_mul_iff_left {a b c : ordinal} (a0 : 0 < a) : a * b < a * c ↔ b < c :=
(mul_is_normal a0).lt_iff

theorem mul_le_mul_iff_left {a b c : ordinal} (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
(mul_is_normal a0).le_iff

theorem mul_lt_mul_of_pos_left {a b c : ordinal}
  (h : a < b) (c0 : 0 < c) : c * a < c * b :=
(mul_lt_mul_iff_left c0).2 h

theorem mul_pos {a b : ordinal} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b :=
by simpa only [mul_zero] using mul_lt_mul_of_pos_left h₂ h₁

theorem mul_ne_zero {a b : ordinal} : a ≠ 0 → b ≠ 0 → a * b ≠ 0 :=
by simpa only [ordinal.pos_iff_ne_zero] using mul_pos

theorem le_of_mul_le_mul_left {a b c : ordinal}
  (h : c * a ≤ c * b) (h0 : 0 < c) : a ≤ b :=
le_imp_le_of_lt_imp_lt (λ h', mul_lt_mul_of_pos_left h' h0) h

theorem mul_right_inj {a b c : ordinal} (a0 : 0 < a) : a * b = a * c ↔ b = c :=
(mul_is_normal a0).inj

theorem mul_is_limit {a b : ordinal}
  (a0 : 0 < a) : is_limit b → is_limit (a * b) :=
(mul_is_normal a0).is_limit

theorem mul_is_limit_left {a b : ordinal}
  (l : is_limit a) (b0 : 0 < b) : is_limit (a * b) :=
begin
  rcases zero_or_succ_or_limit b with rfl|⟨b,rfl⟩|lb,
  { exact (lt_irrefl _).elim b0 },
  { rw mul_succ, exact add_is_limit _ l },
  { exact mul_is_limit l.pos lb }
end

/-! ### Division on ordinals -/

protected lemma div_aux (a b : ordinal.{u}) (h : b ≠ 0) : set.nonempty {o | a < b * succ o} :=
⟨a, succ_le.1 $
  by simpa only [succ_zero, one_mul]
    using mul_le_mul_right (succ a) (succ_le.2 (ordinal.pos_iff_ne_zero.2 h))⟩

/-- `a / b` is the unique ordinal `o` satisfying
  `a = b * o + o'` with `o' < b`. -/
protected def div (a b : ordinal.{u}) : ordinal.{u} :=
if h : b = 0 then 0 else omin {o | a < b * succ o} (ordinal.div_aux a b h)

instance : has_div ordinal := ⟨ordinal.div⟩

@[simp] theorem div_zero (a : ordinal) : a / 0 = 0 := dif_pos rfl

lemma div_def (a) {b : ordinal} (h : b ≠ 0) :
  a / b = omin {o | a < b * succ o} (ordinal.div_aux a b h) := dif_neg h

theorem lt_mul_succ_div (a) {b : ordinal} (h : b ≠ 0) : a < b * succ (a / b) :=
by rw div_def a h; exact omin_mem {o | a < b * succ o} _

theorem lt_mul_div_add (a) {b : ordinal} (h : b ≠ 0) : a < b * (a / b) + b :=
by simpa only [mul_succ] using lt_mul_succ_div a h

theorem div_le {a b c : ordinal} (b0 : b ≠ 0) : a / b ≤ c ↔ a < b * succ c :=
⟨λ h, lt_of_lt_of_le (lt_mul_succ_div a b0) (mul_le_mul_left _ $ succ_le_succ.2 h),
 λ h, by rw div_def a b0; exact omin_le h⟩

theorem lt_div {a b c : ordinal} (c0 : c ≠ 0) : a < b / c ↔ c * succ a ≤ b :=
by rw [← not_le, div_le c0, not_lt]

theorem le_div {a b c : ordinal} (c0 : c ≠ 0) :
  a ≤ b / c ↔ c * a ≤ b :=
begin
  apply limit_rec_on a,
  { simp only [mul_zero, ordinal.zero_le] },
  { intros, rw [succ_le, lt_div c0] },
  { simp only [mul_le_of_limit, limit_le, iff_self, forall_true_iff] {contextual := tt} }
end

theorem div_lt {a b c : ordinal} (b0 : b ≠ 0) :
  a / b < c ↔ a < b * c :=
lt_iff_lt_of_le_iff_le $ le_div b0

theorem div_le_of_le_mul {a b c : ordinal} (h : a ≤ b * c) : a / b ≤ c :=
if b0 : b = 0 then by simp only [b0, div_zero, ordinal.zero_le] else
(div_le b0).2 $ lt_of_le_of_lt h $
mul_lt_mul_of_pos_left (lt_succ_self _) (ordinal.pos_iff_ne_zero.2 b0)

theorem mul_lt_of_lt_div {a b c : ordinal} : a < b / c → c * a < b :=
lt_imp_lt_of_le_imp_le div_le_of_le_mul

@[simp] theorem zero_div (a : ordinal) : 0 / a = 0 :=
ordinal.le_zero.1 $ div_le_of_le_mul $ ordinal.zero_le _

theorem mul_div_le (a b : ordinal) : b * (a / b) ≤ a :=
if b0 : b = 0 then by simp only [b0, zero_mul, ordinal.zero_le] else (le_div b0).1 (le_refl _)

theorem mul_add_div (a) {b : ordinal} (b0 : b ≠ 0) (c) : (b * a + c) / b = a + c / b :=
begin
  apply le_antisymm,
  { apply (div_le b0).2,
    rw [mul_succ, mul_add, add_assoc, add_lt_add_iff_left],
    apply lt_mul_div_add _ b0 },
  { rw [le_div b0, mul_add, add_le_add_iff_left],
    apply mul_div_le }
end

theorem div_eq_zero_of_lt {a b : ordinal} (h : a < b) : a / b = 0 :=
begin
  rw [← ordinal.le_zero, div_le $ ordinal.pos_iff_ne_zero.1 $ lt_of_le_of_lt (ordinal.zero_le _) h],
  simpa only [succ_zero, mul_one] using h
end

@[simp] theorem mul_div_cancel (a) {b : ordinal} (b0 : b ≠ 0) : b * a / b = a :=
by simpa only [add_zero, zero_div] using mul_add_div a b0 0

@[simp] theorem div_one (a : ordinal) : a / 1 = a :=
by simpa only [one_mul] using mul_div_cancel a ordinal.one_ne_zero

@[simp] theorem div_self {a : ordinal} (h : a ≠ 0) : a / a = 1 :=
by simpa only [mul_one] using mul_div_cancel 1 h

theorem mul_sub (a b c : ordinal) : a * (b - c) = a * b - a * c :=
if a0 : a = 0 then by simp only [a0, zero_mul, sub_self] else
eq_of_forall_ge_iff $ λ d,
by rw [sub_le, ← le_div a0, sub_le, ← le_div a0, mul_add_div _ a0]

theorem is_limit_add_iff {a b} : is_limit (a + b) ↔ is_limit b ∨ (b = 0 ∧ is_limit a) :=
begin
  split; intro h,
  { by_cases h' : b = 0,
    { rw [h', add_zero] at h, right, exact ⟨h', h⟩ },
      left, rw [←add_sub_cancel a b], apply sub_is_limit h,
      suffices : a + 0 < a + b, simpa only [add_zero],
      rwa [add_lt_add_iff_left, ordinal.pos_iff_ne_zero] },
  rcases h with h|⟨rfl, h⟩, exact add_is_limit a h, simpa only [add_zero]
end

theorem dvd_add_iff : ∀ {a b c : ordinal}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
| a _ c ⟨b, rfl⟩ :=
 ⟨λ ⟨d, e⟩, ⟨d - b, by rw [mul_sub, ← e, add_sub_cancel]⟩,
  λ ⟨d, e⟩, by { rw [e, ← mul_add], apply dvd_mul_right }⟩

theorem dvd_add {a b c : ordinal} (h₁ : a ∣ b) : a ∣ c → a ∣ b + c :=
(dvd_add_iff h₁).2

theorem dvd_zero (a : ordinal) : a ∣ 0 := ⟨_, (mul_zero _).symm⟩

theorem zero_dvd {a : ordinal} : 0 ∣ a ↔ a = 0 :=
⟨λ ⟨h, e⟩, by simp only [e, zero_mul], λ e, e.symm ▸ dvd_zero _⟩

theorem one_dvd (a : ordinal) : 1 ∣ a := ⟨a, (one_mul _).symm⟩

theorem div_mul_cancel : ∀ {a b : ordinal}, a ≠ 0 → a ∣ b → a * (b / a) = b
| a _ a0 ⟨b, rfl⟩ := by rw [mul_div_cancel _ a0]

theorem le_of_dvd : ∀ {a b : ordinal}, b ≠ 0 → a ∣ b → a ≤ b
| a _ b0 ⟨b, rfl⟩ := by simpa only [mul_one] using mul_le_mul_left a
  (one_le_iff_ne_zero.2 (λ h : b = 0, by simpa only [h, mul_zero] using b0))

theorem dvd_antisymm {a b : ordinal} (h₁ : a ∣ b) (h₂ : b ∣ a) : a = b :=
if a0 : a = 0 then by subst a; exact (zero_dvd.1 h₁).symm else
if b0 : b = 0 then by subst b; exact zero_dvd.1 h₂ else
le_antisymm (le_of_dvd b0 h₁) (le_of_dvd a0 h₂)

/-- `a % b` is the unique ordinal `o'` satisfying
  `a = b * o + o'` with `o' < b`. -/
instance : has_mod ordinal := ⟨λ a b, a - b * (a / b)⟩

theorem mod_def (a b : ordinal) : a % b = a - b * (a / b) := rfl

@[simp] theorem mod_zero (a : ordinal) : a % 0 = a :=
by simp only [mod_def, div_zero, zero_mul, sub_zero]

theorem mod_eq_of_lt {a b : ordinal} (h : a < b) : a % b = a :=
by simp only [mod_def, div_eq_zero_of_lt h, mul_zero, sub_zero]

@[simp] theorem zero_mod (b : ordinal) : 0 % b = 0 :=
by simp only [mod_def, zero_div, mul_zero, sub_self]

theorem div_add_mod (a b : ordinal) : b * (a / b) + a % b = a :=
add_sub_cancel_of_le $ mul_div_le _ _

theorem mod_lt (a) {b : ordinal} (h : b ≠ 0) : a % b < b :=
(add_lt_add_iff_left (b * (a / b))).1 $
by rw div_add_mod; exact lt_mul_div_add a h

@[simp] theorem mod_self (a : ordinal) : a % a = 0 :=
if a0 : a = 0 then by simp only [a0, zero_mod] else
by simp only [mod_def, div_self a0, mul_one, sub_self]

@[simp] theorem mod_one (a : ordinal) : a % 1 = 0 :=
by simp only [mod_def, div_one, one_mul, sub_self]

/-! ### Supremum of a family of ordinals -/

/-- The supremum of a family of ordinals -/
def sup {ι} (f : ι → ordinal) : ordinal :=
omin {c | ∀ i, f i ≤ c}
  ⟨(sup (cardinal.succ ∘ card ∘ f)).ord, λ i, le_of_lt $
    cardinal.lt_ord.2 (lt_of_lt_of_le (cardinal.lt_succ_self _) (le_sup _ _))⟩

theorem le_sup {ι} (f : ι → ordinal) : ∀ i, f i ≤ sup f :=
omin_mem {c | ∀ i, f i ≤ c} _

theorem sup_le {ι} {f : ι → ordinal} {a} : sup f ≤ a ↔ ∀ i, f i ≤ a :=
⟨λ h i, le_trans (le_sup _ _) h, λ h, omin_le h⟩

theorem lt_sup {ι} {f : ι → ordinal} {a} : a < sup f ↔ ∃ i, a < f i :=
by simpa only [not_forall, not_le] using not_congr (@sup_le _ f a)

theorem is_normal.sup {f} (H : is_normal f)
  {ι} {g : ι → ordinal} (h : nonempty ι) : f (sup g) = sup (f ∘ g) :=
eq_of_forall_ge_iff $ λ a,
by rw [sup_le, comp, H.le_set' (λ_:ι, true) g (let ⟨i⟩ := h in ⟨i, ⟨⟩⟩)];
  intros; simp only [sup_le, true_implies_iff]

theorem sup_ord {ι} (f : ι → cardinal) : sup (λ i, (f i).ord) = (cardinal.sup f).ord :=
eq_of_forall_ge_iff $ λ a, by simp only [sup_le, cardinal.ord_le, cardinal.sup_le]

lemma sup_succ {ι} (f : ι → ordinal) : sup (λ i, succ (f i)) ≤ succ (sup f) :=
by { rw [ordinal.sup_le], intro i, rw ordinal.succ_le_succ, apply ordinal.le_sup }

lemma unbounded_range_of_sup_ge {α β : Type u} (r : α → α → Prop) [is_well_order α r] (f : β → α)
  (h : type r ≤ sup.{u u} (typein r ∘ f)) : unbounded r (range f) :=
begin
  apply (not_bounded_iff _).mp, rintro ⟨x, hx⟩, apply not_lt_of_ge h,
  refine lt_of_le_of_lt _ (typein_lt_type r x), rw [sup_le], intro y,
  apply le_of_lt, rw typein_lt_typein, apply hx, apply mem_range_self
end

/-- The supremum of a family of ordinals indexed by the set
  of ordinals less than some `o : ordinal.{u}`.
  (This is not a special case of `sup` over the subtype,
  because `{a // a < o} : Type (u+1)` and `sup` only works over
  families in `Type u`.) -/
def bsup (o : ordinal.{u}) : (Π a < o, ordinal.{max u v}) → ordinal.{max u v} :=
match o, o.out, o.out_eq with
| _, ⟨α, r, _⟩, rfl, f := by exactI sup (λ a, f (typein r a) (typein_lt_type _ _))
end

theorem bsup_le {o f a} : bsup.{u v} o f ≤ a ↔ ∀ i h, f i h ≤ a :=
match o, o.out, o.out_eq, f :
 ∀ o w (e : ⟦w⟧ = o) (f : Π (a : ordinal.{u}), a < o → ordinal.{(max u v)}),
   bsup._match_1 o w e f ≤ a ↔ ∀ i h, f i h ≤ a with
| _, ⟨α, r, _⟩, rfl, f := by rw [bsup._match_1, sup_le]; exactI
  ⟨λ H i h, by simpa only [typein_enum] using H (enum r i h), λ H b, H _ _⟩
end

theorem bsup_type (r : α → α → Prop) [is_well_order α r] (f) :
  bsup (type r) f = sup (λ a, f (typein r a) (typein_lt_type _ _)) :=
eq_of_forall_ge_iff $ λ o,
by rw [bsup_le, sup_le]; exact
  ⟨λ H b, H _ _, λ H i h, by simpa only [typein_enum] using H (enum r i h)⟩

theorem le_bsup {o} (f : Π a < o, ordinal) (i h) : f i h ≤ bsup o f :=
bsup_le.1 (le_refl _) _ _

theorem lt_bsup {o : ordinal} {f : Π a < o, ordinal}
  (hf : ∀{a a'} (ha : a < o) (ha' : a' < o), a < a' → f a ha < f a' ha')
  (ho : o.is_limit) (i h) : f i h < bsup o f :=
lt_of_lt_of_le (hf _ _ $ lt_succ_self i) (le_bsup f i.succ $ ho.2 _ h)

theorem bsup_id {o} (ho : is_limit o) : bsup.{u u} o (λ x _, x) = o :=
begin
  apply le_antisymm, rw [bsup_le], intro i, apply le_of_lt,
  rw [←not_lt], intro h, apply lt_irrefl (bsup.{u u} o (λ x _, x)),
  apply lt_of_le_of_lt _ (lt_bsup _ ho _ h), refl, intros, assumption
end

theorem is_normal.bsup {f} (H : is_normal f)
  {o : ordinal} : ∀ (g : Π a < o, ordinal) (h : o ≠ 0),
  f (bsup o g) = bsup o (λ a h, f (g a h)) :=
induction_on o $ λ α r _ g h,
by resetI; rw [bsup_type,
     H.sup (type_ne_zero_iff_nonempty.1 h), bsup_type]

theorem is_normal.bsup_eq {f} (H : is_normal f) {o : ordinal} (h : is_limit o) :
  bsup.{u} o (λx _, f x) = f o :=
by { rw [←is_normal.bsup.{u u} H (λ x _, x) h.1, bsup_id h] }

/-! ### Ordinal exponential -/

/-- The ordinal exponential, defined by transfinite recursion. -/
def power (a b : ordinal) : ordinal :=
if a = 0 then 1 - b else
limit_rec_on b 1 (λ _ IH, IH * a) (λ b _, bsup.{u u} b)

instance : has_pow ordinal ordinal := ⟨power⟩
local infixr ^ := @pow ordinal ordinal ordinal.has_pow

theorem zero_power' (a : ordinal) : 0 ^ a = 1 - a :=
by simp only [pow, power, if_pos rfl]

@[simp] theorem zero_power {a : ordinal} (a0 : a ≠ 0) : 0 ^ a = 0 :=
by rwa [zero_power', sub_eq_zero_iff_le, one_le_iff_ne_zero]

@[simp] theorem power_zero (a : ordinal) : a ^ 0 = 1 :=
by by_cases a = 0; [simp only [pow, power, if_pos h, sub_zero],
simp only [pow, power, if_neg h, limit_rec_on_zero]]

@[simp] theorem power_succ (a b : ordinal) : a ^ succ b = a ^ b * a :=
if h : a = 0 then by subst a; simp only [zero_power (succ_ne_zero _), mul_zero]
else by simp only [pow, power, limit_rec_on_succ, if_neg h]

theorem power_limit {a b : ordinal} (a0 : a ≠ 0) (h : is_limit b) :
  a ^ b = bsup.{u u} b (λ c _, a ^ c) :=
by simp only [pow, power, if_neg a0]; rw limit_rec_on_limit _ _ _ _ h; refl

theorem power_le_of_limit {a b c : ordinal} (a0 : a ≠ 0) (h : is_limit b) :
  a ^ b ≤ c ↔ ∀ b' < b, a ^ b' ≤ c :=
by rw [power_limit a0 h, bsup_le]

theorem lt_power_of_limit {a b c : ordinal} (b0 : b ≠ 0) (h : is_limit c) :
  a < b ^ c ↔ ∃ c' < c, a < b ^ c' :=
by rw [← not_iff_not, not_exists]; simp only [not_lt, power_le_of_limit b0 h, exists_prop, not_and]

@[simp] theorem power_one (a : ordinal) : a ^ 1 = a :=
by rw [← succ_zero, power_succ]; simp only [power_zero, one_mul]

@[simp] theorem one_power (a : ordinal) : 1 ^ a = 1 :=
begin
  apply limit_rec_on a,
  { simp only [power_zero] },
  { intros _ ih, simp only [power_succ, ih, mul_one] },
  refine λ b l IH, eq_of_forall_ge_iff (λ c, _),
  rw [power_le_of_limit ordinal.one_ne_zero l],
  exact ⟨λ H, by simpa only [power_zero] using H 0 l.pos,
         λ H b' h, by rwa IH _ h⟩,
end

theorem power_pos {a : ordinal} (b)
  (a0 : 0 < a) : 0 < a ^ b :=
begin
  have h0 : 0 < a ^ 0, {simp only [power_zero, zero_lt_one]},
  apply limit_rec_on b,
  { exact h0 },
  { intros b IH, rw [power_succ],
    exact mul_pos IH a0 },
  { exact λ b l _, (lt_power_of_limit (ordinal.pos_iff_ne_zero.1 a0) l).2
      ⟨0, l.pos, h0⟩ },
end

theorem power_ne_zero {a : ordinal} (b)
  (a0 : a ≠ 0) : a ^ b ≠ 0 :=
ordinal.pos_iff_ne_zero.1 $ power_pos b $ ordinal.pos_iff_ne_zero.2 a0

theorem power_is_normal {a : ordinal} (h : 1 < a) : is_normal ((^) a) :=
have a0 : 0 < a, from lt_trans zero_lt_one h,
⟨λ b, by simpa only [mul_one, power_succ] using
  (mul_lt_mul_iff_left (power_pos b a0)).2 h,
 λ b l c, power_le_of_limit (ne_of_gt a0) l⟩

theorem power_lt_power_iff_right {a b c : ordinal}
  (a1 : 1 < a) : a ^ b < a ^ c ↔ b < c :=
(power_is_normal a1).lt_iff

theorem power_le_power_iff_right {a b c : ordinal}
  (a1 : 1 < a) : a ^ b ≤ a ^ c ↔ b ≤ c :=
(power_is_normal a1).le_iff

theorem power_right_inj {a b c : ordinal}
  (a1 : 1 < a) : a ^ b = a ^ c ↔ b = c :=
(power_is_normal a1).inj

theorem power_is_limit {a b : ordinal}
  (a1 : 1 < a) : is_limit b → is_limit (a ^ b) :=
(power_is_normal a1).is_limit

theorem power_is_limit_left {a b : ordinal}
  (l : is_limit a) (hb : b ≠ 0) : is_limit (a ^ b) :=
begin
  rcases zero_or_succ_or_limit b with e|⟨b,rfl⟩|l',
  { exact absurd e hb },
  { rw power_succ,
    exact mul_is_limit (power_pos _ l.pos) l },
  { exact power_is_limit l.one_lt l' }
end

theorem power_le_power_right {a b c : ordinal}
  (h₁ : 0 < a) (h₂ : b ≤ c) : a ^ b ≤ a ^ c :=
begin
  cases lt_or_eq_of_le (one_le_iff_pos.2 h₁) with h₁ h₁,
  { exact (power_le_power_iff_right h₁).2 h₂ },
  { subst a, simp only [one_power] }
end

theorem power_le_power_left {a b : ordinal} (c)
  (ab : a ≤ b) : a ^ c ≤ b ^ c :=
begin
  by_cases a0 : a = 0,
  { subst a, by_cases c0 : c = 0,
    { subst c, simp only [power_zero] },
    { simp only [zero_power c0, ordinal.zero_le] } },
  { apply limit_rec_on c,
    { simp only [power_zero] },
    { intros c IH, simpa only [power_succ] using mul_le_mul IH ab },
    { exact λ c l IH, (power_le_of_limit a0 l).2
        (λ b' h, le_trans (IH _ h) (power_le_power_right
          (lt_of_lt_of_le (ordinal.pos_iff_ne_zero.2 a0) ab) (le_of_lt h))) } }
end

theorem le_power_self {a : ordinal} (b) (a1 : 1 < a) : b ≤ a ^ b :=
(power_is_normal a1).le_self _

theorem power_lt_power_left_of_succ {a b c : ordinal}
  (ab : a < b) : a ^ succ c < b ^ succ c :=
by rw [power_succ, power_succ]; exact
lt_of_le_of_lt
  (mul_le_mul_right _ $ power_le_power_left _ $ le_of_lt ab)
  (mul_lt_mul_of_pos_left ab (power_pos _ (lt_of_le_of_lt (ordinal.zero_le _) ab)))

theorem power_add (a b c : ordinal) : a ^ (b + c) = a ^ b * a ^ c :=
begin
  by_cases a0 : a = 0,
  { subst a,
    by_cases c0 : c = 0, {simp only [c0, add_zero, power_zero, mul_one]},
    have : b+c ≠ 0 := ne_of_gt (lt_of_lt_of_le
      (ordinal.pos_iff_ne_zero.2 c0) (le_add_left _ _)),
    simp only [zero_power c0, zero_power this, mul_zero] },
  cases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1,
  { subst a1, simp only [one_power, mul_one] },
  apply limit_rec_on c,
  { simp only [add_zero, power_zero, mul_one] },
  { intros c IH,
    rw [add_succ, power_succ, IH, power_succ, mul_assoc] },
  { intros c l IH,
    refine eq_of_forall_ge_iff (λ d, (((power_is_normal a1).trans
      (add_is_normal b)).limit_le l).trans _),
    simp only [IH] {contextual := tt},
    exact (((mul_is_normal $ power_pos b (ordinal.pos_iff_ne_zero.2 a0)).trans
      (power_is_normal a1)).limit_le l).symm }
end

theorem power_dvd_power (a) {b c : ordinal}
  (h : b ≤ c) : a ^ b ∣ a ^ c :=
by { rw [← add_sub_cancel_of_le h, power_add], apply dvd_mul_right }

theorem power_dvd_power_iff {a b c : ordinal}
  (a1 : 1 < a) : a ^ b ∣ a ^ c ↔ b ≤ c :=
⟨λ h, le_of_not_lt $ λ hn,
  not_le_of_lt ((power_lt_power_iff_right a1).2 hn) $
   le_of_dvd (power_ne_zero _ $ one_le_iff_ne_zero.1 $ le_of_lt a1) h,
power_dvd_power _⟩

theorem power_mul (a b c : ordinal) : a ^ (b * c) = (a ^ b) ^ c :=
begin
  by_cases b0 : b = 0, {simp only [b0, zero_mul, power_zero, one_power]},
  by_cases a0 : a = 0,
  { subst a,
    by_cases c0 : c = 0, {simp only [c0, mul_zero, power_zero]},
    simp only [zero_power b0, zero_power c0, zero_power (mul_ne_zero b0 c0)] },
  cases eq_or_lt_of_le (one_le_iff_ne_zero.2 a0) with a1 a1,
  { subst a1, simp only [one_power] },
  apply limit_rec_on c,
  { simp only [mul_zero, power_zero] },
  { intros c IH,
    rw [mul_succ, power_add, IH, power_succ] },
  { intros c l IH,
    refine eq_of_forall_ge_iff (λ d, (((power_is_normal a1).trans
      (mul_is_normal (ordinal.pos_iff_ne_zero.2 b0))).limit_le l).trans _),
    simp only [IH] {contextual := tt},
    exact (power_le_of_limit (power_ne_zero _ a0) l).symm }
end

/-! ### Ordinal logarithm -/

/-- The ordinal logarithm is the solution `u` to the equation
  `x = b ^ u * v + w` where `v < b` and `w < b`. -/
def log (b : ordinal) (x : ordinal) : ordinal :=
if h : 1 < b then pred $
  omin {o | x < b^o} ⟨succ x, succ_le.1 (le_power_self _ h)⟩
else 0

@[simp] theorem log_not_one_lt {b : ordinal} (b1 : ¬ 1 < b) (x : ordinal) : log b x = 0 :=
by simp only [log, dif_neg b1]

theorem log_def {b : ordinal} (b1 : 1 < b) (x : ordinal) : log b x =
  pred (omin {o | x < b^o} (log._proof_1 b x b1)) :=
by simp only [log, dif_pos b1]

@[simp] theorem log_zero (b : ordinal) : log b 0 = 0 :=
if b1 : 1 < b then
  by rw [log_def b1, ← ordinal.le_zero, pred_le];
     apply omin_le; change 0<b^succ 0;
     rw [succ_zero, power_one];
     exact lt_trans zero_lt_one b1
else by simp only [log_not_one_lt b1]

theorem succ_log_def {b x : ordinal} (b1 : 1 < b) (x0 : 0 < x) : succ (log b x) =
  omin {o | x < b^o} (log._proof_1 b x b1) :=
begin
  let t := omin {o | x < b^o} (log._proof_1 b x b1),
  have : x < b ^ t := omin_mem {o | x < b^o} _,
  rcases zero_or_succ_or_limit t with h|h|h,
  { refine (not_lt_of_le (one_le_iff_pos.2 x0) _).elim,
    simpa only [h, power_zero] },
  { rw [show log b x = pred t, from log_def b1 x,
        succ_pred_iff_is_succ.2 h] },
  { rcases (lt_power_of_limit (ne_of_gt $ lt_trans zero_lt_one b1) h).1 this with ⟨a, h₁, h₂⟩,
    exact (not_le_of_lt h₁).elim (le_omin.1 (le_refl t) a h₂) }
end

theorem lt_power_succ_log {b : ordinal} (b1 : 1 < b) (x : ordinal) :
  x < b ^ succ (log b x) :=
begin
  cases lt_or_eq_of_le (ordinal.zero_le x) with x0 x0,
  { rw [succ_log_def b1 x0], exact omin_mem {o | x < b^o} _ },
  { subst x, apply power_pos _ (lt_trans zero_lt_one b1) }
end

theorem power_log_le (b) {x : ordinal} (x0 : 0 < x) :
  b ^ log b x ≤ x :=
begin
  by_cases b0 : b = 0,
  { rw [b0, zero_power'],
    refine le_trans (sub_le_self _ _) (one_le_iff_pos.2 x0) },
  cases lt_or_eq_of_le (one_le_iff_ne_zero.2 b0) with b1 b1,
  { refine le_of_not_lt (λ h, not_le_of_lt (lt_succ_self (log b x)) _),
    have := @omin_le {o | x < b^o} _ _ h,
    rwa ← succ_log_def b1 x0 at this },
  { rw [← b1, one_power], exact one_le_iff_pos.2 x0 }
end

theorem le_log {b x c : ordinal} (b1 : 1 < b) (x0 : 0 < x) :
  c ≤ log b x ↔ b ^ c ≤ x :=
⟨λ h, le_trans ((power_le_power_iff_right b1).2 h) (power_log_le b x0),
 λ h, le_of_not_lt $ λ hn,
   not_le_of_lt (lt_power_succ_log b1 x) $
   le_trans ((power_le_power_iff_right b1).2 (succ_le.2 hn)) h⟩

theorem log_lt {b x c : ordinal} (b1 : 1 < b) (x0 : 0 < x) :
  log b x < c ↔ x < b ^ c :=
lt_iff_lt_of_le_iff_le (le_log b1 x0)

theorem log_le_log (b) {x y : ordinal} (xy : x ≤ y) :
  log b x ≤ log b y :=
if x0 : x = 0 then by simp only [x0, log_zero, ordinal.zero_le] else
have x0 : 0 < x, from ordinal.pos_iff_ne_zero.2 x0,
if b1 : 1 < b then
  (le_log b1 (lt_of_lt_of_le x0 xy)).2 $ le_trans (power_log_le _ x0) xy
else by simp only [log_not_one_lt b1, ordinal.zero_le]

theorem log_le_self (b x : ordinal) : log b x ≤ x :=
if x0 : x = 0 then by simp only [x0, log_zero, ordinal.zero_le] else
if b1 : 1 < b then
  le_trans (le_power_self _ b1) (power_log_le b (ordinal.pos_iff_ne_zero.2 x0))
else by simp only [log_not_one_lt b1, ordinal.zero_le]

/-! ### The Cantor normal form -/

theorem CNF_aux {b o : ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) :
  o % b ^ log b o < o :=
lt_of_lt_of_le
  (mod_lt _ $ power_ne_zero _ b0)
  (power_log_le _ $ ordinal.pos_iff_ne_zero.2 o0)

/-- Proving properties of ordinals by induction over their Cantor normal form. -/
@[elab_as_eliminator] noncomputable def CNF_rec {b : ordinal} (b0 : b ≠ 0)
  {C : ordinal → Sort*}
  (H0 : C 0)
  (H : ∀ o, o ≠ 0 → o % b ^ log b o < o → C (o % b ^ log b o) → C o)
  : ∀ o, C o
| o :=
  if o0 : o = 0 then by rw o0; exact H0 else
  have _, from CNF_aux b0 o0,
  H o o0 this (CNF_rec (o % b ^ log b o))
using_well_founded {dec_tac := `[assumption]}

@[simp] theorem CNF_rec_zero {b} (b0) {C H0 H} : @CNF_rec b b0 C H0 H 0 = H0 :=
by rw [CNF_rec, dif_pos rfl]; refl

@[simp] theorem CNF_rec_ne_zero {b} (b0) {C H0 H o} (o0) :
  @CNF_rec b b0 C H0 H o = H o o0 (CNF_aux b0 o0) (@CNF_rec b b0 C H0 H _) :=
by rw [CNF_rec, dif_neg o0]

/-- The Cantor normal form of an ordinal is the list of coefficients
  in the base-`b` expansion of `o`.

    CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)] -/
noncomputable def CNF (b := omega) (o : ordinal) : list (ordinal × ordinal) :=
if b0 : b = 0 then [] else
CNF_rec b0 [] (λ o o0 h IH, (log b o, o / b ^ log b o) :: IH) o

@[simp] theorem zero_CNF (o) : CNF 0 o = [] :=
dif_pos rfl

@[simp] theorem CNF_zero (b) : CNF b 0 = [] :=
if b0 : b = 0 then dif_pos b0 else
(dif_neg b0).trans $ CNF_rec_zero _

theorem CNF_ne_zero {b o : ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) :
  CNF b o = (log b o, o / b ^ log b o) :: CNF b (o % b ^ log b o) :=
by unfold CNF; rw [dif_neg b0, dif_neg b0, CNF_rec_ne_zero b0 o0]

theorem one_CNF {o : ordinal} (o0 : o ≠ 0) :
  CNF 1 o = [(0, o)] :=
by rw [CNF_ne_zero ordinal.one_ne_zero o0, log_not_one_lt (lt_irrefl _), power_zero, mod_one,
       CNF_zero, div_one]

theorem CNF_foldr {b : ordinal} (b0 : b ≠ 0) (o) :
  (CNF b o).foldr (λ p r, b ^ p.1 * p.2 + r) 0 = o :=
CNF_rec b0 (by rw CNF_zero; refl)
  (λ o o0 h IH, by rw [CNF_ne_zero b0 o0, list.foldr_cons, IH, div_add_mod]) o

theorem CNF_pairwise_aux (b := omega) (o) :
  (∀ p ∈ CNF b o, prod.fst p ≤ log b o) ∧
  (CNF b o).pairwise (λ p q, q.1 < p.1) :=
begin
  by_cases b0 : b = 0,
  { simp only [b0, zero_CNF, list.pairwise.nil, and_true], exact λ _, false.elim },
  cases lt_or_eq_of_le (one_le_iff_ne_zero.2 b0) with b1 b1,
  { refine CNF_rec b0 _ _ o,
    { simp only [CNF_zero, list.pairwise.nil, and_true], exact λ _, false.elim },
    intros o o0 H IH, cases IH with IH₁ IH₂,
    simp only [CNF_ne_zero b0 o0, list.forall_mem_cons, list.pairwise_cons, IH₂, and_true],
    refine ⟨⟨le_refl _, λ p m, _⟩, λ p m, _⟩,
    { exact le_trans (IH₁ p m) (log_le_log _ $ le_of_lt H) },
    { refine lt_of_le_of_lt (IH₁ p m) ((log_lt b1 _).2 _),
      { rw ordinal.pos_iff_ne_zero, intro e,
        rw e at m, simpa only [CNF_zero] using m },
      { exact mod_lt _ (power_ne_zero _ b0) } } },
  { by_cases o0 : o = 0,
    { simp only [o0, CNF_zero, list.pairwise.nil, and_true], exact λ _, false.elim },
    rw [← b1, one_CNF o0],
    simp only [list.mem_singleton, log_not_one_lt (lt_irrefl _), forall_eq, le_refl, true_and,
      list.pairwise_singleton] }
end

theorem CNF_pairwise (b := omega) (o) :
  (CNF b o).pairwise (λ p q, prod.fst q < p.1) :=
(CNF_pairwise_aux _ _).2

theorem CNF_fst_le_log (b := omega) (o) :
  ∀ p ∈ CNF b o, prod.fst p ≤ log b o :=
(CNF_pairwise_aux _ _).1

theorem CNF_fst_le (b := omega) (o) (p ∈ CNF b o) : prod.fst p ≤ o :=
le_trans (CNF_fst_le_log _ _ p H) (log_le_self _ _)

theorem CNF_snd_lt {b : ordinal} (b1 : 1 < b) (o) :
  ∀ p ∈ CNF b o, prod.snd p < b :=
begin
  have b0 := ne_of_gt (lt_trans zero_lt_one b1),
  refine CNF_rec b0 (λ _, by rw [CNF_zero]; exact false.elim) _ o,
  intros o o0 H IH,
  simp only [CNF_ne_zero b0 o0, list.mem_cons_iff, forall_eq_or_imp, iff_true_intro IH, and_true],
  rw [div_lt (power_ne_zero _ b0), ← power_succ],
  exact lt_power_succ_log b1 _,
end

theorem CNF_sorted (b := omega) (o) :
  ((CNF b o).map prod.fst).sorted (>) :=
by rw [list.sorted, list.pairwise_map]; exact CNF_pairwise b o

/-! ### Casting naturals into ordinals, compatibility with operations -/

@[simp] theorem nat_cast_mul {m n : ℕ} : ((m * n : ℕ) : ordinal) = m * n :=
by induction n with n IH; [simp only [nat.cast_zero, nat.mul_zero, mul_zero],
  rw [nat.mul_succ, nat.cast_add, IH, nat.cast_succ, mul_add_one]]

@[simp] theorem nat_cast_power {m n : ℕ} : ((pow m n : ℕ) : ordinal) = m ^ n :=
by induction n with n IH; [simp only [pow_zero, nat.cast_zero, power_zero, nat.cast_one],
  rw [pow_succ', nat_cast_mul, IH, nat.cast_succ, ← succ_eq_add_one, power_succ]]

@[simp] theorem nat_cast_le {m n : ℕ} : (m : ordinal) ≤ n ↔ m ≤ n :=
by rw [← cardinal.ord_nat, ← cardinal.ord_nat,
       cardinal.ord_le_ord, cardinal.nat_cast_le]

@[simp] theorem nat_cast_lt {m n : ℕ} : (m : ordinal) < n ↔ m < n :=
by simp only [lt_iff_le_not_le, nat_cast_le]

@[simp] theorem nat_cast_inj {m n : ℕ} : (m : ordinal) = n ↔ m = n :=
by simp only [le_antisymm_iff, nat_cast_le]

@[simp] theorem nat_cast_eq_zero {n : ℕ} : (n : ordinal) = 0 ↔ n = 0 :=
@nat_cast_inj n 0

theorem nat_cast_ne_zero {n : ℕ} : (n : ordinal) ≠ 0 ↔ n ≠ 0 :=
not_congr nat_cast_eq_zero

@[simp] theorem nat_cast_pos {n : ℕ} : (0 : ordinal) < n ↔ 0 < n :=
@nat_cast_lt 0 n

@[simp] theorem nat_cast_sub {m n : ℕ} : ((m - n : ℕ) : ordinal) = m - n :=
(_root_.le_total m n).elim
  (λ h, by rw [nat.sub_eq_zero_iff_le.2 h, sub_eq_zero_iff_le.2 (nat_cast_le.2 h)]; refl)
  (λ h, (add_left_cancel n).1 $ by rw [← nat.cast_add,
     nat.add_sub_cancel' h, add_sub_cancel_of_le (nat_cast_le.2 h)])

@[simp] theorem nat_cast_div {m n : ℕ} : ((m / n : ℕ) : ordinal) = m / n :=
if n0 : n = 0 then by simp only [n0, nat.div_zero, nat.cast_zero, div_zero] else
have n0':_, from nat_cast_ne_zero.2 n0,
le_antisymm
  (by rw [le_div n0', ← nat_cast_mul, nat_cast_le, mul_comm];
      apply nat.div_mul_le_self)
  (by rw [div_le n0', succ, ← nat.cast_succ, ← nat_cast_mul,
          nat_cast_lt, mul_comm, ← nat.div_lt_iff_lt_mul _ _ (nat.pos_of_ne_zero n0)];
      apply nat.lt_succ_self)

@[simp] theorem nat_cast_mod {m n : ℕ} : ((m % n : ℕ) : ordinal) = m % n :=
by rw [← add_left_cancel (n*(m/n)), div_add_mod, ← nat_cast_div, ← nat_cast_mul, ← nat.cast_add,
       nat.div_add_mod]

@[simp] theorem nat_le_card {o} {n : ℕ} : (n : cardinal) ≤ card o ↔ (n : ordinal) ≤ o :=
⟨λ h, by rwa [← cardinal.ord_le, cardinal.ord_nat] at h,
 λ h, card_nat n ▸ card_le_card h⟩

@[simp] theorem nat_lt_card {o} {n : ℕ} : (n : cardinal) < card o ↔ (n : ordinal) < o :=
by rw [← succ_le, ← cardinal.succ_le, ← cardinal.nat_succ, nat_le_card]; refl

@[simp] theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
lt_iff_lt_of_le_iff_le nat_le_card

@[simp] theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp] theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n :=
by simp only [le_antisymm_iff, card_le_nat, nat_le_card]

@[simp] theorem type_fin (n : ℕ) : @type (fin n) (<) _ = n :=
by rw [← card_eq_nat, card_type, mk_fin]

@[simp] theorem lift_nat_cast (n : ℕ) : lift n = n :=
by induction n with n ih; [simp only [nat.cast_zero, lift_zero],
  simp only [nat.cast_succ, lift_add, ih, lift_one]]

theorem lift_type_fin (n : ℕ) : lift (@type (fin n) (<) _) = n :=
by simp only [type_fin, lift_nat_cast]

theorem fintype_card (r : α → α → Prop) [is_well_order α r] [fintype α] : type r = fintype.card α :=
by rw [← card_eq_nat, card_type, fintype_card]

end ordinal

/-! ### Properties of `omega` -/

namespace cardinal
open ordinal

@[simp] theorem ord_omega : ord.{u} omega = ordinal.omega :=
le_antisymm (ord_le.2 $ le_refl _) $
le_of_forall_lt $ λ o h, begin
  rcases ordinal.lt_lift_iff.1 h with ⟨o, rfl, h'⟩,
  rw [lt_ord, ← lift_card, ← lift_omega.{0 u},
      lift_lt, ← typein_enum (<) h'],
  exact lt_omega_iff_fintype.2 ⟨set.fintype_lt_nat _⟩
end

@[simp] theorem add_one_of_omega_le {c} (h : omega ≤ c) : c + 1 = c :=
by rw [add_comm, ← card_ord c, ← card_one,
       ← card_add, one_add_of_omega_le];
   rwa [← ord_omega, ord_le_ord]

end cardinal

namespace ordinal

theorem lt_omega {o : ordinal.{u}} : o < omega ↔ ∃ n : ℕ, o = n :=
by rw [← cardinal.ord_omega, cardinal.lt_ord, lt_omega]; simp only [card_eq_nat]

theorem nat_lt_omega (n : ℕ) : (n : ordinal) < omega :=
lt_omega.2 ⟨_, rfl⟩

theorem omega_pos : 0 < omega := nat_lt_omega 0

theorem omega_ne_zero : omega ≠ 0 := ne_of_gt omega_pos

theorem one_lt_omega : 1 < omega := by simpa only [nat.cast_one] using nat_lt_omega 1

theorem omega_is_limit : is_limit omega :=
⟨omega_ne_zero, λ o h,
  let ⟨n, e⟩ := lt_omega.1 h in
  by rw [e]; exact nat_lt_omega (n+1)⟩

theorem omega_le {o : ordinal.{u}} : omega ≤ o ↔ ∀ n : ℕ, (n : ordinal) ≤ o :=
⟨λ h n, le_trans (le_of_lt (nat_lt_omega _)) h,
 λ H, le_of_forall_lt $ λ a h,
   let ⟨n, e⟩ := lt_omega.1 h in
   by rw [e, ← succ_le]; exact H (n+1)⟩

theorem nat_lt_limit {o} (h : is_limit o) : ∀ n : ℕ, (n : ordinal) < o
| 0     := lt_of_le_of_ne (ordinal.zero_le o) h.1.symm
| (n+1) := h.2 _ (nat_lt_limit n)

theorem omega_le_of_is_limit {o} (h : is_limit o) : omega ≤ o :=
omega_le.2 $ λ n, le_of_lt $ nat_lt_limit h n

theorem add_omega {a : ordinal} (h : a < omega) : a + omega = omega :=
begin
  rcases lt_omega.1 h with ⟨n, rfl⟩,
  clear h, induction n with n IH,
  { rw [nat.cast_zero, zero_add] },
  { rw [nat.cast_succ, add_assoc, one_add_of_omega_le (le_refl _), IH] }
end

theorem add_lt_omega {a b : ordinal} (ha : a < omega) (hb : b < omega) : a + b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat.cast_add]; apply nat_lt_omega
end

theorem mul_lt_omega {a b : ordinal} (ha : a < omega) (hb : b < omega) : a * b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat_cast_mul]; apply nat_lt_omega
end

theorem is_limit_iff_omega_dvd {a : ordinal} : is_limit a ↔ a ≠ 0 ∧ omega ∣ a :=
begin
  refine ⟨λ l, ⟨l.1, ⟨a / omega, le_antisymm _ (mul_div_le _ _)⟩⟩, λ h, _⟩,
  { refine (limit_le l).2 (λ x hx, le_of_lt _),
    rw [← div_lt omega_ne_zero, ← succ_le, le_div omega_ne_zero,
        mul_succ, add_le_of_limit omega_is_limit],
    intros b hb,
    rcases lt_omega.1 hb with ⟨n, rfl⟩,
    exact le_trans (add_le_add_right (mul_div_le _ _) _)
      (le_of_lt $ lt_sub.1 $ nat_lt_limit (sub_is_limit l hx) _) },
  { rcases h with ⟨a0, b, rfl⟩,
    refine mul_is_limit_left omega_is_limit
      (ordinal.pos_iff_ne_zero.2 $ mt _ a0),
    intro e, simp only [e, mul_zero] }
end

local infixr ^ := @pow ordinal ordinal ordinal.has_pow

theorem power_lt_omega {a b : ordinal} (ha : a < omega) (hb : b < omega) : a ^ b < omega :=
match a, b, lt_omega.1 ha, lt_omega.1 hb with
| _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ := by rw [← nat_cast_power]; apply nat_lt_omega
end

theorem add_omega_power {a b : ordinal} (h : a < omega ^ b) : a + omega ^ b = omega ^ b :=
begin
  refine le_antisymm _ (le_add_left _ _),
  revert h, apply limit_rec_on b,
  { intro h, rw [power_zero, ← succ_zero, lt_succ, ordinal.le_zero] at h,
    rw [h, zero_add] },
  { intros b _ h, rw [power_succ] at h,
    rcases (lt_mul_of_limit omega_is_limit).1 h with ⟨x, xo, ax⟩,
    refine le_trans (add_le_add_right (le_of_lt ax) _) _,
    rw [power_succ, ← mul_add, add_omega xo] },
  { intros b l IH h, rcases (lt_power_of_limit omega_ne_zero l).1 h with ⟨x, xb, ax⟩,
    refine (((add_is_normal a).trans (power_is_normal one_lt_omega))
      .limit_le l).2 (λ y yb, _),
    let z := max x y,
    have := IH z (max_lt xb yb)
      (lt_of_lt_of_le ax $ power_le_power_right omega_pos (le_max_left _ _)),
    exact le_trans (add_le_add_left (power_le_power_right omega_pos (le_max_right _ _)) _)
      (le_trans this (power_le_power_right omega_pos $ le_of_lt $ max_lt xb yb)) }
end

theorem add_lt_omega_power {a b c : ordinal} (h₁ : a < omega ^ c) (h₂ : b < omega ^ c) :
  a + b < omega ^ c :=
by rwa [← add_omega_power h₁, add_lt_add_iff_left]

theorem add_absorp {a b c : ordinal} (h₁ : a < omega ^ b) (h₂ : omega ^ b ≤ c) : a + c = c :=
by rw [← add_sub_cancel_of_le h₂, ← add_assoc, add_omega_power h₁]

theorem add_absorp_iff {o : ordinal} (o0 : 0 < o) : (∀ a < o, a + o = o) ↔ ∃ a, o = omega ^ a :=
⟨λ H, ⟨log omega o, begin
  refine ((lt_or_eq_of_le (power_log_le _ o0))
    .resolve_left $ λ h, _).symm,
  have := H _ h,
  have := lt_power_succ_log one_lt_omega o,
  rw [power_succ, lt_mul_of_limit omega_is_limit] at this,
  rcases this with ⟨a, ao, h'⟩,
  rcases lt_omega.1 ao with ⟨n, rfl⟩, clear ao,
  revert h', apply not_lt_of_le,
  suffices e : omega ^ log omega o * ↑n + o = o,
  { simpa only [e] using le_add_right (omega ^ log omega o * ↑n) o },
  induction n with n IH, {simp only [nat.cast_zero, mul_zero, zero_add]},
  simp only [nat.cast_succ, mul_add_one, add_assoc, this, IH]
end⟩,
λ ⟨b, e⟩, e.symm ▸ λ a, add_omega_power⟩

theorem add_mul_limit_aux {a b c : ordinal} (ba : b + a = a)
  (l : is_limit c)
  (IH : ∀ c' < c, (a + b) * succ c' = a * succ c' + b) :
  (a + b) * c = a * c :=
le_antisymm
  ((mul_le_of_limit l).2 $ λ c' h, begin
    apply le_trans (mul_le_mul_left _ (le_of_lt $ lt_succ_self _)),
    rw IH _ h,
    apply le_trans (add_le_add_left _ _),
    { rw ← mul_succ, exact mul_le_mul_left _ (succ_le.2 $ l.2 _ h) },
    { rw ← ba, exact le_add_right _ _ }
  end)
  (mul_le_mul_right _ (le_add_right _ _))

theorem add_mul_succ {a b : ordinal} (c) (ba : b + a = a) :
  (a + b) * succ c = a * succ c + b :=
begin
  apply limit_rec_on c,
  { simp only [succ_zero, mul_one] },
  { intros c IH,
    rw [mul_succ, IH, ← add_assoc, add_assoc _ b, ba, ← mul_succ] },
  { intros c l IH,
    have := add_mul_limit_aux ba l IH,
    rw [mul_succ, add_mul_limit_aux ba l IH, mul_succ, add_assoc] }
end

theorem add_mul_limit {a b c : ordinal} (ba : b + a = a)
  (l : is_limit c) : (a + b) * c = a * c :=
add_mul_limit_aux ba l (λ c' _, add_mul_succ c' ba)

theorem mul_omega {a : ordinal} (a0 : 0 < a) (ha : a < omega) : a * omega = omega :=
le_antisymm
  ((mul_le_of_limit omega_is_limit).2 $ λ b hb, le_of_lt (mul_lt_omega ha hb))
  (by simpa only [one_mul] using mul_le_mul_right omega (one_le_iff_pos.2 a0))

theorem mul_lt_omega_power {a b c : ordinal}
  (c0 : 0 < c) (ha : a < omega ^ c) (hb : b < omega) : a * b < omega ^ c :=
if b0 : b = 0 then by simp only [b0, mul_zero, power_pos _ omega_pos] else begin
  rcases zero_or_succ_or_limit c with rfl|⟨c,rfl⟩|l,
  { exact (lt_irrefl _).elim c0 },
  { rw power_succ at ha,
    rcases ((mul_is_normal $ power_pos _ omega_pos).limit_lt
      omega_is_limit).1 ha with ⟨n, hn, an⟩,
    refine lt_of_le_of_lt (mul_le_mul_right _ (le_of_lt an)) _,
    rw [power_succ, mul_assoc, mul_lt_mul_iff_left (power_pos _ omega_pos)],
    exact mul_lt_omega hn hb },
  { rcases ((power_is_normal one_lt_omega).limit_lt l).1 ha with ⟨x, hx, ax⟩,
    refine lt_of_le_of_lt (mul_le_mul (le_of_lt ax) (le_of_lt hb)) _,
    rw [← power_succ, power_lt_power_iff_right one_lt_omega],
    exact l.2 _ hx }
end

theorem mul_omega_dvd {a : ordinal}
  (a0 : 0 < a) (ha : a < omega) : ∀ {b}, omega ∣ b → a * b = b
| _ ⟨b, rfl⟩ := by rw [← mul_assoc, mul_omega a0 ha]

theorem mul_omega_power_power {a b : ordinal} (a0 : 0 < a) (h : a < omega ^ omega ^ b) :
  a * omega ^ omega ^ b = omega ^ omega ^ b :=
begin
  by_cases b0 : b = 0, {rw [b0, power_zero, power_one] at h ⊢, exact mul_omega a0 h},
  refine le_antisymm _
    (by simpa only [one_mul] using mul_le_mul_right (omega^omega^b) (one_le_iff_pos.2 a0)),
  rcases (lt_power_of_limit omega_ne_zero (power_is_limit_left omega_is_limit b0)).1 h
    with ⟨x, xb, ax⟩,
  refine le_trans (mul_le_mul_right _ (le_of_lt ax)) _,
  rw [← power_add, add_omega_power xb]
end

theorem power_omega {a : ordinal} (a1 : 1 < a) (h : a < omega) : a ^ omega = omega :=
le_antisymm
  ((power_le_of_limit (one_le_iff_ne_zero.1 $ le_of_lt a1) omega_is_limit).2
    (λ b hb, le_of_lt (power_lt_omega h hb)))
  (le_power_self _ a1)

/-! ### Fixed points of normal functions -/

/-- The next fixed point function, the least fixed point of the
  normal function `f` above `a`. -/
def nfp (f : ordinal → ordinal) (a : ordinal) :=
sup (λ n : ℕ, f^[n] a)

theorem iterate_le_nfp (f a n) : f^[n] a ≤ nfp f a :=
le_sup _ n

theorem le_nfp_self (f a) : a ≤ nfp f a :=
iterate_le_nfp f a 0

theorem is_normal.lt_nfp {f} (H : is_normal f) {a b} :
  f b < nfp f a ↔ b < nfp f a :=
lt_sup.trans $ iff.trans
  (by exact
   ⟨λ ⟨n, h⟩, ⟨n, lt_of_le_of_lt (H.le_self _) h⟩,
    λ ⟨n, h⟩, ⟨n+1, by rw iterate_succ'; exact H.lt_iff.2 h⟩⟩)
  lt_sup.symm

theorem is_normal.nfp_le {f} (H : is_normal f) {a b} :
  nfp f a ≤ f b ↔ nfp f a ≤ b :=
le_iff_le_iff_lt_iff_lt.2 H.lt_nfp

theorem is_normal.nfp_le_fp {f} (H : is_normal f) {a b}
  (ab : a ≤ b) (h : f b ≤ b) : nfp f a ≤ b :=
sup_le.2 $ λ i, begin
  induction i with i IH generalizing a, {exact ab},
  exact IH (le_trans (H.le_iff.2 ab) h),
end

theorem is_normal.nfp_fp {f} (H : is_normal f) (a) : f (nfp f a) = nfp f a :=
begin
  refine le_antisymm _ (H.le_self _),
  cases le_or_lt (f a) a with aa aa,
  { rwa le_antisymm (H.nfp_le_fp (le_refl _) aa) (le_nfp_self _ _) },
  rcases zero_or_succ_or_limit (nfp f a) with e|⟨b, e⟩|l,
  { refine @le_trans _ _ _ (f a) _ (H.le_iff.2 _) (iterate_le_nfp f a 1),
    simp only [e, ordinal.zero_le] },
  { have : f b < nfp f a := H.lt_nfp.2 (by simp only [e, lt_succ_self]),
    rw [e, lt_succ] at this,
    have ab : a ≤ b,
    { rw [← lt_succ, ← e],
      exact lt_of_lt_of_le aa (iterate_le_nfp f a 1) },
    refine le_trans (H.le_iff.2 (H.nfp_le_fp ab this))
      (le_trans this (le_of_lt _)),
    simp only [e, lt_succ_self] },
  { exact (H.2 _ l _).2 (λ b h, le_of_lt (H.lt_nfp.2 h)) }
end

theorem is_normal.le_nfp {f} (H : is_normal f) {a b} :
  f b ≤ nfp f a ↔ b ≤ nfp f a :=
⟨le_trans (H.le_self _), λ h,
  by simpa only [H.nfp_fp] using H.le_iff.2 h⟩

theorem nfp_eq_self {f : ordinal → ordinal} {a} (h : f a = a) : nfp f a = a :=
le_antisymm (sup_le.mpr $ λ i, by rw [iterate_fixed h]) (le_nfp_self f a)

/-- The derivative of a normal function `f` is
  the sequence of fixed points of `f`. -/
def deriv (f : ordinal → ordinal) (o : ordinal) : ordinal :=
limit_rec_on o (nfp f 0)
  (λ a IH, nfp f (succ IH))
  (λ a l, bsup.{u u} a)

@[simp] theorem deriv_zero (f) : deriv f 0 = nfp f 0 := limit_rec_on_zero _ _ _

@[simp] theorem deriv_succ (f o) : deriv f (succ o) = nfp f (succ (deriv f o)) :=
limit_rec_on_succ _ _ _ _

theorem deriv_limit (f) {o} : is_limit o →
  deriv f o = bsup.{u u} o (λ a _, deriv f a) :=
limit_rec_on_limit _ _ _ _

theorem deriv_is_normal (f) : is_normal (deriv f) :=
⟨λ o, by rw [deriv_succ, ← succ_le]; apply le_nfp_self,
 λ o l a, by rw [deriv_limit _ l, bsup_le]⟩

theorem is_normal.deriv_fp {f} (H : is_normal f) (o) : f (deriv.{u} f o) = deriv f o :=
begin
  apply limit_rec_on o,
  { rw [deriv_zero, H.nfp_fp] },
  { intros o ih, rw [deriv_succ, H.nfp_fp] },
  intros o l IH,
  rw [deriv_limit _ l, is_normal.bsup.{u u u} H _ l.1],
  refine eq_of_forall_ge_iff (λ c, _),
  simp only [bsup_le, IH] {contextual:=tt}
end

theorem is_normal.fp_iff_deriv {f} (H : is_normal f)
  {a} : f a ≤ a ↔ ∃ o, a = deriv f o :=
⟨λ ha, begin
  suffices : ∀ o (_:a ≤ deriv f o), ∃ o, a = deriv f o,
  from this a ((deriv_is_normal _).le_self _),
  intro o, apply limit_rec_on o,
  { intros h₁,
    refine ⟨0, le_antisymm h₁ _⟩,
    rw deriv_zero,
    exact H.nfp_le_fp (ordinal.zero_le _) ha },
  { intros o IH h₁,
    cases le_or_lt a (deriv f o), {exact IH h},
    refine ⟨succ o, le_antisymm h₁ _⟩,
    rw deriv_succ,
    exact H.nfp_le_fp (succ_le.2 h) ha },
  { intros o l IH h₁,
    cases eq_or_lt_of_le h₁, {exact ⟨_, h⟩},
    rw [deriv_limit _ l, ← not_le, bsup_le, not_ball] at h,
    exact let ⟨o', h, hl⟩ := h in IH o' h (le_of_not_le hl) }
end, λ ⟨o, e⟩, e.symm ▸ le_of_eq (H.deriv_fp _)⟩

end ordinal
