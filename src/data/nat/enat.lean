/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.pfun
import tactic.norm_num

/-!
# Natural numbers with infinity

The natural numbers and an extra `top` element `⊤`.

## Main definitions

The following instances are defined:

* `ordered_add_comm_monoid enat`
* `canonically_ordered_add_monoid enat`

There is no additive analogue of `monoid_with_zero`; if there were then `enat` could
be an `add_monoid_with_top`.

* `to_with_top` : the map from `enat` to `with_top ℕ`, with theorems that it plays well
with `+` and `≤`.

* `with_top_add_equiv : enat ≃+ with_top ℕ`
* `with_top_order_iso : enat ≃o with_top ℕ`

## Implementation details

`enat` is defined to be `roption ℕ`.

`+` and `≤` are defined on `enat`, but there is an issue with `*` because it's not
clear what `0 * ⊤` should be. `mul` is hence left undefined. Similarly `⊤ - ⊤` is ambiguous
so there is no `-` defined on `enat`.

Before the `open_locale classical` line, various proofs are made with decidability assumptions.
This can cause issues -- see for example the non-simp lemma `to_with_top_zero` proved by `rfl`,
followed by `@[simp] lemma to_with_top_zero'` whose proof uses `convert`.


## Tags

enat, with_top ℕ
-/
open roption

/-- Type of natural numbers with infinity (`⊤`) -/
def enat : Type := roption ℕ

namespace enat

instance : has_zero enat := ⟨some 0⟩
instance : inhabited enat := ⟨0⟩
instance : has_one enat := ⟨some 1⟩
instance : has_add enat := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, get x h.1 + get y h.2⟩⟩
instance : has_coe ℕ enat := ⟨some⟩
instance (n : ℕ) : decidable (n : enat).dom := is_true trivial

@[simp] lemma coe_inj {x y : ℕ} : (x : enat) = y ↔ x = y := roption.some_inj

@[simp] lemma dom_coe (x : ℕ) : (x : enat).dom := trivial

instance : add_comm_monoid enat :=
{ add       := (+),
  zero      := (0),
  add_comm  := λ x y, roption.ext' and.comm (λ _ _, add_comm _ _),
  zero_add  := λ x, roption.ext' (true_and _) (λ _ _, zero_add _),
  add_zero  := λ x, roption.ext' (and_true _) (λ _ _, add_zero _),
  add_assoc := λ x y z, roption.ext' and.assoc (λ _ _, add_assoc _ _ _) }

instance : has_le enat := ⟨λ x y, ∃ h : y.dom → x.dom, ∀ hy : y.dom, x.get (h hy) ≤ y.get hy⟩
instance : has_top enat := ⟨none⟩
instance : has_bot enat := ⟨0⟩
instance : has_sup enat := ⟨λ x y, ⟨x.dom ∧ y.dom, λ h, x.get h.1 ⊔ y.get h.2⟩⟩

lemma le_def (x y : enat) : x ≤ y ↔ ∃ h : y.dom → x.dom, ∀ hy : y.dom, x.get (h hy) ≤ y.get hy :=
iff.rfl

@[elab_as_eliminator] protected lemma cases_on {P : enat → Prop} : ∀ a : enat,
  P ⊤ → (∀ n : ℕ, P n) → P a :=
roption.induction_on

@[simp] lemma top_add (x : enat) : ⊤ + x = ⊤ :=
roption.ext' (false_and _) (λ h, h.left.elim)

@[simp] lemma add_top (x : enat) : x + ⊤ = ⊤ :=
by rw [add_comm, top_add]

@[simp, norm_cast] lemma coe_zero : ((0 : ℕ) : enat) = 0 := rfl

@[simp, norm_cast] lemma coe_one : ((1 : ℕ) : enat) = 1 := rfl

@[simp, norm_cast] lemma coe_add (x y : ℕ) : ((x + y : ℕ) : enat) = x + y :=
roption.ext' (and_true _).symm (λ _ _, rfl)

lemma get_coe {x : ℕ} : get (x : enat) true.intro = x := rfl

@[simp, norm_cast] lemma get_coe' (x : ℕ) (h : (x : enat).dom) : get (x : enat) h = x := rfl

lemma coe_add_get {x : ℕ} {y : enat} (h : ((x : enat) + y).dom) :
  get ((x : enat) + y) h = x + get y h.2 := rfl

@[simp] lemma get_add {x y : enat} (h : (x + y).dom) :
  get (x + y) h = x.get h.1 + y.get h.2 := rfl

@[simp] lemma coe_get {x : enat} (h : x.dom) : (x.get h : enat) = x :=
roption.ext' (iff_of_true trivial h) (λ _ _, rfl)

@[simp] lemma get_zero (h : (0 : enat).dom) : (0 : enat).get h = 0 := rfl

@[simp] lemma get_one (h : (1 : enat).dom) : (1 : enat).get h = 1 := rfl

lemma dom_of_le_of_dom {x y : enat} : x ≤ y → y.dom → x.dom := λ ⟨h, _⟩, h

lemma dom_of_le_some {x : enat} {y : ℕ} (h : x ≤ y) : x.dom := dom_of_le_of_dom h trivial

instance decidable_le (x y : enat) [decidable x.dom] [decidable y.dom] : decidable (x ≤ y) :=
if hx : x.dom
then decidable_of_decidable_of_iff
  (show decidable (∀ (hy : (y : enat).dom), x.get hx ≤ (y : enat).get hy),
    from forall_prop_decidable _) $
  by { dsimp [(≤)], simp only [hx, exists_prop_of_true, forall_true_iff] }
else if hy : y.dom
then is_false $ λ h, hx $ dom_of_le_of_dom h hy
else is_true ⟨λ h, (hy h).elim, λ h, (hy h).elim⟩

/-- The coercion `ℕ → enat` preserves `0` and addition. -/
def coe_hom : ℕ →+ enat := ⟨coe, enat.coe_zero, enat.coe_add⟩

instance : partial_order enat :=
{ le          := (≤),
  le_refl     := λ x, ⟨id, λ _, le_refl _⟩,
  le_trans    := λ x y z ⟨hxy₁, hxy₂⟩ ⟨hyz₁, hyz₂⟩,
    ⟨hxy₁ ∘ hyz₁, λ _, le_trans (hxy₂ _) (hyz₂ _)⟩,
  le_antisymm := λ x y ⟨hxy₁, hxy₂⟩ ⟨hyx₁, hyx₂⟩, roption.ext' ⟨hyx₁, hxy₁⟩
    (λ _ _, le_antisymm (hxy₂ _) (hyx₂ _)) }

lemma lt_def (x y : enat) : x < y ↔ ∃ (hx : x.dom), ∀ (hy : y.dom), x.get hx < y.get hy :=
begin
  rw [lt_iff_le_not_le, le_def, le_def, not_exists],
  split,
  { rintro ⟨⟨hyx, H⟩, h⟩,
    by_cases hx : x.dom,
    { use hx, intro hy,
      specialize H hy, specialize h (λ _, hy),
      rw not_forall at h, cases h with hx' h,
      rw not_le at h, exact h },
    { specialize h (λ hx', (hx hx').elim),
      rw not_forall at h, cases h with hx' h,
      exact (hx hx').elim } },
  { rintro ⟨hx, H⟩, exact ⟨⟨λ _, hx, λ hy, (H hy).le⟩, λ hxy h, not_lt_of_le (h _) (H _)⟩ }
end

@[simp, norm_cast] lemma coe_le_coe {x y : ℕ} : (x : enat) ≤ y ↔ x ≤ y :=
⟨λ ⟨_, h⟩, h trivial, λ h, ⟨λ _, trivial, λ _, h⟩⟩

@[simp, norm_cast] lemma coe_lt_coe {x y : ℕ} : (x : enat) < y ↔ x < y :=
by rw [lt_iff_le_not_le, lt_iff_le_not_le, coe_le_coe, coe_le_coe]

@[simp] lemma get_le_get {x y : enat} {hx : x.dom} {hy : y.dom} :
  x.get hx ≤ y.get hy ↔ x ≤ y :=
by conv { to_lhs, rw [← coe_le_coe, coe_get, coe_get]}

lemma le_coe_iff (x : enat) (n : ℕ) : x ≤ n ↔ ∃ h : x.dom, x.get h ≤ n :=
begin
  show (∃ (h : true → x.dom), _) ↔ ∃ h : x.dom, x.get h ≤ n,
  simp only [forall_prop_of_true, dom_coe, get_coe'],
  split; rintro ⟨_, _⟩; refine ⟨_, _⟩; intros; try { assumption }
end

lemma lt_coe_iff (x : enat) (n : ℕ) : x < n ↔ ∃ h : x.dom, x.get h < n :=
by simp only [lt_def, forall_prop_of_true, get_coe', dom_coe]

lemma coe_le_iff (n : ℕ) (x : enat) : (n : enat) ≤ x ↔ ∀ h : x.dom, n ≤ x.get h :=
by simpa only [le_def, exists_prop_of_true, dom_coe, forall_true_iff] using iff.rfl

lemma coe_lt_iff (n : ℕ) (x : enat) : (n : enat) < x ↔ ∀ h : x.dom, n < x.get h :=
by simpa only [lt_def, exists_prop_of_true, dom_coe] using iff.rfl

protected lemma zero_lt_one : (0 : enat) < 1 :=
by { norm_cast, norm_num }

instance semilattice_sup_bot : semilattice_sup_bot enat :=
{ sup := (⊔),
  bot := (⊥),
  bot_le := λ _, ⟨λ _, trivial, λ _, nat.zero_le _⟩,
  le_sup_left := λ _ _, ⟨and.left, λ _, le_sup_left⟩,
  le_sup_right := λ _ _, ⟨and.right, λ _, le_sup_right⟩,
  sup_le := λ x y z ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩, ⟨λ hz, ⟨hx₁ hz, hy₁ hz⟩,
    λ _, sup_le (hx₂ _) (hy₂ _)⟩,
  ..enat.partial_order }

instance order_top : order_top enat :=
{ top := (⊤),
  le_top := λ x, ⟨λ h, false.elim h, λ hy, false.elim hy⟩,
  ..enat.semilattice_sup_bot }

lemma dom_of_lt {x y : enat} : x < y → x.dom :=
enat.cases_on x not_top_lt $ λ _ _, trivial

lemma top_eq_none : (⊤ : enat) = none := rfl

@[simp] lemma coe_lt_top (x : ℕ) : (x : enat) < ⊤ :=
lt_of_le_of_ne le_top (λ h, absurd (congr_arg dom h) true_ne_false)

@[simp] lemma coe_ne_top (x : ℕ) : (x : enat) ≠ ⊤ := ne_of_lt (coe_lt_top x)

lemma ne_top_iff {x : enat} : x ≠ ⊤ ↔ ∃(n : ℕ), x = n := roption.ne_none_iff

lemma ne_top_iff_dom {x : enat} : x ≠ ⊤ ↔ x.dom :=
by classical; exact not_iff_comm.1 roption.eq_none_iff'.symm

lemma ne_top_of_lt {x y : enat} (h : x < y) : x ≠ ⊤ :=
ne_of_lt $ lt_of_lt_of_le h le_top

lemma eq_top_iff_forall_lt (x : enat) : x = ⊤ ↔ ∀ n : ℕ, (n : enat) < x :=
begin
  split,
  { rintro rfl n, exact coe_lt_top _ },
  { contrapose!, rw ne_top_iff, rintro ⟨n, rfl⟩, exact ⟨n, irrefl _⟩ }
end

lemma eq_top_iff_forall_le (x : enat) : x = ⊤ ↔ ∀ n : ℕ, (n : enat) ≤ x :=
(eq_top_iff_forall_lt x).trans
⟨λ h n, (h n).le, λ h n, lt_of_lt_of_le (coe_lt_coe.mpr n.lt_succ_self) (h (n + 1))⟩

lemma pos_iff_one_le {x : enat} : 0 < x ↔ 1 ≤ x :=
enat.cases_on x ⟨λ _, le_top, λ _, coe_lt_top _⟩
  (λ n, ⟨λ h, enat.coe_le_coe.2 (enat.coe_lt_coe.1 h),
    λ h, enat.coe_lt_coe.2 (enat.coe_le_coe.1 h)⟩)

noncomputable instance : linear_order enat :=
{ le_total := λ x y, enat.cases_on x
    (or.inr le_top) (enat.cases_on y (λ _, or.inl le_top)
      (λ x y, (le_total x y).elim (or.inr ∘ coe_le_coe.2)
        (or.inl ∘ coe_le_coe.2))),
  decidable_le := classical.dec_rel _,
  ..enat.partial_order }

noncomputable instance : bounded_lattice enat :=
{ inf := min,
  inf_le_left := min_le_left,
  inf_le_right := min_le_right,
  le_inf := λ _ _ _, le_min,
  ..enat.order_top,
  ..enat.semilattice_sup_bot }

lemma sup_eq_max {a b : enat} : a ⊔ b = max a b :=
le_antisymm (sup_le (le_max_left _ _) (le_max_right _ _))
  (max_le le_sup_left le_sup_right)

lemma inf_eq_min {a b : enat} : a ⊓ b = min a b := rfl

instance : ordered_add_comm_monoid enat :=
{ add_le_add_left := λ a b ⟨h₁, h₂⟩ c,
    enat.cases_on c (by simp)
      (λ c, ⟨λ h, and.intro trivial (h₁ h.2),
        λ _, add_le_add_left (h₂ _) c⟩),
  lt_of_add_lt_add_left := λ a b c, enat.cases_on a
    (λ h, by simpa [lt_irrefl] using h)
    (λ a, enat.cases_on b
      (λ h, absurd h (not_lt_of_ge (by rw add_top; exact le_top)))
      (λ b, enat.cases_on c
        (λ _, coe_lt_top _)
        (λ c h,  coe_lt_coe.2 (by rw [← coe_add, ← coe_add, coe_lt_coe] at h;
            exact lt_of_add_lt_add_left h)))),
  ..enat.linear_order,
  ..enat.add_comm_monoid }

instance : canonically_ordered_add_monoid enat :=
{ le_iff_exists_add := λ a b, enat.cases_on b
    (iff_of_true le_top ⟨⊤, (add_top _).symm⟩)
    (λ b, enat.cases_on a
      (iff_of_false (not_le_of_gt (coe_lt_top _))
        (not_exists.2 (λ x, ne_of_lt (by rw [top_add]; exact coe_lt_top _))))
      (λ a, ⟨λ h, ⟨(b - a : ℕ),
          by rw [← coe_add, coe_inj, add_comm, nat.sub_add_cancel (coe_le_coe.1 h)]⟩,
        (λ ⟨c, hc⟩, enat.cases_on c
          (λ hc, hc.symm ▸ show (a : enat) ≤ a + ⊤, by rw [add_top]; exact le_top)
          (λ c (hc : (b : enat) = a + c),
            coe_le_coe.2 (by rw [← coe_add, coe_inj] at hc;
              rw hc; exact nat.le_add_right _ _)) hc)⟩)),
  ..enat.semilattice_sup_bot,
  ..enat.ordered_add_comm_monoid }

protected lemma add_lt_add_right {x y z : enat} (h : x < y) (hz : z ≠ ⊤) : x + z < y + z :=
begin
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩,
  rcases ne_top_iff.mp hz with ⟨k, rfl⟩,
  induction y using enat.cases_on with n,
  { rw [top_add], apply_mod_cast coe_lt_top },
  norm_cast at h, apply_mod_cast add_lt_add_right h
end

protected lemma add_lt_add_iff_right {x y z : enat} (hz : z ≠ ⊤) : x + z < y + z ↔ x < y :=
⟨lt_of_add_lt_add_right, λ h, enat.add_lt_add_right h hz⟩

protected lemma add_lt_add_iff_left {x y z : enat} (hz : z ≠ ⊤) : z + x < z + y ↔ x < y :=
by rw [add_comm z, add_comm z, enat.add_lt_add_iff_right hz]

protected lemma lt_add_iff_pos_right {x y : enat} (hx : x ≠ ⊤) : x < x + y ↔ 0 < y :=
by { conv_rhs { rw [← enat.add_lt_add_iff_left hx] }, rw [add_zero] }

lemma lt_add_one {x : enat} (hx : x ≠ ⊤) : x < x + 1 :=
by { rw [enat.lt_add_iff_pos_right hx], norm_cast, norm_num }

lemma le_of_lt_add_one {x y : enat} (h : x < y + 1) : x ≤ y :=
begin
  induction y using enat.cases_on with n, apply le_top,
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩,
  apply_mod_cast nat.le_of_lt_succ, apply_mod_cast h
end

lemma add_one_le_of_lt {x y : enat} (h : x < y) : x + 1 ≤ y :=
begin
  induction y using enat.cases_on with n, apply le_top,
  rcases ne_top_iff.mp (ne_top_of_lt h) with ⟨m, rfl⟩,
  apply_mod_cast nat.succ_le_of_lt, apply_mod_cast h
end

lemma add_one_le_iff_lt {x y : enat} (hx : x ≠ ⊤) : x + 1 ≤ y ↔ x < y :=
begin
  split, swap, exact add_one_le_of_lt,
  intro h, rcases ne_top_iff.mp hx with ⟨m, rfl⟩,
  induction y using enat.cases_on with n, apply coe_lt_top,
  apply_mod_cast nat.lt_of_succ_le, apply_mod_cast h
end

lemma lt_add_one_iff_lt {x y : enat} (hx : x ≠ ⊤) : x < y + 1 ↔ x ≤ y :=
begin
  split, exact le_of_lt_add_one,
  intro h, rcases ne_top_iff.mp hx with ⟨m, rfl⟩,
  induction y using enat.cases_on with n, { rw [top_add], apply coe_lt_top },
  apply_mod_cast nat.lt_succ_of_le, apply_mod_cast h
end

lemma add_eq_top_iff {a b : enat} : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ :=
by apply enat.cases_on a; apply enat.cases_on b;
  simp; simp only [(enat.coe_add _ _).symm, enat.coe_ne_top]; simp

protected lemma add_right_cancel_iff {a b c : enat} (hc : c ≠ ⊤) : a + c = b + c ↔ a = b :=
begin
  rcases ne_top_iff.1 hc with ⟨c, rfl⟩,
  apply enat.cases_on a; apply enat.cases_on b;
  simp [add_eq_top_iff, coe_ne_top, @eq_comm _ (⊤ : enat)];
  simp only [(enat.coe_add _ _).symm, add_left_cancel_iff, enat.coe_inj, add_comm];
  tauto
end

protected lemma add_left_cancel_iff {a b c : enat} (ha : a ≠ ⊤) : a + b = a + c ↔ b = c :=
by rw [add_comm a, add_comm a, enat.add_right_cancel_iff ha]

section with_top

/-- Computably converts an `enat` to a `with_top ℕ`. -/
def to_with_top (x : enat) [decidable x.dom] : with_top ℕ := x.to_option

lemma to_with_top_top : to_with_top ⊤ = ⊤ := rfl

@[simp] lemma to_with_top_top' {h : decidable (⊤ : enat).dom} : to_with_top ⊤ = ⊤ :=
by convert to_with_top_top

lemma to_with_top_zero : to_with_top 0 = 0 := rfl

@[simp] lemma to_with_top_zero' {h : decidable (0 : enat).dom} : to_with_top 0 = 0 :=
by convert to_with_top_zero

lemma to_with_top_coe (n : ℕ) : to_with_top n = n := rfl

@[simp] lemma to_with_top_coe' (n : ℕ) {h : decidable (n : enat).dom} : to_with_top (n : enat) = n :=
by convert to_with_top_coe n

@[simp] lemma to_with_top_le {x y : enat} : Π [decidable x.dom]
  [decidable y.dom], by exactI to_with_top x ≤ to_with_top y ↔ x ≤ y :=
enat.cases_on y (by simp) (enat.cases_on x (by simp) (by intros; simp))

@[simp] lemma to_with_top_lt {x y : enat} [decidable x.dom] [decidable y.dom] :
  to_with_top x < to_with_top y ↔ x < y :=
lt_iff_lt_of_le_iff_le to_with_top_le

end with_top

section with_top_equiv

open_locale classical

@[simp] lemma to_with_top_add {x y : enat} : to_with_top (x + y) = to_with_top x + to_with_top y :=
begin
  apply enat.cases_on y; apply enat.cases_on x,
  { simp },
  { simp },
  { simp },
  -- not sure why `simp` can't do this
  { intros, rw [to_with_top_coe', to_with_top_coe'], norm_cast, exact to_with_top_coe' _ }
end

/-- `equiv` between `enat` and `with_top ℕ` (for the order isomorphism see `with_top_order_iso`). -/
noncomputable def with_top_equiv : enat ≃ with_top ℕ :=
{ to_fun := λ x, to_with_top x,
  inv_fun := λ x, match x with (some n) := coe n | none := ⊤ end,
  left_inv := λ x, by apply enat.cases_on x; intros; simp; refl,
  right_inv := λ x, by cases x; simp [with_top_equiv._match_1]; refl }

@[simp] lemma with_top_equiv_top : with_top_equiv ⊤ = ⊤ :=
to_with_top_top'

@[simp] lemma with_top_equiv_coe (n : nat) : with_top_equiv n = n :=
to_with_top_coe' _

@[simp] lemma with_top_equiv_zero : with_top_equiv 0 = 0 :=
with_top_equiv_coe _

@[simp] lemma with_top_equiv_le {x y : enat} : with_top_equiv x ≤ with_top_equiv y ↔ x ≤ y :=
to_with_top_le

@[simp] lemma with_top_equiv_lt {x y : enat} : with_top_equiv x < with_top_equiv y ↔ x < y :=
to_with_top_lt

/-- `to_with_top` induces an order isomorphism between `enat` and `with_top ℕ`. -/
noncomputable def with_top_order_iso : enat ≃o with_top ℕ :=
{ map_rel_iff' := λ _ _, with_top_equiv_le,
  .. with_top_equiv}

@[simp] lemma with_top_equiv_symm_top : with_top_equiv.symm ⊤ = ⊤ :=
rfl

@[simp] lemma with_top_equiv_symm_coe (n : nat) : with_top_equiv.symm n = n :=
rfl

@[simp] lemma with_top_equiv_symm_zero : with_top_equiv.symm 0 = 0 :=
rfl

@[simp] lemma with_top_equiv_symm_le {x y : with_top ℕ} :
  with_top_equiv.symm x ≤ with_top_equiv.symm y ↔ x ≤ y :=
by rw ← with_top_equiv_le; simp

@[simp] lemma with_top_equiv_symm_lt {x y : with_top ℕ} :
  with_top_equiv.symm x < with_top_equiv.symm y ↔ x < y :=
by rw ← with_top_equiv_lt; simp

/-- `to_with_top` induces an additive monoid isomorphism between `enat` and `with_top ℕ`. -/
noncomputable def with_top_add_equiv : enat ≃+ with_top ℕ :=
{ map_add' := λ x y, by simp only [with_top_equiv]; convert to_with_top_add,
  ..with_top_equiv}

end with_top_equiv

lemma lt_wf : well_founded ((<) : enat → enat → Prop) :=
show well_founded (λ a b : enat, a < b),
by haveI := classical.dec; simp only [to_with_top_lt.symm] {eta := ff};
    exact inv_image.wf _ (with_top.well_founded_lt nat.lt_wf)

instance : has_well_founded enat := ⟨(<), lt_wf⟩

section find

variables (P : ℕ → Prop) [decidable_pred P]

/-- The smallest `enat` satisfying a (decidable) predicate `P : ℕ → Prop` -/
def find : enat := ⟨∃ n, P n, nat.find⟩

@[simp] lemma find_get (h : (find P).dom) : (find P).get h = nat.find h := rfl

lemma find_dom (h : ∃ n, P n) : (find P).dom := h

lemma lt_find (n : ℕ) (h : ∀ m ≤ n, ¬P m) : (n : enat) < find P :=
begin
  rw coe_lt_iff, intro h', rw find_get,
  have := @nat.find_spec P _ h',
  contrapose! this,
  exact h _ this
end

lemma lt_find_iff (n : ℕ) : (n : enat) < find P ↔ (∀ m ≤ n, ¬P m) :=
begin
  refine ⟨_, lt_find P n⟩,
  intros h m hm,
  by_cases H : (find P).dom,
  { apply nat.find_min H, rw coe_lt_iff at h, specialize h H, exact lt_of_le_of_lt hm h },
  { exact not_exists.mp H m }
end

lemma find_le (n : ℕ) (h : P n) : find P ≤ n :=
by { rw le_coe_iff, refine ⟨⟨_, h⟩, @nat.find_min' P _ _ _ h⟩ }

lemma find_eq_top_iff : find P = ⊤ ↔ ∀ n, ¬P n :=
(eq_top_iff_forall_lt _).trans
⟨λ h n, (lt_find_iff P n).mp (h n) _ le_rfl, λ h n, lt_find P n $ λ _ _, h _⟩

end find

end enat
