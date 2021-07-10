/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import algebra.linear_ordered_comm_group_with_zero
import algebra.big_operators.ring
import data.real.basic
import algebra.indicator_function
import algebra.algebra.basic

/-!
# Nonnegative real numbers

In this file we define `nnreal` (notation: `ℝ≥0`) to be the type of non-negative real numbers,
a.k.a. the interval `[0, ∞)`. We also define the following operations and structures on `ℝ≥0`:

* the order on `ℝ≥0` is the restriction of the order on `ℝ`; these relations define a conditionally
  complete linear order with a bottom element, `conditionally_complete_linear_order_bot`;

* `a + b` and `a * b` are the restrictions of addition and multiplication of real numbers to `ℝ≥0`;
  these operations together with `0 = ⟨0, _⟩` and `1 = ⟨1, _⟩` turn `ℝ≥0` into a linear ordered
  archimedean commutative semifield; we have no typeclass for this in `mathlib` yet, so we define
  the following instances instead:

  - `linear_ordered_semiring ℝ≥0`;
  - `comm_semiring ℝ≥0`;
  - `canonically_ordered_comm_semiring ℝ≥0`;
  - `linear_ordered_comm_group_with_zero ℝ≥0`;
  - `archimedean ℝ≥0`.

* `real.to_nnreal x` is defined as `⟨max x 0, _⟩`, i.e. `↑(real.to_nnreal x) = x` when `0 ≤ x` and
  `↑(real.to_nnreal x) = 0` otherwise.

We also define an instance `can_lift ℝ ℝ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℝ` and `hx : 0 ≤ x` in the proof context with `x : ℝ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℝ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notations

This file defines `ℝ≥0` as a localized notation for `nnreal`.
-/

noncomputable theory

open_locale classical big_operators

/-- Nonnegative real numbers. -/
def nnreal := {r : ℝ // 0 ≤ r}
localized "notation ` ℝ≥0 ` := nnreal" in nnreal

namespace nnreal

instance : has_coe ℝ≥0 ℝ := ⟨subtype.val⟩

/- Simp lemma to put back `n.val` into the normal form given by the coercion. -/
@[simp] lemma val_eq_coe (n : ℝ≥0) : n.val = n := rfl

instance : can_lift ℝ ℝ≥0 :=
{ coe := coe,
  cond := λ r, 0 ≤ r,
  prf := λ x hx, ⟨⟨x, hx⟩, rfl⟩ }

protected lemma eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m := subtype.eq

protected lemma eq_iff {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) ↔ n = m :=
iff.intro nnreal.eq (congr_arg coe)

lemma ne_iff {x y : ℝ≥0} : (x : ℝ) ≠ (y : ℝ) ↔ x ≠ y :=
not_iff_not_of_iff $ nnreal.eq_iff

/-- Reinterpret a real number `r` as a non-negative real number. Returns `0` if `r < 0`. -/
def _root_.real.to_nnreal (r : ℝ) : ℝ≥0 := ⟨max r 0, le_max_right _ _⟩

lemma _root_.real.coe_to_nnreal (r : ℝ) (hr : 0 ≤ r) : (real.to_nnreal r : ℝ) = r :=
max_eq_left hr

lemma _root_.real.le_coe_to_nnreal (r : ℝ) : r ≤ real.to_nnreal r :=
le_max_left r 0

lemma coe_nonneg (r : ℝ≥0) : (0 : ℝ) ≤ r := r.2
@[norm_cast]
theorem coe_mk (a : ℝ) (ha) : ((⟨a, ha⟩ : ℝ≥0) : ℝ) = a := rfl

instance : has_zero ℝ≥0  := ⟨⟨0, le_refl 0⟩⟩
instance : has_one ℝ≥0   := ⟨⟨1, zero_le_one⟩⟩
instance : has_add ℝ≥0   := ⟨λa b, ⟨a + b, add_nonneg a.2 b.2⟩⟩
instance : has_sub ℝ≥0   := ⟨λa b, real.to_nnreal (a - b)⟩
instance : has_mul ℝ≥0   := ⟨λa b, ⟨a * b, mul_nonneg a.2 b.2⟩⟩
instance : has_inv ℝ≥0   := ⟨λa, ⟨(a.1)⁻¹, inv_nonneg.2 a.2⟩⟩
instance : has_div ℝ≥0   := ⟨λa b, ⟨a / b, div_nonneg a.2 b.2⟩⟩
instance : has_le ℝ≥0    := ⟨λ r s, (r:ℝ) ≤ s⟩
instance : has_bot ℝ≥0   := ⟨0⟩
instance : inhabited ℝ≥0 := ⟨0⟩

protected lemma coe_injective : function.injective (coe : ℝ≥0 → ℝ) := subtype.coe_injective
@[simp, norm_cast] protected lemma coe_eq {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) = r₂ ↔ r₁ = r₂ :=
nnreal.coe_injective.eq_iff
@[simp, norm_cast] protected lemma coe_zero : ((0 : ℝ≥0) : ℝ) = 0 := rfl
@[simp, norm_cast] protected lemma coe_one  : ((1 : ℝ≥0) : ℝ) = 1 := rfl
@[simp, norm_cast] protected lemma coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ := rfl
@[simp, norm_cast] protected lemma coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ := rfl
@[simp, norm_cast] protected lemma coe_inv (r : ℝ≥0) : ((r⁻¹ : ℝ≥0) : ℝ) = r⁻¹ := rfl
@[simp, norm_cast] protected lemma coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = r₁ / r₂ := rfl
@[simp, norm_cast] protected lemma coe_bit0 (r : ℝ≥0) : ((bit0 r : ℝ≥0) : ℝ) = bit0 r := rfl
@[simp, norm_cast] protected lemma coe_bit1 (r : ℝ≥0) : ((bit1 r : ℝ≥0) : ℝ) = bit1 r := rfl

@[simp, norm_cast] protected lemma coe_sub {r₁ r₂ : ℝ≥0} (h : r₂ ≤ r₁) :
  ((r₁ - r₂ : ℝ≥0) : ℝ) = r₁ - r₂ :=
max_eq_left $ le_sub.2 $ by simp [show (r₂ : ℝ) ≤ r₁, from h]

-- TODO: setup semifield!
@[simp] protected lemma coe_eq_zero (r : ℝ≥0) : ↑r = (0 : ℝ) ↔ r = 0 := by norm_cast
lemma coe_ne_zero {r : ℝ≥0} : (r : ℝ) ≠ 0 ↔ r ≠ 0 := by norm_cast

instance : comm_semiring ℝ≥0 :=
{ zero := 0,
  add := (+),
  one := 1,
  mul := (*),
  .. nnreal.coe_injective.comm_semiring _ rfl rfl (λ _ _, rfl) (λ _ _, rfl) }

/-- Coercion `ℝ≥0 → ℝ` as a `ring_hom`. -/
def to_real_hom : ℝ≥0 →+* ℝ :=
⟨coe, nnreal.coe_one, nnreal.coe_mul, nnreal.coe_zero, nnreal.coe_add⟩

@[simp] lemma coe_to_real_hom : ⇑to_real_hom = coe := rfl

section actions

/-- A `mul_action` over `ℝ` restricts to a `mul_action` over `ℝ≥0`. -/
instance {M : Type*} [mul_action ℝ M] : mul_action ℝ≥0 M :=
mul_action.comp_hom M to_real_hom.to_monoid_hom

lemma smul_def {M : Type*} [mul_action ℝ M] (c : ℝ≥0) (x : M) :
  c • x = (c : ℝ) • x := rfl

instance {M N : Type*} [mul_action ℝ M] [mul_action ℝ N] [has_scalar M N]
  [is_scalar_tower ℝ M N] : is_scalar_tower ℝ≥0 M N :=
{ smul_assoc := λ r, (smul_assoc (r : ℝ) : _)}

instance smul_comm_class_left {M N : Type*} [mul_action ℝ N] [has_scalar M N]
  [smul_comm_class ℝ M N] : smul_comm_class ℝ≥0 M N :=
{ smul_comm := λ r, (smul_comm (r : ℝ) : _)}

instance smul_comm_class_right {M N : Type*} [mul_action ℝ N] [has_scalar M N]
  [smul_comm_class M ℝ N] : smul_comm_class M ℝ≥0 N :=
{ smul_comm := λ m r, (smul_comm m (r : ℝ) : _)}

/-- A `distrib_mul_action` over `ℝ` restricts to a `distrib_mul_action` over `ℝ≥0`. -/
instance {M : Type*} [add_monoid M] [distrib_mul_action ℝ M] : distrib_mul_action ℝ≥0 M :=
distrib_mul_action.comp_hom M to_real_hom.to_monoid_hom

/-- A `module` over `ℝ` restricts to a `module` over `ℝ≥0`. -/
instance {M : Type*} [add_comm_monoid M] [module ℝ M] : module ℝ≥0 M :=
module.comp_hom M to_real_hom

/-- An `algebra` over `ℝ` restricts to an `algebra` over `ℝ≥0`. -/
instance {A : Type*} [semiring A] [algebra ℝ A] : algebra ℝ≥0 A :=
{ smul := (•),
  commutes' := λ r x, by simp [algebra.commutes],
  smul_def' := λ r x, by simp [←algebra.smul_def (r : ℝ) x, smul_def],
  to_ring_hom := ((algebra_map ℝ A).comp (to_real_hom : ℝ≥0 →+* ℝ)) }

-- verify that the above produces instances we might care about
example : algebra ℝ≥0 ℝ := by apply_instance
example : distrib_mul_action (units ℝ≥0) ℝ := by apply_instance

end actions

instance : comm_group_with_zero ℝ≥0 :=
{ zero := 0,
  mul := (*),
  one := 1,
  inv := has_inv.inv,
  div := (/),
  .. nnreal.coe_injective.comm_group_with_zero _ rfl rfl (λ _ _, rfl) (λ _, rfl) (λ _ _, rfl) }

@[simp, norm_cast] lemma coe_indicator {α} (s : set α) (f : α → ℝ≥0) (a : α) :
  ((s.indicator f a : ℝ≥0) : ℝ) = s.indicator (λ x, f x) a :=
(to_real_hom : ℝ≥0 →+ ℝ).map_indicator _ _ _

@[simp, norm_cast] lemma coe_pow (r : ℝ≥0) (n : ℕ) : ((r^n : ℝ≥0) : ℝ) = r^n :=
to_real_hom.map_pow r n

@[norm_cast] lemma coe_list_sum (l : list ℝ≥0) :
  ((l.sum : ℝ≥0) : ℝ) = (l.map coe).sum :=
to_real_hom.map_list_sum l

@[norm_cast] lemma coe_list_prod (l : list ℝ≥0) :
  ((l.prod : ℝ≥0) : ℝ) = (l.map coe).prod :=
to_real_hom.map_list_prod l

@[norm_cast] lemma coe_multiset_sum (s : multiset ℝ≥0) :
  ((s.sum : ℝ≥0) : ℝ) = (s.map coe).sum :=
to_real_hom.map_multiset_sum s

@[norm_cast] lemma coe_multiset_prod (s : multiset ℝ≥0) :
  ((s.prod : ℝ≥0) : ℝ) = (s.map coe).prod :=
to_real_hom.map_multiset_prod s

@[norm_cast] lemma coe_sum {α} {s : finset α} {f : α → ℝ≥0} :
  ↑(∑ a in s, f a) = ∑ a in s, (f a : ℝ) :=
to_real_hom.map_sum _ _

lemma _root_.real.to_nnreal_sum_of_nonneg {α} {s : finset α} {f : α → ℝ}
  (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  real.to_nnreal (∑ a in s, f a) = ∑ a in s, real.to_nnreal (f a) :=
begin
  rw [←nnreal.coe_eq, nnreal.coe_sum, real.coe_to_nnreal _ (finset.sum_nonneg hf)],
  exact finset.sum_congr rfl (λ x hxs, by rw real.coe_to_nnreal _ (hf x hxs)),
end

@[norm_cast] lemma coe_prod {α} {s : finset α} {f : α → ℝ≥0} :
  ↑(∏ a in s, f a) = ∏ a in s, (f a : ℝ) :=
to_real_hom.map_prod _ _

lemma _root_.real.to_nnreal_prod_of_nonneg {α} {s : finset α} {f : α → ℝ}
  (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  real.to_nnreal (∏ a in s, f a) = ∏ a in s, real.to_nnreal (f a) :=
begin
  rw [←nnreal.coe_eq, nnreal.coe_prod, real.coe_to_nnreal _ (finset.prod_nonneg hf)],
  exact finset.prod_congr rfl (λ x hxs, by rw real.coe_to_nnreal _ (hf x hxs)),
end

@[norm_cast] lemma nsmul_coe (r : ℝ≥0) (n : ℕ) : ↑(n • r) = n • (r:ℝ) :=
to_real_hom.to_add_monoid_hom.map_nsmul _ _

@[simp, norm_cast] protected lemma coe_nat_cast (n : ℕ) : (↑(↑n : ℝ≥0) : ℝ) = n :=
to_real_hom.map_nat_cast n

instance : linear_order ℝ≥0 :=
linear_order.lift (coe : ℝ≥0 → ℝ) nnreal.coe_injective

@[simp, norm_cast] protected lemma coe_le_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) ≤ r₂ ↔ r₁ ≤ r₂ := iff.rfl
@[simp, norm_cast] protected lemma coe_lt_coe {r₁ r₂ : ℝ≥0} : (r₁ : ℝ) < r₂ ↔ r₁ < r₂ := iff.rfl
@[simp, norm_cast] protected lemma coe_pos {r : ℝ≥0} : (0 : ℝ) < r ↔ 0 < r := iff.rfl

protected lemma coe_mono : monotone (coe : ℝ≥0 → ℝ) := λ _ _, nnreal.coe_le_coe.2

protected lemma _root_.real.to_nnreal_mono : monotone real.to_nnreal :=
λ x y h, max_le_max h (le_refl 0)

@[simp] lemma _root_.real.to_nnreal_coe {r : ℝ≥0} : real.to_nnreal r = r :=
nnreal.eq $ max_eq_left r.2

@[simp] lemma mk_coe_nat (n : ℕ) : @eq ℝ≥0 (⟨(n : ℝ), n.cast_nonneg⟩ : ℝ≥0) n :=
nnreal.eq (nnreal.coe_nat_cast n).symm

@[simp] lemma to_nnreal_coe_nat (n : ℕ) : real.to_nnreal n = n :=
nnreal.eq $ by simp [real.coe_to_nnreal]

/-- `real.to_nnreal` and `coe : ℝ≥0 → ℝ` form a Galois insertion. -/
protected def gi : galois_insertion real.to_nnreal coe :=
galois_insertion.monotone_intro nnreal.coe_mono real.to_nnreal_mono
  real.le_coe_to_nnreal (λ _, real.to_nnreal_coe)

instance : order_bot ℝ≥0 :=
{ bot := ⊥, bot_le := assume ⟨a, h⟩, h, .. nnreal.linear_order }

instance : canonically_linear_ordered_add_monoid ℝ≥0 :=
{ add_le_add_left       := assume a b h c,
    nnreal.coe_le_coe.mp $ (add_le_add_left (nnreal.coe_le_coe.mpr h) c),
  lt_of_add_lt_add_left := assume a b c bc,
    nnreal.coe_lt_coe.mp $ lt_of_add_lt_add_left (nnreal.coe_lt_coe.mpr bc),
  le_iff_exists_add     := assume ⟨a, ha⟩ ⟨b, hb⟩,
    iff.intro
      (assume h : a ≤ b,
        ⟨⟨b - a, le_sub_iff_add_le.2 $ (zero_add _).le.trans h⟩,
          nnreal.eq $ show b = a + (b - a), from (add_sub_cancel'_right _ _).symm⟩)
      (assume ⟨⟨c, hc⟩, eq⟩, eq.symm ▸ show a ≤ a + c, from (le_add_iff_nonneg_right a).2 hc),
  ..nnreal.comm_semiring,
  ..nnreal.order_bot,
  ..nnreal.linear_order }

instance : linear_ordered_add_comm_monoid ℝ≥0 :=
{ .. nnreal.comm_semiring,
  .. nnreal.canonically_linear_ordered_add_monoid }

instance : distrib_lattice ℝ≥0 := by apply_instance

instance : semilattice_inf_bot ℝ≥0 :=
{ .. nnreal.order_bot, .. nnreal.distrib_lattice }

instance : semilattice_sup_bot ℝ≥0 :=
{ .. nnreal.order_bot, .. nnreal.distrib_lattice }

instance : linear_ordered_semiring ℝ≥0 :=
{ add_left_cancel            := assume a b c h, nnreal.eq $
    @add_left_cancel ℝ _ a b c (nnreal.eq_iff.2 h),
  le_of_add_le_add_left      := assume a b c, @le_of_add_le_add_left ℝ _ _ _ a b c,
  mul_lt_mul_of_pos_left     := assume a b c, @mul_lt_mul_of_pos_left ℝ _ a b c,
  mul_lt_mul_of_pos_right    := assume a b c, @mul_lt_mul_of_pos_right ℝ _ a b c,
  zero_le_one                := @zero_le_one ℝ _,
  exists_pair_ne             := ⟨0, 1, ne_of_lt (@zero_lt_one ℝ _ _)⟩,
  .. nnreal.canonically_linear_ordered_add_monoid,
  .. nnreal.comm_semiring, }

instance : linear_ordered_comm_group_with_zero ℝ≥0 :=
{ mul_le_mul_left := assume a b h c, mul_le_mul (le_refl c) h (zero_le a) (zero_le c),
  zero_le_one := zero_le 1,
  .. nnreal.linear_ordered_semiring,
  .. nnreal.comm_group_with_zero }

instance : canonically_ordered_comm_semiring ℝ≥0 :=
{ .. nnreal.canonically_linear_ordered_add_monoid,
  .. nnreal.comm_semiring,
  .. (show no_zero_divisors ℝ≥0, by apply_instance),
  .. nnreal.comm_group_with_zero }

instance : densely_ordered ℝ≥0 :=
⟨assume a b (h : (a : ℝ) < b), let ⟨c, hac, hcb⟩ := exists_between h in
  ⟨⟨c, le_trans a.property $ le_of_lt $ hac⟩, hac, hcb⟩⟩

instance : no_top_order ℝ≥0 :=
⟨assume a, let ⟨b, hb⟩ := no_top (a:ℝ) in ⟨⟨b, le_trans a.property $ le_of_lt $ hb⟩, hb⟩⟩

lemma bdd_above_coe {s : set ℝ≥0} : bdd_above ((coe : ℝ≥0 → ℝ) '' s) ↔ bdd_above s :=
iff.intro
  (assume ⟨b, hb⟩, ⟨real.to_nnreal b, assume ⟨y, hy⟩ hys, show y ≤ max b 0, from
    le_max_of_le_left $ hb $ set.mem_image_of_mem _ hys⟩)
  (assume ⟨b, hb⟩, ⟨b, assume y ⟨x, hx, eq⟩, eq ▸ hb hx⟩)

lemma bdd_below_coe (s : set ℝ≥0) : bdd_below ((coe : ℝ≥0 → ℝ) '' s) :=
⟨0, assume r ⟨q, _, eq⟩, eq ▸ q.2⟩

instance : has_Sup ℝ≥0 :=
⟨λs, ⟨Sup ((coe : ℝ≥0 → ℝ) '' s),
  begin
    cases s.eq_empty_or_nonempty with h h,
    { simp [h, set.image_empty, real.Sup_empty] },
    rcases h with ⟨⟨b, hb⟩, hbs⟩,
    by_cases h' : bdd_above s,
    { exact le_cSup_of_le (bdd_above_coe.2 h') (set.mem_image_of_mem _ hbs) hb },
    { rw [real.Sup_of_not_bdd_above], rwa [bdd_above_coe] }
  end⟩⟩

instance : has_Inf ℝ≥0 :=
⟨λs, ⟨Inf ((coe : ℝ≥0 → ℝ) '' s),
  begin
    cases s.eq_empty_or_nonempty with h h,
    { simp [h, set.image_empty, real.Inf_empty] },
    exact le_cInf (h.image _) (assume r ⟨q, _, eq⟩, eq ▸ q.2)
  end⟩⟩

lemma coe_Sup (s : set ℝ≥0) : (↑(Sup s) : ℝ) = Sup ((coe : ℝ≥0 → ℝ) '' s) := rfl
lemma coe_Inf (s : set ℝ≥0) : (↑(Inf s) : ℝ) = Inf ((coe : ℝ≥0 → ℝ) '' s) := rfl

instance : conditionally_complete_linear_order_bot ℝ≥0 :=
{ Sup     := Sup,
  Inf     := Inf,
  le_cSup := assume s a hs ha, le_cSup (bdd_above_coe.2 hs) (set.mem_image_of_mem _ ha),
  cSup_le := assume s a hs h,show Sup ((coe : ℝ≥0 → ℝ) '' s) ≤ a, from
    cSup_le (by simp [hs]) $ assume r ⟨b, hb, eq⟩, eq ▸ h hb,
  cInf_le := assume s a _ has, cInf_le (bdd_below_coe s) (set.mem_image_of_mem _ has),
  le_cInf := assume s a hs h, show (↑a : ℝ) ≤ Inf ((coe : ℝ≥0 → ℝ) '' s), from
    le_cInf (by simp [hs]) $ assume r ⟨b, hb, eq⟩, eq ▸ h hb,
  cSup_empty := nnreal.eq $ by simp [coe_Sup, real.Sup_empty]; refl,
  decidable_le := begin assume x y, apply classical.dec end,
  .. nnreal.linear_ordered_semiring, .. lattice_of_linear_order,
  .. nnreal.order_bot }

instance : archimedean ℝ≥0 :=
⟨ assume x y pos_y,
  let ⟨n, hr⟩ := archimedean.arch (x:ℝ) (pos_y : (0 : ℝ) < y) in
  ⟨n, show (x:ℝ) ≤ (n • y : ℝ≥0), by simp [*, -nsmul_eq_mul, nsmul_coe]⟩ ⟩

lemma le_of_forall_pos_le_add {a b : ℝ≥0} (h : ∀ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
le_of_forall_le_of_dense $ assume x hxb,
begin
  rcases le_iff_exists_add.1 (le_of_lt hxb) with ⟨ε, rfl⟩,
  exact h _ ((lt_add_iff_pos_right b).1 hxb)
end

-- TODO: generalize to some ordered add_monoids, based on #6145
lemma le_of_add_le_left {a b c : ℝ≥0} (h : a + b ≤ c) : a ≤ c :=
by { refine le_trans _ h, simp }

lemma le_of_add_le_right {a b c : ℝ≥0} (h : a + b ≤ c) : b ≤ c :=
by { refine le_trans _ h, simp }

lemma lt_iff_exists_rat_btwn (a b : ℝ≥0) :
  a < b ↔ (∃q:ℚ, 0 ≤ q ∧ a < real.to_nnreal q ∧ real.to_nnreal q < b) :=
iff.intro
  (assume (h : (↑a:ℝ) < (↑b:ℝ)),
    let ⟨q, haq, hqb⟩ := exists_rat_btwn h in
    have 0 ≤ (q : ℝ), from le_trans a.2 $ le_of_lt haq,
    ⟨q, rat.cast_nonneg.1 this,
      by simp [real.coe_to_nnreal _ this, nnreal.coe_lt_coe.symm, haq, hqb]⟩)
  (assume ⟨q, _, haq, hqb⟩, lt_trans haq hqb)

lemma bot_eq_zero : (⊥ : ℝ≥0) = 0 := rfl

lemma mul_sup (a b c : ℝ≥0) : a * (b ⊔ c) = (a * b) ⊔ (a * c) :=
begin
  cases le_total b c with h h,
  { simp [sup_eq_max, max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h (zero_le a))] },
  { simp [sup_eq_max, max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h (zero_le a))] },
end

lemma mul_finset_sup {α} {f : α → ℝ≥0} {s : finset α} (r : ℝ≥0) :
  r * s.sup f = s.sup (λa, r * f a) :=
begin
  refine s.induction_on _ _,
  { simp [bot_eq_zero] },
  { assume a s has ih, simp [has, ih, mul_sup], }
end

@[simp, norm_cast] lemma coe_max (x y : ℝ≥0) :
  ((max x y : ℝ≥0) : ℝ) = max (x : ℝ) (y : ℝ) :=
by { delta max, split_ifs; refl }

@[simp, norm_cast] lemma coe_min (x y : ℝ≥0) :
  ((min x y : ℝ≥0) : ℝ) = min (x : ℝ) (y : ℝ) :=
by { delta min, split_ifs; refl }

@[simp] lemma zero_le_coe {q : ℝ≥0} : 0 ≤ (q : ℝ) := q.2

end nnreal

namespace real

section to_nnreal

@[simp] lemma to_nnreal_zero : real.to_nnreal 0 = 0 :=
by simp [real.to_nnreal]; refl

@[simp] lemma to_nnreal_one : real.to_nnreal 1 = 1 :=
by simp [real.to_nnreal, max_eq_left (zero_le_one : (0 :ℝ) ≤ 1)]; refl

@[simp] lemma to_nnreal_pos {r : ℝ} : 0 < real.to_nnreal r ↔ 0 < r :=
by simp [real.to_nnreal, nnreal.coe_lt_coe.symm, lt_irrefl]

@[simp] lemma to_nnreal_eq_zero {r : ℝ} : real.to_nnreal r = 0 ↔ r ≤ 0 :=
by simpa [-to_nnreal_pos] using (not_iff_not.2 (@to_nnreal_pos r))

lemma to_nnreal_of_nonpos {r : ℝ} : r ≤ 0 → real.to_nnreal r = 0 :=
to_nnreal_eq_zero.2

@[simp] lemma coe_to_nnreal' (r : ℝ) : (real.to_nnreal r : ℝ) = max r 0 := rfl

@[simp] lemma to_nnreal_le_to_nnreal_iff {r p : ℝ} (hp : 0 ≤ p) :
  real.to_nnreal r ≤ real.to_nnreal p ↔ r ≤ p :=
by simp [nnreal.coe_le_coe.symm, real.to_nnreal, hp]

@[simp] lemma to_nnreal_lt_to_nnreal_iff' {r p : ℝ} :
  real.to_nnreal r < real.to_nnreal p ↔ r < p ∧ 0 < p :=
by simp [nnreal.coe_lt_coe.symm, real.to_nnreal, lt_irrefl]

lemma to_nnreal_lt_to_nnreal_iff {r p : ℝ} (h : 0 < p) :
  real.to_nnreal r < real.to_nnreal p ↔ r < p :=
to_nnreal_lt_to_nnreal_iff'.trans (and_iff_left h)

lemma to_nnreal_lt_to_nnreal_iff_of_nonneg {r p : ℝ} (hr : 0 ≤ r) :
  real.to_nnreal r < real.to_nnreal p ↔ r < p :=
to_nnreal_lt_to_nnreal_iff'.trans ⟨and.left, λ h, ⟨h, lt_of_le_of_lt hr h⟩⟩

@[simp] lemma to_nnreal_add {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
  real.to_nnreal (r + p) = real.to_nnreal r + real.to_nnreal p :=
nnreal.eq $ by simp [real.to_nnreal, hr, hp, add_nonneg]

lemma to_nnreal_add_to_nnreal {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
  real.to_nnreal r + real.to_nnreal p = real.to_nnreal (r + p) :=
(real.to_nnreal_add hr hp).symm

lemma to_nnreal_le_to_nnreal {r p : ℝ} (h : r ≤ p) :
  real.to_nnreal r ≤ real.to_nnreal p :=
real.to_nnreal_mono h

lemma to_nnreal_add_le {r p : ℝ} :
  real.to_nnreal (r + p) ≤ real.to_nnreal r + real.to_nnreal p :=
nnreal.coe_le_coe.1 $ max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) nnreal.zero_le_coe

lemma to_nnreal_le_iff_le_coe {r : ℝ} {p : ℝ≥0} : real.to_nnreal r ≤ p ↔ r ≤ ↑p :=
nnreal.gi.gc r p

lemma le_to_nnreal_iff_coe_le {r : ℝ≥0} {p : ℝ} (hp : 0 ≤ p) : r ≤ real.to_nnreal p ↔ ↑r ≤ p :=
by rw [← nnreal.coe_le_coe, real.coe_to_nnreal p hp]

lemma le_to_nnreal_iff_coe_le' {r : ℝ≥0} {p : ℝ} (hr : 0 < r) : r ≤ real.to_nnreal p ↔ ↑r ≤ p :=
(le_or_lt 0 p).elim le_to_nnreal_iff_coe_le $ λ hp,
  by simp only [(hp.trans_le r.coe_nonneg).not_le, to_nnreal_eq_zero.2 hp.le, hr.not_le]

lemma to_nnreal_lt_iff_lt_coe {r : ℝ} {p : ℝ≥0} (ha : 0 ≤ r) : real.to_nnreal r < p ↔ r < ↑p :=
by rw [← nnreal.coe_lt_coe, real.coe_to_nnreal r ha]

lemma lt_to_nnreal_iff_coe_lt {r : ℝ≥0} {p : ℝ} : r < real.to_nnreal p ↔ ↑r < p :=
begin
  cases le_total 0 p,
  { rw [← nnreal.coe_lt_coe, real.coe_to_nnreal p h] },
  { rw [to_nnreal_eq_zero.2 h], split,
    { intro, have := not_lt_of_le (zero_le r), contradiction },
    { intro rp, have : ¬(p ≤ 0) := not_le_of_lt (lt_of_le_of_lt (nnreal.coe_nonneg _) rp),
      contradiction } }
end

@[simp] lemma to_nnreal_bit0 {r : ℝ} (hr : 0 ≤ r) :
  real.to_nnreal (bit0 r) = bit0 (real.to_nnreal r) :=
real.to_nnreal_add hr hr

@[simp] lemma to_nnreal_bit1 {r : ℝ} (hr : 0 ≤ r) :
  real.to_nnreal (bit1 r) = bit1 (real.to_nnreal r) :=
(real.to_nnreal_add (by simp [hr]) zero_le_one).trans (by simp [to_nnreal_one, bit1, hr])

end to_nnreal

end real

open real

namespace nnreal

section mul

lemma mul_eq_mul_left {a b c : ℝ≥0} (h : a ≠ 0) : (a * b = a * c ↔ b = c) :=
begin
  rw [← nnreal.eq_iff, ← nnreal.eq_iff, nnreal.coe_mul, nnreal.coe_mul], split,
  { exact mul_left_cancel' (mt (@nnreal.eq_iff a 0).1 h) },
  { assume h, rw [h] }
end

lemma _root_.real.to_nnreal_mul {p q : ℝ} (hp : 0 ≤ p) :
  real.to_nnreal (p * q) = real.to_nnreal p * real.to_nnreal q :=
begin
  cases le_total 0 q with hq hq,
  { apply nnreal.eq,
    simp [real.to_nnreal, hp, hq, max_eq_left, mul_nonneg] },
  { have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq,
    rw [to_nnreal_eq_zero.2 hq, to_nnreal_eq_zero.2 hpq, mul_zero] }
end

end mul

section pow

lemma pow_mono_decr_exp {a : ℝ≥0} (m n : ℕ) (mn : m ≤ n) (a1 : a ≤ 1) :
  a ^ n ≤ a ^ m :=
begin
  rcases le_iff_exists_add.mp mn with ⟨k, rfl⟩,
  rw [← mul_one (a ^ m), pow_add],
  refine mul_le_mul rfl.le (pow_le_one _ (zero_le a) a1) _ _;
  exact pow_nonneg (zero_le _) _,
end

end pow

section sub

lemma sub_def {r p : ℝ≥0} : r - p = real.to_nnreal (r - p) := rfl

lemma sub_eq_zero {r p : ℝ≥0} (h : r ≤ p) : r - p = 0 :=
nnreal.eq $ max_eq_right $ sub_le_iff_le_add.2 $ by simpa [nnreal.coe_le_coe] using h

@[simp] lemma sub_self {r : ℝ≥0} : r - r = 0 := sub_eq_zero $ le_refl r

@[simp] lemma sub_zero {r : ℝ≥0} : r - 0 = r :=
by rw [sub_def, nnreal.coe_zero, sub_zero, real.to_nnreal_coe]

lemma sub_pos {r p : ℝ≥0} : 0 < r - p ↔ p < r :=
to_nnreal_pos.trans $ sub_pos.trans $ nnreal.coe_lt_coe

protected lemma sub_lt_self {r p : ℝ≥0} : 0 < r → 0 < p → r - p < r :=
assume hr hp,
begin
  cases le_total r p,
  { rwa [sub_eq_zero h] },
  { rw [← nnreal.coe_lt_coe, nnreal.coe_sub h], exact sub_lt_self _ hp }
end

@[simp] lemma sub_le_iff_le_add {r p q : ℝ≥0} : r - p ≤ q ↔ r ≤ q + p :=
match le_total p r with
| or.inl h := by rw [← nnreal.coe_le_coe, ← nnreal.coe_le_coe, nnreal.coe_sub h, nnreal.coe_add,
    sub_le_iff_le_add]
| or.inr h :=
  have r ≤ p + q, from le_add_right h,
  by simpa [nnreal.coe_le_coe, nnreal.coe_le_coe, sub_eq_zero h, add_comm]
end

@[simp] lemma sub_le_self {r p : ℝ≥0} : r - p ≤ r :=
sub_le_iff_le_add.2 $ le_add_right $ le_refl r

lemma add_sub_cancel {r p : ℝ≥0} : (p + r) - r = p :=
nnreal.eq $ by rw [nnreal.coe_sub, nnreal.coe_add, add_sub_cancel]; exact le_add_self

lemma add_sub_cancel' {r p : ℝ≥0} : (r + p) - r = p :=
by rw [add_comm, add_sub_cancel]

lemma sub_add_eq_max {r p : ℝ≥0} : (r - p) + p = max r p :=
nnreal.eq $ by rw [sub_def, nnreal.coe_add, coe_max, real.to_nnreal, coe_mk,
  ← max_add_add_right, zero_add, sub_add_cancel]

lemma add_sub_eq_max {r p : ℝ≥0} : p + (r - p) = max p r :=
by rw [add_comm, sub_add_eq_max, max_comm]

@[simp] lemma sub_add_cancel_of_le {a b : ℝ≥0} (h : b ≤ a) : (a - b) + b = a :=
by rw [sub_add_eq_max, max_eq_left h]

lemma sub_sub_cancel_of_le {r p : ℝ≥0} (h : r ≤ p) : p - (p - r) = r :=
by rw [nnreal.sub_def, nnreal.sub_def, real.coe_to_nnreal _ $ sub_nonneg.2 h,
  sub_sub_cancel, real.to_nnreal_coe]

lemma lt_sub_iff_add_lt {p q r : ℝ≥0} : p < q - r ↔ p + r < q :=
begin
  split,
  { assume H,
    have : (((q - r) : ℝ≥0) : ℝ) = (q : ℝ) - (r : ℝ) :=
      nnreal.coe_sub (le_of_lt (sub_pos.1 (lt_of_le_of_lt (zero_le _) H))),
    rwa [← nnreal.coe_lt_coe, this, lt_sub_iff_add_lt, ← nnreal.coe_add] at H },
  { assume H,
    have : r ≤ q := le_trans (le_add_self) (le_of_lt H),
    rwa [← nnreal.coe_lt_coe, nnreal.coe_sub this, lt_sub_iff_add_lt, ← nnreal.coe_add] }
end

lemma sub_lt_iff_lt_add {a b c : ℝ≥0} (h : b ≤ a) : a - b < c ↔ a < b + c :=
by simp only [←nnreal.coe_lt_coe, nnreal.coe_sub h, nnreal.coe_add, sub_lt_iff_lt_add']

lemma sub_eq_iff_eq_add {a b c : ℝ≥0} (h : b ≤ a) : a - b = c ↔ a = c + b :=
by rw [←nnreal.eq_iff, nnreal.coe_sub h, ←nnreal.eq_iff, nnreal.coe_add, sub_eq_iff_eq_add]

end sub

section inv

lemma sum_div {ι} (s : finset ι) (f : ι → ℝ≥0) (b : ℝ≥0) :
  (∑ i in s, f i) / b = ∑ i in s, (f i / b) :=
by simp only [div_eq_mul_inv, finset.sum_mul]

@[simp] lemma inv_pos {r : ℝ≥0} : 0 < r⁻¹ ↔ 0 < r :=
by simp [pos_iff_ne_zero]

lemma div_pos {r p : ℝ≥0} (hr : 0 < r) (hp : 0 < p) : 0 < r / p :=
by simpa only [div_eq_mul_inv] using mul_pos hr (inv_pos.2 hp)

protected lemma mul_inv {r p : ℝ≥0} : (r * p)⁻¹ = p⁻¹ * r⁻¹ := nnreal.eq $ mul_inv_rev' _ _

lemma div_self_le (r : ℝ≥0) : r / r ≤ 1 :=
if h : r = 0 then by simp [h] else by rw [div_self h]

@[simp] lemma inv_le {r p : ℝ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p :=
by rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]

lemma inv_le_of_le_mul {r p : ℝ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p :=
by by_cases r = 0; simp [*, inv_le]

@[simp] lemma le_inv_iff_mul_le {r p : ℝ≥0} (h : p ≠ 0) : (r ≤ p⁻¹ ↔ r * p ≤ 1) :=
by rw [← mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

@[simp] lemma lt_inv_iff_mul_lt {r p : ℝ≥0} (h : p ≠ 0) : (r < p⁻¹ ↔ r * p < 1) :=
by rw [← mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

lemma mul_le_iff_le_inv {a b r : ℝ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
have 0 < r, from lt_of_le_of_ne (zero_le r) hr.symm,
by rw [← @mul_le_mul_left _ _ a _ r this, ← mul_assoc, mul_inv_cancel hr, one_mul]

lemma le_div_iff_mul_le {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
by rw [div_eq_inv_mul, ← mul_le_iff_le_inv hr, mul_comm]

lemma div_le_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r :=
@div_le_iff ℝ _ a r b $ pos_iff_ne_zero.2 hr

lemma div_le_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ r * b :=
@div_le_iff' ℝ _ a r b $ pos_iff_ne_zero.2 hr

lemma le_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
@le_div_iff ℝ _ a b r $ pos_iff_ne_zero.2 hr

lemma le_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ r * a ≤ b :=
@le_div_iff' ℝ _ a b r $ pos_iff_ne_zero.2 hr

lemma div_lt_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < b * r :=
lt_iff_lt_of_le_iff_le (le_div_iff hr)

lemma div_lt_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a / r < b ↔ a < r * b :=
lt_iff_lt_of_le_iff_le (le_div_iff' hr)

lemma lt_div_iff {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
lt_iff_lt_of_le_iff_le (div_le_iff hr)

lemma lt_div_iff' {a b r : ℝ≥0} (hr : r ≠ 0) : a < b / r ↔ r * a < b :=
lt_iff_lt_of_le_iff_le (div_le_iff' hr)

lemma mul_lt_of_lt_div {a b r : ℝ≥0} (h : a < b / r) : a * r < b :=
begin
  refine (lt_div_iff $ λ hr, false.elim _).1 h,
  subst r,
  simpa using h
end

lemma div_le_div_left_of_le {a b c : ℝ≥0} (b0 : 0 < b) (c0 : 0 < c) (cb : c ≤ b) :
  a / b ≤ a / c :=
begin
  by_cases a0 : a = 0,
  { rw [a0, zero_div, zero_div] },
  { cases a with a ha,
    replace a0 : 0 < a := lt_of_le_of_ne ha (ne_of_lt (zero_lt_iff.mpr a0)),
    exact (div_le_div_left a0 b0 c0).mpr cb }
end

lemma div_le_div_left {a b c : ℝ≥0} (a0 : 0 < a) (b0 : 0 < b) (c0 : 0 < c) :
  a / b ≤ a / c ↔ c ≤ b :=
by rw [nnreal.div_le_iff b0.ne.symm, div_mul_eq_mul_div, nnreal.le_div_iff_mul_le c0.ne.symm,
  mul_le_mul_left a0]

lemma le_of_forall_lt_one_mul_le {x y : ℝ≥0} (h : ∀a<1, a * x ≤ y) : x ≤ y :=
le_of_forall_ge_of_dense $ assume a ha,
  have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha),
  have hx' : x⁻¹ ≠ 0, by rwa [(≠), inv_eq_zero],
  have a * x⁻¹ < 1, by rwa [← lt_inv_iff_mul_lt hx', inv_inv'],
  have (a * x⁻¹) * x ≤ y, from h _ this,
  by rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this

lemma div_add_div_same (a b c : ℝ≥0) : a / c + b / c = (a + b) / c :=
eq.symm $ right_distrib a b (c⁻¹)

lemma half_pos {a : ℝ≥0} (h : 0 < a) : 0 < a / 2 := div_pos h zero_lt_two

lemma add_halves (a : ℝ≥0) : a / 2 + a / 2 = a := nnreal.eq (add_halves a)

lemma half_lt_self {a : ℝ≥0} (h : a ≠ 0) : a / 2 < a :=
by rw [← nnreal.coe_lt_coe, nnreal.coe_div]; exact
half_lt_self (bot_lt_iff_ne_bot.2 h)

lemma two_inv_lt_one : (2⁻¹:ℝ≥0) < 1 :=
by simpa using half_lt_self zero_ne_one.symm

lemma div_lt_one_of_lt {a b : ℝ≥0} (h : a < b) : a / b < 1 :=
begin
  rwa [div_lt_iff, one_mul],
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)
end

@[field_simps] lemma div_add_div (a : ℝ≥0) {b : ℝ≥0} (c : ℝ≥0) {d : ℝ≥0}
  (hb : b ≠ 0) (hd : d ≠ 0) : a / b + c / d = (a * d + b * c) / (b * d) :=
begin
  rw ← nnreal.eq_iff,
  simp only [nnreal.coe_add, nnreal.coe_div, nnreal.coe_mul],
  exact div_add_div _ _ (coe_ne_zero.2 hb) (coe_ne_zero.2 hd)
end

@[field_simps] lemma add_div' (a b c : ℝ≥0) (hc : c ≠ 0) :
  b + a / c = (b * c + a) / c :=
by simpa using div_add_div b a one_ne_zero hc

@[field_simps] lemma div_add' (a b c : ℝ≥0) (hc : c ≠ 0) :
  a / c + b = (a + b * c) / c :=
by rwa [add_comm, add_div', add_comm]

lemma _root_.real.to_nnreal_inv {x : ℝ} :
  real.to_nnreal x⁻¹ = (real.to_nnreal x)⁻¹ :=
begin
  by_cases hx : 0 ≤ x,
  { nth_rewrite 0 ← real.coe_to_nnreal x hx,
    rw [←nnreal.coe_inv, real.to_nnreal_coe], },
  { have hx' := le_of_not_ge hx,
    rw [to_nnreal_eq_zero.mpr hx', inv_zero, to_nnreal_eq_zero.mpr (inv_nonpos.mpr hx')], },
end

lemma _root_.real.to_nnreal_div {x y : ℝ} (hx : 0 ≤ x) :
  real.to_nnreal (x / y) = real.to_nnreal x / real.to_nnreal y :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ← real.to_nnreal_inv, ← real.to_nnreal_mul hx]

lemma _root_.real.to_nnreal_div' {x y : ℝ} (hy : 0 ≤ y) :
  real.to_nnreal (x / y) = real.to_nnreal x / real.to_nnreal y :=
by rw [div_eq_inv_mul, div_eq_inv_mul, real.to_nnreal_mul (inv_nonneg.2 hy), real.to_nnreal_inv]

end inv

@[simp] lemma abs_eq (x : ℝ≥0) : abs (x : ℝ) = x :=
abs_of_nonneg x.property

end nnreal

/-- The absolute value on `ℝ` as a map to `ℝ≥0`. -/
@[pp_nodot] def real.nnabs (x : ℝ) : ℝ≥0 := ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp] lemma nnreal.coe_nnabs (x : ℝ) : (real.nnabs x : ℝ) = abs x :=
by simp [real.nnabs]

@[simp]
lemma real.nnabs_of_nonneg {x : ℝ} (h : 0 ≤ x) : real.nnabs x = real.to_nnreal x :=
by { ext, simp [real.coe_to_nnreal x h, abs_of_nonneg h] }

lemma real.coe_to_nnreal_le (x : ℝ) : (real.to_nnreal x : ℝ) ≤ abs x :=
begin
  by_cases h : 0 ≤ x,
  { simp [h, real.coe_to_nnreal x h, le_abs_self] },
  { simp [real.to_nnreal, h, le_abs_self, abs_nonneg] }
end

lemma cast_nat_abs_eq_nnabs_cast (n : ℤ) :
  (n.nat_abs : ℝ≥0) = real.nnabs n :=
by { ext, rw [nnreal.coe_nat_cast, int.cast_nat_abs, nnreal.coe_nnabs] }
