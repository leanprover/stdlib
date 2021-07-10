/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.well_founded_set
import algebra.big_operators.finprod
import ring_theory.valuation.basic
import algebra.module.pi
import ring_theory.power_series.basic

/-!
# Hahn Series

## Main Definitions
  * If `Γ` is ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
  * If `R` is a (commutative) additive monoid or group, then so is `hahn_series Γ R`.
  * If `R` is a (comm_)(semi)ring, then so is `hahn_series Γ R`.
  * `hahn_series.add_val Γ R` defines an `add_valuation` on `hahn_series Γ R` when `Γ` is linearly
    ordered.
  * A `hahn_series.summable_family` is a family of Hahn series such that the union of their supports
  is well-founded and only finitely many are nonzero at any given coefficient. They have a formal
  sum, `hahn_series.summable_family.hsum`, which can be bundled as a `linear_map` as
  `hahn_series.summable_family.lsum`. Note that this is different from `summable` in the valuation
  topology, because there are topologically summable families that do not satisfy the axioms of
  `hahn_series.summable_family`, and formally summable families whose sums do not converge
  topologically.

## TODO
  * Given `[linear_ordered_add_comm_group Γ]` and `[field R]`, define `field (hahn_series Γ R)`.
  * Build an API for the variable `X`
  * Define Laurent series

-/

open finset
open_locale big_operators classical
noncomputable theory

/-- If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure hahn_series (Γ : Type*) (R : Type*) [partial_order Γ] [has_zero R] :=
(coeff : Γ → R)
(is_pwo_support' : (function.support coeff).is_pwo)

variables {Γ : Type*} {R : Type*}

namespace hahn_series

section zero
variables [partial_order Γ] [has_zero R]

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
def support (x : hahn_series Γ R) : set Γ := function.support x.coeff

@[simp]
lemma is_pwo_support (x : hahn_series Γ R) : x.support.is_pwo := x.is_pwo_support'

@[simp]
lemma is_wf_support (x : hahn_series Γ R) : x.support.is_wf := x.is_pwo_support.is_wf

@[simp]
lemma mem_support (x : hahn_series Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 := iff.refl _

instance : has_zero (hahn_series Γ R) :=
⟨{ coeff := 0,
   is_pwo_support' := by simp }⟩

instance : inhabited (hahn_series Γ R) := ⟨0⟩

instance [subsingleton R] : subsingleton (hahn_series Γ R) :=
⟨λ a b, a.ext b (subsingleton.elim _ _)⟩

@[simp]
lemma zero_coeff {a : Γ} : (0 : hahn_series Γ R).coeff a = 0 := rfl

lemma ne_zero_of_coeff_ne_zero {x : hahn_series Γ R} {g : Γ} (h : x.coeff g ≠ 0) :
  x ≠ 0 :=
mt (λ x0, (x0.symm ▸ zero_coeff : x.coeff g = 0)) h

@[simp]
lemma support_zero : support (0 : hahn_series Γ R) = ∅ := function.support_zero

@[simp]
lemma support_nonempty_iff {x : hahn_series Γ R} :
  x.support.nonempty ↔ x ≠ 0 :=
begin
  split,
  { rintro ⟨a, ha⟩ rfl,
    apply ha zero_coeff },
  { contrapose!,
    rw set.not_nonempty_iff_eq_empty,
    intro h,
    ext a,
    have ha := set.not_mem_empty a,
    rw [← h, mem_support, not_not] at ha,
    rw [ha, zero_coeff] }
end

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : zero_hom R (hahn_series Γ R) :=
{ to_fun := λ r, { coeff := pi.single a r,
    is_pwo_support' := (set.is_pwo_singleton a).mono pi.support_single_subset },
  map_zero' := ext _ _ (pi.single_zero _) }

variables {a b : Γ} {r : R}

@[simp]
theorem single_coeff_same (a : Γ) (r : R) : (single a r).coeff a = r := pi.single_eq_same a r

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 := pi.single_eq_of_ne h r

theorem single_coeff : (single a r).coeff b = if (b = a) then r else 0 :=
by { split_ifs with h; simp [h] }

@[simp]
lemma support_single_of_ne (h : r ≠ 0) : support (single a r) = {a} :=
pi.support_single_of_ne h

lemma support_single_subset : support (single a r) ⊆ {a} :=
pi.support_single_subset

lemma eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
support_single_subset h

@[simp]
lemma single_eq_zero : (single a (0 : R)) = 0 := (single a).map_zero

lemma single_injective (a : Γ) : function.injective (single a : R → hahn_series Γ R) :=
λ r s rs, by rw [← single_coeff_same a r, ← single_coeff_same a s, rs]

lemma single_ne_zero (h : r ≠ 0) : single a r ≠ 0 :=
λ con, h (single_injective a (con.trans single_eq_zero.symm))

instance [nonempty Γ] [nontrivial R] : nontrivial (hahn_series Γ R) :=
⟨begin
  obtain ⟨r, s, rs⟩ := exists_pair_ne R,
  inhabit Γ,
  refine ⟨single (arbitrary Γ) r, single (arbitrary Γ) s, λ con, rs _⟩,
  rw [← single_coeff_same (arbitrary Γ) r, con, single_coeff_same],
end⟩

section order
variable [has_zero Γ]

/-- The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a
  nonzero coefficient, the order of 0 is 0. -/
def order (x : hahn_series Γ R) : Γ :=
if h : x = 0 then 0 else x.is_wf_support.min (support_nonempty_iff.2 h)

@[simp]
lemma order_zero : order (0 : hahn_series Γ R) = 0 := dif_pos rfl

lemma order_of_ne {x : hahn_series Γ R} (hx : x ≠ 0) :
  order x = x.is_wf_support.min (support_nonempty_iff.2 hx) := dif_neg hx

lemma coeff_order_ne_zero {x : hahn_series Γ R} (hx : x ≠ 0) :
  x.coeff x.order ≠ 0 :=
begin
  rw order_of_ne hx,
  exact x.is_wf_support.min_mem (support_nonempty_iff.2 hx)
end

lemma order_le_of_coeff_ne_zero {Γ} [linear_ordered_cancel_add_comm_monoid Γ]
  {x : hahn_series Γ R} {g : Γ} (h : x.coeff g ≠ 0) :
  x.order ≤ g :=
le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
  (set.is_wf.min_le _ _ ((mem_support _ _).2 h))

@[simp]
lemma order_single (h : r ≠ 0) : (single a r).order = a :=
(order_of_ne (single_ne_zero h)).trans (support_single_subset ((single a r).is_wf_support.min_mem
    (support_nonempty_iff.2 (single_ne_zero h))))

end order

section domain
variables {Γ' : Type*} [partial_order Γ']

/-- Extends the domain of a `hahn_series` by an `order_embedding`. -/
def emb_domain (f : Γ ↪o Γ') : hahn_series Γ R → hahn_series Γ' R :=
λ x, { coeff := λ (b : Γ'),
  if h : b ∈ f '' x.support then x.coeff (classical.some h) else 0,
  is_pwo_support' := (x.is_pwo_support.image_of_monotone f.monotone).mono (λ b hb, begin
    contrapose! hb,
    rw [function.mem_support, dif_neg hb, not_not],
  end) }

@[simp]
lemma emb_domain_coeff {f : Γ ↪o Γ'} {x : hahn_series Γ R} {a : Γ} :
  (emb_domain f x).coeff (f a) = x.coeff a :=
begin
  rw emb_domain,
  dsimp only,
  by_cases ha : a ∈ x.support,
  { rw dif_pos (set.mem_image_of_mem f ha),
    exact congr rfl (f.injective (classical.some_spec (set.mem_image_of_mem f ha)).2) },
  { rw [dif_neg, not_not.1 (λ c, ha ((mem_support _ _).2 c))],
    contrapose! ha,
    obtain ⟨b, hb1, hb2⟩ := (set.mem_image _ _ _).1 ha,
    rwa f.injective hb2 at hb1 }
end

@[simp]
lemma emb_domain_mk_coeff {f : Γ → Γ'}
  (hfi : function.injective f) (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g')
  {x : hahn_series Γ R} {a : Γ} :
  (emb_domain ⟨⟨f, hfi⟩, hf⟩ x).coeff (f a) = x.coeff a :=
emb_domain_coeff

lemma emb_domain_notin_image_support {f : Γ ↪o Γ'} {x : hahn_series Γ R} {b : Γ'}
  (hb : b ∉ f '' x.support) : (emb_domain f x).coeff b = 0 :=
dif_neg hb

lemma support_emb_domain_subset {f : Γ ↪o Γ'} {x : hahn_series Γ R} :
  support (emb_domain f x) ⊆ f '' x.support :=
begin
  intros g hg,
  contrapose! hg,
  rw [mem_support, emb_domain_notin_image_support hg, not_not],
end

lemma emb_domain_notin_range {f : Γ ↪o Γ'} {x : hahn_series Γ R} {b : Γ'}
  (hb : b ∉ set.range f) : (emb_domain f x).coeff b = 0 :=
emb_domain_notin_image_support (λ con, hb (set.image_subset_range _ _ con))

@[simp]
lemma emb_domain_zero {f : Γ ↪o Γ'} : emb_domain f (0 : hahn_series Γ R) = 0 :=
by { ext, simp [emb_domain_notin_image_support] }

@[simp]
lemma emb_domain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
  emb_domain f (single g r) = single (f g) r :=
begin
  ext g',
  by_cases h : g' = f g,
  { simp [h] },
  rw [emb_domain_notin_image_support, single_coeff_of_ne h],
  by_cases hr : r = 0,
  { simp [hr] },
  rwa [support_single_of_ne hr, set.image_singleton, set.mem_singleton_iff],
end

lemma emb_domain_injective {f : Γ ↪o Γ'} :
  function.injective (emb_domain f : hahn_series Γ R → hahn_series Γ' R) :=
λ x y xy, begin
  ext g,
  rw [ext_iff, function.funext_iff] at xy,
  have xyg := xy (f g),
  rwa [emb_domain_coeff, emb_domain_coeff] at xyg,
end

end domain

end zero

section addition

variable [partial_order Γ]

section add_monoid
variable [add_monoid R]

instance : has_add (hahn_series Γ R) :=
{ add := λ x y, { coeff := x.coeff + y.coeff,
                  is_pwo_support' := (x.is_pwo_support.union y.is_pwo_support).mono
                    (function.support_add _ _) } }

instance : add_monoid (hahn_series Γ R) :=
{ zero := 0,
  add := (+),
  add_assoc := λ x y z, by { ext, apply add_assoc },
  zero_add := λ x, by { ext, apply zero_add },
  add_zero := λ x, by { ext, apply add_zero } }

@[simp]
lemma add_coeff' {x y : hahn_series Γ R} :
  (x + y).coeff = x.coeff + y.coeff := rfl

lemma add_coeff {x y : hahn_series Γ R} {a : Γ} :
  (x + y).coeff a = x.coeff a + y.coeff a := rfl

lemma support_add_subset {x y : hahn_series Γ R} :
  support (x + y) ⊆ support x ∪ support y :=
λ a ha, begin
  rw [mem_support, add_coeff] at ha,
  rw [set.mem_union, mem_support, mem_support],
  contrapose! ha,
  rw [ha.1, ha.2, add_zero],
end

lemma min_order_le_order_add {Γ} [linear_ordered_cancel_add_comm_monoid Γ] {x y : hahn_series Γ R}
  (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
  min x.order y.order ≤ (x + y).order :=
begin
  rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy],
  refine le_trans _ (set.is_wf.min_le_min_of_subset support_add_subset),
  { exact x.is_wf_support.union y.is_wf_support },
  { exact set.nonempty.mono (set.subset_union_left _ _) (support_nonempty_iff.2 hx) },
  rw set.is_wf.min_union,
end

/-- `single` as an additive monoid/group homomorphism -/
@[simps] def single.add_monoid_hom (a : Γ) : R →+ (hahn_series Γ R) :=
{ map_add' := λ x y, by { ext b, by_cases h : b = a; simp [h] },
  ..single a }

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps] def coeff.add_monoid_hom (g : Γ) : (hahn_series Γ R) →+ R :=
{ to_fun := λ f, f.coeff g,
  map_zero' := zero_coeff,
  map_add' := λ x y, add_coeff }

section domain
variables {Γ' : Type*} [partial_order Γ']

lemma emb_domain_add (f : Γ ↪o Γ') (x y : hahn_series Γ R) :
  emb_domain f (x + y) = emb_domain f x + emb_domain f y :=
begin
  ext g,
  by_cases hg : g ∈ set.range f,
  { obtain ⟨a, rfl⟩ := hg,
    simp },
  { simp [emb_domain_notin_range, hg] }
end

end domain

end add_monoid

instance [add_comm_monoid R] : add_comm_monoid (hahn_series Γ R) :=
{ add_comm := λ x y, by { ext, apply add_comm }
  .. hahn_series.add_monoid }

section add_group
variable [add_group R]

instance : add_group (hahn_series Γ R) :=
{ neg := λ x, { coeff := λ a, - x.coeff a,
                is_pwo_support' := by { rw function.support_neg,
                  exact x.is_pwo_support }, },
  add_left_neg := λ x, by { ext, apply add_left_neg },
  .. hahn_series.add_monoid }

@[simp]
lemma neg_coeff' {x : hahn_series Γ R} : (- x).coeff = - x.coeff := rfl

lemma neg_coeff {x : hahn_series Γ R} {a : Γ} : (- x).coeff a = - x.coeff a := rfl

@[simp]
lemma support_neg {x : hahn_series Γ R} : (- x).support = x.support :=
by { ext, simp }

@[simp]
lemma sub_coeff' {x y : hahn_series Γ R} :
  (x - y).coeff = x.coeff - y.coeff := by { ext, simp [sub_eq_add_neg] }

lemma sub_coeff {x y : hahn_series Γ R} {a : Γ} :
  (x - y).coeff a = x.coeff a - y.coeff a := by simp

end add_group

instance [add_comm_group R] : add_comm_group (hahn_series Γ R) :=
{ .. hahn_series.add_comm_monoid,
  .. hahn_series.add_group }

end addition

section distrib_mul_action
variables [partial_order Γ] {V : Type*} [monoid R] [add_monoid V] [distrib_mul_action R V]

instance : has_scalar R (hahn_series Γ V) :=
⟨λ r x, { coeff := r • x.coeff,
          is_pwo_support' := x.is_pwo_support.mono (function.support_smul_subset_right r x.coeff) }⟩

@[simp]
lemma smul_coeff {r : R} {x : hahn_series Γ V} {a : Γ} : (r • x).coeff a = r • (x.coeff a) := rfl

instance : distrib_mul_action R (hahn_series Γ V) :=
{ smul := (•),
  one_smul := λ _, by { ext, simp },
  smul_zero := λ _, by { ext, simp },
  smul_add := λ _ _ _, by { ext, simp [smul_add] },
  mul_smul := λ _ _ _, by { ext, simp [mul_smul] } }

variables {S : Type*} [monoid S] [distrib_mul_action S V]

instance [has_scalar R S] [is_scalar_tower R S V] :
  is_scalar_tower R S (hahn_series Γ V) :=
⟨λ r s a, by { ext, simp }⟩

instance [smul_comm_class R S V] :
  smul_comm_class R S (hahn_series Γ V) :=
⟨λ r s a, by { ext, simp [smul_comm] }⟩

end distrib_mul_action

section module
variables [partial_order Γ] [semiring R] {V : Type*} [add_comm_monoid V] [module R V]

instance : module R (hahn_series Γ V) :=
{ zero_smul := λ _, by { ext, simp },
  add_smul := λ _ _ _, by { ext, simp [add_smul] },
  .. hahn_series.distrib_mul_action }

/-- `single` as a linear map -/
@[simps] def single.linear_map (a : Γ) : R →ₗ[R] (hahn_series Γ R) :=
{ map_smul' := λ r s, by { ext b, by_cases h : b = a; simp [h] },
  ..single.add_monoid_hom a }

/-- `coeff g` as a linear map -/
@[simps] def coeff.linear_map (g : Γ) : (hahn_series Γ R) →ₗ[R] R :=
{ map_smul' := λ r s, rfl,
  ..coeff.add_monoid_hom g }

section domain
variables {Γ' : Type*} [partial_order Γ']

lemma emb_domain_smul (f : Γ ↪o Γ') (r : R) (x : hahn_series Γ R) :
  emb_domain f (r • x) = r • emb_domain f x :=
begin
  ext g,
  by_cases hg : g ∈ set.range f,
  { obtain ⟨a, rfl⟩ := hg,
    simp },
  { simp [emb_domain_notin_range, hg] }
end

/-- Extending the domain of Hahn series is a linear map. -/
@[simps] def emb_domain_linear_map (f : Γ ↪o Γ') : hahn_series Γ R →ₗ[R] hahn_series Γ' R :=
{ to_fun := emb_domain f, map_add' := emb_domain_add f, map_smul' := emb_domain_smul f }

end domain

end module

section multiplication

variable [ordered_cancel_add_comm_monoid Γ]

instance [has_zero R] [has_one R] : has_one (hahn_series Γ R) :=
⟨single 0 1⟩

@[simp]
lemma one_coeff [has_zero R] [has_one R] {a : Γ} :
  (1 : hahn_series Γ R).coeff a = if a = 0 then 1 else 0 := single_coeff

@[simp]
lemma single_zero_one [has_zero R] [has_one R] : (single 0 (1 : R)) = 1 := rfl

@[simp]
lemma support_one [mul_zero_one_class R] [nontrivial R] :
  support (1 : hahn_series Γ R) = {0} :=
support_single_of_ne one_ne_zero

@[simp]
lemma order_one [mul_zero_one_class R] :
  order (1 : hahn_series Γ R) = 0 :=
begin
  cases subsingleton_or_nontrivial R with h h; haveI := h,
  { rw [subsingleton.elim (1 : hahn_series Γ R) 0, order_zero] },
  { exact order_single one_ne_zero }
end

instance [non_unital_non_assoc_semiring R] : has_mul (hahn_series Γ R) :=
{ mul := λ x y, { coeff := λ a,
    ∑ ij in (add_antidiagonal x.is_pwo_support y.is_pwo_support a),
    x.coeff ij.fst * y.coeff ij.snd,
    is_pwo_support' := begin
      have h : {a : Γ | ∑ (ij : Γ × Γ) in add_antidiagonal x.is_pwo_support
        y.is_pwo_support a, x.coeff ij.fst * y.coeff ij.snd ≠ 0} ⊆
        {a : Γ | (add_antidiagonal x.is_pwo_support y.is_pwo_support a).nonempty},
      { intros a ha,
        contrapose! ha,
        simp [not_nonempty_iff_eq_empty.1 ha] },
      exact is_pwo_support_add_antidiagonal.mono h,
    end, }, }

@[simp]
lemma mul_coeff [non_unital_non_assoc_semiring R] {x y : hahn_series Γ R} {a : Γ} :
  (x * y).coeff a = ∑ ij in (add_antidiagonal x.is_pwo_support y.is_pwo_support a),
    x.coeff ij.fst * y.coeff ij.snd := rfl

lemma mul_coeff_right' [non_unital_non_assoc_semiring R] {x y : hahn_series Γ R} {a : Γ} {s : set Γ}
  (hs : s.is_pwo) (hys : y.support ⊆ s) :
  (x * y).coeff a = ∑ ij in (add_antidiagonal x.is_pwo_support hs a),
    x.coeff ij.fst * y.coeff ij.snd :=
begin
  rw mul_coeff,
  apply sum_subset_zero_on_sdiff (add_antidiagonal_mono_right hys) _ (λ _ _, rfl),
  intros b hb,
  simp only [not_and, not_not, mem_sdiff, mem_add_antidiagonal,
      ne.def, set.mem_set_of_eq, mem_support] at hb,
  rw [(hb.2 hb.1.1 hb.1.2.1), mul_zero]
end

lemma mul_coeff_left' [non_unital_non_assoc_semiring R] {x y : hahn_series Γ R} {a : Γ} {s : set Γ}
  (hs : s.is_pwo) (hxs : x.support ⊆ s) :
  (x * y).coeff a = ∑ ij in (add_antidiagonal hs y.is_pwo_support a),
    x.coeff ij.fst * y.coeff ij.snd :=
begin
  rw mul_coeff,
  apply sum_subset_zero_on_sdiff (add_antidiagonal_mono_left hxs) _ (λ _ _, rfl),
  intros b hb,
  simp only [not_and, not_not, mem_sdiff, mem_add_antidiagonal,
      ne.def, set.mem_set_of_eq, mem_support] at hb,
  rw [not_not.1 (λ con, hb.1.2.2 (hb.2 hb.1.1 con)), zero_mul],
end

instance [non_unital_non_assoc_semiring R] : distrib (hahn_series Γ R) :=
{ left_distrib := λ x y z, begin
    ext a,
    have hwf := (y.is_pwo_support.union z.is_pwo_support),
    rw [mul_coeff_right' hwf, add_coeff, mul_coeff_right' hwf (set.subset_union_right _ _),
      mul_coeff_right' hwf (set.subset_union_left _ _)],
    { simp only [add_coeff, mul_add, sum_add_distrib] },
    { intro b,
      simp only [add_coeff, ne.def, set.mem_union_eq, set.mem_set_of_eq, mem_support],
      contrapose!,
      intro h,
      rw [h.1, h.2, add_zero], }
  end,
  right_distrib := λ x y z, begin
    ext a,
    have hwf := (x.is_pwo_support.union y.is_pwo_support),
    rw [mul_coeff_left' hwf, add_coeff, mul_coeff_left' hwf (set.subset_union_right _ _),
      mul_coeff_left' hwf (set.subset_union_left _ _)],
    { simp only [add_coeff, add_mul, sum_add_distrib] },
    { intro b,
      simp only [add_coeff, ne.def, set.mem_union_eq, set.mem_set_of_eq, mem_support],
      contrapose!,
      intro h,
      rw [h.1, h.2, add_zero], },
  end,
  .. hahn_series.has_mul,
  .. hahn_series.has_add }

lemma single_mul_coeff_add [non_unital_non_assoc_semiring R] {r : R} {x : hahn_series Γ R} {a : Γ}
  {b : Γ} :
  ((single b r) * x).coeff (a + b) = r * x.coeff a :=
begin
  by_cases hr : r = 0,
  { simp [hr] },
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, ne.def, not_false_iff, smul_eq_mul],
  by_cases hx : x.coeff a = 0,
  { simp only [hx, mul_zero],
    rw [sum_congr _ (λ _ _, rfl), sum_empty],
    ext ⟨a1, a2⟩,
    simp only [not_mem_empty, not_and, set.mem_singleton_iff, not_not,
      mem_add_antidiagonal, set.mem_set_of_eq, iff_false],
    rintro h1 rfl h2,
    rw add_comm at h1,
    rw ← add_right_cancel h1 at hx,
    exact h2 hx, },
  transitivity ∑ (ij : Γ × Γ) in {(b, a)}, (single b r).coeff ij.fst * x.coeff ij.snd,
  { apply sum_congr _ (λ _ _, rfl),
    ext ⟨a1, a2⟩,
    simp only [set.mem_singleton_iff, prod.mk.inj_iff, mem_add_antidiagonal,
      mem_singleton, set.mem_set_of_eq],
    split,
    { rintro ⟨h1, rfl, h2⟩,
      rw add_comm at h1,
      refine ⟨rfl, add_right_cancel h1⟩ },
    { rintro ⟨rfl, rfl⟩,
      refine ⟨add_comm _ _, _⟩,
      simp [hx] } },
  { simp }
end

lemma mul_single_coeff_add [non_unital_non_assoc_semiring R] {r : R} {x : hahn_series Γ R} {a : Γ}
  {b : Γ} :
  (x * (single b r)).coeff (a + b) = x.coeff a * r :=
begin
  by_cases hr : r = 0,
  { simp [hr] },
  simp only [hr, smul_coeff, mul_coeff, support_single_of_ne, ne.def, not_false_iff, smul_eq_mul],
  by_cases hx : x.coeff a = 0,
  { simp only [hx, zero_mul],
    rw [sum_congr _ (λ _ _, rfl), sum_empty],
    ext ⟨a1, a2⟩,
    simp only [not_mem_empty, not_and, set.mem_singleton_iff, not_not,
      mem_add_antidiagonal, set.mem_set_of_eq, iff_false],
    rintro h1 h2 rfl,
    rw ← add_right_cancel h1 at hx,
    exact h2 hx, },
  transitivity ∑ (ij : Γ × Γ) in {(a,b)}, x.coeff ij.fst * (single b r).coeff ij.snd,
  { apply sum_congr _ (λ _ _, rfl),
    ext ⟨a1, a2⟩,
    simp only [set.mem_singleton_iff, prod.mk.inj_iff, mem_add_antidiagonal,
      mem_singleton, set.mem_set_of_eq],
    split,
    { rintro ⟨h1, h2, rfl⟩,
      refine ⟨add_right_cancel h1, rfl⟩ },
    { rintro ⟨rfl, rfl⟩,
      simp [hx] } },
  { simp }
end

@[simp]
lemma mul_single_zero_coeff [non_unital_non_assoc_semiring R] {r : R} {x : hahn_series Γ R}
  {a : Γ} :
  (x * (single 0 r)).coeff a = x.coeff a * r  :=
by rw [← add_zero a, mul_single_coeff_add, add_zero]

lemma single_zero_mul_coeff [non_unital_non_assoc_semiring R] {r : R} {x : hahn_series Γ R}
  {a : Γ} :
  ((single 0 r) * x).coeff a = r * x.coeff a :=
by rw [← add_zero a, single_mul_coeff_add, add_zero]

@[simp]
lemma single_zero_mul_eq_smul [semiring R] {r : R} {x : hahn_series Γ R} :
  (single 0 r) * x = r • x :=
by { ext, exact single_zero_mul_coeff }

theorem support_mul_subset_add_support [non_unital_non_assoc_semiring R] {x y : hahn_series Γ R} :
  support (x * y) ⊆ support x + support y :=
begin
  apply set.subset.trans (λ x hx, _) support_add_antidiagonal_subset_add,
  { exact x.is_pwo_support },
  { exact y.is_pwo_support },
  contrapose! hx,
  simp only [not_nonempty_iff_eq_empty, ne.def, set.mem_set_of_eq] at hx,
  simp [hx],
end

lemma mul_coeff_order_add_order {Γ} [linear_ordered_cancel_add_comm_monoid Γ]
  [non_unital_non_assoc_semiring R]
  {x y : hahn_series Γ R} (hx : x ≠ 0) (hy : y ≠ 0) :
  (x * y).coeff (x.order + y.order) = x.coeff x.order * y.coeff y.order :=
by rw [order_of_ne hx, order_of_ne hy, mul_coeff, finset.add_antidiagonal_min_add_min,
  finset.sum_singleton]

private lemma mul_assoc' [non_unital_semiring R] (x y z : hahn_series Γ R) :
  x * y * z = x * (y * z) :=
begin
  ext b,
  rw [mul_coeff_left' (x.is_pwo_support.add y.is_pwo_support) support_mul_subset_add_support,
      mul_coeff_right' (y.is_pwo_support.add z.is_pwo_support) support_mul_subset_add_support],
  simp only [mul_coeff, add_coeff, sum_mul, mul_sum, sum_sigma'],
  refine sum_bij_ne_zero (λ a has ha0, ⟨⟨a.2.1, a.2.2 + a.1.2⟩, ⟨a.2.2, a.1.2⟩⟩) _ _ _ _,
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H1 H2,
    simp only [true_and, set.image2_add, eq_self_iff_true, mem_add_antidiagonal, ne.def,
      set.image_prod, mem_sigma, set.mem_set_of_eq] at H1 H2 ⊢,
    obtain ⟨⟨rfl, ⟨H3, nz⟩⟩, ⟨rfl, nx, ny⟩⟩ := H1,
    refine ⟨⟨(add_assoc _ _ _).symm, nx, set.add_mem_add ny nz⟩, ny, nz⟩ },
  { rintros ⟨⟨i1,j1⟩, ⟨k1,l1⟩⟩ ⟨⟨i2,j2⟩, ⟨k2,l2⟩⟩ H1 H2 H3 H4 H5,
    simp only [set.image2_add, prod.mk.inj_iff, mem_add_antidiagonal, ne.def,
      set.image_prod, mem_sigma, set.mem_set_of_eq, heq_iff_eq] at H1 H3 H5,
    obtain ⟨⟨rfl, H⟩, rfl, rfl⟩ := H5,
    simp only [and_true, prod.mk.inj_iff, eq_self_iff_true, heq_iff_eq],
    exact add_right_cancel (H1.1.1.trans H3.1.1.symm) },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H1 H2,
    simp only [exists_prop, set.image2_add, prod.mk.inj_iff, mem_add_antidiagonal,
      sigma.exists, ne.def, set.image_prod, mem_sigma, set.mem_set_of_eq, heq_iff_eq,
      prod.exists] at H1 H2 ⊢,
    obtain ⟨⟨rfl, nx, H⟩, rfl, ny, nz⟩ := H1,
    exact ⟨i + k, l, i, k, ⟨⟨add_assoc _ _ _, set.add_mem_add nx ny, nz⟩, rfl, nx, ny⟩,
      λ con, H2 ((mul_assoc _ _ _).symm.trans con), ⟨rfl, rfl⟩, rfl, rfl⟩ },
  { rintros ⟨⟨i,j⟩, ⟨k,l⟩⟩ H1 H2,
    simp [mul_assoc], }
end

instance [non_unital_non_assoc_semiring R] : non_unital_non_assoc_semiring (hahn_series Γ R) :=
{ zero := 0,
  add := (+),
  mul := (*),
  zero_mul := λ _, by { ext, simp },
  mul_zero := λ _, by { ext, simp },
  .. hahn_series.add_comm_monoid,
  .. hahn_series.distrib }

instance [non_unital_semiring R] : non_unital_semiring (hahn_series Γ R) :=
{ zero := 0,
  add := (+),
  mul := (*),
  mul_assoc := mul_assoc',
  .. hahn_series.non_unital_non_assoc_semiring }

instance [non_assoc_semiring R] : non_assoc_semiring (hahn_series Γ R) :=
{ zero := 0,
  one := 1,
  add := (+),
  mul := (*),
  one_mul := λ x, by { ext, exact single_zero_mul_coeff.trans (one_mul _) },
  mul_one := λ x, by { ext, exact mul_single_zero_coeff.trans (mul_one _) },
  .. hahn_series.non_unital_non_assoc_semiring }

instance [semiring R] : semiring (hahn_series Γ R) :=
{ zero := 0,
  one := 1,
  add := (+),
  mul := (*),
  .. hahn_series.non_assoc_semiring,
  .. hahn_series.non_unital_semiring }

instance [comm_semiring R] : comm_semiring (hahn_series Γ R) :=
{ mul_comm := λ x y, begin
    ext,
    simp_rw [mul_coeff, mul_comm],
    refine sum_bij (λ a ha, ⟨a.2, a.1⟩) _ (λ a ha, by simp) _ _,
    { intros a ha,
      simp only [mem_add_antidiagonal, ne.def, set.mem_set_of_eq] at ha ⊢,
      obtain ⟨h1, h2, h3⟩ := ha,
      refine ⟨_, h3, h2⟩,
      rw [add_comm, h1], },
    { rintros ⟨a1, a2⟩ ⟨b1, b2⟩ ha hb hab,
      rw prod.ext_iff at *,
      refine ⟨hab.2, hab.1⟩, },
    { intros a ha,
      refine ⟨a.swap, _, by simp⟩,
      simp only [prod.fst_swap, mem_add_antidiagonal, prod.snd_swap,
        ne.def, set.mem_set_of_eq] at ha ⊢,
      exact ⟨(add_comm _ _).trans ha.1, ha.2.2, ha.2.1⟩ }
  end,
  .. hahn_series.semiring }

instance [ring R] : ring (hahn_series Γ R) :=
{ .. hahn_series.semiring,
  .. hahn_series.add_comm_group }

instance [comm_ring R] : comm_ring (hahn_series Γ R) :=
{ .. hahn_series.comm_semiring,
  .. hahn_series.ring }

instance {Γ} [linear_ordered_cancel_add_comm_monoid Γ] [integral_domain R] :
  integral_domain (hahn_series Γ R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y xy, begin
    by_cases hx : x = 0,
    { left, exact hx },
    right,
    contrapose! xy,
    rw [hahn_series.ext_iff, function.funext_iff, not_forall],
    refine ⟨x.order + y.order, _⟩,
    rw [mul_coeff_order_add_order hx xy, zero_coeff, mul_eq_zero],
    simp [coeff_order_ne_zero, hx, xy],
  end,
  .. hahn_series.nontrivial,
  .. hahn_series.comm_ring }

@[simp]
lemma order_mul {Γ} [linear_ordered_cancel_add_comm_monoid Γ] [integral_domain R]
  {x y : hahn_series Γ R} (hx : x ≠ 0) (hy : y ≠ 0) :
  (x * y).order = x.order + y.order :=
begin
  apply le_antisymm,
  { apply order_le_of_coeff_ne_zero,
    rw [mul_coeff_order_add_order hx hy],
    exact mul_ne_zero (coeff_order_ne_zero hx) (coeff_order_ne_zero hy) },
  { rw [order_of_ne hx, order_of_ne hy, order_of_ne (mul_ne_zero hx hy), ← set.is_wf.min_add],
    exact set.is_wf.min_le_min_of_subset (support_mul_subset_add_support) },
end

section non_unital_non_assoc_semiring
variables [non_unital_non_assoc_semiring R]

@[simp]
lemma single_mul_single {a b : Γ} {r s : R} :
  single a r * single b s = single (a + b) (r * s) :=
begin
  ext x,
  by_cases h : x = a + b,
  { rw [h, mul_single_coeff_add],
    simp },
  { rw [single_coeff_of_ne h, mul_coeff, sum_eq_zero],
    rintros ⟨y1, y2⟩ hy,
    obtain ⟨rfl, hy1, hy2⟩ := mem_add_antidiagonal.1 hy,
    rw [eq_of_mem_support_single hy1, eq_of_mem_support_single hy2] at h,
    exact (h rfl).elim }
end

end non_unital_non_assoc_semiring

section non_assoc_semiring
variables [non_assoc_semiring R]

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps] def C : R →+* (hahn_series Γ R) :=
{ to_fun := single 0,
  map_zero' := single_eq_zero,
  map_one' := rfl,
  map_add' := λ x y, by { ext a, by_cases h : a = 0; simp [h] },
  map_mul' := λ x y, by rw [single_mul_single, zero_add] }

@[simp]
lemma C_zero : C (0 : R) = (0 : hahn_series Γ R) := C.map_zero

@[simp]
lemma C_one : C (1 : R) = (1 : hahn_series Γ R) := C.map_one

lemma C_injective : function.injective (C : R → hahn_series Γ R) :=
begin
  intros r s rs,
  rw [ext_iff, function.funext_iff] at rs,
  have h := rs 0,
  rwa [C_apply, single_coeff_same, C_apply, single_coeff_same] at h,
end

lemma C_ne_zero {r : R} (h : r ≠ 0) : (C r : hahn_series Γ R) ≠ 0 :=
begin
  contrapose! h,
  rw ← C_zero at h,
  exact C_injective h,
end

lemma order_C {r : R} : order (C r : hahn_series Γ R) = 0 :=
begin
  by_cases h : r = 0,
  { rw [h, C_zero, order_zero] },
  { exact order_single h }
end

end non_assoc_semiring

section semiring
variables [semiring R]

lemma C_mul_eq_smul {r : R} {x : hahn_series Γ R} : C r * x = r • x :=
single_zero_mul_eq_smul

end semiring

section domain
variables {Γ' : Type*} [ordered_cancel_add_comm_monoid Γ']

lemma emb_domain_mul [non_unital_non_assoc_semiring R]
  (f : Γ ↪o Γ') (hf : ∀ x y, f (x + y) = f x + f y) (x y : hahn_series Γ R) :
  emb_domain f (x * y) = emb_domain f x * emb_domain f y :=
begin
  ext g,
  by_cases hg : g ∈ set.range f,
  { obtain ⟨g, rfl⟩ := hg,
    simp only [mul_coeff, emb_domain_coeff],
    transitivity ∑ ij in (add_antidiagonal x.is_pwo_support y.is_pwo_support g).map
      (function.embedding.prod_map f.to_embedding f.to_embedding),
      (emb_domain f x).coeff (ij.1) *
      (emb_domain f y).coeff (ij.2),
    { simp },
    apply sum_subset,
    { rintro ⟨i, j⟩ hij,
      simp only [exists_prop, mem_map, prod.mk.inj_iff,
        mem_add_antidiagonal, ne.def, function.embedding.coe_prod_map, mem_support,
        prod.exists] at hij,
      obtain ⟨i, j, ⟨rfl, hx, hy⟩, rfl, rfl⟩ := hij,
      simp [hx, hy, hf], },
    { rintro ⟨_, _⟩ h1 h2,
      contrapose! h2,
      obtain ⟨i, hi, rfl⟩ := support_emb_domain_subset (ne_zero_and_ne_zero_of_mul h2).1,
      obtain ⟨j, hj, rfl⟩ := support_emb_domain_subset (ne_zero_and_ne_zero_of_mul h2).2,
      simp only [exists_prop, mem_map, prod.mk.inj_iff,
        mem_add_antidiagonal, ne.def, function.embedding.coe_prod_map, mem_support,
        prod.exists],
      simp only [mem_add_antidiagonal, emb_domain_coeff, ne.def, mem_support, ← hf] at h1,
      exact ⟨i, j, ⟨f.injective h1.1, h1.2⟩, rfl⟩, } },
  { rw [emb_domain_notin_range hg, eq_comm],
    contrapose! hg,
    obtain ⟨_, _, hi, hj, rfl⟩ := support_mul_subset_add_support ((mem_support _ _).2 hg),
    obtain ⟨i, hi, rfl⟩ := support_emb_domain_subset hi,
    obtain ⟨j, hj, rfl⟩ := support_emb_domain_subset hj,
    refine ⟨i + j, hf i j⟩, }
end

lemma emb_domain_one [non_assoc_semiring R] (f : Γ ↪o Γ') (hf : f 0 = 0):
  emb_domain f (1 : hahn_series Γ R) = (1 : hahn_series Γ' R) :=
emb_domain_single.trans $ hf.symm ▸ rfl

/-- Extending the domain of Hahn series is a ring homomorphism. -/
@[simps] def emb_domain_ring_hom [non_assoc_semiring R] (f : Γ →+ Γ') (hfi : function.injective f)
  (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') :
  hahn_series Γ R →+* hahn_series Γ' R :=
{ to_fun := emb_domain ⟨⟨f, hfi⟩, hf⟩,
  map_one' := emb_domain_one _ f.map_zero,
  map_mul' := emb_domain_mul _ f.map_add,
  map_zero' := emb_domain_zero,
  map_add' := emb_domain_add _}

lemma emb_domain_ring_hom_C [non_assoc_semiring R] {f : Γ →+ Γ'} {hfi : function.injective f}
  {hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g'} {r : R} :
  emb_domain_ring_hom f hfi hf (C r) = C r :=
emb_domain_single.trans (by simp)

end domain

section algebra
variables [comm_semiring R] {A : Type*} [semiring A] [algebra R A]

instance : algebra R (hahn_series Γ A) :=
{ to_ring_hom := C.comp (algebra_map R A),
  smul_def' := λ r x, by { ext, simp },
  commutes' := λ r x, by { ext, simp only [smul_coeff, single_zero_mul_eq_smul, ring_hom.coe_comp,
    ring_hom.to_fun_eq_coe, C_apply, function.comp_app, algebra_map_smul, mul_single_zero_coeff],
    rw [← algebra.commutes, algebra.smul_def], }, }

theorem C_eq_algebra_map : C = (algebra_map R (hahn_series Γ R)) := rfl

theorem algebra_map_apply {r : R} :
  algebra_map R (hahn_series Γ A) r = C (algebra_map R A r) := rfl

instance [nontrivial Γ] [nontrivial R] : nontrivial (subalgebra R (hahn_series Γ R)) :=
⟨⟨⊥, ⊤, begin
  rw [ne.def, set_like.ext_iff, not_forall],
  obtain ⟨a, ha⟩ := exists_ne (0 : Γ),
  refine ⟨single a 1, _⟩,
  simp only [algebra.mem_bot, not_exists, set.mem_range, iff_true, algebra.mem_top],
  intros x,
  rw [ext_iff, function.funext_iff, not_forall],
  refine ⟨a, _⟩,
  rw [single_coeff_same, algebra_map_apply, C_apply, single_coeff_of_ne ha],
  exact zero_ne_one
end⟩⟩

section domain
variables {Γ' : Type*} [ordered_cancel_add_comm_monoid Γ']

/-- Extending the domain of Hahn series is an algebra homomorphism. -/
@[simps] def emb_domain_alg_hom (f : Γ →+ Γ') (hfi : function.injective f)
  (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') :
  hahn_series Γ A →ₐ[R] hahn_series Γ' A :=
{ commutes' := λ r, emb_domain_ring_hom_C,
  .. emb_domain_ring_hom f hfi hf }

end domain

end algebra

end multiplication

section semiring
variables [semiring R]

/-- The ring `hahn_series ℕ R` is isomorphic to `power_series R`. -/
@[simps] def to_power_series : (hahn_series ℕ R) ≃+* power_series R :=
{ to_fun := λ f, power_series.mk f.coeff,
  inv_fun := λ f, ⟨λ n, power_series.coeff R n f, (nat.lt_wf.is_wf _).is_pwo⟩,
  left_inv := λ f, by { ext, simp },
  right_inv := λ f, by { ext, simp },
  map_add' := λ f g, by { ext, simp },
  map_mul' := λ f g, begin
    ext n,
    simp only [power_series.coeff_mul, power_series.coeff_mk, mul_coeff, is_pwo_support],
    classical,
    refine sum_filter_ne_zero.symm.trans
      ((sum_congr _ (λ _ _, rfl)).trans sum_filter_ne_zero),
    ext m,
    simp only [nat.mem_antidiagonal, and.congr_left_iff, mem_add_antidiagonal, ne.def,
      and_iff_left_iff_imp, mem_filter, mem_support],
    intros h1 h2,
    contrapose h1,
    rw ← decidable.or_iff_not_and_not at h1,
    cases h1; simp [h1]
  end }

lemma coeff_to_power_series {f : hahn_series ℕ R} {n : ℕ} :
  power_series.coeff R n f.to_power_series = f.coeff n :=
power_series.coeff_mk _ _

lemma coeff_to_power_series_symm {f : power_series R} {n : ℕ} :
  (hahn_series.to_power_series.symm f).coeff n = power_series.coeff R n f := rfl

variables (Γ) (R) [ordered_semiring Γ] [nontrivial Γ]
/-- Casts a power series as a Hahn series with coefficients from an `ordered_semiring`. -/
def of_power_series : (power_series R) →+* hahn_series Γ R :=
(hahn_series.emb_domain_ring_hom (nat.cast_add_monoid_hom Γ) nat.strict_mono_cast.injective
  (λ _ _, nat.cast_le)).comp
  (ring_equiv.to_ring_hom to_power_series.symm)

variables {Γ} {R}

lemma of_power_series_injective : function.injective (of_power_series Γ R) :=
emb_domain_injective.comp to_power_series.symm.injective

@[simp] lemma of_power_series_apply (x : power_series R) :
  of_power_series Γ R x = hahn_series.emb_domain
  ⟨⟨(coe : ℕ → Γ), nat.strict_mono_cast.injective⟩, λ a b, begin
    simp only [function.embedding.coe_fn_mk],
    exact nat.cast_le,
  end⟩ (to_power_series.symm x) := rfl

lemma of_power_series_apply_coeff (x : power_series R) (n : ℕ) :
  (of_power_series Γ R x).coeff n = power_series.coeff R n x :=
by simp

end semiring

section algebra
variables (R) [comm_semiring R] {A : Type*} [semiring A] [algebra R A]

/-- The `R`-algebra `hahn_series ℕ A` is isomorphic to `power_series A`. -/
@[simps] def to_power_series_alg : (hahn_series ℕ A) ≃ₐ[R] power_series A :=
{ commutes' := λ r, begin
    ext n,
    simp only [algebra_map_apply, power_series.algebra_map_apply, ring_equiv.to_fun_eq_coe, C_apply,
      coeff_to_power_series],
    cases n,
    { simp only [power_series.coeff_zero_eq_constant_coeff, single_coeff_same],
      refl },
    { simp only [n.succ_ne_zero, ne.def, not_false_iff, single_coeff_of_ne],
      rw [power_series.coeff_C, if_neg n.succ_ne_zero] }
  end,
  .. to_power_series }

variables (Γ) (R) [ordered_semiring Γ] [nontrivial Γ]
/-- Casting a power series as a Hahn series with coefficients from an `ordered_semiring`
  is an algebra homomorphism. -/
@[simps] def of_power_series_alg : (power_series A) →ₐ[R] hahn_series Γ A :=
(hahn_series.emb_domain_alg_hom (nat.cast_add_monoid_hom Γ) nat.strict_mono_cast.injective
  (λ _ _, nat.cast_le)).comp
  (alg_equiv.to_alg_hom (to_power_series_alg R).symm)

end algebra

section valuation

variables [linear_ordered_add_comm_group Γ] [integral_domain R]

instance : linear_ordered_comm_group (multiplicative Γ) :=
{ .. (infer_instance : linear_order (multiplicative Γ)),
  .. (infer_instance : ordered_comm_group (multiplicative Γ)) }

instance : linear_ordered_comm_group_with_zero (with_zero (multiplicative Γ)) :=
{ zero_le_one := with_zero.zero_le 1,
  .. (with_zero.ordered_comm_monoid),
  .. (infer_instance : linear_order (with_zero (multiplicative Γ))),
  .. (infer_instance : comm_group_with_zero (with_zero (multiplicative Γ))) }

variables (Γ) (R)

/-- The additive valuation on `hahn_series Γ R`, returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series.  -/
def add_val : add_valuation (hahn_series Γ R) (with_top Γ) :=
add_valuation.of (λ x, if x = (0 : hahn_series Γ R) then (⊤ : with_top Γ) else x.order)
  (if_pos rfl)
  ((if_neg one_ne_zero).trans (by simp [order_of_ne]))
  (λ x y, begin
    by_cases hx : x = 0,
    { by_cases hy : y = 0; { simp [hx, hy] } },
    { by_cases hy : y = 0,
      { simp [hx, hy] },
      { simp only [hx, hy, support_nonempty_iff, if_neg, not_false_iff, is_wf_support],
        by_cases hxy : x + y = 0,
        { simp [hxy] },
        rw [if_neg hxy, ← with_top.coe_min, with_top.coe_le_coe],
        exact min_order_le_order_add hx hy hxy } },
  end)
  (λ x y, begin
    by_cases hx : x = 0,
    { simp [hx] },
    by_cases hy : y = 0,
    { simp [hy] },
    rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy),
      ← with_top.coe_add, with_top.coe_eq_coe, order_mul hx hy],
  end)

variables {Γ} {R}

lemma add_val_apply {x : hahn_series Γ R} :
  add_val Γ R x = if x = (0 : hahn_series Γ R) then (⊤ : with_top Γ) else x.order :=
add_valuation.of_apply _

@[simp]
lemma add_val_apply_of_ne {x : hahn_series Γ R} (hx : x ≠ 0) :
  add_val Γ R x = x.order :=
if_neg hx

lemma add_val_le_of_coeff_ne_zero {x : hahn_series Γ R} {g : Γ} (h : x.coeff g ≠ 0) :
  add_val Γ R x ≤ g :=
begin
  rw [add_val_apply_of_ne (ne_zero_of_coeff_ne_zero h), with_top.coe_le_coe],
  exact order_le_of_coeff_ne_zero h
end

end valuation

lemma is_pwo_Union_support_powers [linear_ordered_add_comm_group Γ] [integral_domain R]
  {x : hahn_series Γ R} (hx : 0 < add_val Γ R x) :
  (⋃ n : ℕ, (x ^ n).support).is_pwo :=
begin
  apply (x.is_wf_support.is_pwo.add_submonoid_closure (λ g hg, _)).mono _,
  { exact with_top.coe_le_coe.1 (le_trans (le_of_lt hx) (add_val_le_of_coeff_ne_zero hg)) },
  refine set.Union_subset (λ n, _),
  induction n with n ih;
  intros g hn,
  { simp only [exists_prop, and_true, set.mem_singleton_iff, set.set_of_eq_eq_singleton,
      mem_support, ite_eq_right_iff, ne.def, not_false_iff, one_ne_zero,
      pow_zero, not_forall, one_coeff] at hn,
    rw [hn, set_like.mem_coe],
    exact add_submonoid.zero_mem _ },
  { obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support hn,
    exact set_like.mem_coe.2 (add_submonoid.add_mem _ (add_submonoid.subset_closure hi) (ih hj)) }
end

section
variables (Γ) (R) [partial_order Γ] [add_comm_monoid R]

/-- An infinite family of Hahn series which has a formal coefficient-wise sum.
  The requirements for this are that the union of the supports of the series is well-founded,
  and that only finitely many series are nonzero at any given coefficient. -/
structure summable_family (α : Type*) :=
(to_fun : α → hahn_series Γ R)
(is_pwo_Union_support' : set.is_pwo (⋃ (a : α), (to_fun a).support))
(finite_co_support' : ∀ (g : Γ), ({a | (to_fun a).coeff g ≠ 0}).finite)

end

namespace summable_family
section add_comm_monoid

variables [partial_order Γ] [add_comm_monoid R] {α : Type*}

instance : has_coe_to_fun (summable_family Γ R α) :=
⟨λ _, (α → hahn_series Γ R), to_fun⟩

lemma is_pwo_Union_support (s : summable_family Γ R α) : set.is_pwo (⋃ (a : α), (s a).support) :=
s.is_pwo_Union_support'

lemma finite_co_support (s : summable_family Γ R α) (g : Γ) :
  (function.support (λ a, (s a).coeff g)).finite :=
s.finite_co_support' g

lemma coe_injective : @function.injective (summable_family Γ R α) (α → hahn_series Γ R) coe_fn
| ⟨f1, hU1, hf1⟩ ⟨f2, hU2, hf2⟩ h :=
begin
  change f1 = f2 at h,
  subst h,
end

@[ext]
lemma ext {s t : summable_family Γ R α} (h : ∀ (a : α), s a = t a) : s = t :=
coe_injective $ funext h

instance : has_add (summable_family Γ R α) :=
⟨λ x y, { to_fun := x + y,
    is_pwo_Union_support' := (x.is_pwo_Union_support.union y.is_pwo_Union_support).mono (begin
      rw ← set.Union_union_distrib,
      exact set.Union_subset_Union (λ a, support_add_subset)
    end),
    finite_co_support' := λ g, ((x.finite_co_support g).union (y.finite_co_support g)).subset begin
      intros a ha,
      change (x a).coeff g + (y a).coeff g ≠ 0 at ha,
      rw [set.mem_union, function.mem_support, function.mem_support],
      contrapose! ha,
      rw [ha.1, ha.2, add_zero]
    end }⟩

instance : has_zero (summable_family Γ R α) :=
⟨⟨0, by simp, by simp⟩⟩

instance : inhabited (summable_family Γ R α) := ⟨0⟩

@[simp]
lemma coe_add {s t : summable_family Γ R α} : ⇑(s + t) = s + t := rfl

lemma add_apply {s t : summable_family Γ R α} {a : α} : (s + t) a = s a + t a := rfl

@[simp]
lemma coe_zero : ((0 : summable_family Γ R α) : α → hahn_series Γ R) = 0 := rfl

lemma zero_apply {a : α} : (0 : summable_family Γ R α) a = 0 := rfl

instance : add_comm_monoid (summable_family Γ R α) :=
{ add := (+),
  zero := 0,
  zero_add := λ s, by { ext, apply zero_add },
  add_zero := λ s, by { ext, apply add_zero },
  add_comm := λ s t, by { ext, apply add_comm },
  add_assoc := λ r s t, by { ext, apply add_assoc } }

/-- The infinite sum of a `summable_family` of Hahn series. -/
def hsum (s : summable_family Γ R α) :
  hahn_series Γ R :=
{ coeff := λ g, ∑ᶠ i, (s i).coeff g,
  is_pwo_support' := s.is_pwo_Union_support.mono (λ g, begin
    contrapose,
    rw [set.mem_Union, not_exists, function.mem_support, not_not],
    simp_rw [mem_support, not_not],
    intro h,
    rw [finsum_congr h, finsum_zero],
  end) }

@[simp]
lemma hsum_coeff {s : summable_family Γ R α} {g : Γ} :
  s.hsum.coeff g = ∑ᶠ i, (s i).coeff g := rfl

lemma support_hsum_subset {s : summable_family Γ R α} :
  s.hsum.support ⊆ ⋃ (a : α), (s a).support :=
λ g hg, begin
  rw [mem_support, hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)] at hg,
  obtain ⟨a, h1, h2⟩ := exists_ne_zero_of_sum_ne_zero hg,
  rw [set.mem_Union],
  exact ⟨a, h2⟩,
end

@[simp]
lemma hsum_add {s t : summable_family Γ R α} : (s + t).hsum = s.hsum + t.hsum :=
begin
  ext g,
  simp only [hsum_coeff, add_coeff, add_apply],
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)
end

end add_comm_monoid

section add_comm_group
variables [partial_order Γ] [add_comm_group R] {α : Type*} {s t : summable_family Γ R α} {a : α}

instance : add_comm_group (summable_family Γ R α) :=
{ neg := λ s, { to_fun := λ a, - s a,
    is_pwo_Union_support' := by { simp_rw [support_neg], exact s.is_pwo_Union_support' },
    finite_co_support' := λ g, by { simp only [neg_coeff', pi.neg_apply, ne.def, neg_eq_zero],
      exact s.finite_co_support g } },
  add_left_neg := λ a, by { ext, apply add_left_neg },
  .. summable_family.add_comm_monoid }

@[simp]
lemma coe_neg : ⇑(-s) = - s := rfl

lemma neg_apply : (-s) a = - (s a) := rfl

@[simp]
lemma coe_sub : ⇑(s - t) = s - t := rfl

lemma sub_apply : (s - t) a = s a - t a := rfl

end add_comm_group

section semiring

variables [ordered_cancel_add_comm_monoid Γ] [semiring R] {α : Type*}

instance : has_scalar (hahn_series Γ R) (summable_family Γ R α) :=
{ smul := λ x s, { to_fun := λ a, x * (s a),
    is_pwo_Union_support' := begin
      apply (x.is_pwo_support.add s.is_pwo_Union_support).mono,
      refine set.subset.trans (set.Union_subset_Union (λ a, support_mul_subset_add_support)) _,
      intro g,
      simp only [set.mem_Union, exists_imp_distrib],
      exact λ a ha, (set.add_subset_add (set.subset.refl _) (set.subset_Union _ a)) ha,
    end,
    finite_co_support' := λ g, begin
      refine ((add_antidiagonal x.is_pwo_support s.is_pwo_Union_support g).finite_to_set.bUnion
        (λ ij hij, _)).subset (λ a ha, _),
      { exact λ ij hij, function.support (λ a, (s a).coeff ij.2) },
      { apply s.finite_co_support },
      { obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support ha,
        simp only [exists_prop, set.mem_Union, mem_add_antidiagonal,
          mul_coeff, ne.def, mem_support, is_pwo_support, prod.exists],
        refine ⟨i, j, mem_coe.2 (mem_add_antidiagonal.2 ⟨rfl, hi, set.mem_Union.2 ⟨a, hj⟩⟩), hj⟩, }
    end } }

@[simp]
lemma smul_apply {x : hahn_series Γ R} {s : summable_family Γ R α} {a : α} :
  (x • s) a = x * (s a) := rfl

instance : module (hahn_series Γ R) (summable_family Γ R α) :=
{ smul := (•),
  smul_zero := λ x, ext (λ a, mul_zero _),
  zero_smul := λ x, ext (λ a, zero_mul _),
  one_smul := λ x, ext (λ a, one_mul _),
  add_smul := λ x y s, ext (λ a, add_mul _ _ _),
  smul_add := λ x s t, ext (λ a, mul_add _ _ _),
  mul_smul := λ x y s, ext (λ a, mul_assoc _ _ _) }

@[simp]
lemma hsum_smul {x : hahn_series Γ R} {s : summable_family Γ R α} :
  (x • s).hsum = x * s.hsum :=
begin
  ext g,
  simp only [mul_coeff, hsum_coeff, smul_apply],
  have h : ∀ i, (s i).support ⊆ ⋃ j, (s j).support := set.subset_Union _,
  refine (eq.trans (finsum_congr (λ a, _))
    (finsum_sum_comm (add_antidiagonal x.is_pwo_support s.is_pwo_Union_support g)
    (λ i ij, x.coeff (prod.fst ij) * (s i).coeff ij.snd) _)).trans _,
  { refine sum_subset (add_antidiagonal_mono_right (set.subset_Union _ a)) _,
    rintro ⟨i, j⟩ hU ha,
    rw mem_add_antidiagonal at *,
    rw [not_not.1 (λ con, ha ⟨hU.1, hU.2.1, con⟩), mul_zero] },
  { rintro ⟨i, j⟩ hij,
    refine (s.finite_co_support j).subset _,
    simp_rw [function.support_subset_iff', function.mem_support, not_not],
    intros a ha,
    rw [ha, mul_zero] },
  { refine (sum_congr rfl _).trans (sum_subset (add_antidiagonal_mono_right _) _).symm,
    { rintro ⟨i, j⟩ hij,
      rw mul_finsum,
      apply s.finite_co_support, },
    { intros x hx,
      simp only [set.mem_Union, ne.def, mem_support],
      contrapose! hx,
      simp [hx] },
    { rintro ⟨i, j⟩ hU ha,
      rw mem_add_antidiagonal at *,
      rw [← hsum_coeff, not_not.1 (λ con, ha ⟨hU.1, hU.2.1, con⟩), mul_zero] } }
end

/-- The summation of a `summable_family` as a `linear_map`. -/
@[simps] def lsum : (summable_family Γ R α) →ₗ[hahn_series Γ R] (hahn_series Γ R) :=
{ to_fun := hsum, map_add' := λ _ _, hsum_add, map_smul' := λ _ _, hsum_smul }

@[simp]
lemma hsum_sub {R : Type*} [ring R] {s t : summable_family Γ R α} :
  (s - t).hsum = s.hsum - t.hsum :=
by rw [← lsum_apply, linear_map.map_sub, lsum_apply, lsum_apply]

end semiring

section of_finsupp
variables [partial_order Γ] [add_comm_monoid R] {α : Type*}

/-- A family with only finitely many nonzero elements is summable. -/
def of_finsupp (f : α →₀ (hahn_series Γ R)) :
  summable_family Γ R α :=
{ to_fun := f,
  is_pwo_Union_support' := begin
      apply (f.support.is_pwo_sup (λ a, (f a).support) (λ a ha, (f a).is_pwo_support)).mono,
      intros g hg,
      obtain ⟨a, ha⟩ := set.mem_Union.1 hg,
      have haf : a ∈ f.support,
      { rw finsupp.mem_support_iff,
        contrapose! ha,
        rw [ha, support_zero],
        exact set.not_mem_empty _ },
      have h : (λ i, (f i).support) a ≤ _ := le_sup haf,
      exact h ha,
    end,
  finite_co_support' := λ g, begin
    refine f.support.finite_to_set.subset (λ a ha, _),
    simp only [coeff.add_monoid_hom_apply, mem_coe, finsupp.mem_support_iff,
    ne.def, function.mem_support],
    contrapose! ha,
    simp [ha]
  end }

@[simp]
lemma coe_of_finsupp {f : α →₀ (hahn_series Γ R)} : ⇑(summable_family.of_finsupp f) = f := rfl

@[simp]
lemma hsum_of_finsupp {f : α →₀ (hahn_series Γ R)} :
  (of_finsupp f).hsum = f.sum (λ a, id) :=
begin
  ext g,
  simp only [hsum_coeff, coe_of_finsupp, finsupp.sum, ne.def],
  simp_rw [← coeff.add_monoid_hom_apply, id.def],
  rw [add_monoid_hom.map_sum, finsum_eq_sum_of_support_subset],
  intros x h,
  simp only [coeff.add_monoid_hom_apply, mem_coe, finsupp.mem_support_iff, ne.def],
  contrapose! h,
  simp [h]
end

end of_finsupp

section emb_domain
variables [partial_order Γ] [add_comm_monoid R] {α β : Type*}

/-- A summable family can be reindexed by an embedding without changing its sum. -/
def emb_domain (s : summable_family Γ R α) (f : α ↪ β) : summable_family Γ R β :=
{ to_fun := λ b, if h : b ∈ set.range f then s (classical.some h) else 0,
  is_pwo_Union_support' := begin
    refine s.is_pwo_Union_support.mono (set.Union_subset (λ b g h, _)),
    by_cases hb : b ∈ set.range f,
    { rw dif_pos hb at h,
      exact set.mem_Union.2 ⟨classical.some hb, h⟩ },
    { contrapose! h,
      simp [hb] }
  end,
  finite_co_support' := λ g, ((s.finite_co_support g).image f).subset begin
    intros b h,
    by_cases hb : b ∈ set.range f,
    { simp only [ne.def, set.mem_set_of_eq, dif_pos hb] at h,
      exact ⟨classical.some hb, h, classical.some_spec hb⟩ },
    { contrapose! h,
      simp only [ne.def, set.mem_set_of_eq, dif_neg hb, not_not, zero_coeff] }
  end }

variables (s : summable_family Γ R α) (f : α ↪ β) {a : α} {b : β}

lemma emb_domain_apply :
  s.emb_domain f b = if h : b ∈ set.range f then s (classical.some h) else 0 := rfl

@[simp] lemma emb_domain_image : s.emb_domain f (f a) = s a :=
begin
  rw [emb_domain_apply, dif_pos (set.mem_range_self a)],
  exact congr rfl (f.injective (classical.some_spec (set.mem_range_self a)))
end

@[simp] lemma emb_domain_notin_range (h : b ∉ set.range f) : s.emb_domain f b = 0 :=
by rw [emb_domain_apply, dif_neg h]

@[simp] lemma hsum_emb_domain :
  (s.emb_domain f).hsum = s.hsum :=
begin
  ext g,
  simp only [hsum_coeff, emb_domain_apply, apply_dite hahn_series.coeff, dite_apply, zero_coeff],
  exact finsum_emb_domain f (λ a, (s a).coeff g)
end

end emb_domain

section powers

variables [linear_ordered_add_comm_group Γ] [integral_domain R]

/-- The powers of an element of positive valuation form a summable family. -/
def powers (x : hahn_series Γ R) (hx : 0 < add_val Γ R x) :
  summable_family Γ R ℕ :=
{ to_fun := λ n, x ^ n,
  is_pwo_Union_support' := is_pwo_Union_support_powers hx,
  finite_co_support' := λ g, begin
    have hpwo := (is_pwo_Union_support_powers hx),
    by_cases hg : g ∈ ⋃ n : ℕ, {g | (x ^ n).coeff g ≠ 0 },
    swap, { exact set.finite_empty.subset (λ n hn, hg (set.mem_Union.2 ⟨n, hn⟩)) },
    apply hpwo.is_wf.induction hg,
    intros y ys hy,
    refine ((((add_antidiagonal x.is_pwo_support hpwo y).finite_to_set.bUnion (λ ij hij,
      hy ij.snd _ _)).image nat.succ).union (set.finite_singleton 0)).subset _,
    { exact (mem_add_antidiagonal.1 (mem_coe.1 hij)).2.2 },
    { obtain ⟨rfl, hi, hj⟩ := mem_add_antidiagonal.1 (mem_coe.1 hij),
      rw [← zero_add ij.snd, ← add_assoc, add_zero],
      exact add_lt_add_right (with_top.coe_lt_coe.1
        (lt_of_lt_of_le hx (add_val_le_of_coeff_ne_zero hi))) _, },
    { intros n hn,
      cases n,
      { exact set.mem_union_right _ (set.mem_singleton 0) },
      { obtain ⟨i, j, hi, hj, rfl⟩ := support_mul_subset_add_support hn,
        refine set.mem_union_left _ ⟨n, set.mem_Union.2 ⟨⟨i, j⟩, set.mem_Union.2 ⟨_, hj⟩⟩, rfl⟩,
        simp only [true_and, set.mem_Union, mem_add_antidiagonal, mem_coe, eq_self_iff_true,
          ne.def, mem_support, set.mem_set_of_eq],
        exact ⟨hi, ⟨n, hj⟩⟩ } }
  end }

variables {x : hahn_series Γ R} (hx : 0 < add_val Γ R x)

@[simp] lemma coe_powers : ⇑(powers x hx) = pow x := rfl

lemma emb_domain_succ_smul_powers :
  (x • powers x hx).emb_domain ⟨nat.succ, nat.succ_injective⟩ =
    powers x hx - of_finsupp (finsupp.single 0 1) :=
begin
  apply summable_family.ext (λ n, _),
  cases n,
  { rw [emb_domain_notin_range, sub_apply, coe_powers, pow_zero, coe_of_finsupp,
      finsupp.single_eq_same, sub_self],
    rw [set.mem_range, not_exists],
    exact nat.succ_ne_zero },
  { refine eq.trans (emb_domain_image _ ⟨nat.succ, nat.succ_injective⟩) _,
    simp only [pow_succ, coe_powers, coe_sub, smul_apply, coe_of_finsupp, pi.sub_apply],
    rw [finsupp.single_eq_of_ne (n.succ_ne_zero).symm, sub_zero] }
end

lemma one_sub_self_mul_hsum_powers :
  (1 - x) * (powers x hx).hsum = 1 :=
begin
  rw [← hsum_smul, sub_smul, one_smul, hsum_sub,
    ← hsum_emb_domain (x • powers x hx) ⟨nat.succ, nat.succ_injective⟩,
    emb_domain_succ_smul_powers],
  simp,
end

end powers

end summable_family

section inversion

variables [linear_ordered_add_comm_group Γ]

section integral_domain
variable [integral_domain R]

lemma unit_aux (x : hahn_series Γ R) {r : R} (hr : r * x.coeff x.order = 1) :
  0 < add_val Γ R (1 - C r * (single (- x.order) 1) * x) :=
begin
  have h10 : (1 : R) ≠ 0 := one_ne_zero,
  have x0 : x ≠ 0 := ne_zero_of_coeff_ne_zero (right_ne_zero_of_mul_eq_one hr),
  refine lt_of_le_of_ne ((add_val Γ R).map_le_sub (ge_of_eq (add_val Γ R).map_one) _) _,
  { simp only [add_valuation.map_mul],
    rw [add_val_apply_of_ne x0, add_val_apply_of_ne (single_ne_zero h10),
      add_val_apply_of_ne _, order_C, order_single h10, with_top.coe_zero, zero_add,
      ← with_top.coe_add, neg_add_self, with_top.coe_zero],
    { exact le_refl 0 },
    { exact C_ne_zero (left_ne_zero_of_mul_eq_one hr) } },
  { rw [add_val_apply, ← with_top.coe_zero],
    split_ifs,
    { apply with_top.coe_ne_top },
    rw [ne.def, with_top.coe_eq_coe],
    intro con,
    apply coeff_order_ne_zero h,
    rw [← con, mul_assoc, sub_coeff, one_coeff, if_pos rfl, C_mul_eq_smul, smul_coeff, smul_eq_mul,
      ← add_neg_self x.order, single_mul_coeff_add, one_mul, hr, sub_self] }
end

lemma is_unit_iff {x : hahn_series Γ R} :
  is_unit x ↔ is_unit (x.coeff x.order) :=
begin
  split,
  { rintro ⟨⟨u, i, ui, iu⟩, rfl⟩,
    refine is_unit_of_mul_eq_one (u.coeff u.order) (i.coeff i.order)
      ((mul_coeff_order_add_order (left_ne_zero_of_mul_eq_one ui)
      (right_ne_zero_of_mul_eq_one ui)).symm.trans _),
    rw [ui, one_coeff, if_pos],
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui)
      (right_ne_zero_of_mul_eq_one ui), ui, order_one] },
  { rintro ⟨⟨u, i, ui, iu⟩, h⟩,
    rw [units.coe_mk] at h,
    rw h at iu,
    have h := summable_family.one_sub_self_mul_hsum_powers (unit_aux x iu),
    rw [sub_sub_cancel] at h,
    exact is_unit_of_mul_is_unit_right (is_unit_of_mul_eq_one _ _ h) },
end

end integral_domain

instance [field R] : field (hahn_series Γ R) :=
{ inv := λ x, if x0 : x = 0 then 0 else (C (x.coeff x.order)⁻¹ * (single (-x.order)) 1 *
      (summable_family.powers _ (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))).hsum),
  inv_zero := dif_pos rfl,
  mul_inv_cancel := λ x x0, begin
    refine (congr rfl (dif_neg x0)).trans _,
    have h := summable_family.one_sub_self_mul_hsum_powers
      (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0))),
    rw [sub_sub_cancel] at h,
    rw [← mul_assoc, mul_comm x, h],
  end,
  .. hahn_series.integral_domain }

end inversion

end hahn_series
