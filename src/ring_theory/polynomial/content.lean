/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import data.finset.gcd
import data.polynomial
import data.polynomial.cancel_leads

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : polynomial R`.
 - `p.content` is the `gcd` of the coefficients of `p`.
 - `p.is_primitive` indicates that `p.content = 1`.

## Main Results
 - `polynomial.content_mul`:
  If `p q : polynomial R`, then `(p * q).content = p.content * q.content`.
 - `polynomial.gcd_monoid`:
  The polynomial ring of a GCD domain is itself a GCD domain.

-/

variables {R : Type*} [integral_domain R]

namespace polynomial
section gcd_monoid
variable [gcd_monoid R]

/-- `p.content` is the `gcd` of the coefficients of `p`. -/
def content (p : polynomial R) : R := (p.support).gcd p.coeff

lemma content_dvd_coeff {p : polynomial R} (n : ℕ) : p.content ∣ p.coeff n :=
begin
  by_cases h : n ∈ p.support,
  { apply finset.gcd_dvd h },
  rw [mem_support_iff_coeff_ne_zero, not_not] at h,
  rw h,
  apply dvd_zero,
end

@[simp] lemma content_C {r : R} : (C r).content = normalize r :=
begin
  rw content,
  by_cases h0 : r = 0,
  { simp [h0] },
  have h : (C r).support = {0} := finsupp.support_single_ne_zero h0,
  simp [h],
end

@[simp] lemma content_zero : content (0 : polynomial R) = 0 :=
by rw [← C_0, content_C, normalize_zero]

@[simp] lemma content_one : content (1 : polynomial R) = 1 :=
by rw [← C_1, content_C, normalize_one]

lemma content_X_mul {p : polynomial R} : content (X * p) = content p :=
begin
  rw [content, content, finset.gcd_def, finset.gcd_def],
  refine congr rfl _,
  have h : (X * p).support = p.support.map ⟨nat.succ, nat.succ_injective⟩,
  { ext a,
    simp only [exists_prop, finset.mem_map, function.embedding.coe_fn_mk, ne.def,
      mem_support_iff_coeff_ne_zero],
    cases a,
    { simp [coeff_X_mul_zero, nat.succ_ne_zero] },
    rw [mul_comm, coeff_mul_X],
    split,
    { intro h,
      use a,
      simp [h] },
    { rintros ⟨b, ⟨h1, h2⟩⟩,
      rw ← nat.succ_injective h2,
      apply h1 } },
  rw h,
  simp only [finset.map_val, function.comp_app, function.embedding.coe_fn_mk, multiset.map_map],
  refine congr (congr rfl _) rfl,
  ext a,
  rw mul_comm,
  simp [coeff_mul_X],
end

@[simp] lemma content_X_pow {k : ℕ} : content ((X : polynomial R) ^ k) = 1 :=
begin
  induction k with k hi,
  { simp },
  rw [pow_succ, content_X_mul, hi]
end

@[simp] lemma content_X : content (X : polynomial R) = 1 :=
by { rw [← mul_one X, content_X_mul, content_one] }

lemma content_C_mul (r : R) (p : polynomial R) : (C r * p).content = normalize r * p.content :=
begin
  by_cases h0 : r = 0, { simp [h0] },
  rw content, rw content, rw ← finset.gcd_mul_left,
  refine congr (congr rfl _) _; ext; simp [h0, mem_support_iff_coeff_ne_zero]
end

@[simp] lemma content_monomial {r : R} {k : ℕ} : content (monomial k r) = normalize r :=
by { rw [single_eq_C_mul_X, content_C_mul, content_X_pow, mul_one] }

lemma content_eq_zero_iff {p : polynomial R} : content p = 0 ↔ p = 0 :=
begin
  rw [content, finset.gcd_eq_zero_iff],
  split; intro h,
  { ext n,
    by_cases h0 : n ∈ p.support,
    { rw [h n h0, coeff_zero], },
    { rw mem_support_iff_coeff_ne_zero at h0,
      push_neg at h0,
      simp [h0] } },
  { intros x h0,
    simp [h] }
end

@[simp] lemma normalize_content {p : polynomial R} : normalize p.content = p.content :=
finset.normalize_gcd

lemma content_eq_gcd_range_of_lt (p : polynomial R) (n : ℕ) (h : p.nat_degree < n) :
  p.content = (finset.range n).gcd p.coeff :=
begin
  apply dvd_antisymm_of_normalize_eq normalize_content finset.normalize_gcd,
  { rw finset.dvd_gcd_iff,
    intros i hi,
    apply content_dvd_coeff _ },
  { apply finset.gcd_mono,
    intro i,
    simp only [nat.lt_succ_iff, mem_support_iff_coeff_ne_zero, ne.def, finset.mem_range],
    contrapose!,
    intro h1,
    apply coeff_eq_zero_of_nat_degree_lt (lt_of_lt_of_le h h1), }
end

lemma content_eq_gcd_range_succ (p : polynomial R) :
  p.content = (finset.range p.nat_degree.succ).gcd p.coeff :=
content_eq_gcd_range_of_lt _ _ (nat.lt_succ_self _)

lemma content_eq_gcd_leading_coeff_content_erase_lead (p : polynomial R) :
  p.content = gcd_monoid.gcd p.leading_coeff (erase_lead p).content :=
begin
  by_cases h : p = 0,
  { simp [h] },
  rw [← leading_coeff_eq_zero, leading_coeff, ← ne.def, ← mem_support_iff_coeff_ne_zero] at h,
  rw [content, ← finset.insert_erase h, finset.gcd_insert, leading_coeff, content,
    erase_lead_support],
  refine congr rfl (finset.gcd_congr rfl (λ i hi, _)),
  rw finset.mem_erase at hi,
  rw [erase_lead_coeff, if_neg hi.1],
end

lemma dvd_content_iff_C_dvd {p : polynomial R} {r : R} : r ∣ p.content ↔ C r ∣ p :=
begin
  rw C_dvd_iff_dvd_coeff,
  split,
  { intros h i,
    apply dvd_trans h (content_dvd_coeff _) },
  { intro h,
    rw [content, finset.dvd_gcd_iff],
    intros i hi,
    apply h i }
end

lemma C_content_dvd (p : polynomial R) : C p.content ∣ p :=
dvd_content_iff_C_dvd.1 (dvd_refl _)

/-- A polynomial over a GCD domain is primitive when the `gcd` of its coefficients is 1 -/
def is_primitive (p : polynomial R) : Prop := p.content = 1

@[simp]
lemma is_primitive_one : is_primitive (1 : polynomial R) :=
by rw [is_primitive, ← C_1, content_C, normalize_one]

lemma monic.is_primitive {p : polynomial R} (hp : p.monic) : p.is_primitive :=
by rw [is_primitive, content_eq_gcd_leading_coeff_content_erase_lead,
  hp.leading_coeff, gcd_one_left]

lemma is_primitive.ne_zero {p : polynomial R} (hp : p.is_primitive) : p ≠ 0 :=
begin
  rintro rfl,
  rw [is_primitive, content_zero] at hp,
  apply zero_ne_one hp,
end

lemma is_primitive.content_eq_one {p : polynomial R} (hp : p.is_primitive) : p.content = 1 := hp

lemma is_primitive_iff_is_unit_of_C_dvd {p : polynomial R} :
  p.is_primitive ↔ ∀ (r : R), C r ∣ p → is_unit r :=
begin
  rw [is_primitive],
  split,
  { intros h r hdvd,
    rw [← dvd_content_iff_C_dvd, h] at hdvd,
    apply is_unit_of_dvd_one _ hdvd },
  { intro h,
    rw [← normalize_content, normalize_eq_one],
    apply h _ (C_content_dvd _) }
end

open_locale classical
noncomputable theory

section prim_part

/-- The primitive part of a polynomial `p` is the primitive polynomial gained by dividing `p` by
  `p.content`. If `p = 0`, then `p.prim_part = 1`.  -/
def prim_part (p : polynomial R) : polynomial R :=
if p = 0 then 1 else classical.some (C_content_dvd p)

lemma eq_C_content_mul_prim_part (p : polynomial R) : p = C p.content * p.prim_part :=
begin
  by_cases h : p = 0, { simp [h] },
  rw [prim_part, if_neg h, ← classical.some_spec (C_content_dvd p)],
end

@[simp]
lemma prim_part_zero : prim_part (0 : polynomial R) = 1 := if_pos rfl

lemma is_primitive_prim_part (p : polynomial R) : p.prim_part.is_primitive :=
begin
  by_cases h : p = 0, { simp [h] },
  rw ← content_eq_zero_iff at h,
  apply mul_left_cancel' h,
  conv_rhs { rw [p.eq_C_content_mul_prim_part, mul_one, content_C_mul, normalize_content] }
end

lemma content_prim_part (p : polynomial R) : p.prim_part.content = 1 :=
p.is_primitive_prim_part

lemma prim_part_ne_zero (p : polynomial R) : p.prim_part ≠ 0 := p.is_primitive_prim_part.ne_zero

lemma nat_degree_prim_part (p : polynomial R) : p.prim_part.nat_degree = p.nat_degree :=
begin
  by_cases h : C p.content = 0,
  { rw [C_eq_zero, content_eq_zero_iff] at h, simp [h] },
  conv_rhs { rw [p.eq_C_content_mul_prim_part,
    nat_degree_mul h p.prim_part_ne_zero, nat_degree_C, zero_add] },
end

@[simp]
lemma is_primitive.prim_part_eq {p : polynomial R} (hp : p.is_primitive) : p.prim_part = p :=
by rw [← one_mul p.prim_part, ← C_1, ← hp.content_eq_one, ← p.eq_C_content_mul_prim_part]

lemma is_unit_prim_part_C (r : R) : is_unit (C r).prim_part :=
begin
  by_cases h0 : r = 0,
  { simp [h0] },
  unfold is_unit,
  refine ⟨⟨C ↑(norm_unit r)⁻¹, C ↑(norm_unit r),
    by rw [← ring_hom.map_mul, units.inv_mul, C_1],
    by rw [← ring_hom.map_mul, units.mul_inv, C_1]⟩, _⟩,
  rw [← normalize_eq_zero, ← C_eq_zero] at h0,
  apply mul_left_cancel' h0,
  conv_rhs { rw [← content_C, ← (C r).eq_C_content_mul_prim_part], },
  simp only [units.coe_mk, normalize_apply, ring_hom.map_mul],
  rw [mul_assoc, ← ring_hom.map_mul, units.mul_inv, C_1, mul_one],
end

lemma prim_part_dvd (p : polynomial R) : p.prim_part ∣ p :=
dvd.intro_left (C p.content) p.eq_C_content_mul_prim_part.symm

end prim_part

lemma gcd_content_eq_of_dvd_sub {a : R} {p q : polynomial R} (h : C a ∣ p - q) :
  gcd_monoid.gcd a p.content = gcd_monoid.gcd a q.content :=
begin
  rw content_eq_gcd_range_of_lt p (max p.nat_degree q.nat_degree).succ
    (lt_of_le_of_lt (le_max_left _ _) (nat.lt_succ_self _)),
  rw content_eq_gcd_range_of_lt q (max p.nat_degree q.nat_degree).succ
    (lt_of_le_of_lt (le_max_right _ _) (nat.lt_succ_self _)),
  apply finset.gcd_eq_of_dvd_sub,
  intros x hx,
  cases h with w hw,
  use w.coeff x,
  rw [← coeff_sub, hw, coeff_C_mul]
end

lemma content_mul_aux {p q : polynomial R} :
  gcd_monoid.gcd (p * q).erase_lead.content p.leading_coeff =
  gcd_monoid.gcd (p.erase_lead * q).content p.leading_coeff :=
begin
  rw [gcd_comm (content _) _, gcd_comm (content _) _],
  apply gcd_content_eq_of_dvd_sub,
  rw [← self_sub_C_mul_X_pow, ← self_sub_C_mul_X_pow, sub_mul, sub_sub, add_comm, sub_add,
    sub_sub_cancel, leading_coeff_mul, ring_hom.map_mul, mul_assoc, mul_assoc],
  apply dvd_sub (dvd.intro _ rfl) (dvd.intro _ rfl),
end

@[simp]
theorem content_mul {p q : polynomial R} : (p * q).content = p.content * q.content :=
begin
  classical,
  suffices h : ∀ (n : ℕ) (p q : polynomial R), ((p * q).degree < n) →
    (p * q).content = p.content * q.content,
  { apply h,
    apply (lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 (nat.lt_succ_self _))) },
  intro n,
  induction n with n ih,
  { intros p q hpq,
    rw [with_bot.coe_zero, nat.with_bot.lt_zero_iff, degree_eq_bot, mul_eq_zero] at hpq,
    rcases hpq with rfl | rfl; simp },
  intros p q hpq,
  by_cases p0 : p = 0, { simp [p0] },
  by_cases q0 : q = 0, { simp [q0] },
  rw [degree_eq_nat_degree (mul_ne_zero p0 q0), with_bot.coe_lt_coe, nat.lt_succ_iff_lt_or_eq,
    ← with_bot.coe_lt_coe, ← degree_eq_nat_degree (mul_ne_zero p0 q0), nat_degree_mul p0 q0] at hpq,
  rcases hpq with hlt | heq, { apply ih _ _ hlt },
  rw [← p.nat_degree_prim_part, ← q.nat_degree_prim_part, ← with_bot.coe_eq_coe, with_bot.coe_add,
    ← degree_eq_nat_degree p.prim_part_ne_zero, ← degree_eq_nat_degree q.prim_part_ne_zero] at heq,
  rw [p.eq_C_content_mul_prim_part, q.eq_C_content_mul_prim_part],
  suffices h : (q.prim_part * p.prim_part).content = 1,
  { rw [mul_assoc, content_C_mul, content_C_mul, mul_comm p.prim_part, mul_assoc, content_C_mul,
    content_C_mul, h, mul_one, content_prim_part, content_prim_part, mul_one, mul_one] },
  rw [← normalize_content, normalize_eq_one, is_unit_iff_dvd_one,
      content_eq_gcd_leading_coeff_content_erase_lead, leading_coeff_mul, gcd_comm],
  apply dvd_trans (gcd_mul_dvd_mul_gcd _ _ _),
  rw [content_mul_aux, ih, content_prim_part, mul_one, gcd_comm,
      ← content_eq_gcd_leading_coeff_content_erase_lead, content_prim_part, one_mul,
      mul_comm q.prim_part, content_mul_aux, ih, content_prim_part, mul_one, gcd_comm,
      ← content_eq_gcd_leading_coeff_content_erase_lead, content_prim_part],
  { rw [← heq, degree_mul, with_bot.add_lt_add_iff_right],
    { apply degree_erase_lt p.prim_part_ne_zero },
    { rw [bot_lt_iff_ne_bot, ne.def, degree_eq_bot],
      apply q.prim_part_ne_zero } },
  { rw [mul_comm, ← heq, degree_mul, with_bot.add_lt_add_iff_left],
    { apply degree_erase_lt q.prim_part_ne_zero },
    { rw [bot_lt_iff_ne_bot, ne.def, degree_eq_bot],
      apply p.prim_part_ne_zero } }
end

theorem is_primitive.mul {p q : polynomial R} (hp : p.is_primitive) (hq : q.is_primitive) :
  (p * q).is_primitive :=
by rw [is_primitive, content_mul, hp.content_eq_one, hq.content_eq_one, mul_one]

@[simp]
theorem prim_part_mul {p q : polynomial R} (h0 : p * q ≠ 0) :
  (p * q).prim_part = p.prim_part * q.prim_part :=
begin
  rw [ne.def, ← content_eq_zero_iff, ← C_eq_zero] at h0,
  apply mul_left_cancel' h0,
  conv_lhs { rw [← (p * q).eq_C_content_mul_prim_part,
    p.eq_C_content_mul_prim_part, q.eq_C_content_mul_prim_part] },
  rw [content_mul, ring_hom.map_mul],
  ring,
end

lemma is_primitive.is_primitive_of_dvd {p q : polynomial R} (hp : p.is_primitive) (hdvd : q ∣ p) :
  q.is_primitive :=
begin
  rcases hdvd with ⟨r, rfl⟩,
  rw [is_primitive, ← normalize_content, normalize_eq_one, is_unit_iff_dvd_one],
  apply dvd.intro r.content,
  rwa [is_primitive, content_mul] at hp,
end

lemma is_primitive.dvd_prim_part_iff_dvd {p q : polynomial R}
  (hp : p.is_primitive) (hq : q ≠ 0) :
  p ∣ q.prim_part ↔ p ∣ q :=
begin
  refine ⟨λ h, dvd.trans h (dvd.intro_left _ q.eq_C_content_mul_prim_part.symm), λ h, _⟩,
  rcases h with ⟨r, rfl⟩,
  apply dvd.intro _,
  rw [prim_part_mul hq, hp.prim_part_eq],
end

theorem exists_primitive_lcm_of_is_primitive {p q : polynomial R}
  (hp : p.is_primitive) (hq : q.is_primitive) :
  ∃ r : polynomial R, r.is_primitive ∧ (∀ s : polynomial R, p ∣ s ∧ q ∣ s ↔ r ∣ s) :=
begin
  classical,
  have h : ∃ (n : ℕ) (r : polynomial R), r.nat_degree = n ∧ r.is_primitive ∧ p ∣ r ∧ q ∣ r :=
    ⟨(p * q).nat_degree, p * q, rfl, hp.mul hq, dvd_mul_right _ _, dvd_mul_left _ _⟩,
  rcases nat.find_spec h with ⟨r, rdeg, rprim, pr, qr⟩,
  refine ⟨r, rprim, λ s, ⟨_, λ rs, ⟨dvd.trans pr rs, dvd.trans qr rs⟩⟩⟩,
  suffices hs : ∀ (n : ℕ) (s : polynomial R), s.nat_degree = n → (p ∣ s ∧ q ∣ s → r ∣ s),
  { apply hs s.nat_degree s rfl },
  clear s,
  by_contra con,
  push_neg at con,
  rcases nat.find_spec con with ⟨s, sdeg, ⟨ps, qs⟩, rs⟩,
  have s0 : s ≠ 0,
  { contrapose! rs, simp [rs] },
  have hs := nat.find_min' h ⟨_, s.nat_degree_prim_part, s.is_primitive_prim_part,
              (hp.dvd_prim_part_iff_dvd s0).2 ps, (hq.dvd_prim_part_iff_dvd s0).2 qs⟩,
  rw ← rdeg at hs,
  by_cases sC : s.nat_degree ≤ 0,
  { rw [eq_C_of_nat_degree_le_zero (le_trans hs sC), is_primitive,
      content_C, normalize_eq_one] at rprim,
    rw [eq_C_of_nat_degree_le_zero (le_trans hs sC), ← dvd_content_iff_C_dvd] at rs,
    apply rs rprim.dvd },
  have hcancel := nat_degree_cancel_leads_lt_of_nat_degree_le_nat_degree hs (lt_of_not_ge sC),
  rw sdeg at hcancel,
  apply nat.find_min con hcancel,
  refine ⟨_, rfl, ⟨dvd_cancel_leads_of_dvd_of_dvd pr ps, dvd_cancel_leads_of_dvd_of_dvd qr qs⟩,
      λ rcs, rs _⟩,
  rw ← rprim.dvd_prim_part_iff_dvd s0,
  rw [cancel_leads, nat.sub_eq_zero_of_le hs, pow_zero, mul_one] at rcs,
  have h := dvd_add rcs (dvd.intro_left _ rfl),
  have hC0 := rprim.ne_zero,
  rw [ne.def, ← leading_coeff_eq_zero, ← C_eq_zero] at hC0,
  rw [sub_add_cancel, ← rprim.dvd_prim_part_iff_dvd (mul_ne_zero hC0 s0)] at h,
  rcases is_unit_prim_part_C r.leading_coeff with ⟨u, hu⟩,
  apply dvd.trans h (dvd_of_associated (associated.symm ⟨u, _⟩)),
  rw [prim_part_mul (mul_ne_zero hC0 s0), hu, mul_comm],
end

lemma dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part
  {p q : polynomial R} (hq : q ≠ 0) :
  p ∣ q ↔ p.content ∣ q.content ∧ p.prim_part ∣ q.prim_part :=
begin
  split; intro h,
  { rcases h with ⟨r, rfl⟩,
    rw [content_mul, p.is_primitive_prim_part.dvd_prim_part_iff_dvd hq],
    exact ⟨dvd.intro _ rfl, dvd.trans p.prim_part_dvd (dvd.intro _ rfl)⟩ },
  { rw [p.eq_C_content_mul_prim_part, q.eq_C_content_mul_prim_part],
    exact mul_dvd_mul (ring_hom.map_dvd C h.1) h.2 }
end

@[priority 100]
instance gcd_monoid : gcd_monoid (polynomial R) :=
gcd_monoid_of_exists_lcm $ λ p q, begin
  rcases exists_primitive_lcm_of_is_primitive p.is_primitive_prim_part q.is_primitive_prim_part
    with ⟨r, rprim, hr⟩,
  refine ⟨C (lcm p.content q.content) * r, λ s, _⟩,
  by_cases hs : s = 0,
  { simp [hs] },
  by_cases hpq : C (lcm p.content q.content) = 0,
  { rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq,
    rcases hpq with hpq | hpq; simp [hpq, hs] },
  iterate 3 { rw dvd_iff_content_dvd_content_and_prim_part_dvd_prim_part hs },
  rw [content_mul, rprim.content_eq_one, mul_one, content_C, normalize_lcm, lcm_dvd_iff,
    prim_part_mul (mul_ne_zero hpq rprim.ne_zero), rprim.prim_part_eq,
    is_unit.mul_left_dvd _ _ _ (is_unit_prim_part_C (lcm p.content q.content)), ← hr s.prim_part],
  tauto,
end

end gcd_monoid
end polynomial
