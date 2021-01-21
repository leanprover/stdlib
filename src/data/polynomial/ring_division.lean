/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker, Johan Commelin
-/

import data.polynomial.div
import data.polynomial.algebra_map

/-!
# Theory of univariate polynomials

This file starts looking like the ring theory of $ R[X] $

-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

open finset

namespace polynomial
universes u v w z
variables {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

section comm_ring
variables [comm_ring R] {p q : polynomial R}

variables [comm_ring S]

lemma nat_degree_pos_of_aeval_root [algebra R S] {p : polynomial R} (hp : p ≠ 0)
  {z : S} (hz : aeval z p = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < p.nat_degree :=
nat_degree_pos_of_eval₂_root hp (algebra_map R S) hz inj

lemma degree_pos_of_aeval_root [algebra R S] {p : polynomial R} (hp : p ≠ 0)
  {z : S} (hz : aeval z p = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  0 < p.degree :=
nat_degree_pos_iff_degree_pos.mp (nat_degree_pos_of_aeval_root hp hz inj)

lemma aeval_mod_by_monic_eq_self_of_root [algebra R S]
  {p q : polynomial R} (hq : q.monic) {x : S} (hx : aeval x q = 0) :
  aeval x (p %ₘ q) = aeval x p :=
eval₂_mod_by_monic_eq_self_of_root hq hx

end comm_ring

section integral_domain
variables [integral_domain R] {p q : polynomial R}

instance : integral_domain (polynomial R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ a b h, begin
    have : leading_coeff 0 = leading_coeff a * leading_coeff b := h ▸ leading_coeff_mul a b,
    rw [leading_coeff_zero, eq_comm] at this,
    erw [← leading_coeff_eq_zero, ← leading_coeff_eq_zero],
    exact eq_zero_or_eq_zero_of_mul_eq_zero this
  end,
  ..polynomial.nontrivial,
  ..polynomial.comm_ring }

lemma nat_degree_mul (hp : p ≠ 0) (hq : q ≠ 0) : nat_degree (p * q) =
  nat_degree p + nat_degree q :=
by rw [← with_bot.coe_eq_coe, ← degree_eq_nat_degree (mul_ne_zero hp hq),
    with_bot.coe_add, ← degree_eq_nat_degree hp,
    ← degree_eq_nat_degree hq, degree_mul]

@[simp] lemma nat_degree_pow (p : polynomial R) (n : ℕ) :
  nat_degree (p ^ n) = n * nat_degree p :=
if hp0 : p = 0
then if hn0 : n = 0 then by simp [hp0, hn0]
  else by rw [hp0, zero_pow (nat.pos_of_ne_zero hn0)]; simp
else nat_degree_pow'
  (by rw [← leading_coeff_pow, ne.def, leading_coeff_eq_zero]; exact pow_ne_zero _ hp0)

lemma root_mul : is_root (p * q) a ↔ is_root p a ∨ is_root q a :=
by simp_rw [is_root, eval_mul, mul_eq_zero]

lemma root_or_root_of_root_mul (h : is_root (p * q) a) : is_root p a ∨ is_root q a :=
root_mul.1 h

lemma degree_le_mul_left (p : polynomial R) (hq : q ≠ 0) : degree p ≤ degree (p * q) :=
if hp : p = 0 then by simp only [hp, zero_mul, le_refl]
else by rw [degree_mul, degree_eq_nat_degree hp,
    degree_eq_nat_degree hq];
  exact with_bot.coe_le_coe.2 (nat.le_add_right _ _)

theorem nat_degree_le_of_dvd {p q : polynomial R} (h1 : p ∣ q) (h2 : q ≠ 0) : p.nat_degree ≤ q.nat_degree :=
begin
  rcases h1 with ⟨q, rfl⟩, rw mul_ne_zero_iff at h2,
  rw [nat_degree_mul h2.1 h2.2], exact nat.le_add_right _ _
end

section roots

open multiset

local attribute [reducible] with_zero

lemma degree_eq_zero_of_is_unit (h : is_unit p) : degree p = 0 :=
let ⟨q, hq⟩ := is_unit_iff_dvd_one.1 h in
have hp0 : p ≠ 0, from λ hp0, by simpa [hp0] using hq,
have hq0 : q ≠ 0, from λ hp0, by simpa [hp0] using hq,
have nat_degree (1 : polynomial R) = nat_degree (p * q),
  from congr_arg _ hq,
by rw [nat_degree_one, nat_degree_mul hp0 hq0, eq_comm,
    _root_.add_eq_zero_iff, ← with_bot.coe_eq_coe,
    ← degree_eq_nat_degree hp0] at this;
  exact this.1

@[simp] lemma degree_coe_units (u : units (polynomial R)) :
  degree (u : polynomial R) = 0 :=
degree_eq_zero_of_is_unit ⟨u, rfl⟩

theorem prime_X_sub_C {r : R} : prime (X - C r) :=
⟨X_sub_C_ne_zero r, not_is_unit_X_sub_C,
 λ _ _, by { simp_rw [dvd_iff_is_root, is_root.def, eval_mul, mul_eq_zero], exact id }⟩

theorem prime_X : prime (X : polynomial R) :=
by { convert (prime_X_sub_C : prime (X - C 0 : polynomial R)), simp }

lemma prime_of_degree_eq_one_of_monic (hp1 : degree p = 1)
  (hm : monic p) : prime p :=
have p = X - C (- p.coeff 0),
  by simpa [hm.leading_coeff] using eq_X_add_C_of_degree_eq_one hp1,
this.symm ▸ prime_X_sub_C

theorem irreducible_X_sub_C (r : R) : irreducible (X - C r) :=
irreducible_of_prime prime_X_sub_C

theorem irreducible_X : irreducible (X : polynomial R) :=
irreducible_of_prime prime_X

lemma irreducible_of_degree_eq_one_of_monic (hp1 : degree p = 1)
  (hm : monic p) : irreducible p :=
irreducible_of_prime (prime_of_degree_eq_one_of_monic hp1 hm)

theorem eq_of_monic_of_associated (hp : p.monic) (hq : q.monic) (hpq : associated p q) : p = q :=
begin
  obtain ⟨u, hu⟩ := hpq,
  unfold monic at hp hq,
  rw eq_C_of_degree_le_zero (le_of_eq $ degree_coe_units _) at hu,
  rw [← hu, leading_coeff_mul, hp, one_mul, leading_coeff_C] at hq,
  rwa [hq, C_1, mul_one] at hu
end

@[simp] lemma root_multiplicity_zero {x : R} : root_multiplicity x 0 = 0 := dif_pos rfl

lemma root_multiplicity_eq_zero {p : polynomial R} {x : R} (h : ¬ is_root p x) :
  root_multiplicity x p = 0 :=
begin
  rw root_multiplicity_eq_multiplicity,
  split_ifs, { refl },
  rw [← enat.coe_inj, enat.coe_get, multiplicity.multiplicity_eq_zero_of_not_dvd, enat.coe_zero],
  intro hdvd,
  exact h (dvd_iff_is_root.mp hdvd)
end

lemma root_multiplicity_pos {p : polynomial R} (hp : p ≠ 0) {x : R} :
  0 < root_multiplicity x p ↔ is_root p x :=
begin
  rw [← dvd_iff_is_root, root_multiplicity_eq_multiplicity, dif_neg hp,
      ← enat.coe_lt_coe, enat.coe_get],
  exact multiplicity.dvd_iff_multiplicity_pos
end

lemma root_multiplicity_mul {p q : polynomial R} {x : R} (hpq : p * q ≠ 0) :
  root_multiplicity x (p * q) = root_multiplicity x p + root_multiplicity x q :=
begin
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq,
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq,
  rw [root_multiplicity_eq_multiplicity (p * q), dif_neg hpq,
      root_multiplicity_eq_multiplicity p, dif_neg hp,
      root_multiplicity_eq_multiplicity q, dif_neg hq,
      @multiplicity.mul' _ _ _ (X - C x) _ _ prime_X_sub_C],
end

lemma root_multiplicity_X_sub_C_self {x : R} :
  root_multiplicity x (X - C x) = 1 :=
by rw [root_multiplicity_eq_multiplicity, dif_neg (X_sub_C_ne_zero x),
       multiplicity.get_multiplicity_self]

lemma root_multiplicity_X_sub_C {x y : R} :
  root_multiplicity x (X - C y) = if x = y then 1 else 0 :=
begin
  split_ifs with hxy,
  { rw hxy,
    exact root_multiplicity_X_sub_C_self },
  exact root_multiplicity_eq_zero (mt root_X_sub_C.mp (ne.symm hxy))
end

/-- The multiplicity of `a` as root of `(X - a) ^ n` is `n`. -/
lemma root_multiplicity_X_sub_C_pow (a : R) (n : ℕ) : root_multiplicity a ((X - C a) ^ n) = n :=
begin
  induction n with n hn,
  { refine root_multiplicity_eq_zero _,
    simp only [eval_one, is_root.def, not_false_iff, one_ne_zero, pow_zero] },
  have hzero :=  (ne_zero_of_monic (monic_pow (monic_X_sub_C a) n.succ)),
  rw pow_succ (X - C a) n at hzero ⊢,
  simp only [root_multiplicity_mul hzero, root_multiplicity_X_sub_C_self, hn, nat.one_add]
end

/-- If `(X - a) ^ n` divides a polynomial `p` then the multiplicity of `a` as root of `p` is at
least `n`. -/
lemma root_multiplicity_of_dvd {p : polynomial R} {a : R} {n : ℕ}
  (hzero : p ≠ 0) (h : (X - C a) ^ n ∣ p) : n ≤ root_multiplicity a p :=
begin
  obtain ⟨q, hq⟩ := exists_eq_mul_right_of_dvd h,
  rw hq at hzero,
  simp only [hq, root_multiplicity_mul hzero, root_multiplicity_X_sub_C_pow,
             ge_iff_le, _root_.zero_le, le_add_iff_nonneg_right],
end

/-- The multiplicity of `p + q` is at least the minimum of the multiplicities. -/
lemma root_multiplicity_add {p q : polynomial R} (a : R) (hzero : p + q ≠ 0) :
  min (root_multiplicity a p) (root_multiplicity a q) ≤ root_multiplicity a (p + q) :=
begin
  refine root_multiplicity_of_dvd hzero _,
  have hdivp : (X - C a) ^ root_multiplicity a p ∣ p := pow_root_multiplicity_dvd p a,
  have hdivq : (X - C a) ^ root_multiplicity a q ∣ q := pow_root_multiplicity_dvd q a,
  exact min_pow_dvd_add hdivp hdivq
end

lemma exists_multiset_roots : ∀ {p : polynomial R} (hp : p ≠ 0),
  ∃ s : multiset R, (s.card : with_bot ℕ) ≤ degree p ∧ ∀ a, s.count a = root_multiplicity a p
| p := λ hp, by haveI := classical.prop_decidable (∃ x, is_root p x); exact
if h : ∃ x, is_root p x
then
  let ⟨x, hx⟩ := h in
  have hpd : 0 < degree p := degree_pos_of_root hp hx,
  have hd0 : p /ₘ (X - C x) ≠ 0 :=
    λ h, by rw [← mul_div_by_monic_eq_iff_is_root.2 hx, h, mul_zero] at hp; exact hp rfl,
  have wf : degree (p /ₘ _) < degree p :=
    degree_div_by_monic_lt _ (monic_X_sub_C x) hp
    ((degree_X_sub_C x).symm ▸ dec_trivial),
  let ⟨t, htd, htr⟩ := @exists_multiset_roots (p /ₘ (X - C x)) hd0 in
  have hdeg : degree (X - C x) ≤ degree p := begin
    rw [degree_X_sub_C, degree_eq_nat_degree hp],
    rw degree_eq_nat_degree hp at hpd,
    exact with_bot.coe_le_coe.2 (with_bot.coe_lt_coe.1 hpd)
  end,
  have hdiv0 : p /ₘ (X - C x) ≠ 0 := mt (div_by_monic_eq_zero_iff (monic_X_sub_C x)
    (ne_zero_of_monic (monic_X_sub_C x))).1 $ not_lt.2 hdeg,
  ⟨x ::ₘ t, calc (card (x ::ₘ t) : with_bot ℕ) = t.card + 1 :
      by exact_mod_cast card_cons _ _
    ... ≤ degree p :
      by rw [← degree_add_div_by_monic (monic_X_sub_C x) hdeg,
          degree_X_sub_C, add_comm];
        exact add_le_add (le_refl (1 : with_bot ℕ)) htd,
  begin
    assume a,
    conv_rhs { rw ← mul_div_by_monic_eq_iff_is_root.mpr hx },
    rw [root_multiplicity_mul (mul_ne_zero (X_sub_C_ne_zero _) hdiv0),
        root_multiplicity_X_sub_C, ← htr a],
    split_ifs with ha,
    { rw [ha, count_cons_self, nat.succ_eq_add_one, add_comm] },
    { rw [count_cons_of_ne ha, zero_add] },
  end⟩
else
  ⟨0, (degree_eq_nat_degree hp).symm ▸ with_bot.coe_le_coe.2 (nat.zero_le _),
    by { intro a, rw [count_zero, root_multiplicity_eq_zero (not_exists.mp h a)] }⟩
using_well_founded {dec_tac := tactic.assumption}

/-- `roots p` noncomputably gives a multiset containing all the roots of `p`,
including their multiplicities. -/
noncomputable def roots (p : polynomial R) : multiset R :=
if h : p = 0 then ∅ else classical.some (exists_multiset_roots h)

@[simp] lemma roots_zero : (0 : polynomial R).roots = 0 :=
dif_pos rfl

lemma card_roots (hp0 : p ≠ 0) : ((roots p).card : with_bot ℕ) ≤ degree p :=
begin
  unfold roots,
  rw dif_neg hp0,
  exact (classical.some_spec (exists_multiset_roots hp0)).1
end

lemma card_roots' {p : polynomial R} (hp0 : p ≠ 0) : p.roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots hp0) (le_of_eq $ degree_eq_nat_degree hp0))

lemma card_roots_sub_C {p : polynomial R} {a : R} (hp0 : 0 < degree p) :
  ((p - C a).roots.card : with_bot ℕ) ≤ degree p :=
calc ((p - C a).roots.card : with_bot ℕ) ≤ degree (p - C a) :
  card_roots $ mt sub_eq_zero.1 $ λ h, not_le_of_gt hp0 $ h.symm ▸ degree_C_le
... = degree p : by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

lemma card_roots_sub_C' {p : polynomial R} {a : R} (hp0 : 0 < degree p) :
  (p - C a).roots.card ≤ nat_degree p :=
with_bot.coe_le_coe.1 (le_trans (card_roots_sub_C hp0) (le_of_eq $ degree_eq_nat_degree
  (λ h, by simp [*, lt_irrefl] at *)))

@[simp] lemma count_roots (hp : p ≠ 0) : p.roots.count a = root_multiplicity a p :=
by { rw [roots, dif_neg hp], exact (classical.some_spec (exists_multiset_roots hp)).2 a }

@[simp] lemma mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ is_root p a :=
by rw [← count_pos, count_roots hp, root_multiplicity_pos hp]

lemma eq_zero_of_infinite_is_root
  (p : polynomial R) (h : set.infinite {x | is_root p x}) : p = 0 :=
begin
  by_contradiction hp,
  apply h,
  convert p.roots.to_finset.finite_to_set using 1,
  ext1 r,
  simp only [mem_roots hp, multiset.mem_to_finset, set.mem_set_of_eq, finset.mem_coe]
end

lemma eq_of_infinite_eval_eq {R : Type*} [integral_domain R]
  (p q : polynomial R) (h : set.infinite {x | eval x p = eval x q}) : p = q :=
begin
  rw [← sub_eq_zero],
  apply eq_zero_of_infinite_is_root,
  simpa only [is_root, eval_sub, sub_eq_zero]
end

lemma roots_mul {p q : polynomial R} (hpq : p * q ≠ 0) : (p * q).roots = p.roots + q.roots :=
multiset.ext.mpr $ λ r,
  by rw [count_add, count_roots hpq, count_roots (left_ne_zero_of_mul hpq),
         count_roots (right_ne_zero_of_mul hpq), root_multiplicity_mul hpq]

@[simp] lemma mem_roots_sub_C {p : polynomial R} {a x : R} (hp0 : 0 < degree p) :
  x ∈ (p - C a).roots ↔ p.eval x = a :=
(mem_roots (show p - C a ≠ 0, from mt sub_eq_zero.1 $ λ h,
    not_le_of_gt hp0 $ h.symm ▸ degree_C_le)).trans
  (by rw [is_root.def, eval_sub, eval_C, sub_eq_zero])

@[simp] lemma roots_X_sub_C (r : R) : roots (X - C r) = r ::ₘ 0 :=
begin
  ext s,
  rw [count_roots (X_sub_C_ne_zero r), root_multiplicity_X_sub_C],
  split_ifs with h,
  { rw [h, count_singleton] },
  { rw [count_cons_of_ne h, count_zero] }
end

@[simp] lemma roots_C (x : R) : (C x).roots = 0 :=
if H : x = 0 then by rw [H, C_0, roots_zero] else multiset.ext.mpr $ λ r,
have h : C x ≠ 0, from λ h, H $ C_inj.1 $ h.symm ▸ C_0.symm,
have not_root : ¬ is_root (C x) r := mt (λ (h : eval r (C x) = 0), trans eval_C.symm h) H,
by rw [count_roots h, count_zero, root_multiplicity_eq_zero not_root]

@[simp] lemma roots_one : (1 : polynomial R).roots = ∅ :=
roots_C 1

lemma roots_list_prod (L : list (polynomial R)) :
  (∀ p ∈ L, (p : _) ≠ 0) → L.prod.roots = (L : multiset (polynomial R)).bind roots :=
list.rec_on L (λ _, roots_one) $ λ hd tl ih H,
begin
  rw list.forall_mem_cons at H,
  rw [list.prod_cons, roots_mul (mul_ne_zero H.1 $ list.prod_ne_zero H.2),
      ← multiset.cons_coe, multiset.cons_bind, ih H.2]
end

lemma roots_multiset_prod (m : multiset (polynomial R)) :
  (∀ p ∈ m, (p : _) ≠ 0) → m.prod.roots = m.bind roots :=
multiset.induction_on m (λ _, roots_one) $ λ hd tl ih H,
begin
  rw multiset.forall_mem_cons at H,
  rw [multiset.prod_cons, roots_mul (mul_ne_zero H.1 $ multiset.prod_ne_zero H.2),
      multiset.cons_bind, ih H.2]
end

lemma roots_prod {ι : Type*} (f : ι → polynomial R) (s : finset ι) :
  s.prod f ≠ 0 → (s.prod f).roots = s.val.bind (λ i, roots (f i)) :=
begin
  refine s.induction_on _ _,
  { intros, exact roots_one },
  intros i s hi ih ne_zero,
  rw prod_insert hi at ⊢ ne_zero,
  rw [roots_mul ne_zero, ih (right_ne_zero_of_mul ne_zero), insert_val,
      ndinsert_of_not_mem hi, cons_bind]
end

lemma roots_prod_X_sub_C (s : finset R) :
  (s.prod (λ a, X - C a)).roots = s.val :=
(roots_prod (λ a, X - C a) s (prod_ne_zero_iff.mpr (λ a _, X_sub_C_ne_zero a))).trans
  (by simp_rw [roots_X_sub_C, bind_cons, bind_zero, add_zero, multiset.map_id'])

lemma card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
  (roots ((X : polynomial R) ^ n - C a)).card ≤ n :=
with_bot.coe_le_coe.1 $
calc ((roots ((X : polynomial R) ^ n - C a)).card : with_bot ℕ)
      ≤ degree ((X : polynomial R) ^ n - C a) : card_roots (X_pow_sub_C_ne_zero hn a)
  ... = n : degree_X_pow_sub_C hn a

section nth_roots

/-- `nth_roots n a` noncomputably returns the solutions to `x ^ n = a`-/
def nth_roots (n : ℕ) (a : R) : multiset R :=
roots ((X : polynomial R) ^ n - C a)

@[simp] lemma mem_nth_roots {n : ℕ} (hn : 0 < n) {a x : R} :
  x ∈ nth_roots n a ↔ x ^ n = a :=
by rw [nth_roots, mem_roots (X_pow_sub_C_ne_zero hn a),
  is_root.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero_iff_eq]

@[simp] lemma nth_roots_zero (r : R) : nth_roots 0 r = 0 :=
by simp only [empty_eq_zero, pow_zero, nth_roots, ← C_1, ← C_sub, roots_C]

lemma card_nth_roots (n : ℕ) (a : R) :
  (nth_roots n a).card ≤ n :=
if hn : n = 0
then if h : (X : polynomial R) ^ n - C a = 0
  then by simp only [nat.zero_le, nth_roots, roots, h, dif_pos rfl, empty_eq_zero, card_zero]
  else with_bot.coe_le_coe.1 (le_trans (card_roots h)
   (by rw [hn, pow_zero, ← C_1, ← @is_ring_hom.map_sub _ _ _ _ (@C R _)];
      exact degree_C_le))
else by rw [← with_bot.coe_le_coe, ← degree_X_pow_sub_C (nat.pos_of_ne_zero hn) a];
  exact card_roots (X_pow_sub_C_ne_zero (nat.pos_of_ne_zero hn) a)

/-- The multiset `nth_roots ↑n (1 : R)` as a finset. -/
def nth_roots_finset (n : ℕ) (R : Type*) [integral_domain R] : finset R :=
multiset.to_finset (nth_roots n (1 : R))

@[simp] lemma mem_nth_roots_finset {n : ℕ} (h : 0 < n) {x : R} :
  x ∈ nth_roots_finset n R ↔ x ^ (n : ℕ) = 1 :=
by rw [nth_roots_finset, mem_to_finset, mem_nth_roots h]

end nth_roots

lemma coeff_comp_degree_mul_degree (hqd0 : nat_degree q ≠ 0) :
  coeff (p.comp q) (nat_degree p * nat_degree q) =
  leading_coeff p * leading_coeff q ^ nat_degree p :=
if hp0 : p = 0 then by simp [hp0] else
calc coeff (p.comp q) (nat_degree p * nat_degree q)
  = p.sum (λ n a, coeff (C a * q ^ n) (nat_degree p * nat_degree q)) :
    by rw [comp, eval₂, coeff_sum]
... = coeff (C (leading_coeff p) * q ^ nat_degree p) (nat_degree p * nat_degree q) :
  finset.sum_eq_single _
  begin
    assume b hbs hbp,
    have hq0 : q ≠ 0, from λ hq0, hqd0 (by rw [hq0, nat_degree_zero]),
    have : coeff p b ≠ 0, rwa finsupp.mem_support_iff at hbs,
    refine coeff_eq_zero_of_degree_lt _,
    rw [degree_mul], erw degree_C this,
    rw [degree_pow, zero_add, degree_eq_nat_degree hq0,
      ← with_bot.coe_nsmul, nsmul_eq_mul, with_bot.coe_lt_coe, nat.cast_id],
    rw mul_lt_mul_right, apply lt_of_le_of_ne, assumption', swap, omega,
    exact le_nat_degree_of_ne_zero this,
  end
  begin
    intro h, contrapose! hp0,
    rw finsupp.mem_support_iff at h, push_neg at h,
    rwa ← leading_coeff_eq_zero,
  end
... = _ :
  have coeff (q ^ nat_degree p) (nat_degree p * nat_degree q) = leading_coeff (q ^ nat_degree p),
    by rw [leading_coeff, nat_degree_pow],
  by rw [coeff_C_mul, this, leading_coeff_pow]

lemma nat_degree_comp : nat_degree (p.comp q) = nat_degree p * nat_degree q :=
le_antisymm nat_degree_comp_le
  (if hp0 : p = 0 then by rw [hp0, zero_comp, nat_degree_zero, zero_mul]
  else if hqd0 : nat_degree q = 0
  then have degree q ≤ 0, by rw [← with_bot.coe_zero, ← hqd0]; exact degree_le_nat_degree,
    by rw [eq_C_of_degree_le_zero this]; simp
  else le_nat_degree_of_ne_zero $
    have hq0 : q ≠ 0, from λ hq0, hqd0 $ by rw [hq0, nat_degree_zero],
    calc coeff (p.comp q) (nat_degree p * nat_degree q)
        = leading_coeff p * leading_coeff q ^ nat_degree p :
      coeff_comp_degree_mul_degree hqd0
    ... ≠ 0 : mul_ne_zero (mt leading_coeff_eq_zero.1 hp0)
      (pow_ne_zero _ (mt leading_coeff_eq_zero.1 hq0)))

lemma leading_coeff_comp (hq : nat_degree q ≠ 0) : leading_coeff (p.comp q) =
  leading_coeff p * leading_coeff q ^ nat_degree p :=
by rw [← coeff_comp_degree_mul_degree hq, ← nat_degree_comp]; refl

lemma units_coeff_zero_smul (c : units (polynomial R)) (p : polynomial R) :
  (c : polynomial R).coeff 0 • p = c * p :=
by rw [←polynomial.C_mul', ←polynomial.eq_C_of_degree_eq_zero (degree_coe_units c)]

@[simp] lemma nat_degree_coe_units (u : units (polynomial R)) :
  nat_degree (u : polynomial R) = 0 :=
nat_degree_eq_of_degree_eq_some (degree_coe_units u)

lemma zero_of_eval_zero [infinite R] (p : polynomial R) (h : ∀ x, p.eval x = 0) : p = 0 :=
by classical; by_contradiction hp; exact
infinite.not_fintype ⟨p.roots.to_finset, λ x, multiset.mem_to_finset.mpr ((mem_roots hp).mpr (h _))⟩

lemma funext [infinite R] {p q : polynomial R} (ext : ∀ r : R, p.eval r = q.eval r) : p = q :=
begin
  rw ← sub_eq_zero,
  apply zero_of_eval_zero,
  intro x,
  rw [eval_sub, sub_eq_zero, ext],
end

end roots

theorem is_unit_iff {f : polynomial R} : is_unit f ↔ ∃ r : R, is_unit r ∧ C r = f :=
⟨λ hf, ⟨f.coeff 0,
  is_unit_C.1 $ eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf) ▸ hf,
  (eq_C_of_degree_eq_zero (degree_eq_zero_of_is_unit hf)).symm⟩,
λ ⟨r, hr, hrf⟩, hrf ▸ is_unit_C.2 hr⟩

lemma coeff_coe_units_zero_ne_zero (u : units (polynomial R)) :
  coeff (u : polynomial R) 0 ≠ 0 :=
begin
  conv in (0) {rw [← nat_degree_coe_units u]},
  rw [← leading_coeff, ne.def, leading_coeff_eq_zero],
  exact units.ne_zero _
end

lemma degree_eq_degree_of_associated (h : associated p q) : degree p = degree q :=
let ⟨u, hu⟩ := h in by simp [hu.symm]

lemma degree_eq_one_of_irreducible_of_root (hi : irreducible p) {x : R} (hx : is_root p x) :
  degree p = 1 :=
let ⟨g, hg⟩ := dvd_iff_is_root.2 hx in
have is_unit (X - C x) ∨ is_unit g, from hi.2 _ _ hg,
this.elim
  (λ h, have h₁ : degree (X - C x) = 1, from degree_X_sub_C x,
    have h₂ : degree (X - C x) = 0, from degree_eq_zero_of_is_unit h,
    by rw h₁ at h₂; exact absurd h₂ dec_trivial)
  (λ hgu, by rw [hg, degree_mul, degree_X_sub_C, degree_eq_zero_of_is_unit hgu, add_zero])

/-- Division by a monic polynomial doesn't change the leading coefficient. -/
lemma leading_coeff_div_by_monic_of_monic {R : Type u} [integral_domain R] {p q : polynomial R}
  (hmonic : q.monic) (hdegree : q.degree ≤ p.degree) : (p /ₘ q).leading_coeff = p.leading_coeff :=
begin
  have hp := mod_by_monic_add_div p hmonic,
  have hzero : (p /ₘ q) ≠ 0,
  { intro h,
    exact not_lt_of_le hdegree ((div_by_monic_eq_zero_iff hmonic (monic.ne_zero hmonic)).1 h) },
  have deglt : (p %ₘ q).degree < (q * (p /ₘ q)).degree,
  { rw degree_mul,
    refine lt_of_lt_of_le (degree_mod_by_monic_lt p hmonic (monic.ne_zero hmonic)) _,
    rw [degree_eq_nat_degree (monic.ne_zero hmonic), degree_eq_nat_degree hzero],
    norm_cast,
    simp only [zero_le, le_add_iff_nonneg_right] },
  have hrew := (leading_coeff_add_of_degree_lt deglt),
  rw leading_coeff_mul q (p /ₘ q) at hrew,
  simp only [hmonic, one_mul, monic.leading_coeff] at hrew,
  nth_rewrite 1 ← hp,
  exact hrew.symm
end

lemma eq_of_monic_of_dvd_of_nat_degree_le (hp : p.monic) (hq : q.monic) (hdiv : p ∣ q)
  (hdeg : q.nat_degree ≤ p.nat_degree) : q = p :=
begin
  obtain ⟨r, hr⟩ := hdiv,
  have rzero : r ≠ 0,
  { intro h,
    simpa [h, monic.ne_zero hq] using hr },
  rw [hr, nat_degree_mul (monic.ne_zero hp) rzero] at hdeg,
  have hdegeq : p.nat_degree + r.nat_degree = p.nat_degree,
  { suffices hdegle : p.nat_degree ≤ p.nat_degree + r.nat_degree,
    { exact le_antisymm hdeg hdegle },
    exact nat.le.intro rfl },
  replace hdegeq := eq_C_of_nat_degree_eq_zero (((@add_right_inj _ _ p.nat_degree) _ 0).1 hdegeq),
  suffices hlead : 1 = r.leading_coeff,
  { have hcoeff := leading_coeff_C (r.coeff 0),
    rw [← hdegeq, ← hlead] at hcoeff,
    rw [← hcoeff, C_1] at hdegeq,
    rwa [hdegeq, mul_one] at hr },
  have hprod : q.leading_coeff = p.leading_coeff * r.leading_coeff,
  { simp only [hr, leading_coeff_mul] },
  rwa [monic.leading_coeff hp, monic.leading_coeff hq, one_mul] at hprod
end

end integral_domain

section

variables [semiring R] [integral_domain S] (φ : R →+* S)

lemma is_unit_of_is_unit_leading_coeff_of_is_unit_map
  (f : polynomial R) (hf : is_unit (leading_coeff f)) (H : is_unit (map φ f)) :
  is_unit f :=
begin
  have dz := degree_eq_zero_of_is_unit H,
  rw degree_map_eq_of_leading_coeff_ne_zero at dz,
  { rw eq_C_of_degree_eq_zero dz,
    apply is_unit.map',
    convert hf,
    rw (degree_eq_iff_nat_degree_eq _).1 dz,
    rintro rfl,
    simpa using H, },
  { intro h,
    have u : is_unit (φ f.leading_coeff) := is_unit.map' _ hf,
    rw h at u,
    simpa using u, }
end

end

section
variables [integral_domain R] [integral_domain S] (φ : R →+* S)
/--
A polynomial over an integral domain `R` is irreducible if it is monic and
  irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
  it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
lemma monic.irreducible_of_irreducible_map (f : polynomial R)
  (h_mon : monic f) (h_irr : irreducible (map φ f)) :
  irreducible f :=
begin
  fsplit,
  { intro h,
    exact h_irr.1 (is_unit.map (monoid_hom.of (map φ)) h), },
  { intros a b h,

    have q := (leading_coeff_mul a b).symm,
    rw ←h at q,
    dsimp [monic] at h_mon,
    rw h_mon at q,
    have au : is_unit a.leading_coeff := is_unit_of_mul_eq_one _ _ q,
    rw mul_comm at q,
    have bu : is_unit b.leading_coeff := is_unit_of_mul_eq_one _ _ q,
    clear q h_mon,

    have h' := congr_arg (map φ) h,
    simp only [map_mul] at h',
    cases h_irr.2 _ _ h' with w w,
    { left,
      exact is_unit_of_is_unit_leading_coeff_of_is_unit_map _ _ au w, },
    { right,
      exact is_unit_of_is_unit_leading_coeff_of_is_unit_map _ _ bu w, }, }
end

end

end polynomial

namespace is_integral_domain

variables {R : Type*} [comm_ring R]

/-- Lift evidence that `is_integral_domain R` to `is_integral_domain (polynomial R)`. -/
lemma polynomial (h : is_integral_domain R) : is_integral_domain (polynomial R) :=
@integral_domain.to_is_integral_domain _ (@polynomial.integral_domain _ (h.to_integral_domain _))

end is_integral_domain
