/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Definition of splitting fields, and definition of homomorphism into any field that splits
-/
import ring_theory.adjoin_root
import ring_theory.polynomial
import field_theory.minpoly
import tactic.field_simp

noncomputable theory
open_locale classical big_operators

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

namespace polynomial

variables [field α] [field β] [field γ]
open polynomial

section splits

variables (i : α →+* β)

/-- a polynomial `splits` iff it is zero or all of its irreducible factors have `degree` 1 -/
def splits (f : polynomial α) : Prop :=
f = 0 ∨ ∀ {g : polynomial β}, irreducible g → g ∣ f.map i → degree g = 1

@[simp] lemma splits_zero : splits i (0 : polynomial α) := or.inl rfl

@[simp] lemma splits_C (a : α) : splits i (C a) :=
if ha : a = 0 then ha.symm ▸ (@C_0 α _).symm ▸ splits_zero i
else
have hia : i a ≠ 0, from mt ((is_add_group_hom.injective_iff i).1
  i.injective _) ha,
or.inr $ λ g hg ⟨p, hp⟩, absurd hg.1 (not_not.2 (is_unit_iff_degree_eq_zero.2 $
  by have := congr_arg degree hp;
    simp [degree_C hia, @eq_comm (with_bot ℕ) 0,
      nat.with_bot.add_eq_zero_iff] at this; clear _fun_match; tauto))

lemma splits_of_degree_eq_one {f : polynomial α} (hf : degree f = 1) : splits i f :=
or.inr $ λ g hg ⟨p, hp⟩,
  by have := congr_arg degree hp;
  simp [nat.with_bot.add_eq_one_iff, hf, @eq_comm (with_bot ℕ) 1,
    mt is_unit_iff_degree_eq_zero.2 hg.1] at this;
  clear _fun_match; tauto

lemma splits_of_degree_le_one {f : polynomial α} (hf : degree f ≤ 1) : splits i f :=
begin
  cases h : degree f with n,
  { rw [degree_eq_bot.1 h]; exact splits_zero i },
  { cases n with n,
    { rw [eq_C_of_degree_le_zero (trans_rel_right (≤) h (le_refl _))];
      exact splits_C _ _ },
    { have hn : n = 0,
      { rw h at hf,
        cases n, { refl }, { exact absurd hf dec_trivial } },
      exact splits_of_degree_eq_one _ (by rw [h, hn]; refl) } }
end

lemma splits_mul {f g : polynomial α} (hf : splits i f) (hg : splits i g) : splits i (f * g) :=
if h : f * g = 0 then by simp [h]
else or.inr $ λ p hp hpf, ((principal_ideal_ring.irreducible_iff_prime.1 hp).2.2 _ _
    (show p ∣ map i f * map i g, by convert hpf; rw polynomial.map_mul)).elim
  (hf.resolve_left (λ hf, by simpa [hf] using h) hp)
  (hg.resolve_left (λ hg, by simpa [hg] using h) hp)

lemma splits_of_splits_mul {f g : polynomial α} (hfg : f * g ≠ 0) (h : splits i (f * g)) :
  splits i f ∧ splits i g :=
⟨or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_right _ _)),
 or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_left _ _))⟩

lemma splits_of_splits_of_dvd {f g : polynomial α} (hf0 : f ≠ 0) (hf : splits i f) (hgf : g ∣ f) :
  splits i g :=
by { obtain ⟨f, rfl⟩ := hgf, exact (splits_of_splits_mul i hf0 hf).1 }

lemma splits_of_splits_gcd_left {f g : polynomial α} (hf0 : f ≠ 0) (hf : splits i f) :
  splits i (euclidean_domain.gcd f g) :=
polynomial.splits_of_splits_of_dvd i hf0 hf (euclidean_domain.gcd_dvd_left f g)

lemma splits_of_splits_gcd_right {f g : polynomial α} (hg0 : g ≠ 0) (hg : splits i g) :
  splits i (euclidean_domain.gcd f g) :=
polynomial.splits_of_splits_of_dvd i hg0 hg (euclidean_domain.gcd_dvd_right f g)

lemma splits_map_iff (j : β →+* γ) {f : polynomial α} :
  splits j (f.map i) ↔ splits (j.comp i) f :=
by simp [splits, polynomial.map_map]

theorem splits_one : splits i 1 :=
splits_C i 1

theorem splits_of_is_unit {u : polynomial α} (hu : is_unit u) : u.splits i :=
splits_of_splits_of_dvd i one_ne_zero (splits_one _) $ is_unit_iff_dvd_one.1 hu

theorem splits_X_sub_C {x : α} : (X - C x).splits i :=
splits_of_degree_eq_one _ $ degree_X_sub_C x

theorem splits_X : X.splits i :=
splits_of_degree_eq_one _ $ degree_X

theorem splits_id_iff_splits {f : polynomial α} :
  (f.map i).splits (ring_hom.id β) ↔ f.splits i :=
by rw [splits_map_iff, ring_hom.id_comp]

theorem splits_mul_iff {f g : polynomial α} (hf : f ≠ 0) (hg : g ≠ 0) :
  (f * g).splits i ↔ f.splits i ∧ g.splits i :=
⟨splits_of_splits_mul i (mul_ne_zero hf hg), λ ⟨hfs, hgs⟩, splits_mul i hfs hgs⟩

theorem splits_prod {ι : Type w} {s : ι → polynomial α} {t : finset ι} :
  (∀ j ∈ t, (s j).splits i) → (∏ x in t, s x).splits i :=
begin
  refine finset.induction_on t (λ _, splits_one i) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht, rw finset.prod_insert hat,
  exact splits_mul i ht.1 (ih ht.2)
end

theorem splits_prod_iff {ι : Type w} {s : ι → polynomial α} {t : finset ι} :
  (∀ j ∈ t, s j ≠ 0) → ((∏ x in t, s x).splits i ↔ ∀ j ∈ t, (s j).splits i) :=
begin
  refine finset.induction_on t (λ _, ⟨λ _ _ h, h.elim, λ _, splits_one i⟩) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht ⊢,
  rw [finset.prod_insert hat, splits_mul_iff i ht.1 (finset.prod_ne_zero_iff.2 ht.2), ih ht.2]
end

lemma degree_eq_one_of_irreducible_of_splits {p : polynomial β}
  (h_nz : p ≠ 0) (hp : irreducible p) (hp_splits : splits (ring_hom.id β) p) :
  p.degree = 1 :=
begin
  rcases hp_splits,
  { contradiction },
  { apply hp_splits hp, simp }
end

lemma exists_root_of_splits {f : polynomial α} (hs : splits i f) (hf0 : degree f ≠ 0) :
  ∃ x, eval₂ i x f = 0 :=
if hf0 : f = 0 then ⟨37, by simp [hf0]⟩
else
  let ⟨g, hg⟩ := wf_dvd_monoid.exists_irreducible_factor
    (show ¬ is_unit (f.map i), from mt is_unit_iff_degree_eq_zero.1 (by rwa degree_map))
    (map_ne_zero hf0) in
  let ⟨x, hx⟩ := exists_root_of_degree_eq_one (hs.resolve_left hf0 hg.1 hg.2) in
  let ⟨i, hi⟩ := hg.2 in
  ⟨x, by rw [← eval_map, hi, eval_mul, show _ = _, from hx, zero_mul]⟩

lemma exists_multiset_of_splits {f : polynomial α} : splits i f →
  ∃ (s : multiset β), f.map i = C (i f.leading_coeff) *
  (s.map (λ a : β, (X : polynomial β) - C a)).prod :=
suffices splits (ring_hom.id _) (f.map i) → ∃ s : multiset β, f.map i =
  (C (f.map i).leading_coeff) * (s.map (λ a : β, (X : polynomial β) - C a)).prod,
by rwa [splits_map_iff, leading_coeff_map i] at this,
wf_dvd_monoid.induction_on_irreducible (f.map i)
  (λ _, ⟨{37}, by simp [i.map_zero]⟩)
  (λ u hu _, ⟨0,
    by conv_lhs { rw eq_C_of_degree_eq_zero (is_unit_iff_degree_eq_zero.1 hu) };
      simp [leading_coeff, nat_degree_eq_of_degree_eq_some (is_unit_iff_degree_eq_zero.1 hu)]⟩)
  (λ f p hf0 hp ih hfs,
    have hpf0 : p * f ≠ 0, from mul_ne_zero hp.ne_zero hf0,
    let ⟨s, hs⟩ := ih (splits_of_splits_mul _ hpf0 hfs).2 in
    ⟨-(p * norm_unit p).coeff 0 ::ₘ s,
      have hp1 : degree p = 1, from hfs.resolve_left hpf0 hp (by simp),
      begin
        rw [multiset.map_cons, multiset.prod_cons, leading_coeff_mul, C_mul, mul_assoc,
          mul_left_comm (C f.leading_coeff), ← hs, ← mul_assoc, mul_left_inj' hf0],
        conv_lhs {rw eq_X_add_C_of_degree_eq_one hp1},
        simp only [mul_add, coe_norm_unit_of_ne_zero hp.ne_zero, mul_comm p, coeff_neg,
          C_neg, sub_eq_add_neg, neg_neg, coeff_C_mul, (mul_assoc _ _ _).symm, C_mul.symm,
          mul_inv_cancel (show p.leading_coeff ≠ 0, from mt leading_coeff_eq_zero.1
            hp.ne_zero), one_mul],
      end⟩)

/-- Pick a root of a polynomial that splits. -/
def root_of_splits {f : polynomial α} (hf : f.splits i) (hfd : f.degree ≠ 0) : β :=
classical.some $ exists_root_of_splits i hf hfd

theorem map_root_of_splits {f : polynomial α} (hf : f.splits i) (hfd) :
  f.eval₂ i (root_of_splits i hf hfd) = 0 :=
classical.some_spec $ exists_root_of_splits i hf hfd

theorem roots_map {f : polynomial α} (hf : f.splits $ ring_hom.id α) :
  (f.map i).roots = (f.roots).map i :=
if hf0 : f = 0 then by rw [hf0, map_zero, roots_zero, roots_zero, multiset.map_zero] else
have hmf0 : f.map i ≠ 0 := map_ne_zero hf0,
let ⟨m, hm⟩ := exists_multiset_of_splits _ hf in
have h1 : ∀ p ∈ m.map (λ r, X - C r), (p : _) ≠ 0,
  from multiset.forall_mem_map_iff.2 $ λ _ _, X_sub_C_ne_zero _,
have h2 : ∀ p ∈ m.map (λ r, X - C (i r)), (p : _) ≠ 0,
  from multiset.forall_mem_map_iff.2 $ λ _ _, X_sub_C_ne_zero _,
begin
  rw map_id at hm, rw hm at hf0 hmf0 ⊢, rw map_mul at hmf0 ⊢,
  rw [roots_mul hf0, roots_mul hmf0, map_C, roots_C, zero_add, roots_C, zero_add,
      map_multiset_prod, multiset.map_map], simp_rw [(∘), map_sub, map_X, map_C],
  rw [roots_multiset_prod _ h2, multiset.bind_map,
      roots_multiset_prod _ h1, multiset.bind_map],
  simp_rw roots_X_sub_C,
  rw [multiset.bind_cons, multiset.bind_zero, add_zero,
      multiset.bind_cons, multiset.bind_zero, add_zero, multiset.map_id']
end

lemma eq_prod_roots_of_splits {p : polynomial α} {i : α →+* β}
  (hsplit : splits i p) :
  p.map i = C (i p.leading_coeff) * ((p.map i).roots.map (λ a, X - C a)).prod :=
begin
  by_cases p_eq_zero : p = 0,
  { rw [p_eq_zero, map_zero, leading_coeff_zero, i.map_zero, C.map_zero, zero_mul] },

  obtain ⟨s, hs⟩ := exists_multiset_of_splits i hsplit,
  have map_ne_zero : p.map i ≠ 0 := map_ne_zero (p_eq_zero),
  have prod_ne_zero : C (i p.leading_coeff) * (multiset.map (λ a, X - C a) s).prod ≠ 0 :=
    by rwa hs at map_ne_zero,

  have ne_zero_of_mem : ∀ (p : polynomial β), p ∈ s.map (λ a, X - C a) → p ≠ 0,
  { intros p mem,
    obtain ⟨a, _, rfl⟩ := multiset.mem_map.mp mem,
    apply X_sub_C_ne_zero },
  have map_bind_roots_eq : (s.map (λ a, X - C a)).bind (λ a, a.roots) = s,
  { refine multiset.induction_on s (by rw [multiset.map_zero, multiset.zero_bind]) _,
    intros a s ih,
    rw [multiset.map_cons, multiset.cons_bind, ih, roots_X_sub_C,
        multiset.cons_add, zero_add] },

  rw [hs, roots_mul prod_ne_zero, roots_C, zero_add,
      roots_multiset_prod _ ne_zero_of_mem,
      map_bind_roots_eq]
end

lemma eq_X_sub_C_of_splits_of_single_root {x : α} {h : polynomial α} (h_splits : splits i h)
  (h_roots : (h.map i).roots = {i x}) : h = (C (leading_coeff h)) * (X - C x) :=
begin
  apply polynomial.map_injective _ i.injective,
  rw [eq_prod_roots_of_splits h_splits, h_roots],
  simp,
end

lemma nat_degree_multiset_prod {R : Type*} [integral_domain R] {s : multiset (polynomial R)}
  (h : ∀ p ∈ s, p ≠ (0 : polynomial R)) :
  nat_degree s.prod = (s.map nat_degree).sum :=
begin
  revert h,
  refine s.induction_on _ _,
  { simp },
  intros p s ih h,
  have hs : ∀ p ∈ s, p ≠ (0 : polynomial R) := λ p hp, h p (multiset.mem_cons_of_mem hp),
  have hprod : s.prod ≠ 0 := multiset.prod_ne_zero (λ p hp, hs p hp),
  rw [multiset.prod_cons, nat_degree_mul (h p (multiset.mem_cons_self _ _)) hprod, ih hs,
      multiset.map_cons, multiset.sum_cons],
end

lemma nat_degree_eq_card_roots {p : polynomial α} {i : α →+* β}
  (hsplit : splits i p) : p.nat_degree = (p.map i).roots.card :=
begin
  by_cases p_eq_zero : p = 0,
  { rw [p_eq_zero, nat_degree_zero, map_zero, roots_zero, multiset.card_zero] },
  have map_ne_zero : p.map i ≠ 0 := map_ne_zero (p_eq_zero),
  rw eq_prod_roots_of_splits hsplit at map_ne_zero,

  conv_lhs { rw [← nat_degree_map i, eq_prod_roots_of_splits hsplit] },
  have : ∀ p' ∈ (map i p).roots.map (λ a, X - C a), p' ≠ (0 : polynomial β),
  { intros p hp,
    obtain ⟨a, ha, rfl⟩ := multiset.mem_map.mp hp,
    exact X_sub_C_ne_zero _ },
  simp [nat_degree_mul (left_ne_zero_of_mul map_ne_zero) (right_ne_zero_of_mul map_ne_zero),
        nat_degree_multiset_prod this]
end

lemma degree_eq_card_roots {p : polynomial α} {i : α →+* β} (p_ne_zero : p ≠ 0)
  (hsplit : splits i p) : p.degree = (p.map i).roots.card :=
by rw [degree_eq_nat_degree p_ne_zero, nat_degree_eq_card_roots hsplit]

section UFD

local attribute [instance, priority 10] principal_ideal_ring.to_unique_factorization_monoid
local infix ` ~ᵤ ` : 50 := associated

open unique_factorization_monoid associates

lemma splits_of_exists_multiset {f : polynomial α} {s : multiset β}
  (hs : f.map i = C (i f.leading_coeff) * (s.map (λ a : β, (X : polynomial β) - C a)).prod) :
  splits i f :=
if hf0 : f = 0 then or.inl hf0
else
  or.inr $ λ p hp hdp,
    have ht : multiset.rel associated
      (factors (f.map i)) (s.map (λ a : β, (X : polynomial β) - C a)) :=
    factors_unique
      (λ p hp, irreducible_of_factor _ hp)
      (λ p' m, begin
          obtain ⟨a,m,rfl⟩ := multiset.mem_map.1 m,
          exact irreducible_of_degree_eq_one (degree_X_sub_C _),
        end)
      (associated.symm $ calc _ ~ᵤ f.map i :
        ⟨(units.map' C : units β →* units (polynomial β)) (units.mk0 (f.map i).leading_coeff
            (mt leading_coeff_eq_zero.1 (map_ne_zero hf0))),
          by conv_rhs {rw [hs, ← leading_coeff_map i, mul_comm]}; refl⟩
        ... ~ᵤ _ : associated.symm (unique_factorization_monoid.factors_prod (by simpa using hf0))),
  let ⟨q, hq, hpq⟩ := exists_mem_factors_of_dvd (by simpa) hp hdp in
  let ⟨q', hq', hqq'⟩ := multiset.exists_mem_of_rel_of_mem ht hq in
  let ⟨a, ha⟩ := multiset.mem_map.1 hq' in
  by rw [← degree_X_sub_C a, ha.2];
    exact degree_eq_degree_of_associated (hpq.trans hqq')

lemma splits_of_splits_id {f : polynomial α} : splits (ring_hom.id _) f → splits i f :=
unique_factorization_monoid.induction_on_prime f (λ _, splits_zero _)
  (λ _ hu _, splits_of_degree_le_one _
    ((is_unit_iff_degree_eq_zero.1 hu).symm ▸ dec_trivial))
  (λ a p ha0 hp ih hfi, splits_mul _
    (splits_of_degree_eq_one _
      ((splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).1.resolve_left
        hp.1 (irreducible_of_prime hp) (by rw map_id)))
    (ih (splits_of_splits_mul _ (mul_ne_zero hp.1 ha0) hfi).2))

end UFD

lemma splits_iff_exists_multiset {f : polynomial α} : splits i f ↔
  ∃ (s : multiset β), f.map i = C (i f.leading_coeff) *
  (s.map (λ a : β, (X : polynomial β) - C a)).prod :=
⟨exists_multiset_of_splits i, λ ⟨s, hs⟩, splits_of_exists_multiset i hs⟩

lemma splits_comp_of_splits (j : β →+* γ) {f : polynomial α}
  (h : splits i f) : splits (j.comp i) f :=
begin
  change i with ((ring_hom.id _).comp i) at h,
  rw [← splits_map_iff],
  rw [← splits_map_iff i] at h,
  exact splits_of_splits_id _ h
end

/-- A monic polynomial `p` that has as much roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
lemma prod_multiset_X_sub_C_of_monic_of_roots_card_eq {p : polynomial α}
  (hmonic : p.monic) (hroots : p.roots.card = p.nat_degree) :
  (multiset.map (λ (a : α), X - C a) p.roots).prod = p :=
begin
  have hprodmonic : (multiset.map (λ (a : α), X - C a) p.roots).prod.monic,
  { simp only [prod_multiset_root_eq_finset_root (ne_zero_of_monic hmonic),
      monic_prod_of_monic, monic_X_sub_C, monic_pow, forall_true_iff] },
  have hdegree : (multiset.map (λ (a : α), X - C a) p.roots).prod.nat_degree = p.nat_degree,
  { rw [← hroots, nat_degree_multiset_prod],
    simp only [eq_self_iff_true, mul_one, nat.cast_id, nsmul_eq_mul, multiset.sum_repeat,
      multiset.map_const,nat_degree_X_sub_C, function.comp, multiset.map_map],
    intros x y,
    simp only [multiset.mem_map] at y,
    rcases y with ⟨a, ha, rfl⟩,
    exact X_sub_C_ne_zero a },
  obtain ⟨q, hq⟩ := prod_multiset_X_sub_C_dvd p,
  have qzero : q ≠ 0,
  { rintro rfl, apply hmonic.ne_zero, simpa only [mul_zero] using hq },
  have degp :
    p.nat_degree = (multiset.map (λ (a : α), X - C a) p.roots).prod.nat_degree + q.nat_degree,
  { nth_rewrite 0 [hq],
    simp only [nat_degree_mul (ne_zero_of_monic hprodmonic) qzero] },
  have degq : q.nat_degree = 0,
  { rw hdegree at degp,
    exact (add_right_inj p.nat_degree).mp (tactic.ring_exp.add_pf_sum_z degp rfl).symm },
  obtain ⟨u, hu⟩ := is_unit_iff_degree_eq_zero.2 ((degree_eq_iff_nat_degree_eq qzero).2 degq),
  have hassoc : associated (multiset.map (λ (a : α), X - C a) p.roots).prod p,
  { rw associated, use u, rw [hu, ← hq] },
  exact eq_of_monic_of_associated hprodmonic hmonic hassoc
end

/-- A polynomial `p` that has as much roots as its degree
can be written `p = p.leading_coeff * ∏(X - a)`, for `a` in `p.roots`. -/
lemma C_leading_coeff_mul_prod_multiset_X_sub_C {p : polynomial α}
  (hroots : p.roots.card = p.nat_degree) :
  (C p.leading_coeff) * (multiset.map (λ (a : α), X - C a) p.roots).prod = p :=
begin
  by_cases hzero : p = 0,
  { rw [hzero, leading_coeff_zero, ring_hom.map_zero, zero_mul], },
  { have hcoeff : p.leading_coeff ≠ 0,
    { intro h, exact hzero (leading_coeff_eq_zero.1 h) },
    have hrootsnorm : (normalize p).roots.card = (normalize p).nat_degree,
    { rw [roots_normalize, normalize_apply, nat_degree_mul hzero (units.ne_zero _), hroots, coe_norm_unit,
        nat_degree_C, add_zero], },
    have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_normalize hzero) hrootsnorm,
    rw [roots_normalize, normalize_apply, coe_norm_unit_of_ne_zero hzero] at hprod,
    calc (C p.leading_coeff) * (multiset.map (λ (a : α), X - C a) p.roots).prod
        = p * C ((p.leading_coeff)⁻¹ * p.leading_coeff) : by rw [hprod, mul_comm, mul_assoc, ← C_mul]
    ... = p * C 1 : by field_simp
    ... = p : by simp only [mul_one, ring_hom.map_one], },
end

/-- A polynomial splits if and only if it has as much roots as its degree. -/
lemma splits_iff_card_roots {p : polynomial α} :
  splits (ring_hom.id α) p ↔ p.roots.card = p.nat_degree :=
begin
  split,
  { intro H, rw [nat_degree_eq_card_roots H, map_id] },
  { intro hroots,
    apply (splits_iff_exists_multiset (ring_hom.id α)).2,
    use p.roots,
    simp only [ring_hom.id_apply, map_id],
    exact (C_leading_coeff_mul_prod_multiset_X_sub_C hroots).symm },
end

end splits

end polynomial


section embeddings

variables (F : Type*) [field F]

/-- If `p` is the minimal polynomial of `a` over `F` then `F[a] ≃ₐ[F] F[x]/(p)` -/
def alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly
  {R : Type*} [comm_ring R] [algebra F R] (x : R) :
  algebra.adjoin F ({x} : set R) ≃ₐ[F] adjoin_root (minpoly F x) :=
alg_equiv.symm $ alg_equiv.of_bijective
  (alg_hom.cod_restrict
    (adjoin_root.lift_hom _ x $ minpoly.aeval F x) _
    (λ p, adjoin_root.induction_on _ p $ λ p,
      (algebra.adjoin_singleton_eq_range F x).symm ▸ (polynomial.aeval _).mem_range.mpr ⟨p, rfl⟩))
  ⟨(alg_hom.injective_cod_restrict _ _ _).2 $ (alg_hom.injective_iff _).2 $ λ p,
    adjoin_root.induction_on _ p $ λ p hp, ideal.quotient.eq_zero_iff_mem.2 $
    ideal.mem_span_singleton.2 $ minpoly.dvd F x hp,
  λ y, let ⟨p, _, hp⟩ := (subalgebra.ext_iff.1 (algebra.adjoin_singleton_eq_range F x) y).1 y.2 in
  ⟨adjoin_root.mk _ p, subtype.eq hp⟩⟩

open finset

-- Speed up the following proof.
local attribute [irreducible] minpoly
-- TODO: Why is this so slow?
/-- If `K` and `L` are field extensions of `F` and we have `s : finset K` such that
the minimal polynomial of each `x ∈ s` splits in `L` then `algebra.adjoin F s` embeds in `L`. -/
theorem lift_of_splits {F K L : Type*} [field F] [field K] [field L]
  [algebra F K] [algebra F L] (s : finset K) :
  (∀ x ∈ s, is_integral F x ∧ polynomial.splits (algebra_map F L) (minpoly F x)) →
  nonempty (algebra.adjoin F (↑s : set K) →ₐ[F] L) :=
begin
  refine finset.induction_on s (λ H, _) (λ a s has ih H, _),
  { rw [coe_empty, algebra.adjoin_empty],
    exact ⟨(algebra.of_id F L).comp (algebra.bot_equiv F K)⟩ },
  rw forall_mem_insert at H, rcases H with ⟨⟨H1, H2⟩, H3⟩, cases ih H3 with f,
  choose H3 H4 using H3,
  rw [coe_insert, set.insert_eq, set.union_comm, algebra.adjoin_union],
  letI := (f : algebra.adjoin F (↑s : set K) →+* L).to_algebra,
  haveI : finite_dimensional F (algebra.adjoin F (↑s : set K)) :=
    (submodule.fg_iff_finite_dimensional _).1 (fg_adjoin_of_finite (set.finite_mem_finset s) H3),
  letI := field_of_finite_dimensional F (algebra.adjoin F (↑s : set K)),
  have H5 : is_integral (algebra.adjoin F (↑s : set K)) a := is_integral_of_is_scalar_tower a H1,
  have H6 : (minpoly (algebra.adjoin F (↑s : set K)) a).splits
    (algebra_map (algebra.adjoin F (↑s : set K)) L),
  { refine polynomial.splits_of_splits_of_dvd _
      (polynomial.map_ne_zero $ minpoly.ne_zero H1 :
        polynomial.map (algebra_map _ _) _ ≠ 0)
      ((polynomial.splits_map_iff _ _).2 _)
      (minpoly.dvd _ _ _),
    { rw ← is_scalar_tower.algebra_map_eq, exact H2 },
    { rw [← is_scalar_tower.aeval_apply, minpoly.aeval] } },
  obtain ⟨y, hy⟩ := polynomial.exists_root_of_splits _ H6 (ne_of_lt (minpoly.degree_pos H5)).symm,
  refine ⟨subalgebra.of_under _ _ _⟩,
  refine (adjoin_root.lift_hom (minpoly (algebra.adjoin F (↑s : set K)) a) y hy).comp _,
  exact alg_equiv.adjoin_singleton_equiv_adjoin_root_minpoly (algebra.adjoin F (↑s : set K)) a
end

end embeddings


namespace polynomial

variables [field α] [field β] [field γ]
open polynomial

section splitting_field

/-- Non-computably choose an irreducible factor from a polynomial. -/
def factor (f : polynomial α) : polynomial α :=
if H : ∃ g, irreducible g ∧ g ∣ f then classical.some H else X

instance irreducible_factor (f : polynomial α) : irreducible (factor f) :=
begin
  rw factor, split_ifs with H, { exact (classical.some_spec H).1 }, { exact irreducible_X }
end

theorem factor_dvd_of_not_is_unit {f : polynomial α} (hf1 : ¬is_unit f) : factor f ∣ f :=
begin
  by_cases hf2 : f = 0, { rw hf2, exact dvd_zero _ },
  rw [factor, dif_pos (wf_dvd_monoid.exists_irreducible_factor hf1 hf2)],
  exact (classical.some_spec $ wf_dvd_monoid.exists_irreducible_factor hf1 hf2).2
end

theorem factor_dvd_of_degree_ne_zero {f : polynomial α} (hf : f.degree ≠ 0) : factor f ∣ f :=
factor_dvd_of_not_is_unit (mt degree_eq_zero_of_is_unit hf)

theorem factor_dvd_of_nat_degree_ne_zero {f : polynomial α} (hf : f.nat_degree ≠ 0) : factor f ∣ f :=
factor_dvd_of_degree_ne_zero (mt nat_degree_eq_of_degree_eq_some hf)

/-- Divide a polynomial f by X - C r where r is a root of f in a bigger field extension. -/
def remove_factor (f : polynomial α) : polynomial (adjoin_root $ factor f) :=
map (adjoin_root.of f.factor) f /ₘ (X - C (adjoin_root.root f.factor))

theorem X_sub_C_mul_remove_factor (f : polynomial α) (hf : f.nat_degree ≠ 0) :
  (X - C (adjoin_root.root f.factor)) * f.remove_factor = map (adjoin_root.of f.factor) f :=
let ⟨g, hg⟩ := factor_dvd_of_nat_degree_ne_zero hf in
mul_div_by_monic_eq_iff_is_root.2 $ by rw [is_root.def, eval_map, hg, eval₂_mul, ← hg,
    adjoin_root.eval₂_root, zero_mul]

theorem nat_degree_remove_factor (f : polynomial α) :
  f.remove_factor.nat_degree = f.nat_degree - 1 :=
by rw [remove_factor, nat_degree_div_by_monic _ (monic_X_sub_C _), nat_degree_map, nat_degree_X_sub_C]

theorem nat_degree_remove_factor' {f : polynomial α} {n : ℕ} (hfn : f.nat_degree = n+1) :
  f.remove_factor.nat_degree = n :=
by rw [nat_degree_remove_factor, hfn, n.add_sub_cancel]

/-- Auxiliary construction to a splitting field of a polynomial. Uses induction on the degree. -/
def splitting_field_aux (n : ℕ) : Π {α : Type u} [field α], by exactI Π (f : polynomial α),
  f.nat_degree = n → Type u :=
nat.rec_on n (λ α _ _ _, α) $ λ n ih α _ f hf, by exactI
ih f.remove_factor (nat_degree_remove_factor' hf)

namespace splitting_field_aux

theorem succ (n : ℕ) (f : polynomial α) (hfn : f.nat_degree = n + 1) :
  splitting_field_aux (n+1) f hfn =
    splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn) := rfl

instance field (n : ℕ) : Π {α : Type u} [field α], by exactI
  Π {f : polynomial α} (hfn : f.nat_degree = n), field (splitting_field_aux n f hfn) :=
nat.rec_on n (λ α _ _ _, ‹field α›) $ λ n ih α _ f hf, ih _

instance inhabited {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n) :
  inhabited (splitting_field_aux n f hfn) := ⟨37⟩

instance algebra (n : ℕ) : Π {α : Type u} [field α], by exactI
  Π {f : polynomial α} (hfn : f.nat_degree = n), algebra α (splitting_field_aux n f hfn) :=
nat.rec_on n (λ α _ _ _, by exactI algebra.id α) $ λ n ih α _ f hfn,
by exactI @@algebra.comap.algebra _ _ _ _ _ _ _ (ih _)

instance algebra' {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  algebra (adjoin_root f.factor) (splitting_field_aux _ _ hfn) :=
splitting_field_aux.algebra n _

instance algebra'' {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  algebra α (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)) :=
splitting_field_aux.algebra (n+1) hfn

instance algebra''' {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  algebra (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)) :=
splitting_field_aux.algebra n _

instance scalar_tower {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  is_scalar_tower α (adjoin_root f.factor) (splitting_field_aux _ _ hfn) :=
is_scalar_tower.of_algebra_map_eq $ λ x, rfl

instance scalar_tower' {n : ℕ} {f : polynomial α} (hfn : f.nat_degree = n + 1) :
  is_scalar_tower α (adjoin_root f.factor)
    (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)) :=
is_scalar_tower.of_algebra_map_eq $ λ x, rfl

theorem algebra_map_succ (n : ℕ) (f : polynomial α) (hfn : f.nat_degree = n + 1) :
  by exact algebra_map α (splitting_field_aux _ _ hfn) =
    (algebra_map (adjoin_root f.factor)
        (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn))).comp
      (adjoin_root.of f.factor) :=
rfl

protected theorem splits (n : ℕ) : ∀ {α : Type u} [field α], by exactI
  ∀ (f : polynomial α) (hfn : f.nat_degree = n),
    splits (algebra_map α $ splitting_field_aux n f hfn) f :=
nat.rec_on n (λ α _ _ hf, by exactI splits_of_degree_le_one _
  (le_trans degree_le_nat_degree $ hf.symm ▸ with_bot.coe_le_coe.2 zero_le_one)) $ λ n ih α _ f hf,
by { resetI, rw [← splits_id_iff_splits, algebra_map_succ, ← map_map, splits_id_iff_splits,
    ← X_sub_C_mul_remove_factor f (λ h, by { rw h at hf, cases hf })],
exact splits_mul _ (splits_X_sub_C _) (ih _ _) }

theorem exists_lift (n : ℕ) : ∀ {α : Type u} [field α], by exactI
  ∀ (f : polynomial α) (hfn : f.nat_degree = n) {β : Type*} [field β], by exactI
    ∀ (j : α →+* β) (hf : splits j f), ∃ k : splitting_field_aux n f hfn →+* β,
      k.comp (algebra_map _ _) = j :=
nat.rec_on n (λ α _ _ _ β _ j _, by exactI ⟨j, j.comp_id⟩) $ λ n ih α _ f hf β _ j hj, by exactI
have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hf, cases hf },
have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
let ⟨r, hr⟩ := exists_root_of_splits _ (splits_of_splits_of_dvd j hfn0 hj
  (factor_dvd_of_nat_degree_ne_zero hndf)) (mt is_unit_iff_degree_eq_zero.2 f.irreducible_factor.1) in
have hmf0 : map (adjoin_root.of f.factor) f ≠ 0, from map_ne_zero hfn0,
have hsf : splits (adjoin_root.lift j r hr) f.remove_factor,
by { rw ← X_sub_C_mul_remove_factor _ hndf at hmf0, refine (splits_of_splits_mul _ hmf0 _).2,
  rwa [X_sub_C_mul_remove_factor _ hndf, ← splits_id_iff_splits, map_map, adjoin_root.lift_comp_of,
      splits_id_iff_splits] },
let ⟨k, hk⟩ := ih f.remove_factor (nat_degree_remove_factor' hf) (adjoin_root.lift j r hr) hsf in
⟨k, by rw [algebra_map_succ, ← ring_hom.comp_assoc, hk, adjoin_root.lift_comp_of]⟩

theorem adjoin_roots (n : ℕ) : ∀ {α : Type u} [field α], by exactI
  ∀ (f : polynomial α) (hfn : f.nat_degree = n),
    algebra.adjoin α (↑(f.map $ algebra_map α $ splitting_field_aux n f hfn).roots.to_finset :
      set (splitting_field_aux n f hfn)) = ⊤ :=
nat.rec_on n (λ α _ f hf, by exactI algebra.eq_top_iff.2 (λ x, subalgebra.range_le _ ⟨x, rfl⟩)) $
λ n ih α _ f hfn, by exactI
have hndf : f.nat_degree ≠ 0, by { intro h, rw h at hfn, cases hfn },
have hfn0 : f ≠ 0, by { intro h, rw h at hndf, exact hndf rfl },
have hmf0 : map (algebra_map α (splitting_field_aux n.succ f hfn)) f ≠ 0 := map_ne_zero hfn0,
by { rw [algebra_map_succ, ← map_map, ← X_sub_C_mul_remove_factor _ hndf, map_mul] at hmf0 ⊢,
rw [roots_mul hmf0, map_sub, map_X, map_C, roots_X_sub_C, multiset.to_finset_add, finset.coe_union,
    multiset.to_finset_cons, multiset.to_finset_zero, insert_emptyc_eq, finset.coe_singleton,
    algebra.adjoin_union, ← set.image_singleton, algebra.adjoin_algebra_map α (adjoin_root f.factor)
      (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)),
    adjoin_root.adjoin_root_eq_top, algebra.map_top,
    is_scalar_tower.range_under_adjoin α (adjoin_root f.factor)
      (splitting_field_aux n f.remove_factor (nat_degree_remove_factor' hfn)),
    ih, subalgebra.res_top] }

end splitting_field_aux

/-- A splitting field of a polynomial. -/
def splitting_field (f : polynomial α) :=
splitting_field_aux _ f rfl

namespace splitting_field

variables (f : polynomial α)

instance : field (splitting_field f) :=
splitting_field_aux.field _ _

instance inhabited : inhabited (splitting_field f) := ⟨37⟩

instance : algebra α (splitting_field f) :=
splitting_field_aux.algebra _ _

protected theorem splits : splits (algebra_map α (splitting_field f)) f :=
splitting_field_aux.splits _ _ _

variables [algebra α β] (hb : splits (algebra_map α β) f)

/-- Embeds the splitting field into any other field that splits the polynomial. -/
def lift : splitting_field f →ₐ[α] β :=
{ commutes' := λ r, by { have := classical.some_spec (splitting_field_aux.exists_lift _ _ _ _ hb),
    exact ring_hom.ext_iff.1 this r },
  .. classical.some (splitting_field_aux.exists_lift _ _ _ _ hb) }

theorem adjoin_roots : algebra.adjoin α
    (↑(f.map (algebra_map α $ splitting_field f)).roots.to_finset : set (splitting_field f)) = ⊤ :=
splitting_field_aux.adjoin_roots _ _ _

end splitting_field

variables (α β) [algebra α β]
/-- Typeclass characterising splitting fields. -/
class is_splitting_field (f : polynomial α) : Prop :=
(splits [] : splits (algebra_map α β) f)
(adjoin_roots [] : algebra.adjoin α (↑(f.map (algebra_map α β)).roots.to_finset : set β) = ⊤)

namespace is_splitting_field

variables {α}
instance splitting_field (f : polynomial α) : is_splitting_field α (splitting_field f) f :=
⟨splitting_field.splits f, splitting_field.adjoin_roots f⟩

section scalar_tower

variables {α β γ} [algebra β γ] [algebra α γ] [is_scalar_tower α β γ]

variables {α}
instance map (f : polynomial α) [is_splitting_field α γ f] :
  is_splitting_field β γ (f.map $ algebra_map α β) :=
⟨by { rw [splits_map_iff, ← is_scalar_tower.algebra_map_eq], exact splits γ f },
 subalgebra.res_inj α $ by { rw [map_map, ← is_scalar_tower.algebra_map_eq, subalgebra.res_top,
    eq_top_iff, ← adjoin_roots γ f, algebra.adjoin_le_iff],
  exact λ x hx, @algebra.subset_adjoin β _ _ _ _ _ _ hx }⟩

variables {α} (β)
theorem splits_iff (f : polynomial α) [is_splitting_field α β f] :
  polynomial.splits (ring_hom.id α) f ↔ (⊤ : subalgebra α β) = ⊥ :=
⟨λ h, eq_bot_iff.2 $ adjoin_roots β f ▸ (roots_map (algebra_map α β) h).symm ▸
  algebra.adjoin_le_iff.2 (λ y hy,
    let ⟨x, hxs, hxy⟩ := finset.mem_image.1 (by rwa multiset.to_finset_map at hy) in
    hxy ▸ subalgebra.algebra_map_mem _ _),
 λ h, @ring_equiv.to_ring_hom_refl α _ ▸
  ring_equiv.trans_symm (ring_equiv.of_bijective _ $ algebra.bijective_algebra_map_iff.2 h) ▸
  by { rw ring_equiv.to_ring_hom_trans, exact splits_comp_of_splits _ _ (splits β f) }⟩

theorem mul (f g : polynomial α) (hf : f ≠ 0) (hg : g ≠ 0) [is_splitting_field α β f]
  [is_splitting_field β γ (g.map $ algebra_map α β)] :
  is_splitting_field α γ (f * g) :=
⟨(is_scalar_tower.algebra_map_eq α β γ).symm ▸ splits_mul _
  (splits_comp_of_splits _ _ (splits β f))
  ((splits_map_iff _ _).1 (splits γ $ g.map $ algebra_map α β)),
 by rw [map_mul, roots_mul (mul_ne_zero (map_ne_zero hf : f.map (algebra_map α γ) ≠ 0)
        (map_ne_zero hg)), multiset.to_finset_add, finset.coe_union, algebra.adjoin_union,
      is_scalar_tower.algebra_map_eq α β γ, ← map_map,
      roots_map (algebra_map β γ) ((splits_id_iff_splits $ algebra_map α β).2 $ splits β f),
      multiset.to_finset_map, finset.coe_image, algebra.adjoin_algebra_map, adjoin_roots,
      algebra.map_top, is_scalar_tower.range_under_adjoin, ← map_map, adjoin_roots,
      subalgebra.res_top]⟩

end scalar_tower

/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [algebra α γ] (f : polynomial α) [is_splitting_field α β f]
  (hf : polynomial.splits (algebra_map α γ) f) : β →ₐ[α] γ :=
if hf0 : f = 0 then (algebra.of_id α γ).comp $
  (algebra.bot_equiv α β : (⊥ : subalgebra α β) →ₐ[α] α).comp $
  by { rw ← (splits_iff β f).1 (show f.splits (ring_hom.id α), from hf0.symm ▸ splits_zero _),
  exact algebra.to_top } else
alg_hom.comp (by { rw ← adjoin_roots β f, exact classical.choice (lift_of_splits _ $ λ y hy,
    have aeval y f = 0, from (eval₂_eq_eval_map _).trans $
      (mem_roots $ by exact map_ne_zero hf0).1 (multiset.mem_to_finset.mp hy),
    ⟨(is_algebraic_iff_is_integral _).1 ⟨f, hf0, this⟩,
      splits_of_splits_of_dvd _ hf0 hf $ minpoly.dvd _ _ this⟩) })
  algebra.to_top

theorem finite_dimensional (f : polynomial α) [is_splitting_field α β f] : finite_dimensional α β :=
finite_dimensional.iff_fg.2 $ @algebra.coe_top α β _ _ _ ▸ adjoin_roots β f ▸
  fg_adjoin_of_finite (set.finite_mem_finset _) (λ y hy,
  if hf : f = 0
  then by { rw [hf, map_zero, roots_zero] at hy, cases hy }
  else (is_algebraic_iff_is_integral _).1 ⟨f, hf, (eval₂_eq_eval_map _).trans $
    (mem_roots $ by exact map_ne_zero hf).1 (multiset.mem_to_finset.mp hy)⟩)

/-- Any splitting field is isomorphic to `splitting_field f`. -/
def alg_equiv (f : polynomial α) [is_splitting_field α β f] : β ≃ₐ[α] splitting_field f :=
begin
  refine alg_equiv.of_bijective (lift β f $ splits (splitting_field f) f)
    ⟨ring_hom.injective (lift β f $ splits (splitting_field f) f).to_ring_hom, _⟩,
  haveI := finite_dimensional (splitting_field f) f,
  haveI := finite_dimensional β f,
  have : finite_dimensional.findim α β = finite_dimensional.findim α (splitting_field f) :=
  le_antisymm
    (linear_map.findim_le_findim_of_injective
      (show function.injective (lift β f $ splits (splitting_field f) f).to_linear_map, from
        ring_hom.injective (lift β f $ splits (splitting_field f) f : β →+* f.splitting_field)))
    (linear_map.findim_le_findim_of_injective
      (show function.injective (lift (splitting_field f) f $ splits β f).to_linear_map, from
        ring_hom.injective (lift (splitting_field f) f $ splits β f : f.splitting_field →+* β))),
  change function.surjective (lift β f $ splits (splitting_field f) f).to_linear_map,
  refine (linear_map.injective_iff_surjective_of_findim_eq_findim this).1 _,
  exact ring_hom.injective (lift β f $ splits (splitting_field f) f : β →+* f.splitting_field)
end

end is_splitting_field

end splitting_field

end polynomial

section alg_equiv_restrict

open polynomial

variables {F K : Type*} [field F] [field K] [algebra F K] (ϕ ψ : K →ₐ[F] K) (χ ω : K ≃ₐ[F] K)
  (p : polynomial F) (E : Type*) [field E] [algebra F E] [algebra E K]  [is_scalar_tower F E K]

lemma is_splitting_field.range_to_alg_hom [hp : is_splitting_field F E p] :
  (is_scalar_tower.to_alg_hom F E K).range =
    algebra.adjoin F (↑(p.map (algebra_map F K)).roots.to_finset : set K) :=
begin
  rw [is_scalar_tower.algebra_map_eq F E K, ←map_map, roots_map, ←finset.image_to_finset,
    finset.coe_image, algebra.adjoin_algebra_map, hp.adjoin_roots, algebra.map_top],
  exact ((splits_id_iff_splits (algebra_map F E)).mpr hp.splits),
end

/-- Restrict algebra homomorphism to range -/
def alg_hom.restrict_is_splitting_field_aux [hp : is_splitting_field F E p] :
  (is_scalar_tower.to_alg_hom F E K).range →ₐ[F] (is_scalar_tower.to_alg_hom F E K).range :=
{ to_fun := λ x, ⟨ϕ x, begin
    suffices : (is_scalar_tower.to_alg_hom F E K).range.map ϕ ≤ _,
    { exact this ⟨x, subtype.mem x, rfl⟩ },
    simp only [is_splitting_field.range_to_alg_hom p, ←algebra.adjoin_image,
      ←finset.coe_image, finset.image_to_finset],
    apply algebra.adjoin_mono,
    by_cases p = 0,
    { rw [h, map_zero, roots_zero, multiset.map_zero] },
    { intro y,
      simp only [finset.mem_coe, multiset.mem_to_finset, multiset.mem_map,
        mem_roots (map_ne_zero h), is_root, eval_map],
      rintros ⟨z, hz1, hz2⟩,
      rw [←hz2, ←alg_hom_eval₂_algebra_map, hz1, ϕ.map_zero] },
  end⟩,
  map_zero' := subtype.ext ϕ.map_zero,
  map_one' := subtype.ext ϕ.map_one,
  map_add' := λ x y, subtype.ext (ϕ.map_add x y),
  map_mul' := λ x y, subtype.ext (ϕ.map_mul x y),
  commutes' := λ x, subtype.ext (ϕ.commutes x) }

/-- Restrict algebra homomorphism to an is_splitting field -/
def alg_hom.restrict_is_splitting_field [hp : is_splitting_field F E p] : E →ₐ[F] E :=
((alg_hom.alg_equiv.of_injective_field (is_scalar_tower.to_alg_hom F E K)).symm.to_alg_hom.comp
  (ϕ.restrict_is_splitting_field_aux p E)).comp
    (alg_hom.alg_equiv.of_injective_field (is_scalar_tower.to_alg_hom F E K)).to_alg_hom

lemma alg_hom.restrict_is_splitting_field_commutes [hp : is_splitting_field F E p] (x : E) :
  algebra_map E K (ϕ.restrict_is_splitting_field p E x) = ϕ (algebra_map E K x) :=
subtype.ext_iff.mp (alg_equiv.apply_symm_apply (alg_hom.alg_equiv.of_injective_field
  (is_scalar_tower.to_alg_hom F E K)) (ϕ.restrict_is_splitting_field_aux p E
    ⟨is_scalar_tower.to_alg_hom F E K x, ⟨x, ⟨subsemiring.mem_top x, rfl⟩⟩⟩))

lemma alg_hom.restrict_is_splitting_field_comp [hp : is_splitting_field F E p] :
  (ϕ.restrict_is_splitting_field p E).comp (ψ.restrict_is_splitting_field p E) =
    (ϕ.comp ψ).restrict_is_splitting_field p E :=
alg_hom.ext (λ _, (algebra_map E K).injective
  (by simp only [alg_hom.comp_apply, alg_hom.restrict_is_splitting_field_commutes]))

/-- Restrict algebra isomorphism to an is_splitting field -/
def alg_equiv.restrict_is_splitting_field [hp : is_splitting_field F E p] : E ≃ₐ[F] E :=
alg_equiv.of_alg_hom (χ.to_alg_hom.restrict_is_splitting_field p E)
  (χ.symm.to_alg_hom.restrict_is_splitting_field p E)
  (alg_hom.ext $ λ _, (algebra_map E K).injective
    (by simp only [alg_hom.comp_apply, alg_hom.restrict_is_splitting_field_commutes,
      alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, alg_hom.id_apply, χ.apply_symm_apply]))
  (alg_hom.ext $ λ _, (algebra_map E K).injective
    (by simp only [alg_hom.comp_apply, alg_hom.restrict_is_splitting_field_commutes,
      alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, alg_hom.id_apply, χ.symm_apply_apply]))

lemma alg_equiv.restrict_is_splitting_field_commutes [is_splitting_field F E p] (x : E) :
  algebra_map E K (χ.restrict_is_splitting_field p E x) = χ (algebra_map E K x) :=
χ.to_alg_hom.restrict_is_splitting_field_commutes p E x

lemma alg_equiv.restrict_is_splitting_field_trans [hp : is_splitting_field F E p] :
  (χ.trans ω).restrict_is_splitting_field p E =
    (χ.restrict_is_splitting_field p E).trans (ω.restrict_is_splitting_field p E) :=
alg_equiv.ext (λ _, (algebra_map E K).injective
(by simp only [alg_equiv.trans_apply, alg_equiv.restrict_is_splitting_field_commutes]))

/-- Restriction to an is_splitting_field as a group homomorphism -/
def alg_equiv.restict_is_splitting_field_hom [hp : is_splitting_field F E p] :
  (K ≃ₐ[F] K) →* (E ≃ₐ[F] E) :=
monoid_hom.mk' (λ χ, χ.restrict_is_splitting_field p E)
  (λ ω χ, (χ.restrict_is_splitting_field_trans ω p E))

end alg_equiv_restrict
