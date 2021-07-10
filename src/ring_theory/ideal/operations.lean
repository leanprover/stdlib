/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.algebra.operations
import algebra.algebra.tower
import data.equiv.ring
import data.nat.choose.sum
import ring_theory.ideal.basic
import ring_theory.non_zero_divisors
/-!
# More operations on modules and ideals
-/
universes u v w x

open_locale big_operators

namespace submodule

variables {R : Type u} {M : Type v}
variables [comm_ring R] [add_comm_group M] [module R M]

instance has_scalar' : has_scalar (ideal R) (submodule R M) :=
⟨λ I N, ⨆ r : I, N.map (r.1 • linear_map.id)⟩

/-- `N.annihilator` is the ideal of all elements `r : R` such that `r • N = 0`. -/
def annihilator (N : submodule R M) : ideal R :=
(linear_map.lsmul R N).ker

/-- `N.colon P` is the ideal of all elements `r : R` such that `r • P ⊆ N`. -/
def colon (N P : submodule R M) : ideal R :=
annihilator (P.map N.mkq)

variables {I J : ideal R} {N N₁ N₂ P P₁ P₂ : submodule R M}

theorem mem_annihilator {r} : r ∈ N.annihilator ↔ ∀ n ∈ N, r • n = (0:M) :=
⟨λ hr n hn, congr_arg subtype.val (linear_map.ext_iff.1 (linear_map.mem_ker.1 hr) ⟨n, hn⟩),
λ h, linear_map.mem_ker.2 $ linear_map.ext $ λ n, subtype.eq $ h n.1 n.2⟩

theorem mem_annihilator' {r} : r ∈ N.annihilator ↔ N ≤ comap (r • linear_map.id) ⊥ :=
mem_annihilator.trans ⟨λ H n hn, (mem_bot R).2 $ H n hn, λ H n hn, (mem_bot R).1 $ H hn⟩

theorem annihilator_bot : (⊥ : submodule R M).annihilator = ⊤ :=
(ideal.eq_top_iff_one _).2 $ mem_annihilator'.2 bot_le

theorem annihilator_eq_top_iff : N.annihilator = ⊤ ↔ N = ⊥ :=
⟨λ H, eq_bot_iff.2 $ λ (n:M) hn, (mem_bot R).2 $
  one_smul R n ▸ mem_annihilator.1 ((ideal.eq_top_iff_one _).1 H) n hn,
  λ H, H.symm ▸ annihilator_bot⟩

theorem annihilator_mono (h : N ≤ P) : P.annihilator ≤ N.annihilator :=
λ r hrp, mem_annihilator.2 $ λ n hn, mem_annihilator.1 hrp n $ h hn

theorem annihilator_supr (ι : Sort w) (f : ι → submodule R M) :
  (annihilator ⨆ i, f i) = ⨅ i, annihilator (f i) :=
le_antisymm (le_infi $ λ i, annihilator_mono $ le_supr _ _)
(λ r H, mem_annihilator'.2 $ supr_le $ λ i,
  have _ := (mem_infi _).1 H i, mem_annihilator'.1 this)

theorem mem_colon {r} : r ∈ N.colon P ↔ ∀ p ∈ P, r • p ∈ N :=
mem_annihilator.trans ⟨λ H p hp, (quotient.mk_eq_zero N).1 (H (quotient.mk p) (mem_map_of_mem hp)),
λ H m ⟨p, hp, hpm⟩, hpm ▸ (N.mkq).map_smul r p ▸ (quotient.mk_eq_zero N).2 $ H p hp⟩

theorem mem_colon' {r} : r ∈ N.colon P ↔ P ≤ comap (r • linear_map.id) N :=
mem_colon

theorem colon_mono (hn : N₁ ≤ N₂) (hp : P₁ ≤ P₂) : N₁.colon P₂ ≤ N₂.colon P₁ :=
λ r hrnp, mem_colon.2 $ λ p₁ hp₁, hn $ mem_colon.1 hrnp p₁ $ hp hp₁

theorem infi_colon_supr (ι₁ : Sort w) (f : ι₁ → submodule R M)
  (ι₂ : Sort x) (g : ι₂ → submodule R M) :
  (⨅ i, f i).colon (⨆ j, g j) = ⨅ i j, (f i).colon (g j) :=
le_antisymm (le_infi $ λ i, le_infi $ λ j, colon_mono (infi_le _ _) (le_supr _ _))
(λ r H, mem_colon'.2 $ supr_le $ λ j, map_le_iff_le_comap.1 $ le_infi $ λ i,
  map_le_iff_le_comap.2 $ mem_colon'.1 $ have _ := ((mem_infi _).1 H i),
  have _ := ((mem_infi _).1 this j), this)

theorem smul_mem_smul {r} {n} (hr : r ∈ I) (hn : n ∈ N) : r • n ∈ I • N :=
(le_supr _ ⟨r, hr⟩ : _ ≤ I • N) ⟨n, hn, rfl⟩

theorem smul_le {P : submodule R M} : I • N ≤ P ↔ ∀ (r ∈ I) (n ∈ N), r • n ∈ P :=
⟨λ H r hr n hn, H $ smul_mem_smul hr hn,
λ H, supr_le $ λ r, map_le_iff_le_comap.2 $ λ n hn, H r.1 r.2 n hn⟩

@[elab_as_eliminator]
theorem smul_induction_on {p : M → Prop} {x} (H : x ∈ I • N)
  (Hb : ∀ (r ∈ I) (n ∈ N), p (r • n)) (H0 : p 0)
  (H1 : ∀ x y, p x → p y → p (x + y))
  (H2 : ∀ (c:R) n, p n → p (c • n)) : p x :=
(@smul_le _ _ _ _ _ _ _ ⟨p, H0, H1, H2⟩).2 Hb H

theorem mem_smul_span_singleton {I : ideal R} {m : M} {x : M} :
  x ∈ I • span R ({m} : set M) ↔ ∃ y ∈ I, y • m = x :=
⟨λ hx, smul_induction_on hx
  (λ r hri n hnm,
    let ⟨s, hs⟩ := mem_span_singleton.1 hnm in ⟨r * s, I.mul_mem_right _ hri, hs ▸ mul_smul r s m⟩)
  ⟨0, I.zero_mem, by rw [zero_smul]⟩
  (λ m1 m2 ⟨y1, hyi1, hy1⟩ ⟨y2, hyi2, hy2⟩,
    ⟨y1 + y2, I.add_mem hyi1 hyi2, by rw [add_smul, hy1, hy2]⟩)
  (λ c r ⟨y, hyi, hy⟩, ⟨c * y, I.mul_mem_left _ hyi, by rw [mul_smul, hy]⟩),
λ ⟨y, hyi, hy⟩, hy ▸ smul_mem_smul hyi (subset_span $ set.mem_singleton m)⟩

theorem smul_le_right : I • N ≤ N :=
smul_le.2 $ λ r hr n, N.smul_mem r

theorem smul_mono (hij : I ≤ J) (hnp : N ≤ P) : I • N ≤ J • P :=
smul_le.2 $ λ r hr n hn, smul_mem_smul (hij hr) (hnp hn)

theorem smul_mono_left (h : I ≤ J) : I • N ≤ J • N :=
smul_mono h (le_refl N)

theorem smul_mono_right (h : N ≤ P) : I • N ≤ I • P :=
smul_mono (le_refl I) h

variables (I J N P)
@[simp] theorem smul_bot : I • (⊥ : submodule R M) = ⊥ :=
eq_bot_iff.2 $ smul_le.2 $ λ r hri s hsb,
(submodule.mem_bot R).2 $ ((submodule.mem_bot R).1 hsb).symm ▸ smul_zero r

@[simp] theorem bot_smul : (⊥ : ideal R) • N = ⊥ :=
eq_bot_iff.2 $ smul_le.2 $ λ r hrb s hsi,
(submodule.mem_bot R).2 $ ((submodule.mem_bot R).1 hrb).symm ▸ zero_smul _ s

@[simp] theorem top_smul : (⊤ : ideal R) • N = N :=
le_antisymm smul_le_right $ λ r hri, one_smul R r ▸ smul_mem_smul mem_top hri

theorem smul_sup : I • (N ⊔ P) = I • N ⊔ I • P :=
le_antisymm (smul_le.2 $ λ r hri m hmnp, let ⟨n, hn, p, hp, hnpm⟩ := mem_sup.1 hmnp in
  mem_sup.2 ⟨_, smul_mem_smul hri hn, _, smul_mem_smul hri hp, hnpm ▸ (smul_add _ _ _).symm⟩)
(sup_le (smul_mono_right le_sup_left)
  (smul_mono_right le_sup_right))

theorem sup_smul : (I ⊔ J) • N = I • N ⊔ J • N :=
le_antisymm (smul_le.2 $ λ r hrij n hn, let ⟨ri, hri, rj, hrj, hrijr⟩ := mem_sup.1 hrij in
  mem_sup.2 ⟨_, smul_mem_smul hri hn, _, smul_mem_smul hrj hn, hrijr ▸ (add_smul _ _ _).symm⟩)
(sup_le (smul_mono_left le_sup_left)
  (smul_mono_left le_sup_right))

protected theorem smul_assoc : (I • J) • N = I • (J • N) :=
le_antisymm (smul_le.2 $ λ rs hrsij t htn,
  smul_induction_on hrsij
  (λ r hr s hs,
    (@smul_eq_mul R _ r s).symm ▸ smul_smul r s t ▸ smul_mem_smul hr (smul_mem_smul hs htn))
  ((zero_smul R t).symm ▸ submodule.zero_mem _)
  (λ x y, (add_smul x y t).symm ▸ submodule.add_mem _)
  (λ r s h, (@smul_eq_mul R _ r s).symm ▸ smul_smul r s t ▸ submodule.smul_mem _ _ h))
(smul_le.2 $ λ r hr sn hsn, suffices J • N ≤ submodule.comap (r • linear_map.id) ((I • J) • N),
  from this hsn,
smul_le.2 $ λ s hs n hn, show r • (s • n) ∈ (I • J) • N,
  from mul_smul r s n ▸ smul_mem_smul (smul_mem_smul hr hs) hn)

variables (S : set R) (T : set M)

theorem span_smul_span : (ideal.span S) • (span R T) =
  span R (⋃ (s ∈ S) (t ∈ T), {s • t}) :=
le_antisymm (smul_le.2 $ λ r hrS n hnT, span_induction hrS
  (λ r hrS, span_induction hnT
    (λ n hnT, subset_span $ set.mem_bUnion hrS $
      set.mem_bUnion hnT $ set.mem_singleton _)
    ((smul_zero r : r • 0 = (0:M)).symm ▸ submodule.zero_mem _)
    (λ x y, (smul_add r x y).symm ▸ submodule.add_mem _)
    (λ c m, by rw [smul_smul, mul_comm, mul_smul]; exact submodule.smul_mem _ _))
  ((zero_smul R n).symm ▸ submodule.zero_mem _)
  (λ r s, (add_smul r s n).symm ▸ submodule.add_mem _)
  (λ c r, by rw [smul_eq_mul, mul_smul]; exact submodule.smul_mem _ _)) $
span_le.2 $ set.bUnion_subset $ λ r hrS, set.bUnion_subset $ λ n hnT, set.singleton_subset_iff.2 $
smul_mem_smul (subset_span hrS) (subset_span hnT)

variables {M' : Type w} [add_comm_group M'] [module R M']

theorem map_smul'' (f : M →ₗ[R] M') : (I • N).map f = I • N.map f :=
le_antisymm (map_le_iff_le_comap.2 $ smul_le.2 $ λ r hr n hn, show f (r • n) ∈ I • N.map f,
    from (f.map_smul r n).symm ▸ smul_mem_smul hr (mem_map_of_mem hn)) $
smul_le.2 $ λ r hr n hn, let ⟨p, hp, hfp⟩ := mem_map.1 hn in
hfp ▸ f.map_smul r p ▸ mem_map_of_mem (smul_mem_smul hr hp)

end submodule

namespace ideal

section chinese_remainder
variables {R : Type u} [comm_ring R] {ι : Type v}

theorem exists_sub_one_mem_and_mem (s : finset ι) {f : ι → ideal R}
  (hf : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i ⊔ f j = ⊤) (i : ι) (his : i ∈ s) :
  ∃ r : R, r - 1 ∈ f i ∧ ∀ j ∈ s, j ≠ i → r ∈ f j :=
begin
  have : ∀ j ∈ s, j ≠ i → ∃ r : R, ∃ H : r - 1 ∈ f i, r ∈ f j,
  { intros j hjs hji, specialize hf i his j hjs hji.symm,
    rw [eq_top_iff_one, submodule.mem_sup] at hf,
    rcases hf with ⟨r, hri, s, hsj, hrs⟩, refine ⟨1 - r, _, _⟩,
    { rw [sub_right_comm, sub_self, zero_sub], exact (f i).neg_mem hri },
    { rw [← hrs, add_sub_cancel'], exact hsj } },
  classical,
  have : ∃ g : ι → R, (∀ j, g j - 1 ∈ f i) ∧ ∀ j ∈ s, j ≠ i → g j ∈ f j,
  { choose g hg1 hg2,
    refine ⟨λ j, if H : j ∈ s ∧ j ≠ i then g j H.1 H.2 else 1, λ j, _, λ j, _⟩,
    { split_ifs with h, { apply hg1 }, rw sub_self, exact (f i).zero_mem },
    { intros hjs hji, rw dif_pos, { apply hg2 }, exact ⟨hjs, hji⟩ } },
  rcases this with ⟨g, hgi, hgj⟩, use (∏ x in s.erase i, g x), split,
  { rw [← quotient.eq, ring_hom.map_one, ring_hom.map_prod],
    apply finset.prod_eq_one, intros, rw [← ring_hom.map_one, quotient.eq], apply hgi },
  intros j hjs hji, rw [← quotient.eq_zero_iff_mem, ring_hom.map_prod],
  refine finset.prod_eq_zero (finset.mem_erase_of_ne_of_mem hji hjs) _,
  rw quotient.eq_zero_iff_mem, exact hgj j hjs hji
end

theorem exists_sub_mem [fintype ι] {f : ι → ideal R}
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) (g : ι → R) :
  ∃ r : R, ∀ i, r - g i ∈ f i :=
begin
  have : ∃ φ : ι → R, (∀ i, φ i - 1 ∈ f i) ∧ (∀ i j, i ≠ j → φ i ∈ f j),
  { have := exists_sub_one_mem_and_mem (finset.univ : finset ι) (λ i _ j _ hij, hf i j hij),
    choose φ hφ,
    existsi λ i, φ i (finset.mem_univ i),
    exact ⟨λ i, (hφ i _).1, λ i j hij, (hφ i _).2 j (finset.mem_univ j) hij.symm⟩ },
  rcases this with ⟨φ, hφ1, hφ2⟩,
  use ∑ i, g i * φ i,
  intros i,
  rw [← quotient.eq, ring_hom.map_sum],
  refine eq.trans (finset.sum_eq_single i _ _) _,
  { intros j _ hji, rw quotient.eq_zero_iff_mem, exact (f i).mul_mem_left _ (hφ2 j i hji) },
  { intros hi, exact (hi $ finset.mem_univ i).elim },
  specialize hφ1 i, rw [← quotient.eq, ring_hom.map_one] at hφ1,
  rw [ring_hom.map_mul, hφ1, mul_one]
end

/-- The homomorphism from `R/(⋂ i, f i)` to `∏ i, (R / f i)` featured in the Chinese
  Remainder Theorem. It is bijective if the ideals `f i` are comaximal. -/
def quotient_inf_to_pi_quotient (f : ι → ideal R) :
  (⨅ i, f i).quotient →+* Π i, (f i).quotient :=
quotient.lift (⨅ i, f i)
  (pi.ring_hom (λ i : ι, (quotient.mk (f i) : _))) $
  λ r hr, begin
    rw submodule.mem_infi at hr,
    ext i,
    exact quotient.eq_zero_iff_mem.2 (hr i)
  end

theorem quotient_inf_to_pi_quotient_bijective [fintype ι] {f : ι → ideal R}
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) :
  function.bijective (quotient_inf_to_pi_quotient f) :=
⟨λ x y, quotient.induction_on₂' x y $ λ r s hrs, quotient.eq.2 $
  (submodule.mem_infi _).2 $ λ i, quotient.eq.1 $
  show quotient_inf_to_pi_quotient f (quotient.mk' r) i = _, by rw hrs; refl,
λ g, let ⟨r, hr⟩ := exists_sub_mem hf (λ i, quotient.out' (g i)) in
⟨quotient.mk _ r, funext $ λ i, quotient.out_eq' (g i) ▸ quotient.eq.2 (hr i)⟩⟩

/-- Chinese Remainder Theorem. Eisenbud Ex.2.6. Similar to Atiyah-Macdonald 1.10 and Stacks 00DT -/
noncomputable def quotient_inf_ring_equiv_pi_quotient [fintype ι] (f : ι → ideal R)
  (hf : ∀ i j, i ≠ j → f i ⊔ f j = ⊤) :
  (⨅ i, f i).quotient ≃+* Π i, (f i).quotient :=
{ .. equiv.of_bijective _ (quotient_inf_to_pi_quotient_bijective hf),
  .. quotient_inf_to_pi_quotient f }

end chinese_remainder

section mul_and_radical
variables {R : Type u} {ι : Type*} [comm_ring R]
variables {I J K L : ideal R}

instance : has_mul (ideal R) := ⟨(•)⟩

@[simp] lemma add_eq_sup : I + J = I ⊔ J := rfl
@[simp] lemma zero_eq_bot : (0 : ideal R) = ⊥ := rfl
@[simp] lemma one_eq_top : (1 : ideal R) = ⊤ :=
by erw [submodule.one_eq_map_top, submodule.map_id]

theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=
submodule.smul_mem_smul hr hs

theorem mul_mem_mul_rev {r s} (hr : r ∈ I) (hs : s ∈ J) : s * r ∈ I * J :=
mul_comm r s ▸ mul_mem_mul hr hs

theorem mul_le : I * J ≤ K ↔ ∀ (r ∈ I) (s ∈ J), r * s ∈ K :=
submodule.smul_le

lemma mul_le_left : I * J ≤ J :=
ideal.mul_le.2 (λ r hr s, J.mul_mem_left _)

lemma mul_le_right : I * J ≤ I :=
ideal.mul_le.2 (λ r hr s hs, I.mul_mem_right _ hr)

@[simp] lemma sup_mul_right_self : I ⊔ (I * J) = I :=
sup_eq_left.2 ideal.mul_le_right

@[simp] lemma sup_mul_left_self : I ⊔ (J * I) = I :=
sup_eq_left.2 ideal.mul_le_left

@[simp] lemma mul_right_self_sup : (I * J) ⊔ I = I :=
sup_eq_right.2 ideal.mul_le_right

@[simp] lemma mul_left_self_sup : (J * I) ⊔ I = I :=
sup_eq_right.2 ideal.mul_le_left

variables (I J K)
protected theorem mul_comm : I * J = J * I :=
le_antisymm (mul_le.2 $ λ r hrI s hsJ, mul_mem_mul_rev hsJ hrI)
  (mul_le.2 $ λ r hrJ s hsI, mul_mem_mul_rev hsI hrJ)

protected theorem mul_assoc : (I * J) * K = I * (J * K) :=
submodule.smul_assoc I J K

theorem span_mul_span (S T : set R) : span S * span T =
  span ⋃ (s ∈ S) (t ∈ T), {s * t} :=
submodule.span_smul_span S T
variables {I J K}

lemma span_mul_span' (S T : set R) : span S * span T = span (S*T) :=
by { unfold span, rw submodule.span_mul_span, }

lemma span_singleton_mul_span_singleton (r s : R) :
  span {r} * span {s} = (span {r * s} : ideal R) :=
by { unfold span, rw [submodule.span_mul_span, set.singleton_mul_singleton], }

lemma span_singleton_pow (s : R) (n : ℕ):
  span {s} ^ n = (span {s ^ n} : ideal R) :=
begin
  induction n with n ih, { simp [set.singleton_one], },
  simp only [pow_succ, ih, span_singleton_mul_span_singleton],
end

theorem mul_le_inf : I * J ≤ I ⊓ J :=
mul_le.2 $ λ r hri s hsj, ⟨I.mul_mem_right s hri, J.mul_mem_left r hsj⟩

theorem prod_le_inf {s : finset ι} {f : ι → ideal R} : s.prod f ≤ s.inf f :=
begin
  classical, refine s.induction_on _ _,
  { rw [finset.prod_empty, finset.inf_empty], exact le_top },
  intros a s has ih,
  rw [finset.prod_insert has, finset.inf_insert],
  exact le_trans mul_le_inf (inf_le_inf (le_refl _) ih)
end

theorem mul_eq_inf_of_coprime (h : I ⊔ J = ⊤) : I * J = I ⊓ J :=
le_antisymm mul_le_inf $ λ r ⟨hri, hrj⟩,
let ⟨s, hsi, t, htj, hst⟩ := submodule.mem_sup.1 ((eq_top_iff_one _).1 h) in
mul_one r ▸ hst ▸ (mul_add r s t).symm ▸ ideal.add_mem (I * J) (mul_mem_mul_rev hsi hrj)
  (mul_mem_mul hri htj)

variables (I)
theorem mul_bot : I * ⊥ = ⊥ :=
submodule.smul_bot I

theorem bot_mul : ⊥ * I = ⊥ :=
submodule.bot_smul I

theorem mul_top : I * ⊤ = I :=
ideal.mul_comm ⊤ I ▸ submodule.top_smul I

theorem top_mul : ⊤ * I = I :=
submodule.top_smul I
variables {I}

theorem mul_mono (hik : I ≤ K) (hjl : J ≤ L) : I * J ≤ K * L :=
submodule.smul_mono hik hjl

theorem mul_mono_left (h : I ≤ J) : I * K ≤ J * K :=
submodule.smul_mono_left h

theorem mul_mono_right (h : J ≤ K) : I * J ≤ I * K :=
submodule.smul_mono_right h

variables (I J K)
theorem mul_sup : I * (J ⊔ K) = I * J ⊔ I * K :=
submodule.smul_sup I J K

theorem sup_mul : (I ⊔ J) * K = I * K ⊔ J * K :=
submodule.sup_smul I J K
variables {I J K}

lemma pow_le_pow {m n : ℕ} (h : m ≤ n) :
  I^n ≤ I^m :=
begin
  cases nat.exists_eq_add_of_le h with k hk,
  rw [hk, pow_add],
  exact le_trans (mul_le_inf) (inf_le_left)
end

lemma mul_eq_bot {R : Type*} [integral_domain R] {I J : ideal R} :
  I * J = ⊥ ↔ I = ⊥ ∨ J = ⊥ :=
⟨λ hij, or_iff_not_imp_left.mpr (λ I_ne_bot, J.eq_bot_iff.mpr (λ j hj,
  let ⟨i, hi, ne0⟩ := I.ne_bot_iff.mp I_ne_bot in
    or.resolve_left (mul_eq_zero.mp ((I * J).eq_bot_iff.mp hij _ (mul_mem_mul hi hj))) ne0)),
 λ h, by cases h; rw [← ideal.mul_bot, h, ideal.mul_comm]⟩

instance {R : Type*} [integral_domain R] : no_zero_divisors (ideal R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ I J, mul_eq_bot.1 }

/-- A product of ideals in an integral domain is zero if and only if one of the terms is zero. -/
lemma prod_eq_bot {R : Type*} [integral_domain R]
  {s : multiset (ideal R)} : s.prod = ⊥ ↔ ∃ I ∈ s, I = ⊥ :=
prod_zero_iff_exists_zero

/-- The radical of an ideal `I` consists of the elements `r` such that `r^n ∈ I` for some `n`. -/
def radical (I : ideal R) : ideal R :=
{ carrier := { r | ∃ n : ℕ, r ^ n ∈ I },
  zero_mem' := ⟨1, (pow_one (0:R)).symm ▸ I.zero_mem⟩,
  add_mem' := λ x y ⟨m, hxmi⟩ ⟨n, hyni⟩, ⟨m + n,
    (add_pow x y (m + n)).symm ▸ I.sum_mem $
    show ∀ c ∈ finset.range (nat.succ (m + n)),
      x ^ c * y ^ (m + n - c) * (nat.choose (m + n) c) ∈ I,
    from λ c hc, or.cases_on (le_total c m)
      (λ hcm, I.mul_mem_right _ $ I.mul_mem_left _ $ nat.add_comm n m ▸
        (nat.add_sub_assoc hcm n).symm ▸
        (pow_add y n (m-c)).symm ▸ I.mul_mem_right _ hyni)
      (λ hmc, I.mul_mem_right _ $ I.mul_mem_right _ $ nat.add_sub_cancel' hmc ▸
        (pow_add x m (c-m)).symm ▸ I.mul_mem_right _ hxmi)⟩,
  smul_mem' := λ r s ⟨n, hsni⟩, ⟨n, (mul_pow r s n).symm ▸ I.mul_mem_left (r^n) hsni⟩ }

theorem le_radical : I ≤ radical I :=
λ r hri, ⟨1, (pow_one r).symm ▸ hri⟩

variables (R)
theorem radical_top : (radical ⊤ : ideal R) = ⊤ :=
(eq_top_iff_one _).2 ⟨0, submodule.mem_top⟩
variables {R}

theorem radical_mono (H : I ≤ J) : radical I ≤ radical J :=
λ r ⟨n, hrni⟩, ⟨n, H hrni⟩

variables (I)
@[simp] theorem radical_idem : radical (radical I) = radical I :=
le_antisymm (λ r ⟨n, k, hrnki⟩, ⟨n * k, (pow_mul r n k).symm ▸ hrnki⟩) le_radical
variables {I}

theorem radical_le_radical_iff : radical I ≤ radical J ↔ I ≤ radical J :=
⟨λ h, le_trans le_radical h, λ h, radical_idem J ▸ radical_mono h⟩

theorem radical_eq_top : radical I = ⊤ ↔ I = ⊤ :=
⟨λ h, (eq_top_iff_one _).2 $ let ⟨n, hn⟩ := (eq_top_iff_one _).1 h in
  @one_pow R _ n ▸ hn, λ h, h.symm ▸ radical_top R⟩

theorem is_prime.radical (H : is_prime I) : radical I = I :=
le_antisymm (λ r ⟨n, hrni⟩, H.mem_of_pow_mem n hrni) le_radical

variables (I J)
theorem radical_sup : radical (I ⊔ J) = radical (radical I ⊔ radical J) :=
le_antisymm (radical_mono $ sup_le_sup le_radical le_radical) $
λ r ⟨n, hrnij⟩, let ⟨s, hs, t, ht, hst⟩ := submodule.mem_sup.1 hrnij in
@radical_idem _ _ (I ⊔ J) ▸ ⟨n, hst ▸ ideal.add_mem _
  (radical_mono le_sup_left hs) (radical_mono le_sup_right ht)⟩

theorem radical_inf : radical (I ⊓ J) = radical I ⊓ radical J :=
le_antisymm (le_inf (radical_mono inf_le_left) (radical_mono inf_le_right))
(λ r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩, ⟨m + n, (pow_add r m n).symm ▸ I.mul_mem_right _ hrm,
(pow_add r m n).symm ▸ J.mul_mem_left _ hrn⟩)

theorem radical_mul : radical (I * J) = radical I ⊓ radical J :=
le_antisymm (radical_inf I J ▸ radical_mono $ @mul_le_inf _ _ I J)
(λ r ⟨⟨m, hrm⟩, ⟨n, hrn⟩⟩, ⟨m + n, (pow_add r m n).symm ▸ mul_mem_mul hrm hrn⟩)
variables {I J}

theorem is_prime.radical_le_iff (hj : is_prime J) :
  radical I ≤ J ↔ I ≤ J :=
⟨le_trans le_radical, λ hij r ⟨n, hrni⟩, hj.mem_of_pow_mem n $ hij hrni⟩

theorem radical_eq_Inf (I : ideal R) :
  radical I = Inf { J : ideal R | I ≤ J ∧ is_prime J } :=
le_antisymm (le_Inf $ λ J hJ, hJ.2.radical_le_iff.2 hJ.1) $
λ r hr, classical.by_contradiction $ λ hri,
let ⟨m, (hrm : r ∉ radical m), him, hm⟩ := zorn.zorn_nonempty_partial_order₀
  {K : ideal R | r ∉ radical K}
  (λ c hc hcc y hyc, ⟨Sup c, λ ⟨n, hrnc⟩, let ⟨y, hyc, hrny⟩ :=
      (submodule.mem_Sup_of_directed ⟨y, hyc⟩ hcc.directed_on).1 hrnc in hc hyc ⟨n, hrny⟩,
    λ z, le_Sup⟩) I hri in
have ∀ x ∉ m, r ∈ radical (m ⊔ span {x}) := λ x hxm, classical.by_contradiction $ λ hrmx, hxm $
  hm (m ⊔ span {x}) hrmx le_sup_left ▸ (le_sup_right : _ ≤ m ⊔ span {x})
    (subset_span $ set.mem_singleton _),
have is_prime m, from ⟨by rintro rfl; rw radical_top at hrm; exact hrm trivial,
  λ x y hxym, or_iff_not_imp_left.2 $ λ hxm, classical.by_contradiction $ λ hym,
  let ⟨n, hrn⟩ := this _ hxm,
      ⟨p, hpm, q, hq, hpqrn⟩ := submodule.mem_sup.1 hrn,
      ⟨c, hcxq⟩ := mem_span_singleton'.1 hq in
  let ⟨k, hrk⟩ := this _ hym,
      ⟨f, hfm, g, hg, hfgrk⟩ := submodule.mem_sup.1 hrk,
      ⟨d, hdyg⟩ := mem_span_singleton'.1 hg in
  hrm ⟨n + k, by rw [pow_add, ← hpqrn, ← hcxq, ← hfgrk, ← hdyg, add_mul, mul_add (c*x),
                     mul_assoc c x (d*y), mul_left_comm x, ← mul_assoc];
    refine m.add_mem (m.mul_mem_right _ hpm) (m.add_mem (m.mul_mem_left _ hfm)
      (m.mul_mem_left _ hxym))⟩⟩,
hrm $ this.radical.symm ▸ (Inf_le ⟨him, this⟩ : Inf {J : ideal R | I ≤ J ∧ is_prime J} ≤ m) hr

@[simp] lemma radical_bot_of_integral_domain {R : Type u} [integral_domain R] :
  radical (⊥ : ideal R) = ⊥ :=
eq_bot_iff.2 (λ x hx, hx.rec_on (λ n hn, pow_eq_zero hn))

instance : comm_semiring (ideal R) := submodule.comm_semiring

variables (R)
theorem top_pow (n : ℕ) : (⊤ ^ n : ideal R) = ⊤ :=
nat.rec_on n one_eq_top $ λ n ih, by rw [pow_succ, ih, top_mul]
variables {R}

variables (I)
theorem radical_pow (n : ℕ) (H : n > 0) : radical (I^n) = radical I :=
nat.rec_on n (not.elim dec_trivial) (λ n ih H,
or.cases_on (lt_or_eq_of_le $ nat.le_of_lt_succ H)
  (λ H, calc radical (I^(n+1))
           = radical I ⊓ radical (I^n) : by { rw pow_succ, exact radical_mul _ _ }
       ... = radical I ⊓ radical I : by rw ih H
       ... = radical I : inf_idem)
  (λ H, H ▸ (pow_one I).symm ▸ rfl)) H

theorem is_prime.mul_le {I J P : ideal R} (hp : is_prime P) :
  I * J ≤ P ↔ I ≤ P ∨ J ≤ P :=
⟨λ h, or_iff_not_imp_left.2 $ λ hip j hj, let ⟨i, hi, hip⟩ := set.not_subset.1 hip in
  (hp.mem_or_mem $ h $ mul_mem_mul hi hj).resolve_left hip,
λ h, or.cases_on h (le_trans $ le_trans mul_le_inf inf_le_left)
  (le_trans $ le_trans mul_le_inf inf_le_right)⟩

theorem is_prime.inf_le {I J P : ideal R} (hp : is_prime P) :
  I ⊓ J ≤ P ↔ I ≤ P ∨ J ≤ P :=
⟨λ h, hp.mul_le.1 $ le_trans mul_le_inf h,
λ h, or.cases_on h (le_trans inf_le_left) (le_trans inf_le_right)⟩

theorem is_prime.prod_le {s : finset ι} {f : ι → ideal R} {P : ideal R}
  (hp : is_prime P) (hne: s.nonempty) :
  s.prod f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
suffices s.prod f ≤ P → ∃ i ∈ s, f i ≤ P,
  from ⟨this, λ ⟨i, his, hip⟩, le_trans prod_le_inf $ le_trans (finset.inf_le his) hip⟩,
begin
  classical,
  obtain ⟨b, hb⟩ : ∃ b, b ∈ s := hne.bex,
  obtain ⟨t, hbt, rfl⟩ : ∃ t, b ∉ t ∧ s = insert b t,
  from ⟨s.erase b, s.not_mem_erase b, (finset.insert_erase hb).symm⟩,
  revert hbt,
  refine t.induction_on _ _,
  { simp only [finset.not_mem_empty, insert_emptyc_eq, exists_prop, finset.prod_singleton,
      imp_self, exists_eq_left, not_false_iff, finset.mem_singleton] },
  intros a s has ih hbs h,
  have : a ∉ insert b s,
  { contrapose! has,
    apply finset.mem_of_mem_insert_of_ne has,
    rintro rfl,
    contradiction },
  rw [finset.insert.comm, finset.prod_insert this, hp.mul_le] at h,
  rw finset.insert.comm,
  cases h,
  { exact ⟨a, finset.mem_insert_self a _, h⟩ },
  obtain ⟨i, hi, ih⟩ : ∃ i ∈ insert b s, f i ≤ P := ih (mt finset.mem_insert_of_mem hbs) h,
  exact ⟨i, finset.mem_insert_of_mem hi, ih⟩
end

theorem is_prime.inf_le' {s : finset ι} {f : ι → ideal R} {P : ideal R} (hp : is_prime P)
  (hsne: s.nonempty) :
  s.inf f ≤ P ↔ ∃ i ∈ s, f i ≤ P :=
⟨λ h, (hp.prod_le hsne).1 $ le_trans prod_le_inf h,
  λ ⟨i, his, hip⟩, le_trans (finset.inf_le his) hip⟩

theorem subset_union {I J K : ideal R} : (I : set R) ⊆ J ∪ K ↔ I ≤ J ∨ I ≤ K :=
⟨λ h, or_iff_not_imp_left.2 $ λ hij s hsi,
  let ⟨r, hri, hrj⟩ := set.not_subset.1 hij in classical.by_contradiction $ λ hsk,
  or.cases_on (h $ I.add_mem hri hsi)
    (λ hj, hrj $ add_sub_cancel r s ▸ J.sub_mem hj ((h hsi).resolve_right hsk))
    (λ hk, hsk $ add_sub_cancel' r s ▸ K.sub_mem hk ((h hri).resolve_left hrj)),
λ h, or.cases_on h (λ h, set.subset.trans h $ set.subset_union_left J K)
  (λ h, set.subset.trans h $ set.subset_union_right J K)⟩

theorem subset_union_prime' {s : finset ι} {f : ι → ideal R} {a b : ι}
  (hp : ∀ i ∈ s, is_prime (f i)) {I : ideal R} :
  (I : set R) ⊆ f a ∪ f b ∪ (⋃ i ∈ (↑s : set ι), f i) ↔ I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i :=
suffices (I : set R) ⊆ f a ∪ f b ∪ (⋃ i ∈ (↑s : set ι), f i) →
  I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i,
  from ⟨this, λ h, or.cases_on h (λ h, set.subset.trans h $ set.subset.trans
      (set.subset_union_left _ _) (set.subset_union_left _ _)) $
    λ h, or.cases_on h (λ h, set.subset.trans h $ set.subset.trans
      (set.subset_union_right _ _) (set.subset_union_left _ _)) $
    λ ⟨i, his, hi⟩, by refine (set.subset.trans hi $ set.subset.trans _ $
        set.subset_union_right _ _);
      exact set.subset_bUnion_of_mem (finset.mem_coe.2 his)⟩,
begin
  generalize hn : s.card = n, intros h,
  unfreezingI { induction n with n ih generalizing a b s },
  { clear hp,
    rw finset.card_eq_zero at hn, subst hn,
    rw [finset.coe_empty, set.bUnion_empty, set.union_empty, subset_union] at h,
    simpa only [exists_prop, finset.not_mem_empty, false_and, exists_false, or_false] },
  classical,
  replace hn : ∃ (i : ι) (t : finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n :=
  finset.card_eq_succ.1 hn,
  unfreezingI { rcases hn with ⟨i, t, hit, rfl, hn⟩ },
  replace hp : is_prime (f i) ∧ ∀ x ∈ t, is_prime (f x) := (t.forall_mem_insert _ _).1 hp,
  by_cases Ht : ∃ j ∈ t, f j ≤ f i,
  { obtain ⟨j, hjt, hfji⟩ : ∃ j ∈ t, f j ≤ f i := Ht,
    obtain ⟨u, hju, rfl⟩ : ∃ u, j ∉ u ∧ insert j u = t,
    { exact ⟨t.erase j, t.not_mem_erase j, finset.insert_erase hjt⟩ },
    have hp' : ∀ k ∈ insert i u, is_prime (f k),
    { rw finset.forall_mem_insert at hp ⊢, exact ⟨hp.1, hp.2.2⟩ },
    have hiu : i ∉ u := mt finset.mem_insert_of_mem hit,
    have hn' : (insert i u).card = n,
    { rwa finset.card_insert_of_not_mem at hn ⊢, exacts [hiu, hju] },
    have h' : (I : set R) ⊆ f a ∪ f b ∪ (⋃ k ∈ (↑(insert i u) : set ι), f k),
    { rw finset.coe_insert at h ⊢, rw finset.coe_insert at h,
      simp only [set.bUnion_insert] at h ⊢,
      rw [← set.union_assoc ↑(f i)] at h,
      erw [set.union_eq_self_of_subset_right hfji] at h,
      exact h },
    specialize @ih a b (insert i u) hp' hn' h',
    refine ih.imp id (or.imp id (exists_imp_exists $ λ k, _)), simp only [exists_prop],
    exact and.imp (λ hk, finset.insert_subset_insert i (finset.subset_insert j u) hk) id },
  by_cases Ha : f a ≤ f i,
  { have h' : (I : set R) ⊆ f i ∪ f b ∪ (⋃ j ∈ (↑t : set ι), f j),
    { rw [finset.coe_insert, set.bUnion_insert, ← set.union_assoc,
          set.union_right_comm ↑(f a)] at h,
      erw [set.union_eq_self_of_subset_left Ha] at h,
      exact h },
    specialize @ih i b t hp.2 hn h', right,
    rcases ih with ih | ih | ⟨k, hkt, ih⟩,
    { exact or.inr ⟨i, finset.mem_insert_self i t, ih⟩ },
    { exact or.inl ih },
    { exact or.inr ⟨k, finset.mem_insert_of_mem hkt, ih⟩ } },
  by_cases Hb : f b ≤ f i,
  { have h' : (I : set R) ⊆ f a ∪ f i ∪ (⋃ j ∈ (↑t : set ι), f j),
    { rw [finset.coe_insert, set.bUnion_insert, ← set.union_assoc, set.union_assoc ↑(f a)] at h,
      erw [set.union_eq_self_of_subset_left Hb] at h,
      exact h },
    specialize @ih a i t hp.2 hn h',
    rcases ih with ih | ih | ⟨k, hkt, ih⟩,
    { exact or.inl ih },
    { exact or.inr (or.inr ⟨i, finset.mem_insert_self i t, ih⟩) },
    { exact or.inr (or.inr ⟨k, finset.mem_insert_of_mem hkt, ih⟩) } },
  by_cases Hi : I ≤ f i,
  { exact or.inr (or.inr ⟨i, finset.mem_insert_self i t, Hi⟩) },
  have : ¬I ⊓ f a ⊓ f b ⊓ t.inf f ≤ f i,
  { rcases t.eq_empty_or_nonempty with (rfl | hsne),
    { rw [finset.inf_empty, inf_top_eq, hp.1.inf_le, hp.1.inf_le, not_or_distrib, not_or_distrib],
      exact ⟨⟨Hi, Ha⟩, Hb⟩ },
    simp only [hp.1.inf_le, hp.1.inf_le' hsne, not_or_distrib],
    exact ⟨⟨⟨Hi, Ha⟩, Hb⟩, Ht⟩ },
  rcases set.not_subset.1 this with ⟨r, ⟨⟨⟨hrI, hra⟩, hrb⟩, hr⟩, hri⟩,
  by_cases HI : (I : set R) ⊆ f a ∪ f b ∪ ⋃ j ∈ (↑t : set ι), f j,
  { specialize ih hp.2 hn HI, rcases ih with ih | ih | ⟨k, hkt, ih⟩,
    { left, exact ih }, { right, left, exact ih },
    { right, right, exact ⟨k, finset.mem_insert_of_mem hkt, ih⟩ } },
  exfalso, rcases set.not_subset.1 HI with ⟨s, hsI, hs⟩,
  rw [finset.coe_insert, set.bUnion_insert] at h,
  have hsi : s ∈ f i := ((h hsI).resolve_left (mt or.inl hs)).resolve_right (mt or.inr hs),
  rcases h (I.add_mem hrI hsI) with ⟨ha | hb⟩ | hi | ht,
  { exact hs (or.inl $ or.inl $ add_sub_cancel' r s ▸ (f a).sub_mem ha hra) },
  { exact hs (or.inl $ or.inr $ add_sub_cancel' r s ▸ (f b).sub_mem hb hrb) },
  { exact hri (add_sub_cancel r s ▸ (f i).sub_mem hi hsi) },
  { rw set.mem_bUnion_iff at ht, rcases ht with ⟨j, hjt, hj⟩,
    simp only [finset.inf_eq_infi, set_like.mem_coe, submodule.mem_infi] at hr,
    exact hs (or.inr $ set.mem_bUnion hjt $ add_sub_cancel' r s ▸ (f j).sub_mem hj $ hr j hjt) }
end

/-- Prime avoidance. Atiyah-Macdonald 1.11, Eisenbud 3.3, Stacks 00DS, Matsumura Ex.1.6. -/
theorem subset_union_prime {s : finset ι} {f : ι → ideal R} (a b : ι)
  (hp : ∀ i ∈ s, i ≠ a → i ≠ b → is_prime (f i)) {I : ideal R} :
  (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i) ↔ ∃ i ∈ s, I ≤ f i :=
suffices (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i) → ∃ i, i ∈ s ∧ I ≤ f i,
  from ⟨λ h, bex_def.2 $ this h, λ ⟨i, his, hi⟩, set.subset.trans hi $ set.subset_bUnion_of_mem $
    show i ∈ (↑s : set ι), from his⟩,
assume h : (I : set R) ⊆ (⋃ i ∈ (↑s : set ι), f i),
begin
  classical, tactic.unfreeze_local_instances,
  by_cases has : a ∈ s,
  { obtain ⟨t, hat, rfl⟩ : ∃ t, a ∉ t ∧ insert a t = s :=
      ⟨s.erase a, finset.not_mem_erase a s, finset.insert_erase has⟩,
    by_cases hbt : b ∈ t,
    { obtain ⟨u, hbu, rfl⟩ : ∃ u, b ∉ u ∧ insert b u = t :=
        ⟨t.erase b, finset.not_mem_erase b t, finset.insert_erase hbt⟩,
      have hp' : ∀ i ∈ u, is_prime (f i),
      { intros i hiu, refine hp i (finset.mem_insert_of_mem (finset.mem_insert_of_mem hiu)) _ _;
        rintro rfl; solve_by_elim only [finset.mem_insert_of_mem, *], },
      rw [finset.coe_insert, finset.coe_insert, set.bUnion_insert, set.bUnion_insert,
          ← set.union_assoc, subset_union_prime' hp', bex_def] at h,
      rwa [finset.exists_mem_insert, finset.exists_mem_insert] },
    { have hp' : ∀ j ∈ t, is_prime (f j),
      { intros j hj, refine hp j (finset.mem_insert_of_mem hj) _ _;
        rintro rfl; solve_by_elim only [finset.mem_insert_of_mem, *], },
      rw [finset.coe_insert, set.bUnion_insert, ← set.union_self (f a : set R),
          subset_union_prime' hp', ← or_assoc, or_self, bex_def] at h,
      rwa finset.exists_mem_insert } },
  { by_cases hbs : b ∈ s,
    { obtain ⟨t, hbt, rfl⟩ : ∃ t, b ∉ t ∧ insert b t = s :=
        ⟨s.erase b, finset.not_mem_erase b s, finset.insert_erase hbs⟩,
      have hp' : ∀ j ∈ t, is_prime (f j),
      { intros j hj, refine hp j (finset.mem_insert_of_mem hj) _ _;
        rintro rfl; solve_by_elim only [finset.mem_insert_of_mem, *], },
      rw [finset.coe_insert, set.bUnion_insert, ← set.union_self (f b : set R),
          subset_union_prime' hp', ← or_assoc, or_self, bex_def] at h,
      rwa finset.exists_mem_insert },
    cases s.eq_empty_or_nonempty with hse hsne,
    { subst hse, rw [finset.coe_empty, set.bUnion_empty, set.subset_empty_iff] at h,
      have : (I : set R) ≠ ∅ := set.nonempty.ne_empty (set.nonempty_of_mem I.zero_mem),
      exact absurd h this },
    { cases hsne.bex with i his,
      obtain ⟨t, hit, rfl⟩ : ∃ t, i ∉ t ∧ insert i t = s :=
        ⟨s.erase i, finset.not_mem_erase i s, finset.insert_erase his⟩,
      have hp' : ∀ j ∈ t, is_prime (f j),
      { intros j hj, refine hp j (finset.mem_insert_of_mem hj) _ _;
        rintro rfl; solve_by_elim only [finset.mem_insert_of_mem, *], },
      rw [finset.coe_insert, set.bUnion_insert, ← set.union_self (f i : set R),
          subset_union_prime' hp', ← or_assoc, or_self, bex_def] at h,
      rwa finset.exists_mem_insert } }
end

end mul_and_radical

section map_and_comap
variables {R : Type u} {S : Type v} [ring R] [ring S]
variables (f : R →+* S)
variables {I J : ideal R} {K L : ideal S}

/-- `I.map f` is the span of the image of the ideal `I` under `f`, which may be bigger than
  the image itself. -/
def map (I : ideal R) : ideal S :=
span (f '' I)

/-- `I.comap f` is the preimage of `I` under `f`. -/
def comap (I : ideal S) : ideal R :=
{ carrier := f ⁻¹' I,
  smul_mem' := λ c x hx, show f (c * x) ∈ I, by { rw f.map_mul, exact I.mul_mem_left _ hx },
  .. I.to_add_submonoid.comap (f : R →+ S) }

variables {f}
theorem map_mono (h : I ≤ J) : map f I ≤ map f J :=
span_mono $ set.image_subset _ h

theorem mem_map_of_mem (f : R →+* S) {I : ideal R} {x : R} (h : x ∈ I) : f x ∈ map f I :=
subset_span ⟨x, h, rfl⟩

lemma apply_coe_mem_map (f : R →+* S) (I : ideal R) (x : I) : f x ∈ I.map f :=
mem_map_of_mem f x.prop

theorem map_le_iff_le_comap :
  map f I ≤ K ↔ I ≤ comap f K :=
span_le.trans set.image_subset_iff

@[simp] theorem mem_comap {x} : x ∈ comap f K ↔ f x ∈ K := iff.rfl

theorem comap_mono (h : K ≤ L) : comap f K ≤ comap f L :=
set.preimage_mono (λ x hx, h hx)
variables (f)

theorem comap_ne_top (hK : K ≠ ⊤) : comap f K ≠ ⊤ :=
(ne_top_iff_one _).2 $ by rw [mem_comap, f.map_one];
  exact (ne_top_iff_one _).1 hK

instance is_prime.comap [hK : K.is_prime] : (comap f K).is_prime :=
⟨comap_ne_top _ hK.1, λ x y,
  by simp only [mem_comap, f.map_mul]; apply hK.2⟩

variables (I J K L)

theorem map_top : map f ⊤ = ⊤ :=
(eq_top_iff_one _).2 $ subset_span ⟨1, trivial, f.map_one⟩

variable (f)
lemma gc_map_comap : galois_connection (ideal.map f) (ideal.comap f) :=
λ I J, ideal.map_le_iff_le_comap

@[simp] lemma comap_id : I.comap (ring_hom.id R) = I :=
ideal.ext $ λ _, iff.rfl

@[simp] lemma map_id : I.map (ring_hom.id R) = I :=
(gc_map_comap (ring_hom.id R)).l_unique galois_connection.id comap_id

lemma comap_comap {T : Type*} [ring T] {I : ideal T} (f : R →+* S)
  (g : S →+*T) : (I.comap g).comap f = I.comap (g.comp f) := rfl

lemma map_map {T : Type*} [ring T] {I : ideal R} (f : R →+* S)
  (g : S →+*T) : (I.map f).map g = I.map (g.comp f) :=
((gc_map_comap f).compose _ _ _ _ (gc_map_comap g)).l_unique
  (gc_map_comap (g.comp f)) (λ _, comap_comap _ _)

variables {f I J K L}

lemma map_le_of_le_comap : I ≤ K.comap f → I.map f ≤ K :=
(gc_map_comap f).l_le

lemma le_comap_of_map_le : I.map f ≤ K → I ≤ K.comap f :=
(gc_map_comap f).le_u

lemma le_comap_map : I ≤ (I.map f).comap f :=
(gc_map_comap f).le_u_l _

lemma map_comap_le : (K.comap f).map f ≤ K :=
(gc_map_comap f).l_u_le _

@[simp] lemma comap_top : (⊤ : ideal S).comap f = ⊤ :=
(gc_map_comap f).u_top

@[simp] lemma comap_eq_top_iff {I : ideal S} : I.comap f = ⊤ ↔ I = ⊤ :=
⟨ λ h, I.eq_top_iff_one.mpr (f.map_one ▸ mem_comap.mp ((I.comap f).eq_top_iff_one.mp h)),
  λ h, by rw [h, comap_top] ⟩

@[simp] lemma map_bot : (⊥ : ideal R).map f = ⊥ :=
(gc_map_comap f).l_bot

variables (f I J K L)

@[simp] lemma map_comap_map : ((I.map f).comap f).map f = I.map f :=
congr_fun (gc_map_comap f).l_u_l_eq_l I

@[simp] lemma comap_map_comap : ((K.comap f).map f).comap f = K.comap f :=
congr_fun (gc_map_comap f).u_l_u_eq_u K

lemma map_sup : (I ⊔ J).map f = I.map f ⊔ J.map f :=
(gc_map_comap f).l_sup

theorem comap_inf : comap f (K ⊓ L) = comap f K ⊓ comap f L := rfl

variables {ι : Sort*}

lemma map_supr (K : ι → ideal R) : (supr K).map f = ⨆ i, (K i).map f :=
(gc_map_comap f).l_supr

lemma comap_infi (K : ι → ideal S) : (infi K).comap f = ⨅ i, (K i).comap f :=
(gc_map_comap f).u_infi

lemma map_Sup (s : set (ideal R)): (Sup s).map f = ⨆ I ∈ s, (I : ideal R).map f :=
(gc_map_comap f).l_Sup

lemma comap_Inf (s : set (ideal S)): (Inf s).comap f = ⨅ I ∈ s, (I : ideal S).comap f :=
(gc_map_comap f).u_Inf

lemma comap_Inf' (s : set (ideal S)) : (Inf s).comap f = ⨅ I ∈ (comap f '' s), I :=
trans (comap_Inf f s) (by rw infi_image)

theorem comap_is_prime [H : is_prime K] : is_prime (comap f K) :=
⟨comap_ne_top f H.ne_top,
  λ x y h, H.mem_or_mem $ by rwa [mem_comap, ring_hom.map_mul] at h⟩

variables {I J K L}

theorem map_inf_le : map f (I ⊓ J) ≤ map f I ⊓ map f J :=
(gc_map_comap f).monotone_l.map_inf_le _ _

theorem le_comap_sup : comap f K ⊔ comap f L ≤ comap f (K ⊔ L) :=
(gc_map_comap f).monotone_u.le_map_sup _ _


section surjective
variables (hf : function.surjective f)
include hf

open function

theorem map_comap_of_surjective (I : ideal S) :
  map f (comap f I) = I :=
le_antisymm (map_le_iff_le_comap.2 (le_refl _))
(λ s hsi, let ⟨r, hfrs⟩ := hf s in
  hfrs ▸ (mem_map_of_mem f $ show f r ∈ I, from hfrs.symm ▸ hsi))

/-- `map` and `comap` are adjoint, and the composition `map f ∘ comap f` is the
  identity -/
def gi_map_comap : galois_insertion (map f) (comap f) :=
galois_insertion.monotone_intro
  ((gc_map_comap f).monotone_u)
  ((gc_map_comap f).monotone_l)
  (λ _, le_comap_map)
  (map_comap_of_surjective _ hf)

lemma map_surjective_of_surjective : surjective (map f) :=
(gi_map_comap f hf).l_surjective

lemma comap_injective_of_surjective : injective (comap f) :=
(gi_map_comap f hf).u_injective

lemma map_sup_comap_of_surjective (I J : ideal S) : (I.comap f ⊔ J.comap f).map f = I ⊔ J :=
(gi_map_comap f hf).l_sup_u _ _

lemma map_supr_comap_of_surjective (K : ι → ideal S) : (⨆i, (K i).comap f).map f = supr K :=
(gi_map_comap f hf).l_supr_u _

lemma map_inf_comap_of_surjective (I J : ideal S) : (I.comap f ⊓ J.comap f).map f = I ⊓ J :=
(gi_map_comap f hf).l_inf_u _ _

lemma map_infi_comap_of_surjective (K : ι → ideal S) : (⨅i, (K i).comap f).map f = infi K :=
(gi_map_comap f hf).l_infi_u _

theorem mem_image_of_mem_map_of_surjective {I : ideal R} {y}
  (H : y ∈ map f I) : y ∈ f '' I :=
submodule.span_induction H (λ _, id) ⟨0, I.zero_mem, f.map_zero⟩
(λ y1 y2 ⟨x1, hx1i, hxy1⟩ ⟨x2, hx2i, hxy2⟩,
  ⟨x1 + x2, I.add_mem hx1i hx2i, hxy1 ▸ hxy2 ▸ f.map_add _ _⟩)
(λ c y ⟨x, hxi, hxy⟩, let ⟨d, hdc⟩ := hf c in ⟨d • x, I.smul_mem _ hxi, hdc ▸ hxy ▸ f.map_mul _ _⟩)

lemma mem_map_iff_of_surjective {I : ideal R} {y} :
  y ∈ map f I ↔ ∃ x, x ∈ I ∧ f x = y :=
⟨λ h, (set.mem_image _ _ _).2 (mem_image_of_mem_map_of_surjective f hf h),
  λ ⟨x, hx⟩, hx.right ▸ (mem_map_of_mem f hx.left)⟩

theorem comap_map_of_surjective (I : ideal R) :
  comap f (map f I) = I ⊔ comap f ⊥ :=
le_antisymm (assume r h, let ⟨s, hsi, hfsr⟩ := mem_image_of_mem_map_of_surjective f hf h in
  submodule.mem_sup.2 ⟨s, hsi, r - s, (submodule.mem_bot S).2 $ by rw [f.map_sub, hfsr, sub_self],
  add_sub_cancel'_right s r⟩)
(sup_le (map_le_iff_le_comap.1 (le_refl _)) (comap_mono bot_le))

lemma le_map_of_comap_le_of_surjective : comap f K ≤ I → K ≤ map f I :=
λ h, (map_comap_of_surjective f hf K) ▸ map_mono h

/-- Correspondence theorem -/
def rel_iso_of_surjective :
  ideal S ≃o { p : ideal R // comap f ⊥ ≤ p } :=
{ to_fun := λ J, ⟨comap f J, comap_mono bot_le⟩,
  inv_fun := λ I, map f I.1,
  left_inv := λ J, map_comap_of_surjective f hf J,
  right_inv := λ I, subtype.eq $ show comap f (map f I.1) = I.1,
    from (comap_map_of_surjective f hf I).symm ▸ le_antisymm
      (sup_le (le_refl _) I.2) le_sup_left,
  map_rel_iff' := λ I1 I2, ⟨λ H, map_comap_of_surjective f hf I1 ▸
    map_comap_of_surjective f hf I2 ▸ map_mono H, comap_mono⟩ }

/-- The map on ideals induced by a surjective map preserves inclusion. -/
def order_embedding_of_surjective : ideal S ↪o ideal R :=
(rel_iso_of_surjective f hf).to_rel_embedding.trans (subtype.rel_embedding _ _)

theorem map_eq_top_or_is_maximal_of_surjective (H : is_maximal I) :
  (map f I) = ⊤ ∨ is_maximal (map f I) :=
begin
  refine or_iff_not_imp_left.2 (λ ne_top, ⟨⟨λ h, ne_top h, λ J hJ, _⟩⟩),
  { refine (rel_iso_of_surjective f hf).injective
      (subtype.ext_iff.2 (eq.trans (H.1.2 (comap f J) (lt_of_le_of_ne _ _)) comap_top.symm)),
    { exact (map_le_iff_le_comap).1 (le_of_lt hJ) },
    { exact λ h, hJ.right (le_map_of_comap_le_of_surjective f hf (le_of_eq h.symm)) } }
end

theorem comap_is_maximal_of_surjective [H : is_maximal K] : is_maximal (comap f K) :=
begin
  refine ⟨⟨comap_ne_top _ H.1.1, λ J hJ, _⟩⟩,
  suffices : map f J = ⊤,
  { replace this := congr_arg (comap f) this,
    rw [comap_top, comap_map_of_surjective _ hf, eq_top_iff] at this,
    rw eq_top_iff,
    exact le_trans this (sup_le (le_of_eq rfl) (le_trans (comap_mono (bot_le)) (le_of_lt hJ))) },
  refine H.1.2 (map f J) (lt_of_le_of_ne (le_map_of_comap_le_of_surjective _ hf (le_of_lt hJ))
    (λ h, ne_of_lt hJ (trans (congr_arg (comap f) h) _))),
  rw [comap_map_of_surjective _ hf, sup_eq_left],
  exact le_trans (comap_mono bot_le) (le_of_lt hJ)
end

end surjective

/-- If `f : R ≃+* S` is a ring isomorphism and `I : ideal R`, then `map f (map f.symm) = I`. -/
@[simp]
lemma map_of_equiv (I : ideal R) (f : R ≃+* S) : (I.map (f : R →+* S)).map (f.symm : S →+* R) = I :=
by simp [← ring_equiv.to_ring_hom_eq_coe, map_map]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : ideal R`, then `comap f.symm (comap f) = I`. -/
@[simp]
lemma comap_of_equiv (I : ideal R) (f : R ≃+* S) :
  (I.comap (f.symm : S →+* R)).comap (f : R →+* S) = I :=
by simp [← ring_equiv.to_ring_hom_eq_coe, comap_comap]

/-- If `f : R ≃+* S` is a ring isomorphism and `I : ideal R`, then `map f I = comap f.symm I`. -/
lemma map_comap_of_equiv (I : ideal R) (f : R ≃+* S) : I.map (f : R →+* S) = I.comap f.symm :=
le_antisymm (le_comap_of_map_le (map_of_equiv I f).le)
  (le_map_of_comap_le_of_surjective _ f.surjective (comap_of_equiv I f).le)

section injective
variables (hf : function.injective f)
include hf

open function

lemma comap_bot_le_of_injective : comap f ⊥ ≤ I :=
begin
  refine le_trans (λ x hx, _) bot_le,
  rw [mem_comap, submodule.mem_bot, ← ring_hom.map_zero f] at hx,
  exact eq.symm (hf hx) ▸ (submodule.zero_mem ⊥)
end

end injective

section bijective
variables (hf : function.bijective f)
include hf

open function

/-- Special case of the correspondence theorem for isomorphic rings -/
def rel_iso_of_bijective : ideal S ≃o ideal R :=
{ to_fun := comap f,
  inv_fun := map f,
  left_inv := (rel_iso_of_surjective f hf.right).left_inv,
  right_inv := λ J, subtype.ext_iff.1
    ((rel_iso_of_surjective f hf.right).right_inv ⟨J, comap_bot_le_of_injective f hf.left⟩),
  map_rel_iff' := (rel_iso_of_surjective f hf.right).map_rel_iff' }

lemma comap_le_iff_le_map : comap f K ≤ I ↔ K ≤ map f I :=
⟨λ h, le_map_of_comap_le_of_surjective f hf.right h,
 λ h, ((rel_iso_of_bijective f hf).right_inv I) ▸ comap_mono h⟩

theorem map.is_maximal (H : is_maximal I) : is_maximal (map f I) :=
by refine or_iff_not_imp_left.1
  (map_eq_top_or_is_maximal_of_surjective f hf.right H) (λ h, H.1.1 _);
calc I = comap f (map f I) : ((rel_iso_of_bijective f hf).right_inv I).symm
   ... = comap f ⊤ : by rw h
   ... = ⊤ : by rw comap_top

end bijective

lemma ring_equiv.bot_maximal_iff (e : R ≃+* S) :
  (⊥ : ideal R).is_maximal ↔ (⊥ : ideal S).is_maximal :=
⟨λ h, (@map_bot _ _ _ _ e.to_ring_hom) ▸ map.is_maximal e.to_ring_hom e.bijective h,
  λ h, (@map_bot _ _ _ _ e.symm.to_ring_hom) ▸ map.is_maximal e.symm.to_ring_hom e.symm.bijective h⟩

end map_and_comap

section map_and_comap

variables {R : Type u} {S : Type v} [comm_ring R] [comm_ring S]
variables (f : R →+* S)
variables {I J : ideal R} {K L : ideal S}

lemma mem_quotient_iff_mem (hIJ : I ≤ J) {x : R} :
  quotient.mk I x ∈ J.map (quotient.mk I) ↔ x ∈ J :=
begin
  refine iff.trans (mem_map_iff_of_surjective _ quotient.mk_surjective) _,
  split,
  { rintros ⟨x, x_mem, x_eq⟩,
    simpa using J.add_mem (hIJ (quotient.eq.mp x_eq.symm)) x_mem },
  { intro x_mem,
    exact ⟨x, x_mem, rfl⟩ }
end

variables (I J K L)

theorem map_mul : map f (I * J) = map f I * map f J :=
le_antisymm (map_le_iff_le_comap.2 $ mul_le.2 $ λ r hri s hsj,
  show f (r * s) ∈ _, by rw f.map_mul;
  exact mul_mem_mul (mem_map_of_mem f hri) (mem_map_of_mem f hsj))
(trans_rel_right _ (span_mul_span _ _) $ span_le.2 $
  set.bUnion_subset $ λ i ⟨r, hri, hfri⟩,
  set.bUnion_subset $ λ j ⟨s, hsj, hfsj⟩,
  set.singleton_subset_iff.2 $ hfri ▸ hfsj ▸
  by rw [← f.map_mul];
  exact mem_map_of_mem f (mul_mem_mul hri hsj))

theorem comap_radical : comap f (radical K) = radical (comap f K) :=
le_antisymm (λ r ⟨n, hfrnk⟩, ⟨n, show f (r ^ n) ∈ K,
  from (f.map_pow r n).symm ▸ hfrnk⟩)
(λ r ⟨n, hfrnk⟩, ⟨n, f.map_pow r n ▸ hfrnk⟩)

@[simp] lemma map_quotient_self :
  map (quotient.mk I) I = ⊥ :=
eq_bot_iff.2 $ ideal.map_le_iff_le_comap.2 $ λ x hx,
(submodule.mem_bot I.quotient).2 $ ideal.quotient.eq_zero_iff_mem.2 hx

variables {I J K L}

theorem map_radical_le : map f (radical I) ≤ radical (map f I) :=
map_le_iff_le_comap.2 $ λ r ⟨n, hrni⟩, ⟨n, f.map_pow r n ▸ mem_map_of_mem f hrni⟩

theorem le_comap_mul : comap f K * comap f L ≤ comap f (K * L) :=
map_le_iff_le_comap.1 $ (map_mul f (comap f K) (comap f L)).symm ▸
mul_mono (map_le_iff_le_comap.2 $ le_refl _) (map_le_iff_le_comap.2 $ le_refl _)

end map_and_comap

section is_primary
variables {R : Type u} [comm_ring R]

/-- A proper ideal `I` is primary iff `xy ∈ I` implies `x ∈ I` or `y ∈ radical I`. -/
def is_primary (I : ideal R) : Prop :=
I ≠ ⊤ ∧ ∀ {x y : R}, x * y ∈ I → x ∈ I ∨ y ∈ radical I

theorem is_primary.to_is_prime (I : ideal R) (hi : is_prime I) : is_primary I :=
⟨hi.1, λ x y hxy, (hi.mem_or_mem hxy).imp id $ λ hyi, le_radical hyi⟩

theorem mem_radical_of_pow_mem {I : ideal R} {x : R} {m : ℕ} (hx : x ^ m ∈ radical I) :
  x ∈ radical I :=
radical_idem I ▸ ⟨m, hx⟩

theorem is_prime_radical {I : ideal R} (hi : is_primary I) : is_prime (radical I) :=
⟨mt radical_eq_top.1 hi.1, λ x y ⟨m, hxy⟩, begin
  rw mul_pow at hxy, cases hi.2 hxy,
  { exact or.inl ⟨m, h⟩ },
  { exact or.inr (mem_radical_of_pow_mem h) }
end⟩

theorem is_primary_inf {I J : ideal R} (hi : is_primary I) (hj : is_primary J)
  (hij : radical I = radical J) : is_primary (I ⊓ J) :=
⟨ne_of_lt $ lt_of_le_of_lt inf_le_left (lt_top_iff_ne_top.2 hi.1), λ x y ⟨hxyi, hxyj⟩,
begin
  rw [radical_inf, hij, inf_idem],
  cases hi.2 hxyi with hxi hyi, cases hj.2 hxyj with hxj hyj,
  { exact or.inl ⟨hxi, hxj⟩ },
  { exact or.inr hyj },
  { rw hij at hyi, exact or.inr hyi }
end⟩

end is_primary

end ideal

namespace ring_hom

variables {R : Type u} {S : Type v}

section ring
variables [ring R] [ring S] (f : R →+* S)

/-- Kernel of a ring homomorphism as an ideal of the domain. -/
def ker : ideal R := ideal.comap f ⊥

/-- An element is in the kernel if and only if it maps to zero.-/
lemma mem_ker {r} : r ∈ ker f ↔ f r = 0 :=
by rw [ker, ideal.mem_comap, submodule.mem_bot]

lemma ker_eq : ((ker f) : set R) = is_add_group_hom.ker f := rfl

lemma ker_eq_comap_bot (f : R →+* S) : f.ker = ideal.comap f ⊥ := rfl

lemma injective_iff_ker_eq_bot : function.injective f ↔ ker f = ⊥ :=
by rw [set_like.ext'_iff, ker_eq]; exact is_add_group_hom.injective_iff_trivial_ker f

lemma ker_eq_bot_iff_eq_zero : ker f = ⊥ ↔ ∀ x, f x = 0 → x = 0 :=
by rw [set_like.ext'_iff, ker_eq]; exact is_add_group_hom.trivial_ker_iff_eq_zero f

/-- If the target is not the zero ring, then one is not in the kernel.-/
lemma not_one_mem_ker [nontrivial S] (f : R →+* S) : (1:R) ∉ ker f :=
by { rw [mem_ker, f.map_one], exact one_ne_zero }

@[simp] lemma ker_coe_equiv (f : R ≃+* S) : ker (f : R →+* S) = ⊥ :=
by simpa only [←injective_iff_ker_eq_bot] using f.injective

end ring

section comm_ring
variables [comm_ring R] [comm_ring S] (f : R →+* S)

/-- The induced map from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_equiv_of_right_inverse`) /
is surjective (`quotient_ker_equiv_of_surjective`).
-/
def ker_lift (f : R →+* S) : f.ker.quotient →+* S :=
ideal.quotient.lift _ f $ λ r, f.mem_ker.mp

@[simp]
lemma ker_lift_mk (f : R →+* S) (r : R) : ker_lift f (ideal.quotient.mk f.ker r) = f r :=
ideal.quotient.lift_mk _ _ _

/-- The induced map from the quotient by the kernel is injective. -/
lemma ker_lift_injective (f : R →+* S) : function.injective (ker_lift f) :=
assume a b, quotient.induction_on₂' a b $
  assume a b (h : f a = f b), quotient.sound' $
show a - b ∈ ker f, by rw [mem_ker, map_sub, h, sub_self]

variable {f}

/-- The first isomorphism theorem for commutative rings, computable version. -/
def quotient_ker_equiv_of_right_inverse
  {g : S → R} (hf : function.right_inverse g f) :
  f.ker.quotient ≃+* S :=
{ to_fun := ker_lift f,
  inv_fun := (ideal.quotient.mk f.ker) ∘ g,
  left_inv := begin
    rintro ⟨x⟩,
    apply ker_lift_injective,
    simp [hf (f x)],
  end,
  right_inv := hf,
  ..ker_lift f}

@[simp]
lemma quotient_ker_equiv_of_right_inverse.apply {g : S → R} (hf : function.right_inverse g f)
  (x : f.ker.quotient) : quotient_ker_equiv_of_right_inverse hf x = ker_lift f x := rfl

@[simp]
lemma quotient_ker_equiv_of_right_inverse.symm.apply {g : S → R} (hf : function.right_inverse g f)
  (x : S) : (quotient_ker_equiv_of_right_inverse hf).symm x = ideal.quotient.mk f.ker (g x) := rfl

/-- The first isomorphism theorem for commutative rings. -/
noncomputable def quotient_ker_equiv_of_surjective (hf : function.surjective f) :
  f.ker.quotient ≃+* S :=
quotient_ker_equiv_of_right_inverse (classical.some_spec hf.has_right_inverse)

end comm_ring

/-- The kernel of a homomorphism to an integral domain is a prime ideal.-/
lemma ker_is_prime [ring R] [integral_domain S] (f : R →+* S) :
  (ker f).is_prime :=
⟨by { rw [ne.def, ideal.eq_top_iff_one], exact not_one_mem_ker f },
λ x y, by simpa only [mem_ker, f.map_mul] using @eq_zero_or_eq_zero_of_mul_eq_zero S _ _ _ _ _⟩

end ring_hom

namespace ideal

variables {R : Type*} {S : Type*}

section ring
variables [ring R] [ring S]

lemma map_eq_bot_iff_le_ker {I : ideal R} (f : R →+* S) : I.map f = ⊥ ↔ I ≤ f.ker :=
by rw [ring_hom.ker, eq_bot_iff, map_le_iff_le_comap]

lemma ker_le_comap {K : ideal S} (f : R →+* S) : f.ker ≤ comap f K :=
λ x hx, mem_comap.2 (((ring_hom.mem_ker f).1 hx).symm ▸ K.zero_mem)

lemma map_Inf {A : set (ideal R)} {f : R →+* S} (hf : function.surjective f) :
  (∀ J ∈ A, ring_hom.ker f ≤ J) → map f (Inf A) = Inf (map f '' A) :=
begin
  refine λ h, le_antisymm (le_Inf _) _,
  { intros j hj y hy,
    cases (mem_map_iff_of_surjective f hf).1 hy with x hx,
    cases (set.mem_image _ _ _).mp hj with J hJ,
    rw [← hJ.right, ← hx.right],
    exact mem_map_of_mem f (Inf_le_of_le hJ.left (le_of_eq rfl) hx.left) },
  { intros y hy,
    cases hf y with x hx,
    refine hx ▸ (mem_map_of_mem f _),
    have : ∀ I ∈ A, y ∈ map f I, by simpa using hy,
    rw [submodule.mem_Inf],
    intros J hJ,
    rcases (mem_map_iff_of_surjective f hf).1 (this J hJ) with ⟨x', hx', rfl⟩,
    have : x - x' ∈ J,
    { apply h J hJ,
      rw [ring_hom.mem_ker, ring_hom.map_sub, hx, sub_self] },
    simpa only [sub_add_cancel] using J.add_mem this hx' }
end

theorem map_is_prime_of_surjective {f : R →+* S} (hf : function.surjective f) {I : ideal R}
  [H : is_prime I] (hk : ring_hom.ker f ≤ I) : is_prime (map f I) :=
begin
  refine ⟨λ h, H.ne_top (eq_top_iff.2 _), λ x y, _⟩,
  { replace h := congr_arg (comap f) h,
    rw [comap_map_of_surjective _ hf, comap_top] at h,
    exact h ▸ sup_le (le_of_eq rfl) hk },
  { refine λ hxy, (hf x).rec_on (λ a ha, (hf y).rec_on (λ b hb, _)),
    rw [← ha, ← hb, ← ring_hom.map_mul, mem_map_iff_of_surjective _ hf] at hxy,
    rcases hxy with ⟨c, hc, hc'⟩,
    rw [← sub_eq_zero, ← ring_hom.map_sub] at hc',
    have : a * b ∈ I,
    { convert I.sub_mem hc (hk (hc' : c - a * b ∈ f.ker)),
      abel },
    exact (H.mem_or_mem this).imp (λ h, ha ▸ mem_map_of_mem f h) (λ h, hb ▸ mem_map_of_mem f h) }
end

theorem map_is_prime_of_equiv (f : R ≃+* S) {I : ideal R} [is_prime I] :
  is_prime (map (f : R →+* S) I) :=
map_is_prime_of_surjective f.surjective $ by simp

end ring

section comm_ring
variables [comm_ring R] [comm_ring S]

@[simp] lemma mk_ker {I : ideal R} : (quotient.mk I).ker = I :=
by ext; rw [ring_hom.ker, mem_comap, submodule.mem_bot, quotient.eq_zero_iff_mem]

theorem map_radical_of_surjective {f : R →+* S} (hf : function.surjective f) {I : ideal R}
  (h : ring_hom.ker f ≤ I) : map f (I.radical) = (map f I).radical :=
begin
  rw [radical_eq_Inf, radical_eq_Inf],
  have : ∀ J ∈ {J : ideal R | I ≤ J ∧ J.is_prime}, f.ker ≤ J := λ J hJ, le_trans h hJ.left,
  convert map_Inf hf this,
  refine funext (λ j, propext ⟨_, _⟩),
  { rintros ⟨hj, hj'⟩,
    haveI : j.is_prime := hj',
    exact ⟨comap f j, ⟨⟨map_le_iff_le_comap.1 hj, comap_is_prime f j⟩,
      map_comap_of_surjective f hf j⟩⟩ },
  { rintro ⟨J, ⟨hJ, hJ'⟩⟩,
    haveI : J.is_prime := hJ.right,
    refine ⟨hJ' ▸ map_mono hJ.left, hJ' ▸ map_is_prime_of_surjective hf (le_trans h hJ.left)⟩ },
end

@[simp] lemma bot_quotient_is_maximal_iff (I : ideal R) :
  (⊥ : ideal I.quotient).is_maximal ↔ I.is_maximal :=
⟨λ hI, (@mk_ker _ _ I) ▸
  @comap_is_maximal_of_surjective _ _ _ _ (quotient.mk I) ⊥ quotient.mk_surjective hI,
 λ hI, @bot_is_maximal _ (@field.to_division_ring _ (@quotient.field _ _ I hI)) ⟩

section quotient_algebra

variables (R) {A : Type*} [comm_ring A] [algebra R A]

/-- The `R`-algebra structure on `A/I` for an `R`-algebra `A` -/
instance {I : ideal A} : algebra R (ideal.quotient I) :=
(ring_hom.comp (ideal.quotient.mk I) (algebra_map R A)).to_algebra

/-- The canonical morphism `A →ₐ[R] I.quotient` as morphism of `R`-algebras, for `I` an ideal of
`A`, where `A` is an `R`-algebra. -/
def quotient.mkₐ (I : ideal A) : A →ₐ[R] I.quotient :=
⟨λ a, submodule.quotient.mk a, rfl, λ _ _, rfl, rfl, λ _ _, rfl, λ _, rfl⟩

lemma quotient.alg_map_eq (I : ideal A) :
  algebra_map R I.quotient = (algebra_map A I.quotient).comp (algebra_map R A) :=
by simp only [ring_hom.algebra_map_to_algebra, ring_hom.comp_id]

instance [algebra S A] [algebra S R] [is_scalar_tower S R A]
  {I : ideal A} : is_scalar_tower S R (ideal.quotient I) :=
is_scalar_tower.of_algebra_map_eq' $ by
  rw [quotient.alg_map_eq R, quotient.alg_map_eq S, ring_hom.comp_assoc,
    is_scalar_tower.algebra_map_eq S R A]

lemma quotient.mkₐ_to_ring_hom (I : ideal A) :
  (quotient.mkₐ R I).to_ring_hom = ideal.quotient.mk I := rfl

@[simp] lemma quotient.mkₐ_eq_mk (I : ideal A) :
  ⇑(quotient.mkₐ R I) = ideal.quotient.mk I := rfl

/-- The canonical morphism `A →ₐ[R] I.quotient` is surjective. -/
lemma quotient.mkₐ_surjective (I : ideal A) : function.surjective (quotient.mkₐ R I) :=
surjective_quot_mk _

/-- The kernel of `A →ₐ[R] I.quotient` is `I`. -/
@[simp]
lemma quotient.mkₐ_ker (I : ideal A) : (quotient.mkₐ R I : A →+* I.quotient).ker = I :=
ideal.mk_ker

variables {R} {B : Type*} [comm_ring B] [algebra R B]

lemma ker_lift.map_smul (f : A →ₐ[R] B) (r : R) (x : f.to_ring_hom.ker.quotient) :
  f.to_ring_hom.ker_lift (r • x) = r • f.to_ring_hom.ker_lift x :=
begin
  obtain ⟨a, rfl⟩ := quotient.mkₐ_surjective R _ x,
  rw [← alg_hom.map_smul, quotient.mkₐ_eq_mk, ring_hom.ker_lift_mk],
  exact f.map_smul _ _
end

/-- The induced algebras morphism from the quotient by the kernel to the codomain.

This is an isomorphism if `f` has a right inverse (`quotient_ker_alg_equiv_of_right_inverse`) /
is surjective (`quotient_ker_alg_equiv_of_surjective`).
-/
def ker_lift_alg (f : A →ₐ[R] B) : f.to_ring_hom.ker.quotient →ₐ[R] B :=
alg_hom.mk' f.to_ring_hom.ker_lift (λ _ _, ker_lift.map_smul f _ _)

@[simp]
lemma ker_lift_alg_mk (f : A →ₐ[R] B) (a : A) :
  ker_lift_alg f (quotient.mk f.to_ring_hom.ker a) = f a := rfl

@[simp]
lemma ker_lift_alg_to_ring_hom (f : A →ₐ[R] B) :
  (ker_lift_alg f).to_ring_hom = ring_hom.ker_lift f := rfl

/-- The induced algebra morphism from the quotient by the kernel is injective. -/
lemma ker_lift_alg_injective (f : A →ₐ[R] B) : function.injective (ker_lift_alg f) :=
ring_hom.ker_lift_injective f

/-- The first isomorphism theorem for agebras, computable version. -/
def quotient_ker_alg_equiv_of_right_inverse
  {f : A →ₐ[R] B} {g : B → A} (hf : function.right_inverse g f) :
  f.to_ring_hom.ker.quotient ≃ₐ[R] B :=
{ ..ring_hom.quotient_ker_equiv_of_right_inverse (λ x, show f.to_ring_hom (g x) = x, from hf x),
  ..ker_lift_alg f}

@[simp]
lemma quotient_ker_alg_equiv_of_right_inverse.apply {f : A →ₐ[R] B} {g : B → A}
  (hf : function.right_inverse g f) (x : f.to_ring_hom.ker.quotient) :
  quotient_ker_alg_equiv_of_right_inverse hf x = ker_lift_alg f x := rfl

@[simp]
lemma quotient_ker_alg_equiv_of_right_inverse_symm.apply {f : A →ₐ[R] B} {g : B → A}
  (hf : function.right_inverse g f) (x : B) :
  (quotient_ker_alg_equiv_of_right_inverse hf).symm x = quotient.mkₐ R f.to_ring_hom.ker (g x) :=
  rfl

/-- The first isomorphism theorem for algebras. -/
noncomputable def quotient_ker_alg_equiv_of_surjective
  {f : A →ₐ[R] B} (hf : function.surjective f) : f.to_ring_hom.ker.quotient ≃ₐ[R] B :=
quotient_ker_alg_equiv_of_right_inverse (classical.some_spec hf.has_right_inverse)

/-- The ring hom `R/I →+* S/J` induced by a ring hom `f : R →+* S` with `I ≤ f⁻¹(J)` -/
def quotient_map {I : ideal R} (J : ideal S) (f : R →+* S) (hIJ : I ≤ J.comap f) :
  I.quotient →+* J.quotient :=
(quotient.lift I ((quotient.mk J).comp f) (λ _ ha,
  by simpa [function.comp_app, ring_hom.coe_comp, quotient.eq_zero_iff_mem] using hIJ ha))

@[simp]
lemma quotient_map_mk {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ I.comap f}
  {x : R} : quotient_map I f H (quotient.mk J x) = quotient.mk I (f x) :=
quotient.lift_mk J _ _

lemma quotient_map_comp_mk {J : ideal R} {I : ideal S} {f : R →+* S} (H : J ≤ I.comap f) :
  (quotient_map I f H).comp (quotient.mk J) = (quotient.mk I).comp f :=
ring_hom.ext (λ x, by simp only [function.comp_app, ring_hom.coe_comp, ideal.quotient_map_mk])

/-- The ring equiv `R/I ≃+* S/J` induced by a ring equiv `f : R ≃+** S`,  where `J = f(I)`. -/
@[simps]
def quotient_equiv (I : ideal R) (J : ideal S) (f : R ≃+* S) (hIJ : J = I.map (f : R →+* S)) :
  I.quotient ≃+* J.quotient :=
{ inv_fun := quotient_map I ↑f.symm (by {rw hIJ, exact le_of_eq (map_comap_of_equiv I f)}),
  left_inv := by {rintro ⟨r⟩, simp },
  right_inv := by {rintro ⟨s⟩, simp },
  ..quotient_map J ↑f (by {rw hIJ, exact @le_comap_map _ S _ _ _ _}) }

/-- `H` and `h` are kept as separate hypothesis since H is used in constructing the quotient map. -/
lemma quotient_map_injective' {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ I.comap f}
  (h : I.comap f ≤ J) : function.injective (quotient_map I f H) :=
begin
  refine (quotient_map I f H).injective_iff.2 (λ a ha, _),
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a,
  rw [quotient_map_mk, quotient.eq_zero_iff_mem] at ha,
  exact (quotient.eq_zero_iff_mem).mpr (h ha),
end

/-- If we take `J = I.comap f` then `quotient_map` is injective automatically. -/
lemma quotient_map_injective {I : ideal S} {f : R →+* S} :
  function.injective (quotient_map I f le_rfl) :=
quotient_map_injective' le_rfl

lemma quotient_map_surjective {J : ideal R} {I : ideal S} {f : R →+* S} {H : J ≤ I.comap f}
  (hf : function.surjective f) : function.surjective (quotient_map I f H) :=
λ x, let ⟨x, hx⟩ := quotient.mk_surjective x in
  let ⟨y, hy⟩ := hf x in ⟨(quotient.mk J) y, by simp [hx, hy]⟩

/-- Commutativity of a square is preserved when taking quotients by an ideal. -/
lemma comp_quotient_map_eq_of_comp_eq {R' S' : Type*} [comm_ring R'] [comm_ring S']
  {f : R →+* S} {f' : R' →+* S'} {g : R →+* R'} {g' : S →+* S'} (hfg : f'.comp g = g'.comp f)
  (I : ideal S') : (quotient_map I g' le_rfl).comp (quotient_map (I.comap g') f le_rfl) =
    (quotient_map I f' le_rfl).comp (quotient_map (I.comap f') g
      (le_of_eq (trans (comap_comap f g') (hfg ▸ (comap_comap g f'))))) :=
begin
  refine ring_hom.ext (λ a, _),
  obtain ⟨r, rfl⟩ := quotient.mk_surjective a,
  simp only [ring_hom.comp_apply, quotient_map_mk],
  exact congr_arg (quotient.mk I) (trans (g'.comp_apply f r).symm (hfg ▸ (f'.comp_apply g r))),
end

variables {I : ideal R} {J: ideal S} [algebra R S]

/-- The algebra hom `A/I →+* S/J` induced by an algebra hom `f : A →ₐ[R] S` with `I ≤ f⁻¹(J)`. -/
def quotient_mapₐ {I : ideal A} (J : ideal S) (f : A →ₐ[R] S) (hIJ : I ≤ J.comap f) :
  I.quotient →ₐ[R] J.quotient :=
{ commutes' := λ r,
  begin
    have h : (algebra_map R I.quotient) r = (quotient.mk I) (algebra_map R A r) := rfl,
    simpa [h]
  end
  ..quotient_map J ↑f hIJ }

@[simp]
lemma quotient_map_mkₐ {I : ideal A} (J : ideal S) (f : A →ₐ[R] S) (H : I ≤ J.comap f)
  {x : A} : quotient_mapₐ J f H (quotient.mk I x) = quotient.mkₐ R J (f x) := rfl

lemma quotient_map_comp_mkₐ {I : ideal A} (J : ideal S) (f : A →ₐ[R] S) (H : I ≤ J.comap f) :
  (quotient_mapₐ J f H).comp (quotient.mkₐ R I) = (quotient.mkₐ R J).comp f :=
alg_hom.ext (λ x, by simp only [quotient_map_mkₐ, quotient.mkₐ_eq_mk, alg_hom.comp_apply])

/-- The algebra equiv `A/I ≃ₐ[R] S/J` induced by an algebra equiv `f : A ≃ₐ[R] S`,
where`J = f(I)`. -/
def quotient_equiv_alg (I : ideal A) (J : ideal S) (f : A ≃ₐ[R] S) (hIJ : J = I.map (f : A →+* S)) :
  I.quotient ≃ₐ[R] J.quotient :=
{ commutes' := λ r,
  begin
    have h : (algebra_map R I.quotient) r = (quotient.mk I) (algebra_map R A r) := rfl,
    simpa [h]
  end,
  ..quotient_equiv I J (f : A ≃+* S) hIJ }

@[priority 100]
instance quotient_algebra : algebra (J.comap (algebra_map R S)).quotient J.quotient :=
(quotient_map J (algebra_map R S) (le_of_eq rfl)).to_algebra

lemma algebra_map_quotient_injective :
  function.injective (algebra_map (J.comap (algebra_map R S)).quotient J.quotient) :=
begin
  rintros ⟨a⟩ ⟨b⟩ hab,
  replace hab := quotient.eq.mp hab,
  rw ← ring_hom.map_sub at hab,
  exact quotient.eq.mpr hab
end

end quotient_algebra

end comm_ring

end ideal

namespace submodule

variables {R : Type u} {M : Type v}
variables [comm_ring R] [add_comm_group M] [module R M]

-- TODO: show `[algebra R A] : algebra (ideal R) A` too

instance module_submodule : module (ideal R) (submodule R M) :=
{ smul_add := smul_sup,
  add_smul := sup_smul,
  mul_smul := submodule.smul_assoc,
  one_smul := by simp,
  zero_smul := bot_smul,
  smul_zero := smul_bot }

end submodule

namespace ring_hom
variables {A B C : Type*} [ring A] [ring B] [ring C]
variables (f : A →+* B) (f_inv : B → A)

/-- Auxiliary definition used to define `lift_of_right_inverse` -/
def lift_of_right_inverse_aux
  (hf : function.right_inverse f_inv f) (g : A →+* C) (hg : f.ker ≤ g.ker) :
  B →+* C :=
{ to_fun := λ b, g (f_inv b),
  map_one' :=
  begin
    rw [← g.map_one, ← sub_eq_zero, ← g.map_sub, ← g.mem_ker],
    apply hg,
    rw [f.mem_ker, f.map_sub, sub_eq_zero, f.map_one],
    exact hf 1
  end,
  map_mul' :=
  begin
    intros x y,
    rw [← g.map_mul, ← sub_eq_zero, ← g.map_sub, ← g.mem_ker],
    apply hg,
    rw [f.mem_ker, f.map_sub, sub_eq_zero, f.map_mul],
    simp only [hf _],
  end,
  .. add_monoid_hom.lift_of_right_inverse f.to_add_monoid_hom f_inv hf ⟨g.to_add_monoid_hom, hg⟩ }

@[simp] lemma lift_of_right_inverse_aux_comp_apply
  (hf : function.right_inverse f_inv f) (g : A →+* C) (hg : f.ker ≤ g.ker) (a : A) :
  (f.lift_of_right_inverse_aux f_inv hf g hg) (f a) = g a :=
f.to_add_monoid_hom.lift_of_right_inverse_comp_apply f_inv hf ⟨g.to_add_monoid_hom, hg⟩ a

/-- `lift_of_right_inverse f hf g hg` is the unique ring homomorphism `φ`

* such that `φ.comp f = g` (`ring_hom.lift_of_right_inverse_comp`),
* where `f : A →+* B` is has a right_inverse `f_inv` (`hf`),
* and `g : B →+* C` satisfies `hg : f.ker ≤ g.ker`.

See `ring_hom.eq_lift_of_right_inverse` for the uniqueness lemma.

```
   A .
   |  \
 f |   \ g
   |    \
   v     \⌟
   B ----> C
      ∃!φ
```
-/
def lift_of_right_inverse
  (hf : function.right_inverse f_inv f) : {g : A →+* C // f.ker ≤ g.ker} ≃ (B →+* C) :=
{ to_fun := λ g, f.lift_of_right_inverse_aux f_inv hf g.1 g.2,
  inv_fun := λ φ, ⟨φ.comp f, λ x hx, (mem_ker _).mpr $ by simp [(mem_ker _).mp hx]⟩,
  left_inv := λ g, by {
    ext,
    simp only [comp_apply, lift_of_right_inverse_aux_comp_apply, subtype.coe_mk,
      subtype.val_eq_coe], },
  right_inv := λ φ, by {
    ext b,
    simp [lift_of_right_inverse_aux, hf b], } }

/-- A non-computable version of `ring_hom.lift_of_right_inverse` for when no computable right
inverse is available, that uses `function.surj_inv`. -/
@[simp]
noncomputable abbreviation lift_of_surjective
  (hf : function.surjective f) : {g : A →+* C // f.ker ≤ g.ker} ≃ (B →+* C) :=
f.lift_of_right_inverse (function.surj_inv hf) (function.right_inverse_surj_inv hf)

lemma lift_of_right_inverse_comp_apply
  (hf : function.right_inverse f_inv f) (g : {g : A →+* C // f.ker ≤ g.ker}) (x : A) :
  (f.lift_of_right_inverse f_inv hf g) (f x) = g x :=
f.lift_of_right_inverse_aux_comp_apply f_inv hf g.1 g.2 x

lemma lift_of_right_inverse_comp (hf : function.right_inverse f_inv f)
  (g : {g : A →+* C // f.ker ≤ g.ker}) :
  (f.lift_of_right_inverse f_inv hf g).comp f = g :=
ring_hom.ext $ f.lift_of_right_inverse_comp_apply f_inv hf g

lemma eq_lift_of_right_inverse (hf : function.right_inverse f_inv f) (g : A →+* C)
  (hg : f.ker ≤ g.ker) (h : B →+* C) (hh : h.comp f = g) :
  h = (f.lift_of_right_inverse f_inv hf ⟨g, hg⟩) :=
begin
  simp_rw ←hh,
  exact ((f.lift_of_right_inverse f_inv hf).apply_symm_apply _).symm,
end

end ring_hom
