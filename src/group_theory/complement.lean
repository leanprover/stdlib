/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.group_action
import group_theory.order_of_element
import group_theory.quotient_group

/-!
# Complements

In this file we define the complement of a subgroup.

## Main definitions

- `is_complement S T` where `S` and `T` are subsets of `G`
- `left_transversals T` where `T` is a subset of `G`
- `right_transversals S` where `S` is a subset of `G`

## Main results

- `is_complement_of_coprime` : Subgroups of coprime order are complements
- `schur_zassenhaus` : Schur-Zassenhaus for abelian normal subgroups
-/

open_locale big_operators

namespace subgroup

variables {G : Type*} [group G] (H K : subgroup G) (S T : set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection -/
@[to_additive "`S` and `T` are complements if `(*) : S × T → G` is a bijection"]
def is_complement : Prop := ∀ g : G, ∃! x : S × T, x.1.1 * x.2.1 = g

/-- The set of left-complements of `T : set G` -/
@[to_additive "The set of left-complements of `T : set G`"]
def left_transversals : set (set G) := {S : set G | is_complement S T}

/-- The set of right-complements of `S : set G` -/
@[to_additive "The set of right-complements of `S : set G`"]
def right_transversals : set (set G) := {T : set G | is_complement S T}

variables {H K S T}

@[to_additive] lemma is_complement_iff_bijective :
  is_complement S T ↔ function.bijective (λ x : S × T, x.1.1 * x.2.1) :=
(function.bijective_iff_exists_unique _).symm

@[to_additive] lemma is_complement.symm (h : is_complement (H : set G) (K : set G)) :
  is_complement (K : set G) (H : set G) :=
begin
  let ϕ : H × K ≃ K × H := equiv.mk (λ x, ⟨x.2⁻¹, x.1⁻¹⟩) (λ x, ⟨x.2⁻¹, x.1⁻¹⟩)
    (λ x, prod.ext (inv_inv _) (inv_inv _)) (λ x, prod.ext (inv_inv _) (inv_inv _)),
  refine λ g, (equiv.exists_unique_congr ϕ (λ x, _)).mp (h g⁻¹),
  rw [eq_inv_iff_eq_inv, mul_inv_rev],
  exact eq_comm,
end

@[to_additive] lemma is_complement_comm :
  is_complement (H : set G) (K : set G) ↔ is_complement (K : set G) (H : set G) :=
⟨is_complement.symm, is_complement.symm⟩

@[to_additive] lemma mem_left_transversals_iff_exists_unique_inv_mul_mem :
  S ∈ left_transversals T ↔ ∀ g : G, ∃! s : S, (s : G)⁻¹ * g ∈ T :=
begin
  refine ⟨λ h g, _, λ h g, _⟩,
  { obtain ⟨x, h1, h2⟩ := h g,
    exact ⟨x.1, (congr_arg (∈ T) (eq_inv_mul_of_mul_eq h1)).mp x.2.2, λ y hy,
      (prod.ext_iff.mp (h2 ⟨y, y⁻¹ * g, hy⟩ (mul_inv_cancel_left y g))).1⟩ },
  { obtain ⟨x, h1, h2⟩ := h g,
    refine ⟨⟨x, x⁻¹ * g, h1⟩, mul_inv_cancel_left x g, λ y hy, _⟩,
    have := h2 y.1 ((congr_arg (∈ T) (eq_inv_mul_of_mul_eq hy)).mp y.2.2),
    exact prod.ext this (subtype.ext (eq_inv_mul_of_mul_eq ((congr_arg _ this).mp hy))) },
end

@[to_additive] lemma mem_right_transversals_iff_exists_unique_mul_inv_mem :
  S ∈ right_transversals T ↔ ∀ g : G, ∃! s : S, g * (s : G)⁻¹ ∈ T :=
begin
  refine ⟨λ h g, _, λ h g, _⟩,
  { obtain ⟨x, h1, h2⟩ := h g,
    exact ⟨x.2, (congr_arg (∈ T) (eq_mul_inv_of_mul_eq h1)).mp x.1.2, λ y hy,
      (prod.ext_iff.mp (h2 ⟨⟨g * y⁻¹, hy⟩, y⟩ (inv_mul_cancel_right g y))).2⟩ },
  { obtain ⟨x, h1, h2⟩ := h g,
    refine ⟨⟨⟨g * x⁻¹, h1⟩, x⟩, inv_mul_cancel_right g x, λ y hy, _⟩,
    have := h2 y.2 ((congr_arg (∈ T) (eq_mul_inv_of_mul_eq hy)).mp y.1.2),
    exact prod.ext (subtype.ext (eq_mul_inv_of_mul_eq ((congr_arg _ this).mp hy))) this },
end

@[to_additive] lemma mem_left_transverals_iff_exists_unique_quotient_mk'_eq :
  S ∈ left_transversals (H : set G) ↔
  ∀ q : quotient (quotient_group.left_rel H), ∃! s : S, quotient.mk' s.1 = q :=
begin
  have key : ∀ g h, quotient.mk' g = quotient.mk' h ↔ g⁻¹ * h ∈ H :=
  @quotient.eq' G (quotient_group.left_rel H),
  simp_rw [mem_left_transversals_iff_exists_unique_inv_mul_mem, set_like.mem_coe, ←key],
  exact ⟨λ h q, quotient.induction_on' q h, λ h g, h (quotient.mk' g)⟩,
end

@[to_additive] lemma mem_right_transverals_iff_exists_unique_quotient_mk'_eq :
  S ∈ right_transversals (H : set G) ↔
  ∀ q : quotient (quotient_group.right_rel H), ∃! s : S, quotient.mk' s.1 = q :=
begin
  have key : ∀ g h, quotient.mk' g = quotient.mk' h ↔ h * g⁻¹ ∈ H :=
  @quotient.eq' G (quotient_group.right_rel H),
  simp_rw [mem_right_transversals_iff_exists_unique_mul_inv_mem, set_like.mem_coe, ←key],
  exact ⟨λ h q, quotient.induction_on' q h, λ h g, h (quotient.mk' g)⟩,
end

@[to_additive] lemma mem_left_transverals_iff_bijective : S ∈ left_transversals (H : set G) ↔
  function.bijective (S.restrict (quotient.mk' : G → quotient (quotient_group.left_rel H))) :=
mem_left_transverals_iff_exists_unique_quotient_mk'_eq.trans
  (function.bijective_iff_exists_unique (S.restrict quotient.mk')).symm

@[to_additive] lemma mem_right_transverals_iff_bijective : S ∈ right_transversals (H : set G) ↔
  function.bijective (set.restrict (quotient.mk' : G → quotient (quotient_group.right_rel H)) S) :=
mem_right_transverals_iff_exists_unique_quotient_mk'_eq.trans
  (function.bijective_iff_exists_unique (S.restrict quotient.mk')).symm

@[to_additive] instance : inhabited (left_transversals (H : set G)) :=
⟨⟨set.range quotient.out', mem_left_transverals_iff_bijective.mpr ⟨by
{ rintros ⟨_, q₁, rfl⟩ ⟨_, q₂, rfl⟩ hg,
  rw (q₁.out_eq'.symm.trans hg).trans q₂.out_eq' }, λ q, ⟨⟨q.out', q, rfl⟩, quotient.out_eq' q⟩⟩⟩⟩

@[to_additive] instance : inhabited (right_transversals (H : set G)) :=
let hf  : function.has_right_inverse (quotient.mk' : G → quotient (quotient_group.right_rel H)) :=
function.surjective.has_right_inverse quotient.surjective_quotient_mk', f := classical.some hf in
⟨⟨set.range f, mem_right_transverals_iff_bijective.mpr ⟨by
{ rintros ⟨_, q₁, rfl⟩ ⟨_, q₂, rfl⟩ hg,
  rw [subtype.ext_iff, subtype.coe_mk, subtype.coe_mk,
      ←classical.some_spec hf q₁, ←classical.some_spec hf q₂],
  exact congr_arg f hg }, λ q, ⟨⟨f q, q, rfl⟩, classical.some_spec hf q⟩⟩⟩⟩

lemma is_complement_of_disjoint [fintype G] [fintype H] [fintype K]
  (h1 : fintype.card H * fintype.card K = fintype.card G)
  (h2 : disjoint H K) :
  is_complement (H : set G) (K : set G) :=
begin
  refine function.bijective.exists_unique ((fintype.bijective_iff_injective_and_card _).mpr
    ⟨λ x y h, _, (fintype.card_prod H K).trans h1⟩),
  rw [←eq_inv_mul_iff_mul_eq, ←mul_assoc, ←mul_inv_eq_iff_eq_mul] at h,
  change ↑(x.2 * y.2⁻¹) = ↑(x.1⁻¹ * y.1) at h,
  rw [prod.ext_iff, ←@inv_mul_eq_one H _ x.1 y.1, ←@mul_inv_eq_one K _ x.2 y.2, subtype.ext_iff,
      subtype.ext_iff, coe_one, coe_one, h, and_self, ←mem_bot, ←h2.eq_bot, mem_inf],
  exact ⟨subtype.mem ((x.1)⁻¹ * (y.1)), (congr_arg (∈ K) h).mp (subtype.mem (x.2 * (y.2)⁻¹))⟩,
end

lemma is_complement_of_coprime [fintype G] [fintype H] [fintype K]
  (h1 : fintype.card H * fintype.card K = fintype.card G)
  (h2 : nat.coprime (fintype.card H) (fintype.card K)) :
  is_complement (H : set G) (K : set G) :=
is_complement_of_disjoint h1 (disjoint_iff.mpr (inf_eq_bot_of_coprime h2))

section schur_zassenhaus

@[to_additive] instance : mul_action G (left_transversals (H : set G)) :=
{ smul := λ g T, ⟨left_coset g T, mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g', by
  { obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g⁻¹ * g'),
    simp_rw [←mul_assoc, ←mul_inv_rev] at ht1 ht2,
    refine ⟨⟨g * t, mem_left_coset g t.2⟩, ht1, _⟩,
    rintros ⟨_, t', ht', rfl⟩ h,
    exact subtype.ext ((mul_right_inj g).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h))) })⟩,
  one_smul := λ T, subtype.ext (one_left_coset T),
  mul_smul := λ g g' T, subtype.ext (left_coset_assoc ↑T g g').symm }

lemma smul_symm_apply_eq_mul_symm_apply_inv_smul
  (g : G) (α : left_transversals (H : set G)) (q : quotient_group.quotient H) :
  ↑((equiv.of_bijective _ (mem_left_transverals_iff_bijective.mp (g • α).2)).symm q) =
    g * ((equiv.of_bijective _ (mem_left_transverals_iff_bijective.mp α.2)).symm
      (g⁻¹ • q : quotient_group.quotient H)) :=
begin
  let w := (equiv.of_bijective _ (mem_left_transverals_iff_bijective.mp α.2)),
  let y := (equiv.of_bijective _ (mem_left_transverals_iff_bijective.mp (g • α).2)),
  change ↑(y.symm q) = ↑(⟨_, mem_left_coset g (subtype.mem _)⟩ : (g • α).1),
  refine subtype.ext_iff.mp (y.symm_apply_eq.mpr _),
  change q = g • (w (w.symm (g⁻¹ • q : quotient_group.quotient H))),
  rw [equiv.apply_symm_apply, ←mul_smul, mul_inv_self, one_smul],
end

variables [is_commutative H] [fintype (quotient_group.quotient H)]

variables (α β γ : left_transversals (H : set G))

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff [hH : normal H] : H :=
let α' := (equiv.of_bijective _ (mem_left_transverals_iff_bijective.mp α.2)).symm,
    β' := (equiv.of_bijective _ (mem_left_transverals_iff_bijective.mp β.2)).symm in
∏ (q : quotient_group.quotient H), ⟨(α' q) * (β' q)⁻¹,
  hH.mem_comm (quotient.exact' ((β'.symm_apply_apply q).trans (α'.symm_apply_apply q).symm))⟩

@[to_additive] lemma diff_mul_diff [normal H] : diff α β * diff β γ = diff α γ :=
finset.prod_mul_distrib.symm.trans (finset.prod_congr rfl (λ x hx, subtype.ext
  (by rw [coe_mul, coe_mk, coe_mk, coe_mk, mul_assoc, inv_mul_cancel_left])))

@[to_additive] lemma diff_self [normal H] : diff α α = 1 :=
mul_right_eq_self.mp (diff_mul_diff α α α)

@[to_additive] lemma diff_inv [normal H]: (diff α β)⁻¹ = diff β α :=
inv_eq_of_mul_eq_one ((diff_mul_diff α β α).trans (diff_self α))

lemma smul_diff_smul [hH : normal H] (g : G) :
  diff (g • α) (g • β) = ⟨g * diff α β * g⁻¹, hH.conj_mem (diff α β).1 (diff α β).2 g⟩ :=
begin
  let ϕ : H →* H :=
  { to_fun := λ h, ⟨g * h * g⁻¹, hH.conj_mem h.1 h.2 g⟩,
    map_one' := subtype.ext (by rw [coe_mk, coe_one, mul_one, mul_inv_self]),
    map_mul' := λ h₁ h₂, subtype.ext (by rw [coe_mk, coe_mul, coe_mul, coe_mk, coe_mk, mul_assoc,
      mul_assoc, mul_assoc, mul_assoc, mul_assoc, inv_mul_cancel_left]) },
  refine eq.trans (finset.prod_bij' (λ q _, (↑g)⁻¹ * q) (λ _ _, finset.mem_univ _)
    (λ q _, subtype.ext _) (λ q _, ↑g * q) (λ _ _, finset.mem_univ _)
    (λ q _, mul_inv_cancel_left g q) (λ q _, inv_mul_cancel_left g q)) (finset.prod_hom _ ϕ),
  change _ * _ = g * (_ * _) * g⁻¹,
  simp_rw [smul_symm_apply_eq_mul_symm_apply_inv_smul, mul_inv_rev, mul_assoc],
  refl,
end

lemma smul_diff [H.normal] (h : H) :
  diff (h • α) β = h ^ (fintype.card (quotient_group.quotient H)) * diff α β :=
begin
  rw [diff, diff, ←finset.card_univ, ←finset.prod_const, ←finset.prod_mul_distrib],
  refine finset.prod_congr rfl (λ q _, _),
  rw [subtype.ext_iff, coe_mul, coe_mk, coe_mk, ←mul_assoc, mul_right_cancel_iff],
  rw [show h • α = (h : G) • α, from rfl, smul_symm_apply_eq_mul_symm_apply_inv_smul],
  rw [mul_left_cancel_iff, ←subtype.ext_iff, equiv.apply_eq_iff_eq, inv_smul_eq_iff],
  exact self_eq_mul_left.mpr ((quotient_group.eq_one_iff _).mpr h.2),
end

variables (H)

instance setoid_diff [H.normal] : setoid (left_transversals (H : set G)) :=
setoid.mk (λ α β, diff α β = 1) ⟨λ α, diff_self α, λ α β h₁,
  by rw [←diff_inv, h₁, one_inv], λ α β γ h₁ h₂, by rw [←diff_mul_diff, h₁, h₂, one_mul]⟩

/-- The quotient of the transverals of an abelian normal `N` by the `diff` relation -/
def quotient_diff [H.normal] :=
quotient H.setoid_diff

instance [H.normal] : inhabited H.quotient_diff :=
quotient.inhabited

variables {H}

instance [H.normal] : mul_action G H.quotient_diff :=
{ smul := λ g, quotient.map (λ α, g • α) (λ α β h, (smul_diff_smul α β g).trans
    (subtype.ext (mul_inv_eq_one.mpr (mul_right_eq_self.mpr (subtype.ext_iff.mp h))))),
  mul_smul := λ g₁ g₂ q, quotient.induction_on q (λ α, congr_arg quotient.mk (mul_smul g₁ g₂ α)),
  one_smul := λ q, quotient.induction_on q (λ α, congr_arg quotient.mk (one_smul G α)) }

variables [fintype H]

lemma exists_smul_eq [H.normal] (α β : H.quotient_diff)
  (hH : nat.coprime (fintype.card H) (fintype.card (quotient_group.quotient H))) :
  ∃ h : H, h • α = β :=
quotient.induction_on α (quotient.induction_on β
  (λ β α, exists_imp_exists (λ n, quotient.sound)
    ⟨(pow_coprime hH).symm (diff α β)⁻¹, by
    { change diff ((_ : H) • _) _ = 1,
      rw smul_diff,
      change pow_coprime hH ((pow_coprime hH).symm (diff α β)⁻¹) * (diff α β) = 1,
      rw [equiv.apply_symm_apply, inv_mul_self] }⟩))

lemma smul_injective [H.normal] (α : H.quotient_diff)
  (hH : nat.coprime (fintype.card H) (fintype.card (quotient_group.quotient H)))
  {h₁ h₂ : H} (hh : h₁ • α = h₂ • α) : h₁ = h₂ :=
begin
  revert hh,
  refine quotient.induction_on α (λ α hα, _),
  replace hα : diff (h₁ • α) (h₂ • α) = 1 := quotient.exact hα,
  rw [smul_diff, ←diff_inv, smul_diff, diff_self, mul_one, mul_inv_eq_one] at hα,
  exact (pow_coprime hH).injective hα,
end

theorem schur_zassenhaus [fintype G] [H.normal]
  (hH : nat.coprime (fintype.card H) (fintype.card (quotient_group.quotient H))) :
  ∃ K : subgroup G, is_complement (H : set G) (K : set G) :=
begin
  classical,
  refine nonempty_of_inhabited.elim (λ α : H.quotient_diff, ⟨mul_action.stabilizer G α, _⟩),
  let ϕ : H ≃ mul_action.orbit G α := equiv.of_bijective (λ h, ⟨h • α, h, rfl⟩)
    ⟨λ h₁ h₂ hh, smul_injective α hH (subtype.ext_iff.mp hh),
      λ β, exists_imp_exists (λ h hh, subtype.ext hh) (exists_smul_eq α β hH)⟩,
  have key := card_eq_card_quotient_mul_card_subgroup (mul_action.stabilizer G α),
  rw ← fintype.card_congr (ϕ.trans (mul_action.orbit_equiv_quotient_stabilizer G α)) at key,
  apply is_complement_of_coprime key.symm,
  rw [card_eq_card_quotient_mul_card_subgroup H, mul_comm, mul_right_inj'] at key,
  { rw ← key, convert hH },
  { rw [←pos_iff_ne_zero, fintype.card_pos_iff],
    apply_instance },
end

end schur_zassenhaus

end subgroup
