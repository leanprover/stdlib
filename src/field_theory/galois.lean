/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.primitive_element
import field_theory.fixed

/-!
# Galois Extensions

In this file we define Galois extensions as extensions which are both separable and normal.

## Main definitions

- `is_galois F E` where `E` is an extension of `F`
- `fixed_field H` where `H : subgroup (E ≃ₐ[F] E)`
- `fixing_subgroup K` where `K : intermediate_field F E`
- `galois_correspondence` where `E/F` is finite dimensional and Galois

## Main results

- `fixing_subgroup_of_fixed_field` : If `E/F` is finite dimensional (but not necessarily Galois)
  then `fixing_subgroup (fixed_field H) = H`
- `fixed_field_of_fixing_subgroup`: If `E/F` is finite dimensional and Galois
  then `fixed_field (fixing_subgroup K) = K`
Together, these two result prove the Galois correspondence

- `is_galois.tfae` : Equivalent characterizations of a Galois extension of finite degree
-/

noncomputable theory
open_locale classical

open finite_dimensional alg_equiv


section

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

/-- A field extension E/F is galois if it is both separable and normal -/
@[class] def is_galois : Prop := is_separable F E ∧ normal F E

namespace is_galois

instance self : is_galois F F :=
⟨is_separable_self F, normal_self F⟩

@[priority 100] -- see Note [lower instance priority]
instance to_is_separable [h : is_galois F E] : is_separable F E := h.1

@[priority 100] -- see Note [lower instance priority]
instance to_normal [h : is_galois F E] : normal F E := h.2

variables (F) {E}

lemma integral [is_galois F E] (x : E) : is_integral F x := normal.is_integral F x

lemma separable [h : is_galois F E] (x : E) : (minpoly F x).separable := (h.1 x).2

-- TODO(Commelin, Browning): rename this to `splits`
lemma normal [is_galois F E] (x : E) : (minpoly F x).splits (algebra_map F E) := normal.splits F x

variables (F) (E)

instance of_fixed_field (G : Type*) [group G] [fintype G] [mul_semiring_action G E] :
  is_galois (mul_action.fixed_points G E) E :=
⟨fixed_points.separable G E, fixed_points.normal G E⟩

lemma intermediate_field.adjoin_simple.card_aut_eq_findim
  [finite_dimensional F E] {α : E} (hα : is_integral F α)
  (h_sep : (minpoly F α).separable)
  (h_splits : (minpoly F α).splits (algebra_map F F⟮α⟯)) :
  fintype.card (F⟮α⟯ ≃ₐ[F] F⟮α⟯) = findim F F⟮α⟯ :=
begin
  letI : fintype (F⟮α⟯ →ₐ[F] F⟮α⟯) := intermediate_field.fintype_of_alg_hom_adjoin_integral F hα,
  rw intermediate_field.adjoin.findim hα,
  rw ← intermediate_field.card_alg_hom_adjoin_integral F hα h_sep h_splits,
  exact fintype.card_congr (alg_equiv_equiv_alg_hom F F⟮α⟯)
end

lemma card_aut_eq_findim [finite_dimensional F E] [h : is_galois F E] :
  fintype.card (E ≃ₐ[F] E) = findim F E :=
begin
  cases field.exists_primitive_element h.1 with α hα,
  let iso : F⟮α⟯ ≃ₐ[F] E := {
    to_fun := λ e, e.val,
    inv_fun := λ e, ⟨e, by { rw hα, exact intermediate_field.mem_top }⟩,
    left_inv := λ _, by { ext, refl },
    right_inv := λ _, rfl,
    map_mul' := λ _ _, rfl,
    map_add' := λ _ _, rfl,
    commutes' := λ _, rfl },
  have H : is_integral F α := is_galois.integral F α,
  have h_sep : (minpoly F α).separable := is_galois.separable F α,
  have h_splits : (minpoly F α).splits (algebra_map F E) := is_galois.normal F α,
  replace h_splits : polynomial.splits (algebra_map F F⟮α⟯) (minpoly F α),
  { convert polynomial.splits_comp_of_splits
    (algebra_map F E) iso.symm.to_alg_hom.to_ring_hom h_splits },
  rw ← linear_equiv.findim_eq iso.to_linear_equiv,
  rw ← intermediate_field.adjoin_simple.card_aut_eq_findim F E H h_sep h_splits,
  apply fintype.card_congr,
  apply equiv.mk (λ ϕ, iso.trans (trans ϕ iso.symm)) (λ ϕ, iso.symm.trans (trans ϕ iso)),
  { intro ϕ, ext1, simp only [trans_apply, apply_symm_apply] },
  { intro ϕ, ext1, simp only [trans_apply, symm_apply_apply] },
end

end is_galois

end

section is_galois_tower

variables (F K E : Type*) [field F] [field K] [field E] {E' : Type*} [field E'] [algebra F E']
variables [algebra F K] [algebra F E] [algebra K E] [is_scalar_tower F K E]

lemma is_galois.tower_top_of_is_galois [is_galois F E] : is_galois K E :=
⟨is_separable_tower_top_of_is_separable F K E, normal.tower_top_of_normal F K E⟩

variables {F E}

@[priority 100] -- see Note [lower instance priority]
instance is_galois.tower_top_intermediate_field (K : intermediate_field F E) [h : is_galois F E] :
  is_galois K E := is_galois.tower_top_of_is_galois F K E

lemma is_galois_iff_is_galois_bot : is_galois (⊥ : intermediate_field F E) E ↔ is_galois F E :=
begin
  split,
  { introI h,
    exact is_galois.tower_top_of_is_galois (⊥ : intermediate_field F E) F E },
  { introI h, apply_instance },
end

lemma is_galois.of_alg_equiv [h : is_galois F E] (f : E ≃ₐ[F] E') : is_galois F E' :=
⟨is_separable.of_alg_hom F E f.symm, normal.of_alg_equiv f⟩

lemma alg_equiv.transfer_galois (f : E ≃ₐ[F] E') : is_galois F E ↔ is_galois F E' :=
⟨λ h, by exactI is_galois.of_alg_equiv f, λ h, by exactI is_galois.of_alg_equiv f.symm⟩

lemma is_galois_iff_is_galois_top : is_galois F (⊤ : intermediate_field F E) ↔ is_galois F E :=
(intermediate_field.top_equiv).transfer_galois

instance is_galois_bot : is_galois F (⊥ : intermediate_field F E) :=
intermediate_field.bot_equiv.transfer_galois.mpr (is_galois.self F)

end is_galois_tower

section galois_correspondence

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]
variables (H : subgroup (E ≃ₐ[F] E)) (K : intermediate_field F E)

namespace intermediate_field

instance subgroup_action : faithful_mul_semiring_action H E :=
{ smul := λ h x, h x,
  smul_zero := λ _, map_zero _,
  smul_add := λ _, map_add _,
  one_smul := λ _, rfl,
  smul_one := λ _, map_one _,
  mul_smul := λ _ _ _, rfl,
  smul_mul := λ _, map_mul _,
  eq_of_smul_eq_smul' := λ x y z, subtype.ext (alg_equiv.ext z) }

/-- The intermediate_field fixed by a subgroup -/
def fixed_field : intermediate_field F E :=
{ carrier := mul_action.fixed_points H E,
  zero_mem' := λ g, smul_zero g,
  add_mem' := λ a b hx hy g, by rw [smul_add g a b, hx, hy],
  neg_mem' := λ a hx g, by rw [smul_neg g a, hx],
  one_mem' := λ g, smul_one g,
  mul_mem' := λ a b hx hy g, by rw [smul_mul' g a b, hx, hy],
  inv_mem' := λ a hx g, by rw [smul_inv _ g a, hx],
  algebra_map_mem' := λ a g, commutes g a }

lemma findim_fixed_field_eq_card [finite_dimensional F E] :
  findim (fixed_field H) E = fintype.card H :=
fixed_points.findim_eq_card H E

/-- The subgroup fixing an intermediate_field -/
def fixing_subgroup : subgroup (E ≃ₐ[F] E) :=
{ carrier := λ ϕ, ∀ x : K, ϕ x = x,
  one_mem' := λ _, rfl,
  mul_mem' := λ _ _ hx hy _, (congr_arg _ (hy _)).trans (hx _),
  inv_mem' := λ _ hx _, (equiv.symm_apply_eq (to_equiv _)).mpr (hx _).symm }

lemma le_iff_le : K ≤ fixed_field H ↔ H ≤ fixing_subgroup K :=
⟨λ h g hg x, h (subtype.mem x) ⟨g, hg⟩, λ h x hx g, h (subtype.mem g) ⟨x, hx⟩⟩

/-- The fixing_subgroup of `K : intermediate_field F E` is isomorphic to `E ≃ₐ[K] E` -/
def fixing_subgroup_equiv : fixing_subgroup K ≃* (E ≃ₐ[K] E) :=
{ to_fun := λ ϕ, of_bijective (alg_hom.mk ϕ (map_one ϕ) (map_mul ϕ)
    (map_zero ϕ) (map_add ϕ) (ϕ.mem)) (bijective ϕ),
  inv_fun := λ ϕ, ⟨of_bijective (alg_hom.mk ϕ (ϕ.map_one) (ϕ.map_mul)
    (ϕ.map_zero) (ϕ.map_add) (λ r, ϕ.commutes (algebra_map F K r)))
      (ϕ.bijective), ϕ.commutes⟩,
  left_inv := λ _, by { ext, refl },
  right_inv := λ _, by { ext, refl },
  map_mul' := λ _ _, by { ext, refl } }

theorem fixing_subgroup_fixed_field [finite_dimensional F E] :
  fixing_subgroup (fixed_field H) = H :=
begin
  have H_le : H ≤ (fixing_subgroup (fixed_field H)) := (le_iff_le _ _).mp (le_refl _),
  suffices : fintype.card H = fintype.card (fixing_subgroup (fixed_field H)),
  { exact subgroup.ext' (set.eq_of_inclusion_surjective ((fintype.bijective_iff_injective_and_card
    (set.inclusion H_le)).mpr ⟨set.inclusion_injective H_le, this⟩).2).symm },
  apply fintype.card_congr,
  refine (fixed_points.to_alg_hom_equiv H E).trans _,
  refine (alg_equiv_equiv_alg_hom (fixed_field H) E).symm.trans _,
  exact (fixing_subgroup_equiv (fixed_field H)).to_equiv.symm
end

instance fixed_field.algebra : algebra K (fixed_field (fixing_subgroup K)) :=
{ smul := λ x y, ⟨x*y, λ ϕ, by rw [smul_mul', (show ϕ • ↑x = ↑x, by exact subtype.mem ϕ x),
    (show ϕ • ↑y = ↑y, by exact subtype.mem y ϕ)]⟩,
  to_fun := λ x, ⟨x, λ ϕ, subtype.mem ϕ x⟩,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ _ _, rfl }

instance fixed_field.is_scalar_tower : is_scalar_tower K (fixed_field (fixing_subgroup K)) E :=
⟨λ _ _ _, mul_assoc _ _ _⟩

end intermediate_field

namespace is_galois
theorem fixed_field_fixing_subgroup [finite_dimensional F E] [h : is_galois F E] :
  intermediate_field.fixed_field (intermediate_field.fixing_subgroup K) = K :=
begin
  have K_le : K ≤ intermediate_field.fixed_field (intermediate_field.fixing_subgroup K) :=
    (intermediate_field.le_iff_le _ _).mpr (le_refl _),
  suffices : findim K E =
    findim (intermediate_field.fixed_field (intermediate_field.fixing_subgroup K)) E,
  { exact (intermediate_field.eq_of_le_of_findim_eq' K_le this).symm },
  rw [intermediate_field.findim_fixed_field_eq_card,
    fintype.card_congr (intermediate_field.fixing_subgroup_equiv K).to_equiv],
  exact (card_aut_eq_findim K E).symm,
end

lemma card_fixing_subgroup_eq_findim [finite_dimensional F E] [is_galois F E] :
  fintype.card (intermediate_field.fixing_subgroup K) = findim K E :=
by conv { to_rhs, rw [←fixed_field_fixing_subgroup K,
  intermediate_field.findim_fixed_field_eq_card] }

/-- The Galois correspondence from intermediate fields to subgroups -/
def intermediate_field_equiv_subgroup [finite_dimensional F E] [is_galois F E] :
  intermediate_field F E ≃o order_dual (subgroup (E ≃ₐ[F] E)) :=
{ to_fun := intermediate_field.fixing_subgroup,
  inv_fun := intermediate_field.fixed_field,
  left_inv := λ K, fixed_field_fixing_subgroup K,
  right_inv := λ H, intermediate_field.fixing_subgroup_fixed_field H,
  map_rel_iff' := λ K L, by { rw [←fixed_field_fixing_subgroup L, intermediate_field.le_iff_le,
                                  fixed_field_fixing_subgroup L, ←order_dual.dual_le], refl } }

/-- The Galois correspondence as a galois_insertion -/
def galois_insertion_intermediate_field_subgroup [finite_dimensional F E] :
  galois_insertion (order_dual.to_dual ∘
      (intermediate_field.fixing_subgroup : intermediate_field F E → subgroup (E ≃ₐ[F] E)))
    ((intermediate_field.fixed_field : subgroup (E ≃ₐ[F] E) → intermediate_field F E) ∘
      order_dual.to_dual) :=
{ choice := λ K _, intermediate_field.fixing_subgroup K,
  gc := λ K H, (intermediate_field.le_iff_le H K).symm,
  le_l_u := λ H, le_of_eq (intermediate_field.fixing_subgroup_fixed_field H).symm,
  choice_eq := λ K _, rfl }

/-- The Galois correspondence as a galois_coinsertion -/
def galois_coinsertion_intermediate_field_subgroup [finite_dimensional F E] [is_galois F E] :
  galois_coinsertion (order_dual.to_dual ∘
      (intermediate_field.fixing_subgroup : intermediate_field F E → subgroup (E ≃ₐ[F] E)))
    ((intermediate_field.fixed_field : subgroup (E ≃ₐ[F] E) → intermediate_field F E) ∘
      order_dual.to_dual) :=
{ choice := λ H _, intermediate_field.fixed_field H,
  gc := λ K H, (intermediate_field.le_iff_le H K).symm,
  u_l_le := λ K, le_of_eq (fixed_field_fixing_subgroup K),
  choice_eq := λ H _, rfl }

end is_galois

end galois_correspondence

section galois_equivalent_definitions

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

namespace is_galois

lemma is_separable_splitting_field [finite_dimensional F E] [h : is_galois F E] :
  ∃ p : polynomial F, p.separable ∧ p.is_splitting_field F E :=
begin
  cases field.exists_primitive_element h.1 with α h1,
  use [minpoly F α, separable F α, is_galois.normal F α],
  rw [eq_top_iff, ←intermediate_field.top_to_subalgebra, ←h1],
  rw intermediate_field.adjoin_simple_to_subalgebra_of_integral F α (integral F α),
  apply algebra.adjoin_mono,
  rw [set.singleton_subset_iff, finset.mem_coe, multiset.mem_to_finset, polynomial.mem_roots],
  { dsimp only [polynomial.is_root],
    rw [polynomial.eval_map, ←polynomial.aeval_def],
    exact minpoly.aeval _ _ },
  { exact polynomial.map_ne_zero (minpoly.ne_zero (integral F α)) }
end

lemma of_fixed_field_eq_bot [finite_dimensional F E]
  (h : intermediate_field.fixed_field (⊤ : subgroup (E ≃ₐ[F] E)) = ⊥) : is_galois F E :=
begin
  rw [←is_galois_iff_is_galois_bot, ←h],
  exact is_galois.of_fixed_field E (⊤ : subgroup (E ≃ₐ[F] E)),
end

lemma of_card_aut_eq_findim [finite_dimensional F E]
  (h : fintype.card (E ≃ₐ[F] E) = findim F E) : is_galois F E :=
begin
  apply of_fixed_field_eq_bot,
  have p : 0 < findim (intermediate_field.fixed_field (⊤ : subgroup (E ≃ₐ[F] E))) E := findim_pos,
  rw [←intermediate_field.findim_eq_one_iff, ←mul_left_inj' (ne_of_lt p).symm, findim_mul_findim,
      ←h, one_mul, intermediate_field.findim_fixed_field_eq_card],
  exact fintype.card_congr { to_fun := λ g, ⟨g, subgroup.mem_top g⟩, inv_fun := coe,
    left_inv := λ g, rfl, right_inv := λ _, by { ext, refl } },
end

variables {F} {E} {p : polynomial F}

lemma of_separable_splitting_field_aux [hFE : finite_dimensional F E]
  [sp : p.is_splitting_field F E] (hp : p.separable) (K : intermediate_field F E) {x : E}
  (hx : x ∈ (p.map (algebra_map F E)).roots) :
  fintype.card ((↑K⟮x⟯ : intermediate_field F E) →ₐ[F] E) =
    fintype.card (K →ₐ[F] E) * findim K K⟮x⟯ :=
begin
  have h : is_integral K x := is_integral_of_is_scalar_tower x (is_integral_of_noetherian hFE x),
  have h1 : p ≠ 0 := λ hp, by rwa [hp, polynomial.map_zero, polynomial.roots_zero] at hx,
  have h2 : (minpoly K x) ∣ p.map (algebra_map F K),
  { apply minpoly.dvd,
    rw [polynomial.aeval_def, polynomial.eval₂_map, ←polynomial.eval_map],
    exact (polynomial.mem_roots (polynomial.map_ne_zero h1)).mp hx },
  let key_equiv : ((↑K⟮x⟯ : intermediate_field F E) →ₐ[F] E) ≃ Σ (f : K →ₐ[F] E),
    @alg_hom K K⟮x⟯ E _ _ _ _ (ring_hom.to_algebra f) :=
  equiv.trans (alg_equiv.arrow_congr (intermediate_field.lift2_alg_equiv K⟮x⟯) (alg_equiv.refl))
    alg_hom_equiv_sigma,
  haveI : Π (f : K →ₐ[F] E), fintype (@alg_hom K K⟮x⟯ E _ _ _ _ (ring_hom.to_algebra f)) := λ f, by
  { apply fintype.of_injective (sigma.mk f) (λ _ _ H, eq_of_heq ((sigma.mk.inj H).2)),
    exact fintype.of_equiv _ key_equiv },
  rw [fintype.card_congr key_equiv, fintype.card_sigma, intermediate_field.adjoin.findim h],
  apply finset.sum_const_nat,
  intros f hf,
  rw ← @intermediate_field.card_alg_hom_adjoin_integral K _ E _ _ x E _ (ring_hom.to_algebra f) h,
  { apply fintype.card_congr, refl },
  { exact polynomial.separable.of_dvd ((polynomial.separable_map (algebra_map F K)).mpr hp) h2 },
  { refine polynomial.splits_of_splits_of_dvd _ (polynomial.map_ne_zero h1) _ h2,
    rw [polynomial.splits_map_iff, ←is_scalar_tower.algebra_map_eq],
    exact sp.splits },
end

lemma of_separable_splitting_field [sp : p.is_splitting_field F E] (hp : p.separable) :
  is_galois F E :=
begin
  haveI hFE : finite_dimensional F E := polynomial.is_splitting_field.finite_dimensional E p,
  let s := (p.map (algebra_map F E)).roots.to_finset,
  have adjoin_root := intermediate_field.ext (subalgebra.ext_iff.mp (eq.trans (top_le_iff.mp
    (eq.trans_le sp.adjoin_roots.symm (intermediate_field.algebra_adjoin_le_adjoin F ↑s)))
    intermediate_field.top_to_subalgebra.symm)),
  let P : intermediate_field F E → Prop := λ K, fintype.card (K →ₐ[F] E) = findim F K,
  suffices : P (intermediate_field.adjoin F ↑s),
  { rw adjoin_root at this,
    apply of_card_aut_eq_findim,
    rw ← eq.trans this (linear_equiv.findim_eq intermediate_field.top_equiv.to_linear_equiv),
    exact fintype.card_congr (equiv.trans (alg_equiv_equiv_alg_hom F E)
      (alg_equiv.arrow_congr intermediate_field.top_equiv.symm alg_equiv.refl)) },
  apply intermediate_field.induction_on_adjoin_finset s P,
  { have key := intermediate_field.card_alg_hom_adjoin_integral F
      (show is_integral F (0 : E), by exact is_integral_zero),
    rw [minpoly.zero, polynomial.nat_degree_X] at key,
    specialize key polynomial.separable_X (polynomial.splits_X (algebra_map F E)),
    rw [←@subalgebra.findim_bot F E _ _ _, ←intermediate_field.bot_to_subalgebra] at key,
    refine eq.trans _ key,
    apply fintype.card_congr,
    rw intermediate_field.adjoin_zero },
  intros K x hx hK,
  simp only [P] at *,
  rw [of_separable_splitting_field_aux hp K (multiset.mem_to_finset.mp hx),
    hK, findim_mul_findim],
  exact (linear_equiv.findim_eq (intermediate_field.lift2_alg_equiv K⟮x⟯).to_linear_equiv).symm,
end

/--Equivalent characterizations of a Galois extension of finite degree-/
theorem tfae [finite_dimensional F E] :
  tfae [is_galois F E,
    intermediate_field.fixed_field (⊤ : subgroup (E ≃ₐ[F] E)) = ⊥,
    fintype.card (E ≃ₐ[F] E) = findim F E,
    ∃ p : polynomial F, p.separable ∧ p.is_splitting_field F E] :=
begin
  tfae_have : 1 → 2,
  { exact λ h, order_iso.map_bot (@intermediate_field_equiv_subgroup F _ E _ _ _ h).symm },
  tfae_have : 1 → 3,
  { introI _, exact card_aut_eq_findim F E },
  tfae_have : 1 → 4,
  { introI _, exact is_separable_splitting_field F E },
  tfae_have : 2 → 1,
  { exact of_fixed_field_eq_bot F E },
  tfae_have : 3 → 1,
  { exact of_card_aut_eq_findim F E },
  tfae_have : 4 → 1,
  { rintros ⟨h, hp1, _⟩, exactI of_separable_splitting_field hp1 },
  tfae_finish,
end

end is_galois

end galois_equivalent_definitions
