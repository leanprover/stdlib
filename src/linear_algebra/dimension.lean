/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen
-/
import linear_algebra.basis
import linear_algebra.std_basis
import set_theory.cardinal_ordinal

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `module.rank : cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

Although this definition works for any module over a (semi)ring,
for now we quickly specialize to division rings and then to fields.
There's lots of generalization still to be done.

## Main statements

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.
* `dim_quotient_add_dim`: if V₁ is a submodule of V, then
  `module.rank (V/V₁) + module.rank V₁ = module.rank V`.
* `dim_range_add_dim_ker`: the rank-nullity theorem.

## Implementation notes

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `V`, `V'`, ... all live in different universes,
and `V₁`, `V₂`, ... all live in the same universe.
-/

noncomputable theory

universes u v v' v'' u₁' w w'

variables {K : Type u} {V V₁ V₂ V₃ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}
variables {ι : Type w} {ι' : Type w'} {η : Type u₁'} {φ : η → Type*}

open_locale classical big_operators

open basis submodule function set

section module

section
variables [semiring K] [add_comm_monoid V] [module K V]
include K

variables (K V)

/-- The rank of a module, defined as a term of type `cardinal`.

We define this as the supremum of the cardinalities of linearly independent subsets.

In a vector space, this is the same as the dimension of the space
(i.e. the cardinality of any basis).

The definition is marked as protected to avoid conflicts with `_root_.rank`,
the rank of a linear map.
-/
protected def module.rank : cardinal :=
cardinal.sup.{v v}
  (λ ι : {s : set V // linear_independent K (coe : s → V)}, cardinal.mk ι.1)

end

section division_ring
variables [division_ring K] [add_comm_group V] [module K V] [add_comm_group V₁] [module K V₁]
variables {K V}

theorem basis.le_span {J : set V} (v : basis ι K V)
   (hJ : span K J = ⊤) : cardinal.mk (range v) ≤ cardinal.mk J :=
begin
  cases le_or_lt cardinal.omega (cardinal.mk J) with oJ oJ,
  { have := cardinal.mk_range_eq_of_injective v.injective,
    let S : J → set ι := λ j, ↑(v.repr j).support,
    let S' : J → set V := λ j, v '' S j,
    have hs : range v ⊆ ⋃ j, S' j,
    { intros b hb,
      rcases mem_range.1 hb with ⟨i, hi⟩,
      have : span K J ≤ comap v.repr.to_linear_map (finsupp.supported K K (⋃ j, S j)) :=
        span_le.2 (λ j hj x hx, ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩),
      rw hJ at this,
      replace : v.repr (v i) ∈ (finsupp.supported K K (⋃ j, S j)) := this trivial,
      rw [v.repr_self, finsupp.mem_supported,
        finsupp.support_single_ne_zero one_ne_zero] at this,
      { subst b,
        rcases mem_Union.1 (this (finset.mem_singleton_self _)) with ⟨j, hj⟩,
        exact mem_Union.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩ },
      { apply_instance } },
    refine le_of_not_lt (λ IJ, _),
    suffices : cardinal.mk (⋃ j, S' j) < cardinal.mk (range v),
    { exact not_le_of_lt this ⟨set.embedding_of_subset _ _ hs⟩ },
    refine lt_of_le_of_lt (le_trans cardinal.mk_Union_le_sum_mk
      (cardinal.sum_le_sum _ (λ _, cardinal.omega) _)) _,
    { exact λ j, le_of_lt (cardinal.lt_omega_iff_finite.2 $ (finset.finite_to_set _).image _) },
    { rwa [cardinal.sum_const, cardinal.mul_eq_max oJ (le_refl _), max_eq_left oJ] } },
  { rcases exists_finite_card_le_of_finite_of_linear_independent_of_span
      (cardinal.lt_omega_iff_finite.1 oJ) v.linear_independent.to_subtype_range _ with ⟨fI, hi⟩,
    { rwa [← cardinal.nat_cast_le, cardinal.finset_card, set.finite.coe_sort_to_finset,
           cardinal.finset_card, set.finite.coe_sort_to_finset] at hi, },
    { rw hJ, apply set.subset_univ } },
end

/-- The dimension theorem: if `v` and `v'` are two bases, their index types
have the same cardinalities. -/
theorem mk_eq_mk_of_basis (v : basis ι K V) (v' : basis ι' K V) :
  cardinal.lift.{w w'} (cardinal.mk ι) = cardinal.lift.{w' w} (cardinal.mk ι') :=
begin
  rw ←cardinal.lift_inj.{(max w w') v},
  rw [cardinal.lift_lift, cardinal.lift_lift],
  apply le_antisymm,
  { convert cardinal.lift_le.{v (max w w')}.2 (v.le_span v'.span_eq),
    { rw cardinal.lift_max.{w v w'},
      apply (cardinal.mk_range_eq_of_injective v.injective).symm, },
    { rw cardinal.lift_max.{w' v w},
      apply (cardinal.mk_range_eq_of_injective v'.injective).symm, }, },
  { convert cardinal.lift_le.{v (max w w')}.2 (v'.le_span v.span_eq),
    { rw cardinal.lift_max.{w' v w},
      apply (cardinal.mk_range_eq_of_injective v'.injective).symm, },
    { rw cardinal.lift_max.{w v w'},
      apply (cardinal.mk_range_eq_of_injective v.injective).symm, }, }
end

theorem mk_eq_mk_of_basis' {ι' : Type w} (v : basis ι K V) (v' : basis ι' K V) :
  cardinal.mk ι = cardinal.mk ι' :=
cardinal.lift_inj.1 $ mk_eq_mk_of_basis v v'

theorem basis.mk_eq_dim'' {ι : Type v} (v : basis ι K V) :
  cardinal.mk ι = module.rank K V :=
begin
  apply le_antisymm,
  { transitivity,
    swap,
    apply cardinal.le_sup,
    exact ⟨set.range v, by { convert v.reindex_range.linear_independent, ext, simp }⟩,
    exact (cardinal.eq_congr (equiv.of_injective v v.injective)).le, },
  { exact cardinal.sup_le.mpr (λ i,
      (cardinal.mk_le_mk_of_subset (basis.subset_extend i.2)).trans
        (mk_eq_mk_of_basis' (basis.extend i.2) v).le), },
end

attribute [irreducible] module.rank

theorem basis.mk_range_eq_dim (v : basis ι K V) :
  cardinal.mk (range v) = module.rank K V :=
v.reindex_range.mk_eq_dim''

theorem basis.mk_eq_dim (v : basis ι K V) :
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (module.rank K V) :=
by rw [←v.mk_range_eq_dim, cardinal.mk_range_eq_of_injective v.injective]

theorem {m} basis.mk_eq_dim' (v : basis ι K V) :
  cardinal.lift.{w (max v m)} (cardinal.mk ι) = cardinal.lift.{v (max w m)} (module.rank K V) :=
by simpa using v.mk_eq_dim

theorem dim_le {n : ℕ}
  (H : ∀ s : finset V, linear_independent K (λ i : s, (i : V)) → s.card ≤ n) :
  module.rank K V ≤ n :=
begin
  rw ← (basis.of_vector_space K V).mk_eq_dim'',
  refine cardinal.card_le_of (λ s, _),
  rw ← finset.card_map ⟨_, subtype.val_injective⟩,
  apply H,
  refine (of_vector_space_index.linear_independent K V).mono (λ y (h : y ∈ (s.map _).1), _),
  rw [← finset.mem_def, finset.mem_map] at h,
  rcases h with ⟨x, hx, rfl⟩,
  exact x.2
end

/-- If a vector space has a finite dimension, all bases are indexed by a finite type. -/
lemma basis.nonempty_fintype_index_of_dim_lt_omega {ι : Type*}
  (b : basis ι K V) (h : module.rank K V < cardinal.omega) :
  nonempty (fintype ι) :=
by rwa [← cardinal.lift_lt, ← b.mk_eq_dim,
        -- ensure `omega` has the correct universe
        cardinal.lift_omega, ← cardinal.lift_omega.{u_1 v},
        cardinal.lift_lt, cardinal.lt_omega_iff_fintype] at h

/-- If a vector space has a finite dimension, all bases are indexed by a finite type. -/
noncomputable def basis.fintype_index_of_dim_lt_omega {ι : Type*}
  (b : basis ι K V) (h : module.rank K V < cardinal.omega) :
  fintype ι :=
classical.choice (b.nonempty_fintype_index_of_dim_lt_omega h)

/-- If a vector space has a finite dimension, all bases are indexed by a finite set. -/
lemma basis.finite_index_of_dim_lt_omega {ι : Type*} {s : set ι}
  (b : basis s K V) (h : module.rank K V < cardinal.omega) :
  s.finite :=
b.nonempty_fintype_index_of_dim_lt_omega h

/-- If a vector space has a finite dimension, the index set of `basis.of_vector_space` is finite. -/
lemma basis.finite_of_vector_space_index_of_dim_lt_omega (h : module.rank K V < cardinal.omega) :
  (basis.of_vector_space_index K V).finite :=
(basis.of_vector_space K V).nonempty_fintype_index_of_dim_lt_omega h

variables [add_comm_group V'] [module K V']

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
theorem linear_equiv.lift_dim_eq (f : V ≃ₗ[K] V') :
  cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K V') :=
let b := basis.of_vector_space K V in
calc cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v v'} (cardinal.mk _) :
  congr_arg _ b.mk_eq_dim''.symm
... = cardinal.lift.{v' v} (module.rank K V') : (b.map f).mk_eq_dim

/-- Two linearly equivalent vector spaces have the same dimension. -/
theorem linear_equiv.dim_eq (f : V ≃ₗ[K] V₁) :
  module.rank K V = module.rank K V₁ :=
cardinal.lift_inj.1 f.lift_dim_eq

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_lift_dim_eq
  (cond : cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K V')) :
  nonempty (V ≃ₗ[K] V') :=
begin
  let B := basis.of_vector_space K V,
  let B' := basis.of_vector_space K V',
  have : cardinal.lift.{v v'} (cardinal.mk _) = cardinal.lift.{v' v} (cardinal.mk _),
    by rw [B.mk_eq_dim'', cond, B'.mk_eq_dim''],
  exact (cardinal.lift_mk_eq.{v v' 0}.1 this).map (B.equiv B')
end

/-- Two vector spaces are isomorphic if they have the same dimension. -/
theorem nonempty_linear_equiv_of_dim_eq (cond : module.rank K V = module.rank K V₁) :
  nonempty (V ≃ₗ[K] V₁) :=
nonempty_linear_equiv_of_lift_dim_eq $ congr_arg _ cond

section

variables (V V' V₁)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def linear_equiv.of_lift_dim_eq
  (cond : cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K V')) :
  V ≃ₗ[K] V' :=
classical.choice (nonempty_linear_equiv_of_lift_dim_eq cond)

/-- Two vector spaces are isomorphic if they have the same dimension. -/
def linear_equiv.of_dim_eq (cond : module.rank K V = module.rank K V₁) : V ≃ₗ[K] V₁ :=
classical.choice (nonempty_linear_equiv_of_dim_eq cond)

end

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem linear_equiv.nonempty_equiv_iff_lift_dim_eq :
  nonempty (V ≃ₗ[K] V') ↔
    cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K V') :=
⟨λ ⟨h⟩, linear_equiv.lift_dim_eq h, λ h, nonempty_linear_equiv_of_lift_dim_eq h⟩

/-- Two vector spaces are isomorphic if and only if they have the same dimension. -/
theorem linear_equiv.nonempty_equiv_iff_dim_eq :
  nonempty (V ≃ₗ[K] V₁) ↔ module.rank K V = module.rank K V₁ :=
⟨λ ⟨h⟩, linear_equiv.dim_eq h, λ h, nonempty_linear_equiv_of_dim_eq h⟩

@[simp] lemma dim_bot : module.rank K (⊥ : submodule K V) = 0 :=
begin
  letI := classical.dec_eq V,
  rw [← cardinal.lift_inj, ← (basis.empty (⊥ : submodule K V)).mk_eq_dim,
    cardinal.mk_pempty],
  apply_instance,
end

@[simp] lemma dim_top : module.rank K (⊤ : submodule K V) = module.rank K V :=
linear_equiv.dim_eq (linear_equiv.of_top _ rfl)

lemma dim_of_field (K : Type*) [field K] : module.rank K K = 1 :=
by rw [←cardinal.lift_inj, ← (basis.singleton punit K).mk_eq_dim, cardinal.mk_punit]

lemma dim_span {v : ι → V} (hv : linear_independent K v) :
  module.rank K ↥(span K (range v)) = cardinal.mk (range v) :=
by rw [←cardinal.lift_inj, ← (basis.span hv).mk_eq_dim,
    cardinal.mk_range_eq_of_injective (@linear_independent.injective ι K V v _ _ _ _ hv)]

lemma dim_span_set {s : set V} (hs : linear_independent K (λ x, x : s → V)) :
  module.rank K ↥(span K s) = cardinal.mk s :=
by { rw [← @set_of_mem_eq _ s, ← subtype.range_coe_subtype], exact dim_span hs }

lemma {m} cardinal_lift_le_dim_of_linear_independent
  {ι : Type w} {v : ι → V} (hv : linear_independent K v) :
  cardinal.lift.{w (max v m)} (cardinal.mk ι) ≤ cardinal.lift.{v (max w m)} (module.rank K V) :=
begin
  let v' := basis.sum_extend hv,
  rw [← cardinal.lift_umax, ← cardinal.lift_umax.{v}],
  simpa using le_trans
    (cardinal.lift_mk_le.{w _ (max v m)}.2 ⟨function.embedding.inl⟩)
    (le_of_eq $ basis.mk_eq_dim'.{_ _ _ (max w m)} v'),
end

lemma cardinal_le_dim_of_linear_independent
  {ι : Type v} {v : ι → V} (hv : linear_independent K v) :
  cardinal.mk ι ≤ module.rank K V :=
by simpa using cardinal_lift_le_dim_of_linear_independent hv

lemma cardinal_le_dim_of_linear_independent'
  {s : set V} (hs : linear_independent K (λ x, x : s → V)) :
  cardinal.mk s ≤ module.rank K V :=
cardinal_le_dim_of_linear_independent hs

lemma dim_span_le (s : set V) : module.rank K (span K s) ≤ cardinal.mk s :=
begin
  classical,
  rcases
    exists_linear_independent (linear_independent_empty K V) (set.empty_subset s)
    with ⟨b, hb, _, hsb, hlib⟩,
  have hsab : span K s = span K b,
    from span_eq_of_le _ hsb (span_le.2 (λ x hx, subset_span (hb hx))),
  convert cardinal.mk_le_mk_of_subset hb,
  rw [hsab, dim_span_set hlib]
end

lemma dim_span_of_finset (s : finset V) :
  module.rank K (span K (↑s : set V)) < cardinal.omega :=
calc module.rank K (span K (↑s : set V)) ≤ cardinal.mk (↑s : set V) : dim_span_le ↑s
                             ... = s.card : by rw [cardinal.finset_card, finset.coe_sort_coe]
                             ... < cardinal.omega : cardinal.nat_lt_omega _

theorem dim_prod : module.rank K (V × V₁) = module.rank K V + module.rank K V₁ :=
begin
  let b := basis.of_vector_space K V,
  let c := basis.of_vector_space K V₁,
  rw [← cardinal.lift_inj,
      ← (basis.prod b c).mk_eq_dim,
      cardinal.lift_add, cardinal.lift_mk,
      ← b.mk_eq_dim, ← c.mk_eq_dim,
      cardinal.lift_mk, cardinal.lift_mk,
      cardinal.add_def (ulift _)],
  exact cardinal.lift_inj.1 (cardinal.lift_mk_eq.2
      ⟨equiv.ulift.trans (equiv.sum_congr equiv.ulift equiv.ulift).symm ⟩),
end

end division_ring

section field
variables [field K] [add_comm_group V] [module K V] [add_comm_group V₁] [module K V₁]
variables [add_comm_group V'] [module K V']
variables {K V}

theorem dim_quotient_add_dim (p : submodule K V) :
  module.rank K p.quotient + module.rank K p = module.rank K V :=
by classical; exact let ⟨f⟩ := quotient_prod_linear_equiv p in dim_prod.symm.trans f.dim_eq

theorem dim_quotient_le (p : submodule K V) :
  module.rank K p.quotient ≤ module.rank K V :=
by { rw ← dim_quotient_add_dim p, exact self_le_add_right _ _ }

/-- rank-nullity theorem -/
theorem dim_range_add_dim_ker (f : V →ₗ[K] V₁) :
  module.rank K f.range + module.rank K f.ker = module.rank K V :=
begin
  haveI := λ (p : submodule K V), classical.dec_eq p.quotient,
  rw [← f.quot_ker_equiv_range.dim_eq, dim_quotient_add_dim]
end

lemma dim_range_le (f : V →ₗ[K] V₁) : module.rank K f.range ≤ module.rank K V :=
by { rw ← dim_range_add_dim_ker f, exact self_le_add_right _ _ }

lemma dim_map_le (f : V →ₗ[K] V₁) (p : submodule K V) : module.rank K (p.map f) ≤ module.rank K p :=
begin
  have h := dim_range_le (f.comp (submodule.subtype p)),
  rwa [linear_map.range_comp, range_subtype] at h,
end

lemma dim_range_of_surjective (f : V →ₗ[K] V') (h : surjective f) :
  module.rank K f.range = module.rank K V' :=
by rw [linear_map.range_eq_top.2 h, dim_top]

lemma dim_eq_of_surjective (f : V →ₗ[K] V₁) (h : surjective f) :
  module.rank K V = module.rank K V₁ + module.rank K f.ker :=
by rw [← dim_range_add_dim_ker f, ← dim_range_of_surjective f h]

lemma dim_le_of_surjective (f : V →ₗ[K] V₁) (h : surjective f) :
  module.rank K V₁ ≤ module.rank K V :=
by { rw [dim_eq_of_surjective f h], refine self_le_add_right _ _ }

lemma dim_eq_of_injective (f : V →ₗ[K] V₁) (h : injective f) :
  module.rank K V = module.rank K f.range :=
by rw [← dim_range_add_dim_ker f, linear_map.ker_eq_bot.2 h]; simp [dim_bot]

lemma dim_submodule_le (s : submodule K V) : module.rank K s ≤ module.rank K V :=
by { rw ← dim_quotient_add_dim s, exact self_le_add_left _ _ }

lemma dim_le_of_injective (f : V →ₗ[K] V₁) (h : injective f) :
  module.rank K V ≤ module.rank K V₁ :=
by { rw [dim_eq_of_injective f h], exact dim_submodule_le _ }

lemma dim_le_of_submodule (s t : submodule K V) (h : s ≤ t) :
  module.rank K s ≤ module.rank K t :=
dim_le_of_injective (of_le h) $ assume ⟨x, hx⟩ ⟨y, hy⟩ eq,
  subtype.eq $ show x = y, from subtype.ext_iff_val.1 eq

lemma linear_independent_le_dim
  {v : ι → V} (hv : linear_independent K v) :
  cardinal.lift.{w v} (cardinal.mk ι) ≤ cardinal.lift.{v w} (module.rank K V) :=
calc
  cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (cardinal.mk (set.range v)) :
     (cardinal.mk_range_eq_of_injective (linear_independent.injective hv)).symm
  ... = cardinal.lift.{v w} (module.rank K (submodule.span K (set.range v))) :
    by rw (dim_span hv).symm
  ... ≤ cardinal.lift.{v w} (module.rank K V) :
    cardinal.lift_le.2 (dim_submodule_le (submodule.span K _))

theorem {u₁} linear_independent_le_dim' {v : ι → V} (hs : linear_independent K v) :
  ((cardinal.mk ι).lift : cardinal.{(max w v u₁)}) ≤
    ((module.rank K V).lift : cardinal.{(max v w u₁)}) :=
cardinal.mk_range_eq_lift hs.injective ▸ dim_span hs ▸ cardinal.lift_le.2 (dim_submodule_le _)

section
variables [add_comm_group V₂] [module K V₂]
variables [add_comm_group V₃] [module K V₃]
open linear_map

/-- This is mostly an auxiliary lemma for `dim_sup_add_dim_inf_eq`. -/
lemma dim_add_dim_split
  (db : V₂ →ₗ[K] V) (eb : V₃ →ₗ[K] V) (cd : V₁ →ₗ[K] V₂) (ce : V₁ →ₗ[K] V₃)
  (hde : ⊤ ≤ db.range ⊔ eb.range)
  (hgd : ker cd = ⊥)
  (eq : db.comp cd = eb.comp ce)
  (eq₂ : ∀d e, db d = eb e → (∃c, cd c = d ∧ ce c = e)) :
  module.rank K V + module.rank K V₁ = module.rank K V₂ + module.rank K V₃ :=
have hf : surjective (coprod db eb),
begin
  refine (range_eq_top.1 $ top_unique $ _),
  rwa [← map_top, ← prod_top, map_coprod_prod, ←range_eq_map, ←range_eq_map]
end,
begin
  conv {to_rhs, rw [← dim_prod, dim_eq_of_surjective _ hf] },
  congr' 1,
  apply linear_equiv.dim_eq,
  refine linear_equiv.of_bijective _ _ _,
  { refine cod_restrict _ (prod cd (- ce)) _,
    { assume c,
      simp only [add_eq_zero_iff_eq_neg, linear_map.prod_apply, mem_ker,
        coprod_apply, neg_neg, map_neg, neg_apply],
      exact linear_map.ext_iff.1 eq c } },
  { rw [ker_cod_restrict, ker_prod, hgd, bot_inf_eq] },
  { rw [eq_top_iff, range_cod_restrict, ← map_le_iff_le_comap, map_top, range_subtype],
    rintros ⟨d, e⟩,
    have h := eq₂ d (-e),
    simp only [add_eq_zero_iff_eq_neg, linear_map.prod_apply, mem_ker, set_like.mem_coe,
      prod.mk.inj_iff, coprod_apply, map_neg, neg_apply, linear_map.mem_range] at ⊢ h,
    assume hde,
    rcases h hde with ⟨c, h₁, h₂⟩,
    refine ⟨c, h₁, _⟩,
    rw [h₂, _root_.neg_neg] }
end

lemma dim_sup_add_dim_inf_eq (s t : submodule K V) :
  module.rank K (s ⊔ t : submodule K V) + module.rank K (s ⊓ t : submodule K V) =
    module.rank K s + module.rank K t :=
dim_add_dim_split (of_le le_sup_left) (of_le le_sup_right) (of_le inf_le_left) (of_le inf_le_right)
  begin
    rw [← map_le_map_iff' (ker_subtype $ s ⊔ t), map_sup, map_top,
      ← linear_map.range_comp, ← linear_map.range_comp, subtype_comp_of_le, subtype_comp_of_le,
      range_subtype, range_subtype, range_subtype],
    exact le_refl _
  end
  (ker_of_le _ _ _)
  begin ext ⟨x, hx⟩, refl end
  begin
    rintros ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ eq,
    have : b₁ = b₂ := congr_arg subtype.val eq,
    subst this,
    exact ⟨⟨b₁, hb₁, hb₂⟩, rfl, rfl⟩
  end

lemma dim_add_le_dim_add_dim (s t : submodule K V) :
  module.rank K (s ⊔ t : submodule K V) ≤ module.rank K s + module.rank K t :=
by { rw [← dim_sup_add_dim_inf_eq], exact self_le_add_right _ _ }

end

section fintype
variable [fintype η]
variables [∀i, add_comm_group (φ i)] [∀i, module K (φ i)]

open linear_map

lemma dim_pi : module.rank K (Πi, φ i) = cardinal.sum (λi, module.rank K (φ i)) :=
begin
  let b := assume i, basis.of_vector_space K (φ i),
  let this : basis (Σ j, _) K (Π j, φ j) := pi.basis b,
  rw [←cardinal.lift_inj, ← this.mk_eq_dim],
  simp [λ i, (b i).mk_range_eq_dim.symm, cardinal.sum_mk]
end

lemma dim_fun {V η : Type u} [fintype η] [add_comm_group V] [module K V] :
  module.rank K (η → V) = fintype.card η * module.rank K V :=
by rw [dim_pi, cardinal.sum_const, cardinal.fintype_card]

lemma dim_fun_eq_lift_mul :
  module.rank K (η → V) = (fintype.card η : cardinal.{max u₁' v}) *
    cardinal.lift.{v u₁'} (module.rank K V) :=
by rw [dim_pi, cardinal.sum_const_eq_lift_mul, cardinal.fintype_card, cardinal.lift_nat_cast]

lemma dim_fun' : module.rank K (η → K) = fintype.card η :=
by rw [dim_fun_eq_lift_mul, dim_of_field K, cardinal.lift_one, mul_one, cardinal.nat_cast_inj]

lemma dim_fin_fun (n : ℕ) : module.rank K (fin n → K) = n :=
by simp [dim_fun']

end fintype

lemma exists_mem_ne_zero_of_ne_bot {s : submodule K V} (h : s ≠ ⊥) : ∃ b : V, b ∈ s ∧ b ≠ 0 :=
begin
  classical,
  by_contradiction hex,
  have : ∀x∈s, (x:V) = 0, { simpa only [not_exists, not_and, not_not, ne.def] using hex },
  exact (h $ bot_unique $ assume s hs, (submodule.mem_bot K).2 $ this s hs)
end

lemma exists_mem_ne_zero_of_dim_pos {s : submodule K V} (h : 0 < module.rank K s) :
  ∃ b : V, b ∈ s ∧ b ≠ 0 :=
exists_mem_ne_zero_of_ne_bot $ assume eq, by rw [eq, dim_bot] at h; exact lt_irrefl _ h

section rank

/-- `rank f` is the rank of a `linear_map f`, defined as the dimension of `f.range`. -/
def rank (f : V →ₗ[K] V') : cardinal := module.rank K f.range

lemma rank_le_domain (f : V →ₗ[K] V₁) : rank f ≤ module.rank K V :=
by { rw [← dim_range_add_dim_ker f], exact self_le_add_right _ _ }

lemma rank_le_range (f : V →ₗ[K] V₁) : rank f ≤ module.rank K V₁ :=
dim_submodule_le _

lemma rank_add_le (f g : V →ₗ[K] V') : rank (f + g) ≤ rank f + rank g :=
calc rank (f + g) ≤ module.rank K (f.range ⊔ g.range : submodule K V') :
  begin
    refine dim_le_of_submodule _ _ _,
    exact (linear_map.range_le_iff_comap.2 $ eq_top_iff'.2 $
      assume x, show f x + g x ∈ (f.range ⊔ g.range : submodule K V'), from
        mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩)
  end
  ... ≤ rank f + rank g : dim_add_le_dim_add_dim _ _

@[simp] lemma rank_zero : rank (0 : V →ₗ[K] V') = 0 :=
by rw [rank, linear_map.range_zero, dim_bot]

lemma rank_finset_sum_le {η} (s : finset η) (f : η → V →ₗ[K] V') :
  rank (∑ d in s, f d) ≤ ∑ d in s, rank (f d) :=
@finset.sum_hom_rel _ _ _ _ _ (λa b, rank a ≤ b) f (λ d, rank (f d)) s (le_of_eq rank_zero)
      (λ i g c h, le_trans (rank_add_le _ _) (add_le_add_left h _))

variables [add_comm_group V''] [module K V'']

lemma rank_comp_le1 (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') : rank (f.comp g) ≤ rank f :=
begin
  refine dim_le_of_submodule _ _ _,
  rw [linear_map.range_comp],
  exact linear_map.map_le_range,
end

variables [add_comm_group V'₁] [module K V'₁]

lemma rank_comp_le2 (g : V →ₗ[K] V') (f : V' →ₗ V'₁) : rank (f.comp g) ≤ rank g :=
by rw [rank, rank, linear_map.range_comp]; exact dim_map_le _ _

end rank

lemma dim_zero_iff_forall_zero : module.rank K V = 0 ↔ ∀ x : V, x = 0 :=
begin
  split,
  { intros h x,
    have card_mk_range := (basis.of_vector_space K V).mk_range_eq_dim,
    rw [h, cardinal.mk_emptyc_iff, coe_of_vector_space, subtype.range_coe] at card_mk_range,
    simpa [card_mk_range] using (of_vector_space K V).mem_span x },
  { intro h,
    have : (⊤ : submodule K V) = ⊥,
    { ext x, simp [h x] },
    rw [←dim_top, this, dim_bot] }
end

lemma dim_zero_iff : module.rank K V = 0 ↔ subsingleton V :=
dim_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm

/-- The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensional.

See also `finite_dimensional.fin_basis`.
-/
def basis.of_dim_eq_zero {ι : Type*} [is_empty ι] (hV : module.rank K V = 0) :
  basis ι K V :=
begin
  haveI : subsingleton V := dim_zero_iff.1 hV,
  exact basis.empty _
end

@[simp] lemma basis.of_dim_eq_zero_apply {ι : Type*} [is_empty ι]
  (hV : module.rank K V = 0) (i : ι) :
  basis.of_dim_eq_zero hV i = 0 :=
rfl


lemma dim_pos_iff_exists_ne_zero : 0 < module.rank K V ↔ ∃ x : V, x ≠ 0 :=
begin
  rw ←not_iff_not,
  simpa using dim_zero_iff_forall_zero
end

lemma dim_pos_iff_nontrivial : 0 < module.rank K V ↔ nontrivial V :=
dim_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm

lemma dim_pos [h : nontrivial V] : 0 < module.rank K V :=
dim_pos_iff_nontrivial.2 h

lemma le_dim_iff_exists_linear_independent {c : cardinal} :
  c ≤ module.rank K V ↔ ∃ s : set V, cardinal.mk s = c ∧ linear_independent K (coe : s → V) :=
begin
  split,
  { intro h,
    let t := basis.of_vector_space K V,
    rw [← t.mk_eq_dim'', cardinal.le_mk_iff_exists_subset] at h,
    rcases h with ⟨s, hst, hsc⟩,
    exact ⟨s, hsc, (of_vector_space_index.linear_independent K V).mono hst⟩ },
  { rintro ⟨s, rfl, si⟩,
    exact cardinal_le_dim_of_linear_independent si }
end

lemma le_dim_iff_exists_linear_independent_finset {n : ℕ} :
  ↑n ≤ module.rank K V ↔
    ∃ s : finset V, s.card = n ∧ linear_independent K (coe : (s : set V) → V) :=
begin
  simp only [le_dim_iff_exists_linear_independent, cardinal.mk_eq_nat_iff_finset],
  split,
  { rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩,
    exact ⟨t, rfl, si⟩ },
  { rintro ⟨s, rfl, si⟩,
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩ }
end

lemma le_rank_iff_exists_linear_independent {c : cardinal} {f : V →ₗ[K] V'} :
  c ≤ rank f ↔
  ∃ s : set V, cardinal.lift.{v v'} (cardinal.mk s) = cardinal.lift.{v' v} c ∧
    linear_independent K (λ x : s, f x) :=
begin
  rcases f.range_restrict.exists_right_inverse_of_surjective f.range_range_restrict with ⟨g, hg⟩,
  have fg : left_inverse f.range_restrict g, from linear_map.congr_fun hg,
  refine ⟨λ h, _, _⟩,
  { rcases le_dim_iff_exists_linear_independent.1 h with ⟨s, rfl, si⟩,
    refine ⟨g '' s, cardinal.mk_image_eq_lift _ _ fg.injective, _⟩,
    replace fg : ∀ x, f (g x) = x, by { intro x, convert congr_arg subtype.val (fg x) },
    replace si : linear_independent K (λ x : s, f (g x)),
      by simpa only [fg] using si.map' _ (ker_subtype _),
    exact si.image_of_comp s g f },
  { rintro ⟨s, hsc, si⟩,
    have : linear_independent K (λ x : s, f.range_restrict x),
      from linear_independent.of_comp (f.range.subtype) (by convert si),
    convert cardinal_le_dim_of_linear_independent this.image,
    rw [← cardinal.lift_inj, ← hsc, cardinal.mk_image_eq_of_inj_on_lift],
    exact inj_on_iff_injective.2 this.injective }
end

lemma le_rank_iff_exists_linear_independent_finset {n : ℕ} {f : V →ₗ[K] V'} :
  ↑n ≤ rank f ↔ ∃ s : finset V, s.card = n ∧ linear_independent K (λ x : (s : set V), f x) :=
begin
  simp only [le_rank_iff_exists_linear_independent, cardinal.lift_nat_cast,
    cardinal.lift_eq_nat_iff, cardinal.mk_eq_nat_iff_finset],
  split,
  { rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩,
    exact ⟨t, rfl, si⟩ },
  { rintro ⟨s, rfl, si⟩,
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩ }
end

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
lemma dim_le_one_iff : module.rank K V ≤ 1 ↔ ∃ v₀ : V, ∀ v, ∃ r : K, r • v₀ = v :=
begin
  let b := basis.of_vector_space K V,
  split,
  { intro hd,
    rw [← b.mk_eq_dim'', cardinal.le_one_iff_subsingleton, subsingleton_coe] at hd,
    rcases eq_empty_or_nonempty (of_vector_space_index K V) with hb | ⟨⟨v₀, hv₀⟩⟩,
    { use 0,
      have h' : ∀ v : V, v = 0, { simpa [hb, submodule.eq_bot_iff] using b.span_eq.symm },
      intro v,
      simp [h' v] },
    { use v₀,
      have h' : (K ∙ v₀) = ⊤, { simpa [hd.eq_singleton_of_mem hv₀] using b.span_eq },
      intro v,
      have hv : v ∈ (⊤ : submodule K V) := mem_top,
      rwa [←h', mem_span_singleton] at hv } },
  { rintros ⟨v₀, hv₀⟩,
    have h : (K ∙ v₀) = ⊤,
    { ext, simp [mem_span_singleton, hv₀] },
    rw [←dim_top, ←h],
    convert dim_span_le _,
    simp }
end

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
lemma dim_submodule_le_one_iff (s : submodule K V) : module.rank K s ≤ 1 ↔ ∃ v₀ ∈ s, s ≤ K ∙ v₀ :=
begin
  simp_rw [dim_le_one_iff, le_span_singleton_iff],
  split,
  { rintro ⟨⟨v₀, hv₀⟩, h⟩,
    use [v₀, hv₀],
    intros v hv,
    obtain ⟨r, hr⟩ := h ⟨v, hv⟩,
    use r,
    simp_rw [subtype.ext_iff, coe_smul, submodule.coe_mk] at hr,
    exact hr },
  { rintro ⟨v₀, hv₀, h⟩,
    use ⟨v₀, hv₀⟩,
    rintro ⟨v, hv⟩,
    obtain ⟨r, hr⟩ := h v hv,
    use r,
    simp_rw [subtype.ext_iff, coe_smul, submodule.coe_mk],
    exact hr }
end

/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
lemma dim_submodule_le_one_iff' (s : submodule K V) : module.rank K s ≤ 1 ↔ ∃ v₀, s ≤ K ∙ v₀ :=
begin
  rw dim_submodule_le_one_iff,
  split,
  { rintros ⟨v₀, hv₀, h⟩,
    exact ⟨v₀, h⟩ },
  { rintros ⟨v₀, h⟩,
    by_cases hw : ∃ w : V, w ∈ s ∧ w ≠ 0,
    { rcases hw with ⟨w, hw, hw0⟩,
      use [w, hw],
      rcases mem_span_singleton.1 (h hw) with ⟨r', rfl⟩,
      have h0 : r' ≠ 0,
      { rintro rfl,
        simpa using hw0 },
      rwa span_singleton_smul_eq _ h0 },
    { push_neg at hw,
      rw ←submodule.eq_bot_iff at hw,
      simp [hw] } }
end

end field

end module

section unconstrained_universes

variables {E : Type v'}
variables [division_ring K] [add_comm_group V] [module K V]
          [add_comm_group E] [module K E]
open module

/-- Version of linear_equiv.dim_eq without universe constraints. -/
theorem linear_equiv.dim_eq_lift (f : V ≃ₗ[K] E) :
  cardinal.lift.{v v'} (module.rank K V) = cardinal.lift.{v' v} (module.rank K E) :=
begin
  let b := basis.of_vector_space K V,
  rw [← cardinal.lift_inj.1 b.mk_eq_dim, ← (b.map f).mk_eq_dim, cardinal.lift_mk],
end

end unconstrained_universes
