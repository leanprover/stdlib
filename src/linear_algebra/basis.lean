/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import linear_algebra.linear_independent
import linear_algebra.projection

/-!

# Bases

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `is_basis R v` states that the vector family `v` is a basis, i.e. it is linearly independent and
  spans the entire space.

* `is_basis.repr hv x` is the basis version of `linear_independent.repr hv x`. It returns the
  linear combination representing `x : M` on a basis `v` of `M` (using classical choice).
  The argument `hv` must be a proof that `is_basis R v`. `is_basis.repr hv` is given as a linear
  map as well.

* `is_basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis `v : ι → M₁`, given `hv : is_basis R v`.

## Main statements

* `is_basis.ext` states that two linear maps are equal if they coincide on a basis.

* `exists_is_basis` states that every vector space has a basis.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent. For bases, this is useful as well because we can easily derive ordered bases by using an
ordered index type `ι`.

## Tags

basis, bases

-/

noncomputable theory

universe u

open function set submodule
open_locale classical big_operators

variables {ι : Type*} {ι' : Type*} {R : Type*} {K : Type*}
variables {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}

section module

open linear_map

variables {v : ι → M}
variables [ring R] [add_comm_group M] [add_comm_group M'] [add_comm_group M'']
variables [module R M] [module R M'] [module R M'']
variables {a b : R} {x y : M}

variables (R) (v)
/-- A family of vectors is a basis if it is linearly independent and all vectors are in the span. -/
def is_basis := linear_independent R v ∧ span R (range v) = ⊤
variables {R} {v}

section is_basis
variables {s t : set M} (hv : is_basis R v)

lemma is_basis.mem_span (hv : is_basis R v) : ∀ x, x ∈ span R (range v) := eq_top_iff'.1 hv.2

lemma is_basis.comp (hv : is_basis R v) (f : ι' → ι) (hf : bijective f) :
  is_basis R (v ∘ f) :=
begin
  split,
  { apply hv.1.comp f hf.1 },
  { rw[set.range_comp, range_iff_surjective.2 hf.2, image_univ, hv.2] }
end

lemma is_basis.injective [nontrivial R] (hv : is_basis R v) : injective v :=
  λ x y h, linear_independent.injective hv.1 h

lemma is_basis.range (hv : is_basis R v) : is_basis R (λ x, x : range v → M) :=
⟨hv.1.to_subtype_range, by { convert hv.2, ext i, exact ⟨λ ⟨p, hp⟩, hp ▸ p.2, λ hi, ⟨⟨i, hi⟩, rfl⟩⟩ }⟩

/-- Given a basis, any vector can be written as a linear combination of the basis vectors. They are
given by this linear map. This is one direction of `module_equiv_finsupp`. -/
def is_basis.repr : M →ₗ (ι →₀ R) :=
(hv.1.repr).comp (linear_map.id.cod_restrict _ hv.mem_span)

lemma is_basis.total_repr (x) : finsupp.total ι M R v (hv.repr x) = x :=
hv.1.total_repr ⟨x, _⟩

lemma is_basis.total_comp_repr : (finsupp.total ι M R v).comp hv.repr = linear_map.id :=
linear_map.ext hv.total_repr

lemma is_basis.ext {f g : M →ₗ[R] M'} (hv : is_basis R v) (h : ∀i, f (v i) = g (v i)) : f = g :=
linear_map.ext_on_range hv.2 h

lemma is_basis.repr_ker : hv.repr.ker = ⊥ :=
linear_map.ker_eq_bot.2 $ left_inverse.injective hv.total_repr

lemma is_basis.repr_range : hv.repr.range = finsupp.supported R R univ :=
by rw [is_basis.repr, linear_map.range, submodule.map_comp,
  linear_map.map_cod_restrict, submodule.map_id, comap_top, map_top, hv.1.repr_range,
  finsupp.supported_univ]

lemma is_basis.repr_total (x : ι →₀ R) (hx : x ∈ finsupp.supported R R (univ : set ι)) :
  hv.repr (finsupp.total ι M R v x) = x :=
begin
  rw [← hv.repr_range, linear_map.mem_range] at hx,
  cases hx with w hw,
  rw [← hw, hv.total_repr],
end

lemma is_basis.repr_eq_single {i} : hv.repr (v i) = finsupp.single i 1 :=
by apply hv.1.repr_eq_single; simp

@[simp]
lemma is_basis.repr_self_apply (i j : ι) : hv.repr (v i) j = if i = j then 1 else 0 :=
by rw [hv.repr_eq_single, finsupp.single_apply]

lemma is_basis.repr_eq_iff {f : M →ₗ[R] (ι →₀ R)} :
  hv.repr = f ↔ ∀ i, f (v i) = finsupp.single i 1 :=
begin
  split,
  { rintros rfl i,
    exact hv.repr_eq_single },
  intro h,
  refine hv.ext (λ _, _),
  rw [h, hv.repr_eq_single]
end

lemma is_basis.repr_apply_eq {f : M → ι → R}
  (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x)
  (f_eq : ∀ i, f (v i) = finsupp.single i 1) (x : M) (i : ι) :
  hv.repr x i = f x i :=
begin
  let f_i : M →ₗ[R] R :=
  { to_fun := λ x, f x i,
    map_add' := λ _ _, by rw [hadd, pi.add_apply],
    map_smul' := λ _ _, by rw [hsmul, pi.smul_apply] },
  show (finsupp.lapply i).comp hv.repr x = f_i x,
  congr' 1,
  refine hv.ext (λ j, _),
  show hv.repr (v j) i = f (v j) i,
  rw [hv.repr_eq_single, f_eq]
end

lemma is_basis.range_repr_self (i : ι) :
  hv.range.repr (v i) = finsupp.single ⟨v i, mem_range_self i⟩ 1 :=
hv.1.to_subtype_range.repr_eq_single _ _ rfl

@[simp] lemma is_basis.range_repr (i : ι) :
  hv.range.repr x ⟨v i, mem_range_self i⟩ = hv.repr x i :=
begin
  by_cases H : (0 : R) = 1,
  { exact eq_of_zero_eq_one H _ _ },
  refine (hv.repr_apply_eq _ _ _ x i).symm,
  { intros x y,
    ext j,
    rw [linear_map.map_add, finsupp.add_apply],
    refl },
  { intros c x,
    ext j,
    rw [linear_map.map_smul, finsupp.smul_apply],
    refl },
  { intro i,
    ext j,
    haveI : nontrivial R := ⟨⟨0, 1, H⟩⟩,
    simp [hv.range_repr_self, finsupp.single_apply, hv.injective] }
end

/-- Construct a linear map given the value at the basis. -/
def is_basis.constr (f : ι → M') : M →ₗ[R] M' :=
(finsupp.total M' M' R id).comp $ (finsupp.lmap_domain R R f).comp hv.repr

theorem is_basis.constr_apply (f : ι → M') (x : M) :
  (hv.constr f : M → M') x = (hv.repr x).sum (λb a, a • f b) :=
by dsimp [is_basis.constr] ;
   rw [finsupp.total_apply, finsupp.sum_map_domain_index]; simp [add_smul]

@[simp] lemma constr_basis {f : ι → M'} {i : ι} (hv : is_basis R v) :
  (hv.constr f : M → M') (v i) = f i :=
by simp [is_basis.constr_apply, hv.repr_eq_single, finsupp.sum_single_index]

lemma constr_eq {g : ι → M'} {f : M →ₗ[R] M'} (hv : is_basis R v)
  (h : ∀i, g i = f (v i)) : hv.constr g = f :=
hv.ext $ λ i, (constr_basis hv).trans (h i)

lemma constr_self (f : M →ₗ[R] M') : hv.constr (λ i, f (v i)) = f :=
constr_eq hv $ λ x, rfl

lemma constr_zero (hv : is_basis R v) : hv.constr (λi, (0 : M')) = 0 :=
constr_eq hv $ λ x, rfl

lemma constr_add {g f : ι → M'} (hv : is_basis R v) :
  hv.constr (λi, f i + g i) = hv.constr f + hv.constr g :=
constr_eq hv $ λ b, by simp

lemma constr_neg {f : ι → M'} (hv : is_basis R v) : hv.constr (λi, - f i) = - hv.constr f :=
constr_eq hv $ λ b, by simp

lemma constr_sub {g f : ι → M'} (hs : is_basis R v) :
  hv.constr (λi, f i - g i) = hs.constr f - hs.constr g :=
by simp [sub_eq_add_neg, constr_add, constr_neg]

-- this only works on functions if `R` is a commutative ring
lemma constr_smul {ι R M} [comm_ring R] [add_comm_group M] [module R M]
  {v : ι → R} {f : ι → M} {a : R} (hv : is_basis R v) :
  hv.constr (λb, a • f b) = a • hv.constr f :=
constr_eq hv $ by simp [constr_basis hv] {contextual := tt}

lemma constr_range [nonempty ι] (hv : is_basis R v) {f : ι  → M'} :
  (hv.constr f).range = span R (range f) :=
by rw [is_basis.constr, linear_map.range_comp, linear_map.range_comp, is_basis.repr_range,
    finsupp.lmap_domain_supported, ←set.image_univ, ←finsupp.span_eq_map_total, image_id]

/-- Canonical equivalence between a module and the linear combinations of basis vectors. -/
def module_equiv_finsupp (hv : is_basis R v) : M ≃ₗ[R] ι →₀ R :=
(hv.1.total_equiv.trans (linear_equiv.of_top _ hv.2)).symm

@[simp] theorem module_equiv_finsupp_apply_basis (hv : is_basis R v) (i : ι) :
  module_equiv_finsupp hv (v i) = finsupp.single i 1 :=
(linear_equiv.symm_apply_eq _).2 $ by simp [linear_independent.total_equiv]

/-- Isomorphism between the two modules, given two modules `M` and `M'` with respective bases
`v` and `v'` and a bijection between the indexing sets of the two bases. -/
def linear_equiv_of_is_basis {v : ι → M} {v' : ι' → M'} (hv : is_basis R v) (hv' : is_basis R v')
  (e : ι ≃ ι') : M ≃ₗ[R] M' :=
{ inv_fun := hv'.constr (v ∘ e.symm),
  left_inv := have (hv'.constr (v ∘ e.symm)).comp (hv.constr (v' ∘ e)) = linear_map.id,
      from hv.ext $ by simp,
    λ x, congr_arg (λ h : M →ₗ[R] M, h x) this,
  right_inv := have (hv.constr (v' ∘ e)).comp (hv'.constr (v ∘ e.symm)) = linear_map.id,
      from hv'.ext $ by simp,
    λ y, congr_arg (λ h : M' →ₗ[R] M', h y) this,
  ..hv.constr (v' ∘ e) }

/-- Isomorphism between the two modules, given two modules `M` and `M'` with respective bases
`v` and `v'` and a bijection between the two bases. -/
def linear_equiv_of_is_basis' {v : ι → M} {v' : ι' → M'} (f : M → M') (g : M' → M)
  (hv : is_basis R v) (hv' : is_basis R v')
  (hf : ∀i, f (v i) ∈ range v') (hg : ∀i, g (v' i) ∈ range v)
  (hgf : ∀i, g (f (v i)) = v i) (hfg : ∀i, f (g (v' i)) = v' i) :
  M ≃ₗ M' :=
{ inv_fun := hv'.constr (g ∘ v'),
  left_inv :=
    have (hv'.constr (g ∘ v')).comp (hv.constr (f ∘ v)) = linear_map.id,
    from hv.ext $ λ i, exists.elim (hf i)
      (λ i' hi', by simp [constr_basis, hi'.symm]; rw [hi', hgf]),
    λ x, congr_arg (λ h:M →ₗ[R] M, h x) this,
  right_inv :=
    have (hv.constr (f ∘ v)).comp (hv'.constr (g ∘ v')) = linear_map.id,
    from hv'.ext $ λ i', exists.elim (hg i')
      (λ i hi, by simp [constr_basis, hi.symm]; rw [hi, hfg]),
    λ y, congr_arg (λ h:M' →ₗ[R] M', h y) this,
  ..hv.constr (f ∘ v) }

@[simp] lemma linear_equiv_of_is_basis_comp {ι'' : Type*} {v : ι → M} {v' : ι' → M'}
  {v'' : ι'' → M''} (hv : is_basis R v) (hv' : is_basis R v') (hv'' : is_basis R v'')
  (e : ι ≃ ι') (f : ι' ≃ ι'' ) :
  (linear_equiv_of_is_basis hv hv' e).trans (linear_equiv_of_is_basis hv' hv'' f) =
  linear_equiv_of_is_basis hv hv'' (e.trans f) :=
begin
  apply linear_equiv.injective_to_linear_map,
  apply hv.ext,
  intros i,
  simp [linear_equiv_of_is_basis]
end

@[simp] lemma linear_equiv_of_is_basis_refl :
  linear_equiv_of_is_basis hv hv (equiv.refl ι) = linear_equiv.refl R M :=
begin
  apply linear_equiv.injective_to_linear_map,
  apply hv.ext,
  intros i,
  simp [linear_equiv_of_is_basis]
end

lemma linear_equiv_of_is_basis_trans_symm (e : ι ≃ ι') {v' : ι' → M'} (hv' : is_basis R v') :
  (linear_equiv_of_is_basis hv hv' e).trans (linear_equiv_of_is_basis hv' hv e.symm) = linear_equiv.refl R M :=
by simp

lemma linear_equiv_of_is_basis_symm_trans (e : ι ≃ ι') {v' : ι' → M'} (hv' : is_basis R v') :
  (linear_equiv_of_is_basis hv' hv e.symm).trans (linear_equiv_of_is_basis hv hv' e) = linear_equiv.refl R M' :=
by simp

lemma is_basis_inl_union_inr {v : ι → M} {v' : ι' → M'}
  (hv : is_basis R v) (hv' : is_basis R v') :
  is_basis R (sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) :=
begin
  split,
  apply linear_independent_inl_union_inr' hv.1 hv'.1,
  rw [sum.elim_range, span_union,
      set.range_comp, span_image (inl R M M'), hv.2,  map_top,
      set.range_comp, span_image (inr R M M'), hv'.2, map_top],
  exact linear_map.sup_range_inl_inr
end

end is_basis

lemma is_basis_singleton_one (R : Type*) [unique ι] [ring R] :
  is_basis R (λ (_ : ι), (1 : R)) :=
begin
  split,
  { refine linear_independent_iff.2 (λ l hl, _),
    rw [finsupp.total_unique, smul_eq_mul, mul_one] at hl,
    exact finsupp.unique_ext hl },
  { refine top_unique (λ _ _, _),
    simp only [mem_span_singleton, range_const, mul_one, exists_eq, smul_eq_mul] }
end

protected lemma linear_equiv.is_basis (hs : is_basis R v)
  (f : M ≃ₗ[R] M') : is_basis R (f ∘ v) :=
begin
  split,
  { simpa only using hs.1.map' (f : M →ₗ[R] M') f.ker },
  { rw [set.range_comp, ← linear_equiv.coe_coe, span_image, hs.2, map_top, f.range] }
end

lemma is_basis_span (hs : linear_independent R v) :
  @is_basis ι R (span R (range v)) (λ i : ι, ⟨v i, subset_span (mem_range_self _)⟩) _ _ _ :=
begin
split,
{ apply linear_independent_span hs },
{ rw eq_top_iff',
  intro x,
  have h₁ : subtype.val '' set.range (λ i, subtype.mk (v i) _) = range v,
    by rw ←set.range_comp,
  have h₂ : map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _)))
              = span R (range v),
    by rw [←span_image, submodule.subtype_eq_val, h₁],
  have h₃ : (x : M) ∈ map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _))),
    by rw h₂; apply subtype.mem x,
  rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩,
  have h_x_eq_y : x = y,
    by rw [subtype.ext_iff, ← hy₂]; simp,
  rw h_x_eq_y,
  exact hy₁ }
end

lemma is_basis_empty (h_empty : ¬ nonempty ι) (h : ∀x:M, x = 0) : is_basis R (λ x : ι, (0 : M)) :=
⟨ linear_independent_empty_type h_empty,
  eq_top_iff'.2 $ assume x, (h x).symm ▸ submodule.zero_mem _ ⟩

lemma is_basis_empty_bot (h_empty : ¬ nonempty ι) :
  is_basis R (λ _ : ι, (0 : (⊥ : submodule R M))) :=
begin
  apply is_basis_empty h_empty,
  intro x,
  apply subtype.ext_iff_val.2,
  exact (submodule.mem_bot R).1 (subtype.mem x),
end

open fintype
variables [fintype ι] (h : is_basis R v)

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def is_basis.equiv_fun : M ≃ₗ[R] (ι → R) :=
linear_equiv.trans (module_equiv_finsupp h)
  { to_fun := finsupp.to_fun,
    map_add' := λ x y, by ext; exact finsupp.add_apply,
    map_smul' := λ x y, by ext; exact finsupp.smul_apply,
    ..finsupp.equiv_fun_on_fintype }

/-- A module over a finite ring that admits a finite basis is finite. -/
def module.fintype_of_fintype [fintype R] : fintype M :=
fintype.of_equiv _ h.equiv_fun.to_equiv.symm

theorem module.card_fintype [fintype R] [fintype M] :
  card M = (card R) ^ (card ι) :=
calc card M = card (ι → R)    : card_congr h.equiv_fun.to_equiv
        ... = card R ^ card ι : card_fun

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp] lemma is_basis.equiv_fun_symm_apply (x : ι → R) :
  h.equiv_fun.symm x = ∑ i, x i • v i :=
begin
  change finsupp.sum
      ((finsupp.equiv_fun_on_fintype.symm : (ι → R) ≃ (ι →₀ R)) x) (λ (i : ι) (a : R), a • v i)
    = ∑ i, x i • v i,
  dsimp [finsupp.equiv_fun_on_fintype, finsupp.sum],
  rw finset.sum_filter,
  refine finset.sum_congr rfl (λi hi, _),
  by_cases H : x i = 0; simp [H]
end

lemma is_basis.equiv_fun_apply (u : M) : h.equiv_fun u = h.repr u := rfl

lemma is_basis.equiv_fun_total (u : M) : ∑ i, h.equiv_fun u i • v i = u:=
begin
  conv_rhs { rw ← h.total_repr u },
  simp [finsupp.total_apply, finsupp.sum_fintype, h.equiv_fun_apply]
end

@[simp]
lemma is_basis.equiv_fun_self (i j : ι) : h.equiv_fun (v i) j = if i = j then 1 else 0 :=
by { rw [h.equiv_fun_apply, h.repr_self_apply] }

@[simp] theorem is_basis.constr_apply_fintype (f : ι → M') (x : M) :
  (h.constr f : M → M') x = ∑ i, (h.equiv_fun x i) • f i :=
by simp [h.constr_apply, h.equiv_fun_apply, finsupp.sum_fintype]

end module

section vector_space

variables [field K] [add_comm_group V] [add_comm_group V'] [vector_space K V] [vector_space K V']
variables {v : ι → V} {s t : set V} {x y z : V}

include K

open submodule

lemma exists_subset_is_basis (hs : linear_independent K (λ x, x : s → V)) :
  ∃b, s ⊆ b ∧ is_basis K (coe : b → V) :=
let ⟨b, hb₀, hx, hb₂, hb₃⟩ := exists_linear_independent hs (@subset_univ _ _) in
⟨ b, hx,
  @linear_independent.restrict_of_comp_subtype _ _ _ id _ _ _ _ hb₃,
  by simp; exact eq_top_iff.2 hb₂⟩

lemma exists_sum_is_basis (hs : linear_independent K v) :
  ∃ (ι' : Type u) (v' : ι' → V), is_basis K (sum.elim v v') :=
begin
  -- This is a hack: we jump through hoops to reuse `exists_subset_is_basis`.
  let s := set.range v,
  let e : ι ≃ s := equiv.set.range v hs.injective,
  have : (λ x, x : s → V) = v ∘ e.symm := by { funext, dsimp, rw [equiv.set.apply_range_symm v], },
  have : linear_independent K (λ x, x : s → V),
  { rw this,
    exact linear_independent.comp hs _ (e.symm.injective), },
  obtain ⟨b, ss, is⟩ := exists_subset_is_basis this,
  let e' : ι ⊕ (b \ s : set V) ≃ b :=
  calc ι ⊕ (b \ s : set V) ≃ s ⊕ (b \ s : set V) : equiv.sum_congr e (equiv.refl _)
                       ... ≃ b                   : equiv.set.sum_diff_subset ss,
  refine ⟨(b \ s : set V), λ x, x.1, _⟩,
  convert is_basis.comp is e' _,
  { funext x,
    cases x; simp; refl, },
  { exact e'.bijective, },
end

variables (K V)
lemma exists_is_basis : ∃b : set V, is_basis K (λ i, i : b → V) :=
let ⟨b, _, hb⟩ := exists_subset_is_basis (linear_independent_empty K V : _) in ⟨b, hb⟩
variables {K V}

lemma linear_map.exists_left_inverse_of_injective (f : V →ₗ[K] V')
  (hf_inj : f.ker = ⊥) : ∃g:V' →ₗ V, g.comp f = linear_map.id :=
begin
  rcases exists_is_basis K V with ⟨B, hB⟩,
  have hB₀ : _ := hB.1.to_subtype_range,
  have : linear_independent K (λ x, x : f '' B → V'),
  { have h₁ := hB₀.image_subtype
      (show disjoint (span K (range (λ i : B, i.val))) (linear_map.ker f), by simp [hf_inj]),
    rwa subtype.range_coe at h₁ },
  rcases exists_subset_is_basis this with ⟨C, BC, hC⟩,
  haveI : inhabited V := ⟨0⟩,
  use hC.constr (C.restrict (inv_fun f)),
  refine hB.ext (λ b, _),
  rw image_subset_iff at BC,
  have : f b = (⟨f b, BC b.2⟩ : C) := rfl,
  dsimp,
  rw [this, constr_basis hC],
  exact left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _
end

lemma submodule.exists_is_compl (p : submodule K V) : ∃ q : submodule K V, is_compl p q :=
let ⟨f, hf⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype in
⟨f.ker, linear_map.is_compl_of_proj $ linear_map.ext_iff.1 hf⟩

lemma linear_map.exists_right_inverse_of_surjective (f : V →ₗ[K] V')
  (hf_surj : f.range = ⊤) : ∃g:V' →ₗ V, f.comp g = linear_map.id :=
begin
  rcases exists_is_basis K V' with ⟨C, hC⟩,
  haveI : inhabited V := ⟨0⟩,
  use hC.constr (C.restrict (inv_fun f)),
  refine hC.ext (λ c, _),
  simp [constr_basis hC, right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) c]
end

open submodule linear_map

theorem quotient_prod_linear_equiv (p : submodule K V) :
  nonempty ((p.quotient × p) ≃ₗ[K] V) :=
let ⟨q, hq⟩ := p.exists_is_compl in nonempty.intro $
((quotient_equiv_of_is_compl p q hq).prod (linear_equiv.refl _ _)).trans
  (prod_equiv_of_is_compl q p hq.symm)

open fintype
variables (K) (V)

theorem vector_space.card_fintype [fintype K] [fintype V] :
  ∃ n : ℕ, card V = (card K) ^ n :=
exists.elim (exists_is_basis K V) $ λ b hb, ⟨card b, module.card_fintype hb⟩

end vector_space

namespace pi
open set linear_map

section module
variables {η : Type*} {ιs : η → Type*} {Ms : η → Type*}
variables [ring R] [∀i, add_comm_group (Ms i)] [∀i, module R (Ms i)]

lemma linear_independent_std_basis [decidable_eq η]
  (v : Πj, ιs j → (Ms j)) (hs : ∀i, linear_independent R (v i)) :
  linear_independent R (λ (ji : Σ j, ιs j), std_basis R Ms ji.1 (v ji.1 ji.2)) :=
begin
  have hs' : ∀j : η, linear_independent R (λ i : ιs j, std_basis R Ms j (v j i)),
  { intro j,
    exact (hs j).map' _ (ker_std_basis _ _ _) },
  apply linear_independent_Union_finite hs',
  { assume j J _ hiJ,
    simp [(set.Union.equations._eqn_1 _).symm, submodule.span_image, submodule.span_Union],
    have h₀ : ∀ j, span R (range (λ (i : ιs j), std_basis R Ms j (v j i)))
        ≤ range (std_basis R Ms j),
    { intro j,
      rw [span_le, linear_map.range_coe],
      apply range_comp_subset_range },
    have h₁ : span R (range (λ (i : ιs j), std_basis R Ms j (v j i)))
        ≤ ⨆ i ∈ {j}, range (std_basis R Ms i),
    { rw @supr_singleton _ _ _ (λ i, linear_map.range (std_basis R (λ (j : η), Ms j) i)),
      apply h₀ },
    have h₂ : (⨆ j ∈ J, span R (range (λ (i : ιs j), std_basis R Ms j (v j i)))) ≤
               ⨆ j ∈ J, range (std_basis R (λ (j : η), Ms j) j) :=
      supr_le_supr (λ i, supr_le_supr (λ H, h₀ i)),
    have h₃ : disjoint (λ (i : η), i ∈ {j}) J,
    { convert set.disjoint_singleton_left.2 hiJ,
      rw ←@set_of_mem_eq _ {j},
      refl },
    exact (disjoint_std_basis_std_basis _ _ _ _ h₃).mono h₁ h₂ }
end

variable [fintype η]

lemma is_basis_std_basis [decidable_eq η] (s : Πj, ιs j → (Ms j)) (hs : ∀j, is_basis R (s j)) :
  is_basis R (λ (ji : Σ j, ιs j), std_basis R Ms ji.1 (s ji.1 ji.2)) :=
begin
  split,
  { apply linear_independent_std_basis _ (assume i, (hs i).1) },
  have h₁ : Union (λ j, set.range (std_basis R Ms j ∘ s j))
    ⊆ range (λ (ji : Σ (j : η), ιs j), (std_basis R Ms (ji.fst)) (s (ji.fst) (ji.snd))),
  { apply Union_subset, intro i,
    apply range_comp_subset_range (λ x : ιs i, (⟨i, x⟩ : Σ (j : η), ιs j))
        (λ (ji : Σ (j : η), ιs j), std_basis R Ms (ji.fst) (s (ji.fst) (ji.snd))) },
  have h₂ : ∀ i, span R (range (std_basis R Ms i ∘ s i)) = range (std_basis R Ms i),
  { intro i,
    rw [set.range_comp, submodule.span_image, (assume i, (hs i).2), submodule.map_top] },
  apply eq_top_mono,
  apply span_mono h₁,
  rw span_Union,
  simp only [h₂],
  apply supr_range_std_basis
end

section
variables (R η)

lemma is_basis_fun₀ [decidable_eq η] : is_basis R
    (λ (ji : Σ (j : η), unit),
       (std_basis R (λ (i : η), R) (ji.fst)) 1) :=
@is_basis_std_basis R η (λi:η, unit) (λi:η, R) _ _ _ _ _ (λ _ _, (1 : R))
  (assume i, @is_basis_singleton_one _ _ _ _)

lemma is_basis_fun [decidable_eq η] : is_basis R (λ i, std_basis R (λi:η, R) i 1) :=
begin
  apply (is_basis_fun₀ R η).comp (λ i, ⟨i, punit.star⟩),
  apply bijective_iff_has_inverse.2,
  use sigma.fst,
  simp [function.left_inverse, function.right_inverse]
end

@[simp] lemma is_basis_fun_repr [decidable_eq η] (x : η → R) (i : η) :
  (pi.is_basis_fun R η).repr x i = x i :=
begin
  conv_rhs { rw ← (pi.is_basis_fun R η).total_repr x },
  rw [finsupp.total_apply, finsupp.sum_fintype],
  show (pi.is_basis_fun R η).repr x i =
    (∑ j, λ i, (pi.is_basis_fun R η).repr x j • std_basis R (λ _, R) j 1 i) i,
  rw [finset.sum_apply, finset.sum_eq_single i],
  { simp only [pi.smul_apply, smul_eq_mul, std_basis_same, mul_one] },
  { rintros b - hb, simp only [std_basis_ne _ _ _ _ hb.symm, smul_zero] },
  { intro,
    have := finset.mem_univ i,
    contradiction },
  { intros, apply zero_smul },
end

end

end module

end pi
