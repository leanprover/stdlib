/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
import algebra.big_operators.finsupp
import linear_algebra.finsupp
import linear_algebra.prod
import linear_algebra.pi
import order.zorn
import data.finset.order
import data.equiv.fin

/-!

# Linear independence

This file defines linear independence in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define `linear_independent R v` as `ker (finsupp.total ι M R v) = ⊥`. Here `finsupp.total` is the
linear map sending a function `f : ι →₀ R` with finite support to the linear combination of vectors
from `v` with these coefficients. Then we prove that several other statements are equivalent to this
one, including injectivity of `finsupp.total ι M R v` and some versions with explicitly written
linear combinations.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `linear_independent R v` states that the elements of the family `v` are linearly independent.

* `linear_independent.repr hv x` returns the linear combination representing `x : span R (range v)`
on the linearly independent vectors `v`, given `hv : linear_independent R v`
(using classical choice). `linear_independent.repr hv` is provided as a linear map.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `fintype.linear_independent_iff`: if `ι` is a finite type, then any function `f : ι → R` has
  finite support, so we can reformulate the statement using `∑ i : ι, f i • v i` instead of a sum
  over an auxiliary `s : finset ι`;
* `linear_independent_empty_type`: a family indexed by an empty type is linearly independent;
* `linear_independent_unique_iff`: if `ι` is a singleton, then `linear_independent K v` is
  equivalent to `v (default ι) ≠ 0`;
* linear_independent_option`, `linear_independent_sum`, `linear_independent_fin_cons`,
  `linear_independent_fin_succ`: type-specific tests for linear independence of families of vector
  fields;
* `linear_independent_insert`, `linear_independent_union`, `linear_independent_pair`,
  `linear_independent_singleton`: linear independence tests for set operations.

In many cases we additionally provide dot-style operations (e.g., `linear_independent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that any family of vectors includes a linear independent subfamily spanning the same
submodule.

## Implementation notes

We use families instead of sets because it allows us to say that two identical vectors are linearly
dependent.

If you want to use sets, use the family `(λ x, x : s → M)` given a set `s : set M`. The lemmas
`linear_independent.to_subtype_range` and `linear_independent.of_subtype_range` connect those two
worlds.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

noncomputable theory

open function set submodule
open_locale classical big_operators

universe u

variables {ι : Type*} {ι' : Type*} {R : Type*} {K : Type*}
variables {M : Type*} {M' M'' : Type*} {V : Type u} {V' : Type*}


section module

variables {v : ι → M}
variables [semiring R] [add_comm_monoid M] [add_comm_monoid M'] [add_comm_monoid M'']
variables [module R M] [module R M'] [module R M'']
variables {a b : R} {x y : M}

variables (R) (v)

/-- `linear_independent R v` states the family of vectors `v` is linearly independent over `R`. -/
def linear_independent : Prop := (finsupp.total ι M R v).ker = ⊥
variables {R} {v}

theorem linear_independent_iff : linear_independent R v ↔
  ∀l, finsupp.total ι M R v l = 0 → l = 0 :=
by simp [linear_independent, linear_map.ker_eq_bot']

theorem linear_independent_iff' : linear_independent R v ↔
  ∀ s : finset ι, ∀ g : ι → R, ∑ i in s, g i • v i = 0 → ∀ i ∈ s, g i = 0 :=
linear_independent_iff.trans
⟨λ hf s g hg i his, have h : _ := hf (∑ i in s, finsupp.single i (g i)) $
      by simpa only [linear_map.map_sum, finsupp.total_single] using hg, calc
    g i = (finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (finsupp.single i (g i)) :
      by rw [finsupp.lapply_apply, finsupp.single_eq_same]
    ... = ∑ j in s, (finsupp.lapply i : (ι →₀ R) →ₗ[R] R) (finsupp.single j (g j)) :
      eq.symm $ finset.sum_eq_single i
        (λ j hjs hji, by rw [finsupp.lapply_apply, finsupp.single_eq_of_ne hji])
        (λ hnis, hnis.elim his)
    ... = (∑ j in s, finsupp.single j (g j)) i : (finsupp.lapply i : (ι →₀ R) →ₗ[R] R).map_sum.symm
    ... = 0 : finsupp.ext_iff.1 h i,
λ hf l hl, finsupp.ext $ λ i, classical.by_contradiction $ λ hni, hni $ hf _ _ hl _ $
  finsupp.mem_support_iff.2 hni⟩

theorem linear_independent_iff'' :
  linear_independent R v ↔ ∀ (s : finset ι) (g : ι → R) (hg : ∀ i ∉ s, g i = 0),
    ∑ i in s, g i • v i = 0 → ∀ i, g i = 0 :=
linear_independent_iff'.trans ⟨λ H s g hg hv i, if his : i ∈ s then H s g hv i his else hg i his,
λ H s g hg i hi, by { convert H s (λ j, if j ∈ s then g j else 0) (λ j hj, if_neg hj)
    (by simp_rw [ite_smul, zero_smul, finset.sum_extend_by_zero, hg]) i,
  exact (if_pos hi).symm }⟩

theorem linear_dependent_iff : ¬ linear_independent R v ↔
  ∃ s : finset ι, ∃ g : ι → R, (∑ i in s, g i • v i) = 0 ∧ (∃ i ∈ s, g i ≠ 0) :=
begin
  rw linear_independent_iff',
  simp only [exists_prop, not_forall],
end

theorem fintype.linear_independent_iff [fintype ι] :
  linear_independent R v ↔ ∀ g : ι → R, ∑ i, g i • v i = 0 → ∀ i, g i = 0 :=
begin
  refine ⟨λ H g, by simpa using linear_independent_iff'.1 H finset.univ g,
    λ H, linear_independent_iff''.2 $ λ s g hg hs i, H _ _ _⟩,
  rw ← hs,
  refine (finset.sum_subset (finset.subset_univ _) (λ i _ hi, _)).symm,
  rw [hg i hi, zero_smul]
end

/-- A finite family of vectors `v i` is linear independent iff the linear map that sends
`c : ι → R` to `∑ i, c i • v i` has the trivial kernel. -/
theorem fintype.linear_independent_iff' [fintype ι] :
  linear_independent R v ↔
    (linear_map.lsum R (λ i : ι, R) ℕ (λ i, linear_map.id.smul_right (v i))).ker = ⊥ :=
by simp [fintype.linear_independent_iff, linear_map.ker_eq_bot', funext_iff]

lemma linear_independent_empty_type [is_empty ι] : linear_independent R v :=
begin
 rw [linear_independent_iff],
 intros,
 ext i,
 exact is_empty_elim i
end

lemma linear_independent.ne_zero [nontrivial R]
  (i : ι) (hv : linear_independent R v) : v i ≠ 0 :=
λ h, @zero_ne_one R _ _ $ eq.symm begin
  suffices : (finsupp.single i 1 : ι →₀ R) i = 0, {simpa},
  rw linear_independent_iff.1 hv (finsupp.single i 1),
  { simp },
  { simp [h] }
end

/-- A subfamily of a linearly independent family (i.e., a composition with an injective map) is a
linearly independent family. -/
lemma linear_independent.comp
  (h : linear_independent R v) (f : ι' → ι) (hf : injective f) : linear_independent R (v ∘ f) :=
begin
  rw [linear_independent_iff, finsupp.total_comp],
  intros l hl,
  have h_map_domain : ∀ x, (finsupp.map_domain f l) (f x) = 0,
    by rw linear_independent_iff.1 h (finsupp.map_domain f l) hl; simp,
  ext x,
  convert h_map_domain x,
  rw [finsupp.map_domain_apply hf]
end

/-- If `v` is a linearly independent family of vectors and the kernel of a linear map `f` is
disjoint with the sumodule spaned by the vectors of `v`, then `f ∘ v` is a linearly independent
family of vectors. See also `linear_independent.map'` for a special case assuming `ker f = ⊥`. -/
lemma linear_independent.map (hv : linear_independent R v) {f : M →ₗ[R] M'}
  (hf_inj : disjoint (span R (range v)) f.ker) : linear_independent R (f ∘ v) :=
begin
  rw [disjoint, ← set.image_univ, finsupp.span_image_eq_map_total, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot, finsupp.supported_univ, top_inf_eq] at hf_inj,
  unfold linear_independent at hv ⊢,
  rw [hv, le_bot_iff] at hf_inj,
  haveI : inhabited M := ⟨0⟩,
  rw [finsupp.total_comp, @finsupp.lmap_domain_total _ _ R _ _ _ _ _ _ _ _ _ _ f,
    linear_map.ker_comp, hf_inj],
  exact λ _, rfl,
end

/-- An injective linear map sends linearly independent families of vectors to linearly independent
families of vectors. See also `linear_independent.map` for a more general statement. -/
lemma linear_independent.map' (hv : linear_independent R v) (f : M →ₗ[R] M')
  (hf_inj : f.ker = ⊥) : linear_independent R (f ∘ v) :=
hv.map $ by simp [hf_inj]

/-- If the image of a family of vectors under a linear map is linearly independent, then so is
the original family. -/
lemma linear_independent.of_comp (f : M →ₗ[R] M') (hfv : linear_independent R (f ∘ v)) :
  linear_independent R v :=
linear_independent_iff'.2 $ λ s g hg i his,
have ∑ (i : ι) in s, g i • f (v i) = 0,
  by simp_rw [← f.map_smul, ← f.map_sum, hg, f.map_zero],
linear_independent_iff'.1 hfv s g this i his

/-- If `f` is an injective linear map, then the family `f ∘ v` is linearly independent
if and only if the family `v` is linearly independent. -/
protected lemma linear_map.linear_independent_iff (f : M →ₗ[R] M') (hf_inj : f.ker = ⊥) :
  linear_independent R (f ∘ v) ↔ linear_independent R v :=
⟨λ h, h.of_comp f, λ h, h.map $ by simp only [hf_inj, disjoint_bot_right]⟩

@[nontriviality]
lemma linear_independent_of_subsingleton [subsingleton R] : linear_independent R v :=
linear_independent_iff.2 (λ l hl, subsingleton.elim _ _)

theorem linear_independent_equiv (e : ι ≃ ι') {f : ι' → M} :
  linear_independent R (f ∘ e) ↔ linear_independent R f :=
⟨λ h, function.comp.right_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
λ h, h.comp _ e.injective⟩

theorem linear_independent_equiv' (e : ι ≃ ι') {f : ι' → M} {g : ι → M} (h : f ∘ e = g) :
  linear_independent R g ↔ linear_independent R f :=
h ▸ linear_independent_equiv e

theorem linear_independent_subtype_range {ι} {f : ι → M} (hf : injective f) :
  linear_independent R (coe : range f → M) ↔ linear_independent R f :=
iff.symm $ linear_independent_equiv' (equiv.of_injective f hf) rfl

alias linear_independent_subtype_range ↔ linear_independent.of_subtype_range _

theorem linear_independent_image {ι} {s : set ι} {f : ι → M} (hf : set.inj_on f s) :
  linear_independent R (λ x : s, f x) ↔ linear_independent R (λ x : f '' s, (x : M)) :=
linear_independent_equiv' (equiv.set.image_of_inj_on _ _ hf) rfl

lemma linear_independent_span (hs : linear_independent R v) :
  @linear_independent ι R (span R (range v))
      (λ i : ι, ⟨v i, subset_span (mem_range_self i)⟩) _ _ _ :=
linear_independent.of_comp (span R (range v)).subtype hs

/-- See `linear_independent.fin_cons` for a family of elements in a vector space. -/
lemma linear_independent.fin_cons' {m : ℕ} (x : M) (v : fin m → M)
  (hli : linear_independent R v)
  (x_ortho : (∀ (c : R) (y : submodule.span R (set.range v)), c • x + y = (0 : M) → c = 0)) :
  linear_independent R (fin.cons x v : fin m.succ → M) :=
begin
  rw fintype.linear_independent_iff at hli ⊢,
  rintros g total_eq j,
  have zero_not_mem : (0 : fin m.succ) ∉ finset.univ.image (fin.succ : fin m → fin m.succ),
  { rw finset.mem_image,
    rintro ⟨x, hx, succ_eq⟩,
    exact fin.succ_ne_zero _ succ_eq },
  simp only [submodule.coe_mk, fin.univ_succ, finset.sum_insert zero_not_mem,
  fin.cons_zero, fin.cons_succ,
  forall_true_iff, imp_self, fin.succ_inj, finset.sum_image] at total_eq,
  have : g 0 = 0,
  { refine x_ortho (g 0) ⟨∑ (i : fin m), g i.succ • v i, _⟩ total_eq,
    exact sum_mem _ (λ i _, smul_mem _ _ (subset_span ⟨i, rfl⟩)) },
  refine fin.cases this (λ j, _) j,
  apply hli (λ i, g i.succ),
  simpa only [this, zero_smul, zero_add] using total_eq
end

/-- A set of linearly independent vectors in a module `M` over a semiring `K` is also linearly
independent over a subring `R` of `K`.
The implementation uses minimal assumptions about the relationship between `R`, `K` and `M`.
The version where `K` is an `R`-algebra is `linear_independent.restrict_scalars_algebras`.
 -/
lemma linear_independent.restrict_scalars [semiring K] [smul_with_zero R K] [module K M]
  [is_scalar_tower R K M]
  (hinj : function.injective (λ r : R, r • (1 : K))) (li : linear_independent K v) :
  linear_independent R v :=
begin
  refine linear_independent_iff'.mpr (λ s g hg i hi, hinj (eq.trans _ (zero_smul _ _).symm)),
  refine (linear_independent_iff'.mp li : _) _ _ _ i hi,
  simp_rw [smul_assoc, one_smul],
  exact hg,
end

section subtype
/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

theorem linear_independent_comp_subtype {s : set ι} :
  linear_independent R (v ∘ coe : s → M) ↔
  ∀ l ∈ (finsupp.supported R R s), (finsupp.total ι M R v) l = 0 → l = 0 :=
begin
  simp only [linear_independent_iff, (∘), finsupp.mem_supported, finsupp.total_apply,
    set.subset_def, finset.mem_coe],
  split,
  { intros h l hl₁ hl₂,
    have := h (l.subtype_domain s) ((finsupp.sum_subtype_domain_index hl₁).trans hl₂),
    exact (finsupp.subtype_domain_eq_zero_iff hl₁).1 this },
  { intros h l hl,
    refine finsupp.emb_domain_eq_zero.1 (h (l.emb_domain $ function.embedding.subtype s) _ _),
    { suffices : ∀ i hi, ¬l ⟨i, hi⟩ = 0 → i ∈ s, by simpa,
      intros, assumption },
    { rwa [finsupp.emb_domain_eq_map_domain, finsupp.sum_map_domain_index],
      exacts [λ _, zero_smul _ _, λ _ _ _, add_smul _ _ _] } }
end

lemma linear_dependent_comp_subtype' {s : set ι} :
  ¬ linear_independent R (v ∘ coe : s → M) ↔
  ∃ f : ι →₀ R, f ∈ finsupp.supported R R s ∧ finsupp.total ι M R v f = 0 ∧ f ≠ 0 :=
by simp [linear_independent_comp_subtype]

/-- A version of `linear_dependent_comp_subtype'` with `finsupp.total` unfolded. -/
lemma linear_dependent_comp_subtype {s : set ι} :
  ¬ linear_independent R (v ∘ coe : s → M) ↔
  ∃ f : ι →₀ R, f ∈ finsupp.supported R R s ∧ ∑ i in f.support, f i • v i = 0 ∧ f ≠ 0 :=
linear_dependent_comp_subtype'

theorem linear_independent_subtype {s : set M} :
  linear_independent R (λ x, x : s → M) ↔
  ∀ l ∈ (finsupp.supported R R s), (finsupp.total M M R id) l = 0 → l = 0 :=
by apply @linear_independent_comp_subtype _ _ _ id

theorem linear_independent_comp_subtype_disjoint {s : set ι} :
  linear_independent R (v ∘ coe : s → M) ↔
  disjoint (finsupp.supported R R s) (finsupp.total ι M R v).ker :=
by rw [linear_independent_comp_subtype, linear_map.disjoint_ker]

theorem linear_independent_subtype_disjoint {s : set M} :
  linear_independent R (λ x, x : s → M) ↔
  disjoint (finsupp.supported R R s) (finsupp.total M M R id).ker :=
by apply @linear_independent_comp_subtype_disjoint _ _ _ id

theorem linear_independent_iff_total_on {s : set M} :
  linear_independent R (λ x, x : s → M) ↔ (finsupp.total_on M M R id s).ker = ⊥ :=
by rw [finsupp.total_on, linear_map.ker, linear_map.comap_cod_restrict, map_bot, comap_bot,
  linear_map.ker_comp, linear_independent_subtype_disjoint, disjoint, ← map_comap_subtype,
  map_le_iff_le_comap, comap_bot, ker_subtype, le_bot_iff]

lemma linear_independent.restrict_of_comp_subtype {s : set ι}
  (hs : linear_independent R (v ∘ coe : s → M)) :
  linear_independent R (s.restrict v) :=
hs

variables (R M)
lemma linear_independent_empty : linear_independent R (λ x, x : (∅ : set M) → M) :=
by simp [linear_independent_subtype_disjoint]
variables {R M}

lemma linear_independent.mono {t s : set M} (h : t ⊆ s) :
  linear_independent R (λ x, x : s → M) → linear_independent R (λ x, x : t → M) :=
begin
 simp only [linear_independent_subtype_disjoint],
 exact (disjoint.mono_left (finsupp.supported_mono h))
end

lemma linear_independent_of_finite (s : set M)
  (H : ∀ t ⊆ s, finite t → linear_independent R (λ x, x : t → M)) :
  linear_independent R (λ x, x : s → M) :=
linear_independent_subtype.2 $
  λ l hl, linear_independent_subtype.1 (H _ hl (finset.finite_to_set _)) l (subset.refl _)

lemma linear_independent_Union_of_directed {η : Type*}
  {s : η → set M} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent R (λ x, x : s i → M)) :
  linear_independent R (λ x, x : (⋃ i, s i) → M) :=
begin
  by_cases hη : nonempty η,
  { resetI,
    refine linear_independent_of_finite (⋃ i, s i) (λ t ht ft, _),
    rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩,
    rcases hs.finset_le fi.to_finset with ⟨i, hi⟩,
    exact (h i).mono (subset.trans hI $ bUnion_subset $
      λ j hj, hi j (fi.mem_to_finset.2 hj)) },
  { refine (linear_independent_empty _ _).mono _,
    rintro _ ⟨_, ⟨i, _⟩, _⟩, exact hη ⟨i⟩ }
end

lemma linear_independent_sUnion_of_directed {s : set (set M)}
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, linear_independent R (λ x, x : (a : set M) → M)) :
  linear_independent R (λ x, x : (⋃₀ s) → M) :=
by rw sUnion_eq_Union; exact
linear_independent_Union_of_directed hs.directed_coe (by simpa using h)

lemma linear_independent_bUnion_of_directed {η} {s : set η} {t : η → set M}
  (hs : directed_on (t ⁻¹'o (⊆)) s) (h : ∀a∈s, linear_independent R (λ x, x : t a → M)) :
  linear_independent R (λ x, x : (⋃a∈s, t a) → M) :=
by rw bUnion_eq_Union; exact
linear_independent_Union_of_directed (directed_comp.2 $ hs.directed_coe) (by simpa using h)

end subtype

end module

/-! ### Properties which require `ring R` -/

section module
variables {v : ι → M}
variables [ring R] [add_comm_group M] [add_comm_group M'] [add_comm_group M'']
variables [module R M] [module R M'] [module R M'']
variables {a b : R} {x y : M}

theorem linear_independent_iff_injective_total : linear_independent R v ↔
  function.injective (finsupp.total ι M R v) :=
linear_independent_iff.trans (finsupp.total ι M R v).to_add_monoid_hom.injective_iff.symm

alias linear_independent_iff_injective_total ↔ linear_independent.injective_total _

lemma linear_independent.injective [nontrivial R] (hv : linear_independent R v) :
  injective v :=
begin
  intros i j hij,
  let l : ι →₀ R := finsupp.single i (1 : R) - finsupp.single j 1,
  have h_total : finsupp.total ι M R v l = 0,
  { simp_rw [linear_map.map_sub, finsupp.total_apply],
    simp [hij] },
  have h_single_eq : finsupp.single i (1 : R) = finsupp.single j 1,
  { rw linear_independent_iff at hv,
    simp [eq_add_of_sub_eq' (hv l h_total)] },
  simpa [finsupp.single_eq_single_iff] using h_single_eq
end

theorem linear_independent.to_subtype_range {ι} {f : ι → M} (hf : linear_independent R f) :
  linear_independent R (coe : range f → M) :=
begin
  nontriviality R,
  exact (linear_independent_subtype_range hf.injective).2 hf
end

theorem linear_independent.to_subtype_range' {ι} {f : ι → M} (hf : linear_independent R f)
  {t} (ht : range f = t) :
  linear_independent R (coe : t → M) :=
ht ▸ hf.to_subtype_range

theorem linear_independent.image_of_comp {ι ι'} (s : set ι) (f : ι → ι') (g : ι' → M)
  (hs : linear_independent R (λ x : s, g (f x))) :
  linear_independent R (λ x : f '' s, g x) :=
begin
  nontriviality R,
  have : inj_on f s, from inj_on_iff_injective.2 hs.injective.of_comp,
  exact (linear_independent_equiv' (equiv.set.image_of_inj_on f s this) rfl).1 hs
end

theorem linear_independent.image {ι} {s : set ι} {f : ι → M}
  (hs : linear_independent R (λ x : s, f x)) : linear_independent R (λ x : f '' s, (x : M)) :=
by convert linear_independent.image_of_comp s f id hs

lemma linear_independent.group_smul
  {G : Type*} [hG : group G] [distrib_mul_action G R] [distrib_mul_action G M]
  [is_scalar_tower G R M] [smul_comm_class G R M] {v : ι → M} (hv : linear_independent R v)
  (w : ι → G) : linear_independent R (w • v) :=
begin
  rw linear_independent_iff'' at hv ⊢,
  intros s g hgs hsum i,
  refine (smul_eq_zero_iff_eq (w i)).1 _,
  refine hv s (λ i, w i • g i) (λ i hi, _) _ i,
  { dsimp only,
    exact (hgs i hi).symm ▸ smul_zero _ },
  { rw [← hsum, finset.sum_congr rfl _],
    intros, erw [pi.smul_apply, smul_assoc, smul_comm] },
end

-- This lemma cannot be proved with `linear_independent.group_smul` since the action of
-- `units R` on `R` is not commutative.
lemma linear_independent.units_smul {v : ι → M} (hv : linear_independent R v)
  (w : ι → units R) : linear_independent R (w • v) :=
begin
  rw linear_independent_iff'' at hv ⊢,
  intros s g hgs hsum i,
  rw ← (w i).mul_left_eq_zero,
  refine hv s (λ i, g i • w i) (λ i hi, _) _ i,
  { dsimp only,
    exact (hgs i hi).symm ▸ zero_smul _ _ },
  { rw [← hsum, finset.sum_congr rfl _],
    intros,
    erw [pi.smul_apply, smul_assoc],
    refl }
end

section subtype
/-! The following lemmas use the subtype defined by a set in `M` as the index set `ι`. -/

lemma linear_independent.disjoint_span_image (hv : linear_independent R v) {s t : set ι}
  (hs : disjoint s t) :
  disjoint (submodule.span R $ v '' s) (submodule.span R $ v '' t) :=
begin
  simp only [disjoint_def, finsupp.mem_span_image_iff_total],
  rintros _ ⟨l₁, hl₁, rfl⟩ ⟨l₂, hl₂, H⟩,
  rw [hv.injective_total.eq_iff] at H, subst l₂,
  have : l₁ = 0 := finsupp.disjoint_supported_supported hs (submodule.mem_inf.2 ⟨hl₁, hl₂⟩),
  simp [this]
end

lemma linear_independent_sum {v : ι ⊕ ι' → M} :
  linear_independent R v ↔ linear_independent R (v ∘ sum.inl) ∧
    linear_independent R (v ∘ sum.inr) ∧
      disjoint (submodule.span R (range (v ∘ sum.inl))) (submodule.span R (range (v ∘ sum.inr))) :=
begin
  rw [range_comp v, range_comp v],
  refine ⟨λ h, ⟨h.comp _ sum.inl_injective, h.comp _ sum.inr_injective,
    h.disjoint_span_image is_compl_range_inl_range_inr.1⟩, _⟩,
  rintro ⟨hl, hr, hlr⟩,
  rw [linear_independent_iff'] at *,
  intros s g hg i hi,
  have : ∑ i in s.preimage sum.inl (sum.inl_injective.inj_on _), (λ x, g x • v x) (sum.inl i) +
    ∑ i in s.preimage sum.inr (sum.inr_injective.inj_on _), (λ x, g x • v x) (sum.inr i) = 0,
  { rw [finset.sum_preimage', finset.sum_preimage', ← finset.sum_union, ← finset.filter_or],
    { simpa only [← mem_union, range_inl_union_range_inr, mem_univ, finset.filter_true] },
    { exact finset.disjoint_filter.2 (λ x hx, disjoint_left.1 is_compl_range_inl_range_inr.1) } },
  { rw ← eq_neg_iff_add_eq_zero at this,
    rw [disjoint_def'] at hlr,
    have A := hlr _ (sum_mem _ $ λ i hi, _) _ (neg_mem _ $ sum_mem _ $ λ i hi, _) this,
    { cases i with i i,
      { exact hl _ _ A i (finset.mem_preimage.2 hi) },
      { rw [this, neg_eq_zero] at A,
        exact hr _ _ A i (finset.mem_preimage.2 hi) } },
    { exact smul_mem _ _ (subset_span ⟨sum.inl i, mem_range_self _, rfl⟩) },
    { exact smul_mem _ _ (subset_span ⟨sum.inr i, mem_range_self _, rfl⟩) } }
end

lemma linear_independent.sum_type {v' : ι' → M} (hv : linear_independent R v)
  (hv' : linear_independent R v')
  (h : disjoint (submodule.span R (range v)) (submodule.span R (range v'))) :
  linear_independent R (sum.elim v v') :=
linear_independent_sum.2 ⟨hv, hv', h⟩

lemma linear_independent.union {s t : set M}
  (hs : linear_independent R (λ x, x : s → M)) (ht : linear_independent R (λ x, x : t → M))
  (hst : disjoint (span R s) (span R t)) :
  linear_independent R (λ x, x : (s ∪ t) → M) :=
(hs.sum_type ht $ by simpa).to_subtype_range' $ by simp

lemma linear_independent_Union_finite_subtype {ι : Type*} {f : ι → set M}
  (hl : ∀i, linear_independent R (λ x, x : f i → M))
  (hd : ∀i, ∀t:set ι, finite t → i ∉ t → disjoint (span R (f i)) (⨆i∈t, span R (f i))) :
  linear_independent R (λ x, x : (⋃i, f i) → M) :=
begin
  rw [Union_eq_Union_finset f],
  apply linear_independent_Union_of_directed,
  apply directed_of_sup,
  exact (assume t₁ t₂ ht, Union_subset_Union $ assume i, Union_subset_Union_const $ assume h, ht h),
  assume t, rw [set.Union, ← finset.sup_eq_supr],
  refine t.induction_on _ _,
  { rw finset.sup_empty,
    apply linear_independent_empty_type, },
  { rintros i s his ih,
    rw [finset.sup_insert],
    refine (hl _).union ih _,
    rw [finset.sup_eq_supr],
    refine (hd i _ _ his).mono_right _,
    { simp only [(span_Union _).symm],
      refine span_mono (@supr_le_supr2 (set M) _ _ _ _ _ _),
      rintros i, exact ⟨i, le_refl _⟩ },
    { exact s.finite_to_set } }
end

lemma linear_independent_Union_finite {η : Type*} {ιs : η → Type*}
  {f : Π j : η, ιs j → M}
  (hindep : ∀j, linear_independent R (f j))
  (hd : ∀i, ∀t:set η, finite t → i ∉ t →
      disjoint (span R (range (f i))) (⨆i∈t, span R (range (f i)))) :
  linear_independent R (λ ji : Σ j, ιs j, f ji.1 ji.2) :=
begin
  nontriviality R,
  apply linear_independent.of_subtype_range,
  { rintros ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy,
    by_cases h_cases : x₁ = y₁,
    subst h_cases,
    { apply sigma.eq,
      rw linear_independent.injective (hindep _) hxy,
      refl },
    { have h0 : f x₁ x₂ = 0,
      { apply disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁)
          (λ h, h_cases (eq_of_mem_singleton h))) (f x₁ x₂) (subset_span (mem_range_self _)),
        rw supr_singleton,
        simp only at hxy,
        rw hxy,
        exact (subset_span (mem_range_self y₂)) },
      exact false.elim ((hindep x₁).ne_zero _ h0) } },
  rw range_sigma_eq_Union_range,
  apply linear_independent_Union_finite_subtype (λ j, (hindep j).to_subtype_range) hd,
end

end subtype

section repr
variables (hv : linear_independent R v)

/-- Canonical isomorphism between linear combinations and the span of linearly independent vectors.
-/
def linear_independent.total_equiv (hv : linear_independent R v) :
  (ι →₀ R) ≃ₗ[R] span R (range v) :=
begin
apply linear_equiv.of_bijective
  (linear_map.cod_restrict (span R (range v)) (finsupp.total ι M R v) _),
{ rw linear_map.ker_cod_restrict,
  apply hv },
{ rw [linear_map.range_eq_map, linear_map.map_cod_restrict, ← linear_map.range_le_iff_comap,
    range_subtype, map_top],
  rw finsupp.range_total,
  apply le_refl (span R (range v)) },
{ intro l,
  rw ← finsupp.range_total,
  rw linear_map.mem_range,
  apply mem_range_self l }
end

/-- Linear combination representing a vector in the span of linearly independent vectors.

Given a family of linearly independent vectors, we can represent any vector in their span as
a linear combination of these vectors. These are provided by this linear map.
It is simply one direction of `linear_independent.total_equiv`. -/
def linear_independent.repr (hv : linear_independent R v) :
  span R (range v) →ₗ[R] ι →₀ R := hv.total_equiv.symm

lemma linear_independent.total_repr (x) : finsupp.total ι M R v (hv.repr x) = x :=
subtype.ext_iff.1 (linear_equiv.apply_symm_apply hv.total_equiv x)

lemma linear_independent.total_comp_repr :
  (finsupp.total ι M R v).comp hv.repr = submodule.subtype _ :=
linear_map.ext $ hv.total_repr

lemma linear_independent.repr_ker : hv.repr.ker = ⊥ :=
by rw [linear_independent.repr, linear_equiv.ker]

lemma linear_independent.repr_range : hv.repr.range = ⊤ :=
by rw [linear_independent.repr, linear_equiv.range]

lemma linear_independent.repr_eq
  {l : ι →₀ R} {x} (eq : finsupp.total ι M R v l = ↑x) :
  hv.repr x = l :=
begin
  have : ↑((linear_independent.total_equiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l)
      = finsupp.total ι M R v l := rfl,
  have : (linear_independent.total_equiv hv : (ι →₀ R) →ₗ[R] span R (range v)) l = x,
  { rw eq at this,
    exact subtype.ext_iff.2 this },
  rw ←linear_equiv.symm_apply_apply hv.total_equiv l,
  rw ←this,
  refl,
end

lemma linear_independent.repr_eq_single (i) (x) (hx : ↑x = v i) :
  hv.repr x = finsupp.single i 1 :=
begin
  apply hv.repr_eq,
  simp [finsupp.total_single, hx]
end

-- TODO: why is this so slow?
lemma linear_independent_iff_not_smul_mem_span :
  linear_independent R v ↔ (∀ (i : ι) (a : R), a • (v i) ∈ span R (v '' (univ \ {i})) → a = 0) :=
⟨ λ hv i a ha, begin
  rw [finsupp.span_image_eq_map_total, mem_map] at ha,
  rcases ha with ⟨l, hl, e⟩,
  rw sub_eq_zero.1 (linear_independent_iff.1 hv (l - finsupp.single i a) (by simp [e])) at hl,
  by_contra hn,
  exact (not_mem_of_mem_diff (hl $ by simp [hn])) (mem_singleton _),
end, λ H, linear_independent_iff.2 $ λ l hl, begin
  ext i, simp only [finsupp.zero_apply],
  by_contra hn,
  refine hn (H i _ _),
  refine (finsupp.mem_span_image_iff_total _).2 ⟨finsupp.single i (l i) - l, _, _⟩,
  { rw finsupp.mem_supported',
    intros j hj,
    have hij : j = i :=
      not_not.1
          (λ hij : j ≠ i, hj ((mem_diff _).2 ⟨mem_univ _, λ h, hij (eq_of_mem_singleton h)⟩)),
    simp [hij] },
  { simp [hl] }
end⟩

variable (R)

lemma exists_maximal_independent' (s : ι → M) :
  ∃ I : set ι, linear_independent R (λ x : I, s x) ∧
    ∀ J : set ι, I ⊆ J → linear_independent R (λ x : J, s x) → I = J :=
begin
  let indep : set ι → Prop := λ I, linear_independent R (s ∘ coe : I → M),
  let X := { I : set ι // indep I },
  let r : X → X → Prop := λ I J, I.1 ⊆ J.1,
  have key : ∀ c : set X, zorn.chain r c → indep (⋃ (I : X) (H : I ∈ c), I),
  { intros c hc,
    dsimp [indep],
    rw [linear_independent_comp_subtype],
    intros f hsupport hsum,
    rcases eq_empty_or_nonempty c with rfl | ⟨a, hac⟩,
    { simpa using hsupport },
    haveI : is_refl X r := ⟨λ _, set.subset.refl _⟩,
    obtain ⟨I, I_mem, hI⟩ : ∃ I ∈ c, (f.support : set ι) ⊆ I :=
      finset.exists_mem_subset_of_subset_bUnion_of_directed_on hac hc.directed_on hsupport,
    exact linear_independent_comp_subtype.mp I.2 f hI hsum },
  have trans : transitive r := λ I J K, set.subset.trans,
  obtain ⟨⟨I, hli : indep I⟩, hmax : ∀ a, r ⟨I, hli⟩ a → r a ⟨I, hli⟩⟩ :=
    @zorn.exists_maximal_of_chains_bounded _ r
    (λ c hc, ⟨⟨⋃ I ∈ c, (I : set ι), key c hc⟩, λ I, set.subset_bUnion_of_mem⟩) trans,
  exact ⟨I, hli, λ J hsub hli, set.subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩,
end

lemma exists_maximal_independent (s : ι → M) : ∃ I : set ι, linear_independent R (λ x : I, s x) ∧
  ∀ i ∉ I, ∃ a : R, a ≠ 0 ∧ a • s i ∈ span R (s '' I) :=
begin
  classical,
  rcases exists_maximal_independent' R s with ⟨I, hIlinind, hImaximal⟩,
  use [I, hIlinind],
  intros i hi,
  specialize hImaximal (I ∪ {i}) (by simp),
  set J := I ∪ {i} with hJ,
  have memJ : ∀ {x}, x ∈ J ↔ x = i ∨ x ∈ I, by simp [hJ],
  have hiJ : i ∈ J := by simp,
  have h := mt hImaximal _, swap,
  { intro h2,
    rw h2 at hi,
    exact absurd hiJ hi },
  obtain ⟨f, supp_f, sum_f, f_ne⟩ := linear_dependent_comp_subtype.mp h,
  have hfi : f i ≠ 0,
  { contrapose hIlinind,
    refine linear_dependent_comp_subtype.mpr ⟨f, _, sum_f, f_ne⟩,
    simp only [finsupp.mem_supported, hJ] at ⊢ supp_f,
    rintro x hx,
    refine (memJ.mp (supp_f hx)).resolve_left _,
    rintro rfl,
    exact hIlinind (finsupp.mem_support_iff.mp hx) },
  use [f i, hfi],
  have hfi' : i ∈ f.support := finsupp.mem_support_iff.mpr hfi,
  rw [← finset.insert_erase hfi', finset.sum_insert (finset.not_mem_erase _ _),
      add_eq_zero_iff_eq_neg] at sum_f,
  rw sum_f,
  refine neg_mem _ (sum_mem _ (λ c hc, smul_mem _ _ (subset_span ⟨c, _, rfl⟩))),
  exact (memJ.mp (supp_f (finset.erase_subset _ _ hc))).resolve_left (finset.ne_of_mem_erase hc),
end
end repr

lemma surjective_of_linear_independent_of_span [nontrivial R]
  (hv : linear_independent R v) (f : ι' ↪ ι)
  (hss : range v ⊆ span R (range (v ∘ f))) :
  surjective f :=
begin
  intros i,
  let repr : (span R (range (v ∘ f)) : Type*) → ι' →₀ R := (hv.comp f f.injective).repr,
  let l := (repr ⟨v i, hss (mem_range_self i)⟩).map_domain f,
  have h_total_l : finsupp.total ι M R v l = v i,
  { dsimp only [l],
    rw finsupp.total_map_domain,
    rw (hv.comp f f.injective).total_repr,
    { refl },
    { exact f.injective } },
  have h_total_eq : (finsupp.total ι M R v) l = (finsupp.total ι M R v) (finsupp.single i 1),
    by rw [h_total_l, finsupp.total_single, one_smul],
  have l_eq : l = _ := linear_map.ker_eq_bot.1 hv h_total_eq,
  dsimp only [l] at l_eq,
  rw ←finsupp.emb_domain_eq_map_domain at l_eq,
  rcases finsupp.single_of_emb_domain_single (repr ⟨v i, _⟩) f i (1 : R) zero_ne_one.symm l_eq
    with ⟨i', hi'⟩,
  use i',
  exact hi'.2
end

lemma eq_of_linear_independent_of_span_subtype [nontrivial R] {s t : set M}
  (hs : linear_independent R (λ x, x : s → M)) (h : t ⊆ s) (hst : s ⊆ span R t) : s = t :=
begin
  let f : t ↪ s := ⟨λ x, ⟨x.1, h x.2⟩, λ a b hab, subtype.coe_injective (subtype.mk.inj hab)⟩,
  have h_surj : surjective f,
  { apply surjective_of_linear_independent_of_span hs f _,
    convert hst; simp [f, comp], },
  show s = t,
  { apply subset.antisymm _ h,
    intros x hx,
    rcases h_surj ⟨x, hx⟩ with ⟨y, hy⟩,
    convert y.mem,
    rw ← subtype.mk.inj hy,
    refl }
end

open linear_map

lemma linear_independent.image_subtype {s : set M} {f : M →ₗ M'}
  (hs : linear_independent R (λ x, x : s → M))
  (hf_inj : disjoint (span R s) f.ker) : linear_independent R (λ x, x : f '' s → M') :=
begin
  rw [← @subtype.range_coe _ s] at hf_inj,
  refine (hs.map hf_inj).to_subtype_range' _,
  simp [set.range_comp f]
end

lemma linear_independent.inl_union_inr {s : set M} {t : set M'}
  (hs : linear_independent R (λ x, x : s → M))
  (ht : linear_independent R (λ x, x : t → M')) :
  linear_independent R (λ x, x : inl R M M' '' s ∪ inr R M M' '' t → M × M') :=
begin
  refine (hs.image_subtype _).union (ht.image_subtype _) _; [simp, simp, skip],
  simp only [span_image],
  simp [disjoint_iff, prod_inf_prod]
end

lemma linear_independent_inl_union_inr' {v : ι → M} {v' : ι' → M'}
  (hv : linear_independent R v) (hv' : linear_independent R v') :
  linear_independent R (sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) :=
(hv.map' (inl R M M') ker_inl).sum_type (hv'.map' (inr R M M') ker_inr) $
begin
  refine is_compl_range_inl_inr.disjoint.mono _ _;
    simp only [span_le, range_coe, range_comp_subset_range],
end

/-- Dedekind's linear independence of characters -/
-- See, for example, Keith Conrad's note
--  <https://kconrad.math.uconn.edu/blurbs/galoistheory/linearchar.pdf>
theorem linear_independent_monoid_hom (G : Type*) [monoid G] (L : Type*) [comm_ring L]
  [no_zero_divisors L] :
  @linear_independent _ L (G → L) (λ f, f : (G →* L) → (G → L)) _ _ _ :=
by letI := classical.dec_eq (G →* L);
   letI : mul_action L L := distrib_mul_action.to_mul_action;
-- We prove linear independence by showing that only the trivial linear combination vanishes.
exact linear_independent_iff'.2
-- To do this, we use `finset` induction,
(λ s, finset.induction_on s (λ g hg i, false.elim) $ λ a s has ih g hg,
-- Here
-- * `a` is a new character we will insert into the `finset` of characters `s`,
-- * `ih` is the fact that only the trivial linear combination of characters in `s` is zero
-- * `hg` is the fact that `g` are the coefficients of a linear combination summing to zero
-- and it remains to prove that `g` vanishes on `insert a s`.

-- We now make the key calculation:
-- For any character `i` in the original `finset`, we have `g i • i = g i • a` as functions on the
-- monoid `G`.
have h1 : ∀ i ∈ s, (g i • i : G → L) = g i • a, from λ i his, funext $ λ x : G,
  -- We prove these expressions are equal by showing
  -- the differences of their values on each monoid element `x` is zero
  eq_of_sub_eq_zero $ ih (λ j, g j * j x - g j * a x)
    (funext $ λ y : G, calc
    -- After that, it's just a chase scene.
          (∑ i in s, ((g i * i x - g i * a x) • i : G → L)) y
        = ∑ i in s, (g i * i x - g i * a x) * i y : finset.sum_apply _ _ _
    ... = ∑ i in s, (g i * i x * i y - g i * a x * i y) : finset.sum_congr rfl
      (λ _ _, sub_mul _ _ _)
    ... = ∑ i in s, g i * i x * i y - ∑ i in s, g i * a x * i y : finset.sum_sub_distrib
    ... = (g a * a x * a y + ∑ i in s, g i * i x * i y)
          - (g a * a x * a y + ∑ i in s, g i * a x * i y) : by rw add_sub_add_left_eq_sub
    ... = ∑ i in insert a s, g i * i x * i y - ∑ i in insert a s, g i * a x * i y :
      by rw [finset.sum_insert has, finset.sum_insert has]
    ... = ∑ i in insert a s, g i * i (x * y) - ∑ i in insert a s, a x * (g i * i y) :
      congr (congr_arg has_sub.sub (finset.sum_congr rfl $ λ i _, by rw [i.map_mul, mul_assoc]))
        (finset.sum_congr rfl $ λ _ _, by rw [mul_assoc, mul_left_comm])
    ... = (∑ i in insert a s, (g i • i : G → L)) (x * y)
          - a x * (∑ i in insert a s, (g i • i : G → L)) y :
      by rw [finset.sum_apply, finset.sum_apply, finset.mul_sum]; refl
    ... = 0 - a x * 0 : by rw hg; refl
    ... = 0 : by rw [mul_zero, sub_zero])
    i
    his,
-- On the other hand, since `a` is not already in `s`, for any character `i ∈ s`
-- there is some element of the monoid on which it differs from `a`.
have h2 : ∀ i : G →* L, i ∈ s → ∃ y, i y ≠ a y, from λ i his,
  classical.by_contradiction $ λ h,
  have hia : i = a, from monoid_hom.ext $ λ y, classical.by_contradiction $ λ hy, h ⟨y, hy⟩,
  has $ hia ▸ his,
-- From these two facts we deduce that `g` actually vanishes on `s`,
have h3 : ∀ i ∈ s, g i = 0, from λ i his, let ⟨y, hy⟩ := h2 i his in
  have h : g i • i y = g i • a y, from congr_fun (h1 i his) y,
  or.resolve_right (mul_eq_zero.1 $ by rw [mul_sub, sub_eq_zero]; exact h) (sub_ne_zero_of_ne hy),
-- And so, using the fact that the linear combination over `s` and over `insert a s` both vanish,
-- we deduce that `g a = 0`.
have h4 : g a = 0, from calc
  g a = g a * 1 : (mul_one _).symm
  ... = (g a • a : G → L) 1 : by rw ← a.map_one; refl
  ... = (∑ i in insert a s, (g i • i : G → L)) 1 : begin
      rw finset.sum_eq_single a,
      { intros i his hia, rw finset.mem_insert at his,
        rw [h3 i (his.resolve_left hia), zero_smul] },
      { intros haas, exfalso, apply haas, exact finset.mem_insert_self a s }
    end
  ... = 0 : by rw hg; refl,
-- Now we're done; the last two facts together imply that `g` vanishes on every element
-- of `insert a s`.
(finset.forall_mem_insert _ _ _).2 ⟨h4, h3⟩)

lemma le_of_span_le_span [nontrivial R] {s t u: set M}
  (hl : linear_independent R (coe : u → M )) (hsu : s ⊆ u) (htu : t ⊆ u)
  (hst : span R s ≤ span R t) : s ⊆ t :=
begin
  have := eq_of_linear_independent_of_span_subtype
    (hl.mono (set.union_subset hsu htu))
    (set.subset_union_right _ _)
    (set.union_subset (set.subset.trans subset_span hst) subset_span),
  rw ← this, apply set.subset_union_left
end

lemma span_le_span_iff [nontrivial R] {s t u: set M}
  (hl : linear_independent R (coe : u → M)) (hsu : s ⊆ u) (htu : t ⊆ u) :
  span R s ≤ span R t ↔ s ⊆ t :=
⟨le_of_span_le_span hl hsu htu, span_mono⟩

end module

section nontrivial

variables [ring R] [nontrivial R] [add_comm_group M] [add_comm_group M']
variables [module R M] [no_zero_smul_divisors R M] [module R M']
variables {v : ι → M} {s t : set M} {x y z : M}

lemma linear_independent_unique_iff
  (v : ι → M) [unique ι] :
  linear_independent R v ↔ v (default ι) ≠ 0 :=
begin
  simp only [linear_independent_iff, finsupp.total_unique, smul_eq_zero],
  refine ⟨λ h hv, _, λ hv l hl, finsupp.unique_ext $ hl.resolve_right hv⟩,
  have := h (finsupp.single (default ι) 1) (or.inr hv),
  exact one_ne_zero (finsupp.single_eq_zero.1 this)
end

alias linear_independent_unique_iff ↔ _ linear_independent_unique

lemma linear_independent_singleton {x : M} (hx : x ≠ 0) :
  linear_independent R (λ x, x : ({x} : set M) → M) :=
linear_independent_unique coe hx

end nontrivial

/-!
### Properties which require `division_ring K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/

section module

variables [division_ring K] [add_comm_group V] [add_comm_group V']
variables [module K V] [module K V']
variables {v : ι → V} {s t : set V} {x y z : V}

open submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/

lemma mem_span_insert_exchange : x ∈ span K (insert y s) → x ∉ span K s → y ∈ span K (insert x s) :=
begin
  simp [mem_span_insert],
  rintro a z hz rfl h,
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩,
  have a0 : a ≠ 0, {rintro rfl, simp * at *},
  simp [a0, smul_add, smul_smul]
end

lemma linear_independent_iff_not_mem_span :
  linear_independent K v ↔ (∀i, v i ∉ span K (v '' (univ \ {i}))) :=
begin
  apply linear_independent_iff_not_smul_mem_span.trans,
  split,
  { intros h i h_in_span,
    apply one_ne_zero (h i 1 (by simp [h_in_span])) },
  { intros h i a ha,
    by_contradiction ha',
    exact false.elim (h _ ((smul_mem_iff _ ha').1 ha)) }
end

lemma linear_independent.insert (hs : linear_independent K (λ b, b : s → V)) (hx : x ∉ span K s) :
  linear_independent K (λ b, b : insert x s → V) :=
begin
  rw ← union_singleton,
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem _) hx,
  apply hs.union (linear_independent_singleton x0),
  rwa [disjoint_span_singleton' x0]
end

lemma linear_independent_option' :
  linear_independent K (λ o, option.cases_on' o x v : option ι → V) ↔
    linear_independent K v ∧ (x ∉ submodule.span K (range v)) :=
begin
  rw [← linear_independent_equiv (equiv.option_equiv_sum_punit ι).symm, linear_independent_sum,
    @range_unique _ punit, @linear_independent_unique_iff punit, disjoint_span_singleton],
  dsimp [(∘)],
  refine ⟨λ h, ⟨h.1, λ hx, h.2.1 $ h.2.2 hx⟩, λ h, ⟨h.1, _, λ hx, (h.2 hx).elim⟩⟩,
  rintro rfl,
  exact h.2 (zero_mem _)
end

lemma linear_independent.option (hv : linear_independent K v)
  (hx : x ∉ submodule.span K (range v)) :
  linear_independent K (λ o, option.cases_on' o x v : option ι → V) :=
linear_independent_option'.2 ⟨hv, hx⟩

lemma linear_independent_option {v : option ι → V} :
  linear_independent K v ↔
    linear_independent K (v ∘ coe : ι → V) ∧ v none ∉ submodule.span K (range (v ∘ coe : ι → V)) :=
by simp only [← linear_independent_option', option.cases_on'_none_coe]

theorem linear_independent_insert' {ι} {s : set ι} {a : ι} {f : ι → V} (has : a ∉ s) :
  linear_independent K (λ x : insert a s, f x) ↔
  linear_independent K (λ x : s, f x) ∧ f a ∉ submodule.span K (f '' s) :=
by { rw [← linear_independent_equiv ((equiv.option_equiv_sum_punit _).trans
  (equiv.set.insert has).symm), linear_independent_option], simp [(∘), range_comp f] }

theorem linear_independent_insert (hxs : x ∉ s) :
  linear_independent K (λ b : insert x s, (b : V)) ↔
  linear_independent K (λ b : s, (b : V)) ∧ x ∉ submodule.span K s :=
(@linear_independent_insert' _ _ _ _ _ _ _ _ id hxs).trans $ by simp

lemma linear_independent_pair {x y : V} (hx : x ≠ 0) (hy : ∀ a : K, a • x ≠ y) :
  linear_independent K (coe : ({x, y} : set V) → V) :=
pair_comm y x ▸ (linear_independent_singleton hx).insert $ mt mem_span_singleton.1
  (not_exists.2 hy)

lemma linear_independent_fin_cons {n} {v : fin n → V} :
  linear_independent K (fin.cons x v : fin (n + 1) → V) ↔
    linear_independent K v ∧ x ∉ submodule.span K (range v) :=
begin
  rw [← linear_independent_equiv (fin_succ_equiv n).symm, linear_independent_option],
  convert iff.rfl,
  { ext,
    -- TODO: why doesn't simp use `fin_succ_equiv_symm_coe` here?
    rw [comp_app, comp_app, fin_succ_equiv_symm_coe, fin.cons_succ] },
  { rw [comp_app, fin_succ_equiv_symm_none, fin.cons_zero] },
  { ext,
    rw [comp_app, comp_app, fin_succ_equiv_symm_coe, fin.cons_succ] }
end

lemma linear_independent_fin_snoc {n} {v : fin n → V} :
  linear_independent K (fin.snoc v x : fin (n + 1) → V) ↔
    linear_independent K v ∧ x ∉ submodule.span K (range v) :=
by rw [fin.snoc_eq_cons_rotate, linear_independent_equiv, linear_independent_fin_cons]

/-- See `linear_independent.fin_cons'` for an uglier version that works if you
only have a module over a semiring. -/
lemma linear_independent.fin_cons {n} {v : fin n → V} (hv : linear_independent K v)
  (hx : x ∉ submodule.span K (range v)) :
  linear_independent K (fin.cons x v : fin (n + 1) → V) :=
linear_independent_fin_cons.2 ⟨hv, hx⟩

lemma linear_independent_fin_succ {n} {v : fin (n + 1) → V} :
  linear_independent K v ↔
    linear_independent K (fin.tail v) ∧ v 0 ∉ submodule.span K (range $ fin.tail v) :=
by rw [← linear_independent_fin_cons, fin.cons_self_tail]

lemma linear_independent_fin_succ' {n} {v : fin (n + 1) → V} :
  linear_independent K v ↔
    linear_independent K (fin.init v) ∧ v (fin.last _) ∉ submodule.span K (range $ fin.init v) :=
by rw [← linear_independent_fin_snoc, fin.snoc_init_self]

lemma linear_independent_fin2 {f : fin 2 → V} :
  linear_independent K f ↔ f 1 ≠ 0 ∧ ∀ a : K, a • f 1 ≠ f 0 :=
by rw [linear_independent_fin_succ, linear_independent_unique_iff, range_unique,
  mem_span_singleton, not_exists,
  show fin.tail f (default (fin 1)) = f 1, by rw ← fin.succ_zero_eq_one; refl]

lemma exists_linear_independent (hs : linear_independent K (λ x, x : s → V)) (hst : s ⊆ t) :
  ∃b⊆t, s ⊆ b ∧ t ⊆ span K b ∧ linear_independent K (λ x, x : b → V) :=
begin
  rcases zorn.zorn_subset_nonempty {b | b ⊆ t ∧ linear_independent K (λ x, x : b → V)} _ _
    ⟨hst, hs⟩ with ⟨b, ⟨bt, bi⟩, sb, h⟩,
  { refine ⟨b, bt, sb, λ x xt, _, bi⟩,
    by_contra hn,
    apply hn,
    rw ← h _ ⟨insert_subset.2 ⟨xt, bt⟩, bi.insert hn⟩ (subset_insert _ _),
    exact subset_span (mem_insert _ _) },
  { refine λ c hc cc c0, ⟨⋃₀ c, ⟨_, _⟩, λ x, _⟩,
    { exact sUnion_subset (λ x xc, (hc xc).1) },
    { exact linear_independent_sUnion_of_directed cc.directed_on (λ x xc, (hc xc).2) },
    { exact subset_sUnion_of_mem } }
end

/-- `linear_independent.extend` adds vectors to a linear independent set `s ⊆ t` until it spans
all elements of `t`. -/
noncomputable def linear_independent.extend (hs : linear_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : set V :=
classical.some (exists_linear_independent hs hst)

lemma linear_independent.extend_subset (hs : linear_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : hs.extend hst ⊆ t :=
let ⟨hbt, hsb, htb, hli⟩ := classical.some_spec (exists_linear_independent hs hst) in hbt

lemma linear_independent.subset_extend (hs : linear_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : s ⊆ hs.extend hst :=
let ⟨hbt, hsb, htb, hli⟩ := classical.some_spec (exists_linear_independent hs hst) in hsb

lemma linear_independent.subset_span_extend (hs : linear_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : t ⊆ span K (hs.extend hst) :=
let ⟨hbt, hsb, htb, hli⟩ := classical.some_spec (exists_linear_independent hs hst) in htb

lemma linear_independent.linear_independent_extend (hs : linear_independent K (λ x, x : s → V))
  (hst : s ⊆ t) : linear_independent K (coe : hs.extend hst → V) :=
let ⟨hbt, hsb, htb, hli⟩ := classical.some_spec (exists_linear_independent hs hst) in hli

variables {K V}

-- TODO(Mario): rewrite?
lemma exists_of_linear_independent_of_finite_span {t : finset V}
  (hs : linear_independent K (λ x, x : s → V)) (hst : s ⊆ (span K ↑t : submodule K V)) :
  ∃t':finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card :=
have ∀t, ∀(s' : finset V), ↑s' ⊆ s → s ∩ ↑t = ∅ → s ⊆ (span K ↑(s' ∪ t) : submodule K V) →
  ∃t':finset V, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
assume t, finset.induction_on t
  (assume s' hs' _ hss',
    have s = ↑s',
      from eq_of_linear_independent_of_span_subtype hs hs' $
          by simpa using hss',
    ⟨s', by simp [this]⟩)
  (assume b₁ t hb₁t ih s' hs' hst hss',
    have hb₁s : b₁ ∉ s,
      from assume h,
      have b₁ ∈ s ∩ ↑(insert b₁ t), from ⟨h, finset.mem_insert_self _ _⟩,
      by rwa [hst] at this,
    have hb₁s' : b₁ ∉ s', from assume h, hb₁s $ hs' h,
    have hst : s ∩ ↑t = ∅,
      from eq_empty_of_subset_empty $ subset.trans
        (by simp [inter_subset_inter, subset.refl]) (le_of_eq hst),
    classical.by_cases
      (assume : s ⊆ (span K ↑(s' ∪ t) : submodule K V),
        let ⟨u, hust, hsu, eq⟩ := ih _ hs' hst this in
        have hb₁u : b₁ ∉ u, from assume h, (hust h).elim hb₁s hb₁t,
        ⟨insert b₁ u, by simp [insert_subset_insert hust],
          subset.trans hsu (by simp), by simp [eq, hb₁t, hb₁s', hb₁u]⟩)
      (assume : ¬ s ⊆ (span K ↑(s' ∪ t) : submodule K V),
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this in
        have hb₂t' : b₂ ∉ s' ∪ t, from assume h, hb₂t $ subset_span h,
        have s ⊆ (span K ↑(insert b₂ s' ∪ t) : submodule K V), from
          assume b₃ hb₃,
          have ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : set V),
            by simp [insert_eq, -singleton_union, -union_singleton, union_subset_union, subset.refl,
              subset_union_right],
          have hb₃ : b₃ ∈ span K (insert b₁ (insert b₂ ↑(s' ∪ t) : set V)),
            from span_mono this (hss' hb₃),
          have s ⊆ (span K (insert b₁ ↑(s' ∪ t)) : submodule K V),
            by simpa [insert_eq, -singleton_union, -union_singleton] using hss',
          have hb₁ : b₁ ∈ span K (insert b₂ ↑(s' ∪ t)),
            from mem_span_insert_exchange (this hb₂s) hb₂t,
          by rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃,
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset, hb₂s, hs']) hst this in
        ⟨u, subset.trans hust $ union_subset_union (subset.refl _) (by simp [subset_insert]),
          hsu, by simp [eq, hb₂t', hb₁t, hb₁s']⟩)),
begin
  have eq : t.filter (λx, x ∈ s) ∪ t.filter (λx, x ∉ s) = t,
  { ext1 x,
    by_cases x ∈ s; simp * },
  apply exists.elim (this (t.filter (λx, x ∉ s)) (t.filter (λx, x ∈ s))
    (by simp [set.subset_def]) (by simp [set.ext_iff] {contextual := tt}) (by rwa [eq])),
  intros u h,
  exact ⟨u, subset.trans h.1 (by simp [subset_def, and_imp, or_imp_distrib] {contextual:=tt}),
    h.2.1, by simp only [h.2.2, eq]⟩
end

lemma exists_finite_card_le_of_finite_of_linear_independent_of_span
  (ht : finite t) (hs : linear_independent K (λ x, x : s → V)) (hst : s ⊆ span K t) :
  ∃h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
have s ⊆ (span K ↑(ht.to_finset) : submodule K V), by simp; assumption,
let ⟨u, hust, hsu, eq⟩ := exists_of_linear_independent_of_finite_span hs this in
have finite s, from u.finite_to_set.subset hsu,
⟨this, by rw [←eq]; exact (finset.card_le_of_subset $ finset.coe_subset.mp $ by simp [hsu])⟩

end module
