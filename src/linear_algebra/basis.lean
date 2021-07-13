/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import algebra.big_operators.finsupp
import data.fintype.card
import linear_algebra.finsupp
import linear_algebra.linear_independent
import linear_algebra.linear_pmap
import linear_algebra.projection

/-!

# Bases

This file defines bases in a module or vector space.

It is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

## Main definitions

All definitions are given for families of vectors, i.e. `v : ι → M` where `M` is the module or
vector space and `ι : Type*` is an arbitrary indexing type.

* `basis ι R M` is the type of `ι`-indexed `R`-bases for a module `M`,
  represented by a linear equiv `M ≃ₗ[R] ι →₀ R`.
* the basis vectors of a basis `b : basis ι R M` are available as `b i`, where `i : ι`

* `basis.repr` is the isomorphism sending `x : M` to its coordinates `basis.repr x : ι →₀ R`.
  The converse, turning this isomorphism into a basis, is called `basis.of_repr`.
* If `ι` is finite, there is a variant of `repr` called `basis.equiv_fun b : M ≃ₗ[R] ι → R`
  (saving you from having to work with `finsupp`). The converse, turning this isomorphism into
  a basis, is called `basis.of_equiv_fun`.

* `basis.constr hv f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.
* `basis.reindex` uses an equiv to map a basis to a different indexing set.
* `basis.map` uses a linear equiv to map a basis to a different module.

## Main statements

* `basis.mk`: a linear independent set of vectors spanning the whole module determines a basis

* `basis.ext` states that two linear maps are equal if they coincide on a basis.
  Similar results are available for linear equivs (if they coincide on the basis vectors),
  elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.

* `basis.of_vector_space` states that every vector space has a basis.

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

variables [semiring R]
variables [add_comm_monoid M] [module R M] [add_comm_monoid M'] [module R M']

section
variables (ι) (R) (M)

/-- A `basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.

The basis vectors are available as `coe_fn (b : basis ι R M) : ι → M`.
To turn a linear independent family of vectors spanning `M` into a basis, use `basis.mk`.
They are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,
available as `basis.repr`.
-/
structure basis := of_repr :: (repr : M ≃ₗ[R] (ι →₀ R))

end

namespace basis

instance : inhabited (basis ι R (ι →₀ R)) := ⟨basis.of_repr (linear_equiv.refl _ _)⟩

variables (b b₁ : basis ι R M) (i : ι) (c : R) (x : M)

section repr

/-- `b i` is the `i`th basis vector. -/
instance : has_coe_to_fun (basis ι R M) :=
{ F := λ _, ι → M,
  coe := λ b i, b.repr.symm (finsupp.single i 1) }

@[simp] lemma coe_of_repr (e : M ≃ₗ[R] (ι →₀ R)) :
  ⇑(of_repr e) = λ i, e.symm (finsupp.single i 1) :=
rfl

protected lemma injective [nontrivial R] : injective b :=
b.repr.symm.injective.comp (λ _ _, (finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).mp)

lemma repr_symm_single_one : b.repr.symm (finsupp.single i 1) = b i := rfl

lemma repr_symm_single : b.repr.symm (finsupp.single i c) = c • b i :=
calc b.repr.symm (finsupp.single i c)
    = b.repr.symm (c • finsupp.single i 1) : by rw [finsupp.smul_single', mul_one]
... = c • b i : by rw [linear_equiv.map_smul, repr_symm_single_one]

@[simp] lemma repr_self : b.repr (b i) = finsupp.single i 1 :=
linear_equiv.apply_symm_apply _ _

lemma repr_self_apply (j) [decidable (i = j)] :
  b.repr (b i) j = if i = j then 1 else 0 :=
by rw [repr_self, finsupp.single_apply]

@[simp] lemma repr_symm_apply (v) : b.repr.symm v = finsupp.total ι M R b v :=
calc b.repr.symm v = b.repr.symm (v.sum finsupp.single) : by simp
... = ∑ i in v.support, b.repr.symm (finsupp.single i (v i)) :
  by rw [finsupp.sum, linear_equiv.map_sum]
... = finsupp.total ι M R b v :
  by simp [repr_symm_single, finsupp.total_apply, finsupp.sum]

@[simp] lemma coe_repr_symm : ↑b.repr.symm = finsupp.total ι M R b :=
linear_map.ext (λ v, b.repr_symm_apply v)

@[simp] lemma repr_total (v) : b.repr (finsupp.total _ _ _ b v) = v :=
by { rw ← b.coe_repr_symm, exact b.repr.apply_symm_apply v }

@[simp] lemma total_repr : finsupp.total _ _ _ b (b.repr x) = x :=
by { rw ← b.coe_repr_symm, exact b.repr.symm_apply_apply x }

lemma repr_range : (b.repr : M →ₗ[R] (ι →₀ R)).range = finsupp.supported R R univ :=
by rw [linear_equiv.range, finsupp.supported_univ]

end repr

section coord

/-- `b.coord i` is the linear function giving the `i`'th coordinate of a vector
with respect to the basis `b`.

`b.coord i` is an element of the dual space. In particular, for
finite-dimensional spaces it is the `ι`th basis vector of the dual space.
-/
@[simps]
def coord (i : ι) : M →ₗ[R] R :=
(finsupp.lapply i).comp b.repr

lemma forall_coord_eq_zero_iff {x : M} :
  (∀ i, b.coord i x = 0) ↔ x = 0 :=
iff.trans
  (by simp only [b.coord_apply, finsupp.ext_iff, finsupp.zero_apply])
  b.repr.map_eq_zero_iff

end coord

section ext

variables {M₁ : Type*} [add_comm_monoid M₁] [module R M₁]

/-- Two linear maps are equal if they are equal on basis vectors. -/
theorem ext {f₁ f₂ : M →ₗ[R] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
by { ext x,
     rw [← b.total_repr x, finsupp.total_apply, finsupp.sum],
     simp only [linear_map.map_sum, linear_map.map_smul, h] }

/-- Two linear equivs are equal if they are equal on basis vectors. -/
theorem ext' {f₁ f₂ : M ≃ₗ[R] M₁} (h : ∀ i, f₁ (b i) = f₂ (b i)) : f₁ = f₂ :=
by { ext x,
      rw [← b.total_repr x, finsupp.total_apply, finsupp.sum],
      simp only [linear_equiv.map_sum, linear_equiv.map_smul, h] }

/-- Two elements are equal if their coordinates are equal. -/
theorem ext_elem {x y : M}
  (h : ∀ i, b.repr x i = b.repr y i) : x = y :=
by { rw [← b.total_repr x, ← b.total_repr y], congr' 1, ext i, exact h i }

lemma repr_eq_iff {b : basis ι R M} {f : M →ₗ[R] ι →₀ R} :
  ↑b.repr = f ↔ ∀ i, f (b i) = finsupp.single i 1 :=
⟨λ h i, h ▸ b.repr_self i,
 λ h, b.ext (λ i, (b.repr_self i).trans (h i).symm)⟩

lemma repr_eq_iff' {b : basis ι R M} {f : M ≃ₗ[R] ι →₀ R} :
  b.repr = f ↔ ∀ i, f (b i) = finsupp.single i 1 :=
⟨λ h i, h ▸ b.repr_self i,
  λ h, b.ext' (λ i, (b.repr_self i).trans (h i).symm)⟩

lemma apply_eq_iff {b : basis ι R M} {x : M} {i : ι} :
  b i = x ↔ b.repr x = finsupp.single i 1 :=
⟨λ h, h ▸ b.repr_self i,
 λ h, b.repr.injective ((b.repr_self i).trans h.symm)⟩

/-- An unbundled version of `repr_eq_iff` -/
lemma repr_apply_eq (f : M → ι → R)
  (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : R) (x : M), f (c • x) = c • f x)
  (f_eq : ∀ i, f (b i) = finsupp.single i 1) (x : M) (i : ι) :
  b.repr x i = f x i :=
begin
  let f_i : M →ₗ[R] R :=
  { to_fun := λ x, f x i,
    map_add' := λ _ _, by rw [hadd, pi.add_apply],
    map_smul' := λ _ _, by rw [hsmul, pi.smul_apply] },
  have : (finsupp.lapply i).comp ↑b.repr = f_i,
  { refine b.ext (λ j, _),
    show b.repr (b j) i = f (b j) i,
    rw [b.repr_self, f_eq] },
  calc b.repr x i = f_i x : by { rw ← this, refl }
              ... = f x i : rfl
end

/-- Two bases are equal if they assign the same coordinates. -/
lemma eq_of_repr_eq_repr {b₁ b₂ : basis ι R M} (h : ∀ x i, b₁.repr x i = b₂.repr x i) :
  b₁ = b₂ :=
have b₁.repr = b₂.repr, by { ext, apply h },
by { cases b₁, cases b₂, simpa }

/-- Two bases are equal if their basis vectors are the same. -/
@[ext] lemma eq_of_apply_eq {b₁ b₂ : basis ι R M} (h : ∀ i, b₁ i = b₂ i) : b₁ = b₂ :=
suffices b₁.repr = b₂.repr, by { cases b₁, cases b₂, simpa },
repr_eq_iff'.mpr (λ i, by rw [h, b₂.repr_self])

end ext

section map

variables (f : M ≃ₗ[R] M')

/-- Apply the linear equivalence `f` to the basis vectors. -/
@[simps] protected def map : basis ι R M' :=
of_repr (f.symm.trans b.repr)

@[simp] lemma map_apply (i) : b.map f i = f (b i) := rfl

end map

section reindex

variables (b' : basis ι' R M')
variables (e : ι ≃ ι')

/-- `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'` -/
def reindex : basis ι' R M :=
basis.of_repr (b.repr.trans (finsupp.dom_lcongr e))

lemma reindex_apply (i' : ι') : b.reindex e i' = b (e.symm i') :=
show (b.repr.trans (finsupp.dom_lcongr e)).symm (finsupp.single i' 1) =
  b.repr.symm (finsupp.single (e.symm i') 1),
by rw [linear_equiv.symm_trans_apply, finsupp.dom_lcongr_symm, finsupp.dom_lcongr_single]

@[simp] lemma coe_reindex : (b.reindex e : ι' → M) = b ∘ e.symm :=
funext (b.reindex_apply e)

@[simp] lemma coe_reindex_repr : ((b.reindex e).repr x : ι' → R) = b.repr x ∘ e.symm :=
funext $ λ i',
show (finsupp.dom_lcongr e : _ ≃ₗ[R] _) (b.repr x) i' = _,
by simp

@[simp] lemma reindex_repr (i' : ι') : (b.reindex e).repr x i' = b.repr x (e.symm i') :=
by rw coe_reindex_repr

/-- `simp` normal form version of `range_reindex` -/
@[simp] lemma range_reindex' : set.range (b ∘ e.symm) = set.range b :=
by rw [range_comp, equiv.range_eq_univ, set.image_univ]

lemma range_reindex : set.range (b.reindex e) = set.range b :=
by rw [coe_reindex, range_reindex']

/-- `b.reindex_range` is a basis indexed by `range b`, the basis vectors themselves. -/
def reindex_range : basis (range b) R M :=
if h : nontrivial R then
  by letI := h; exact b.reindex (equiv.of_injective b (basis.injective b))
else
  by letI : subsingleton R := not_nontrivial_iff_subsingleton.mp h; exact
    basis.of_repr (module.subsingleton_equiv R M (range b))

lemma finsupp.single_apply_left {α β γ : Type*} [has_zero γ]
  {f : α → β} (hf : function.injective f)
  (x z : α) (y : γ) :
  finsupp.single (f x) y (f z) = finsupp.single x y z :=
by simp [finsupp.single_apply, hf.eq_iff]

lemma reindex_range_self (i : ι) (h := set.mem_range_self i) :
  b.reindex_range ⟨b i, h⟩ = b i :=
begin
  by_cases htr : nontrivial R,
  { letI := htr,
    simp [htr, reindex_range, reindex_apply, equiv.apply_of_injective_symm b b.injective,
      subtype.coe_mk] },
  { letI : subsingleton R := not_nontrivial_iff_subsingleton.mp htr,
    letI := module.subsingleton R M,
    simp [reindex_range] }
end

lemma reindex_range_repr_self (i : ι) :
  b.reindex_range.repr (b i) = finsupp.single ⟨b i, mem_range_self i⟩ 1 :=
calc b.reindex_range.repr (b i) = b.reindex_range.repr (b.reindex_range ⟨b i, mem_range_self i⟩) :
  congr_arg _ (b.reindex_range_self _ _).symm
... = finsupp.single ⟨b i, mem_range_self i⟩ 1 : b.reindex_range.repr_self _

@[simp] lemma reindex_range_apply (x : range b) : b.reindex_range x = x :=
by { rcases x with ⟨bi, ⟨i, rfl⟩⟩, exact b.reindex_range_self i, }

lemma reindex_range_repr' (x : M) {bi : M} {i : ι} (h : b i = bi) :
  b.reindex_range.repr x ⟨bi, ⟨i, h⟩⟩ = b.repr x i :=
begin
  nontriviality,
  subst h,
  refine (b.repr_apply_eq (λ x i, b.reindex_range.repr x ⟨b i, _⟩) _ _ _ x i).symm,
  { intros x y,
    ext i,
    simp only [pi.add_apply, linear_equiv.map_add, finsupp.coe_add] },
  { intros c x,
    ext i,
    simp only [pi.smul_apply, linear_equiv.map_smul, finsupp.coe_smul] },
  { intros i,
    ext j,
    simp only [reindex_range_repr_self],
    refine @finsupp.single_apply_left _ _ _ _ (λ i, (⟨b i, _⟩ : set.range b)) _ _ _ _,
    exact λ i j h, b.injective (subtype.mk.inj h) }
end

@[simp] lemma reindex_range_repr (x : M) (i : ι) (h := set.mem_range_self i) :
  b.reindex_range.repr x ⟨b i, h⟩ = b.repr x i :=
b.reindex_range_repr' _ rfl

section fintype

variables [fintype ι]

/-- `b.reindex_finset_range` is a basis indexed by `finset.univ.image b`,
the finite set of basis vectors themselves. -/
def reindex_finset_range : basis (finset.univ.image b) R M :=
b.reindex_range.reindex ((equiv.refl M).subtype_equiv (by simp))

lemma reindex_finset_range_self (i : ι) (h := finset.mem_image_of_mem b (finset.mem_univ i)) :
  b.reindex_finset_range ⟨b i, h⟩ = b i :=
by { rw [reindex_finset_range, reindex_apply, reindex_range_apply], refl }

@[simp] lemma reindex_finset_range_apply (x : finset.univ.image b) :
  b.reindex_finset_range x = x :=
by { rcases x with ⟨bi, hbi⟩, rcases finset.mem_image.mp hbi with ⟨i, -, rfl⟩,
     exact b.reindex_finset_range_self i }

lemma reindex_finset_range_repr_self (i : ι) :
  b.reindex_finset_range.repr (b i) =
    finsupp.single ⟨b i, finset.mem_image_of_mem b (finset.mem_univ i)⟩ 1 :=
begin
  ext ⟨bi, hbi⟩,
  rw [reindex_finset_range, reindex_repr, reindex_range_repr_self],
  convert finsupp.single_apply_left ((equiv.refl M).subtype_equiv _).symm.injective _ _ _,
  refl
end

@[simp] lemma reindex_finset_range_repr (x : M) (i : ι)
  (h := finset.mem_image_of_mem b (finset.mem_univ i)) :
  b.reindex_finset_range.repr x ⟨b i, h⟩ = b.repr x i :=
by simp [reindex_finset_range]

end fintype

end reindex

protected lemma linear_independent : linear_independent R b :=
linear_independent_iff.mpr $ λ l hl,
calc l = b.repr (finsupp.total _ _ _ b l) : (b.repr_total l).symm
   ... = 0 : by rw [hl, linear_equiv.map_zero]

protected lemma ne_zero [nontrivial R] (i) : b i ≠ 0 :=
b.linear_independent.ne_zero i

protected lemma mem_span (x : M) : x ∈ span R (range b) :=
by { rw [← b.total_repr x, finsupp.total_apply, finsupp.sum],
     exact submodule.sum_mem _ (λ i hi, submodule.smul_mem _ _ (submodule.subset_span ⟨i, rfl⟩)) }

protected lemma span_eq : span R (range b) = ⊤ :=
eq_top_iff.mpr $ λ x _, b.mem_span x

section constr

variables (S : Type*) [semiring S] [module S M']
variables [smul_comm_class R S M']

/-- Construct a linear map given the value at the basis.

This definition is parameterized over an extra `semiring S`,
such that `smul_comm_class R S M'` holds.
If `R` is commutative, you can set `S := R`; if `R` is not commutative,
you can recover an `add_equiv` by setting `S := ℕ`.
See library note [bundled maps over different rings].
-/
def constr : (ι → M') ≃ₗ[S] (M →ₗ[R] M') :=
{ to_fun := λ f, (finsupp.total M' M' R id).comp $ (finsupp.lmap_domain R R f).comp b.repr,
  inv_fun := λ f i, f (b i),
  left_inv := λ f, by { ext, simp },
  right_inv := λ f, by { refine b.ext (λ i, _), simp },
  map_add' := λ f g, by { refine b.ext (λ i, _), simp },
  map_smul' := λ c f, by { refine b.ext (λ i, _), simp } }

theorem constr_def (f : ι → M') :
  b.constr S f = (finsupp.total M' M' R id).comp ((finsupp.lmap_domain R R f).comp b.repr) :=
rfl

theorem constr_apply (f : ι → M') (x : M) :
  b.constr S f x = (b.repr x).sum (λ b a, a • f b) :=
by { simp only [constr_def, linear_map.comp_apply, finsupp.lmap_domain_apply, finsupp.total_apply],
     rw finsupp.sum_map_domain_index; simp [add_smul] }

@[simp] lemma constr_basis (f : ι → M') (i : ι) :
  (b.constr S f : M → M') (b i) = f i :=
by simp [basis.constr_apply, b.repr_self]

lemma constr_eq {g : ι → M'} {f : M →ₗ[R] M'}
  (h : ∀i, g i = f (b i)) : b.constr S g = f :=
b.ext $ λ i, (b.constr_basis S g i).trans (h i)

lemma constr_self (f : M →ₗ[R] M') : b.constr S (λ i, f (b i)) = f :=
b.constr_eq S $ λ x, rfl

lemma constr_range [nonempty ι] {f : ι  → M'} :
  (b.constr S f).range = span R (range f) :=
by rw [b.constr_def S f, linear_map.range_comp, linear_map.range_comp, linear_equiv.range,
       ← finsupp.supported_univ, finsupp.lmap_domain_supported, ←set.image_univ,
       ← finsupp.span_image_eq_map_total, set.image_id]

@[simp]
lemma constr_comp (f : M' →ₗ[R] M') (v : ι → M') :
  b.constr S (f ∘ v) = f.comp (b.constr S v) :=
b.ext (λ i, by simp only [basis.constr_basis, linear_map.comp_apply])

end constr

section equiv

variables (b' : basis ι' R M') (e : ι ≃ ι')
variables [add_comm_monoid M''] [module R M'']

/-- If `b` is a basis for `M` and `b'` a basis for `M'`, and the index types are equivalent,
`b.equiv b' e` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `b' (e i)`. -/
protected def equiv : M ≃ₗ[R] M' :=
b.repr.trans (b'.reindex e.symm).repr.symm

@[simp] lemma equiv_apply : b.equiv b' e (b i) = b' (e i) :=
by simp [basis.equiv]

@[simp] lemma equiv_refl :
  b.equiv b (equiv.refl ι) = linear_equiv.refl R M :=
b.ext' (λ i, by simp)

@[simp] lemma equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm :=
b'.ext' $ λ i, (b.equiv b' e).injective (by simp)

@[simp] lemma equiv_trans {ι'' : Type*} (b'' : basis ι'' R M'')
  (e : ι ≃ ι') (e' : ι' ≃ ι'') :
  (b.equiv b' e).trans (b'.equiv b'' e') = b.equiv b'' (e.trans e') :=
b.ext' (λ i, by simp)

@[simp]
lemma map_equiv (b : basis ι R M) (b' : basis ι' R M') (e : ι ≃ ι') :
  b.map (b.equiv b' e) = b'.reindex e.symm :=
by { ext i, simp }

end equiv

section prod

variables (b' : basis ι' R M')

/-- `basis.prod` maps a `ι`-indexed basis for `M` and a `ι'`-indexed basis for `M'`
to a `ι ⊕ ι'`-index basis for `M × M'`. -/
protected def prod : basis (ι ⊕ ι') R (M × M') :=
of_repr ((b.repr.prod b'.repr).trans (finsupp.sum_finsupp_lequiv_prod_finsupp R).symm)

@[simp]
lemma prod_repr_inl (x) (i) : (b.prod b').repr x (sum.inl i) = b.repr x.1 i := rfl

@[simp]
lemma prod_repr_inr (x) (i) : (b.prod b').repr x (sum.inr i) = b'.repr x.2 i := rfl

lemma prod_apply_inl_fst (i) :
  (b.prod b' (sum.inl i)).1 = b i :=
b.repr.injective $ by
{ ext j,
  simp only [basis.prod, basis.coe_of_repr, linear_equiv.symm_trans_apply, linear_equiv.prod_symm,
      linear_equiv.prod_apply, b.repr.apply_symm_apply, linear_equiv.symm_symm, repr_self,
      equiv.to_fun_as_coe, finsupp.fst_sum_finsupp_lequiv_prod_finsupp],
  apply finsupp.single_apply_left sum.inl_injective }

lemma prod_apply_inr_fst (i) :
(b.prod b' (sum.inr i)).1 = 0 :=
b.repr.injective $ by
{ ext i,
  simp only [basis.prod, basis.coe_of_repr, linear_equiv.symm_trans_apply, linear_equiv.prod_symm,
      linear_equiv.prod_apply, b.repr.apply_symm_apply, linear_equiv.symm_symm, repr_self,
      equiv.to_fun_as_coe, finsupp.fst_sum_finsupp_lequiv_prod_finsupp, linear_equiv.map_zero,
      finsupp.zero_apply],
  apply finsupp.single_eq_of_ne sum.inr_ne_inl }

lemma prod_apply_inl_snd (i) :
  (b.prod b' (sum.inl i)).2 = 0 :=
b'.repr.injective $ by
{ ext j,
  simp only [basis.prod, basis.coe_of_repr, linear_equiv.symm_trans_apply, linear_equiv.prod_symm,
      linear_equiv.prod_apply, b'.repr.apply_symm_apply, linear_equiv.symm_symm, repr_self,
      equiv.to_fun_as_coe, finsupp.snd_sum_finsupp_lequiv_prod_finsupp, linear_equiv.map_zero,
      finsupp.zero_apply],
  apply finsupp.single_eq_of_ne sum.inl_ne_inr }

lemma prod_apply_inr_snd (i) :
(b.prod b' (sum.inr i)).2 = b' i :=
b'.repr.injective $ by
{ ext i,
  simp only [basis.prod, basis.coe_of_repr, linear_equiv.symm_trans_apply, linear_equiv.prod_symm,
      linear_equiv.prod_apply, b'.repr.apply_symm_apply, linear_equiv.symm_symm, repr_self,
      equiv.to_fun_as_coe, finsupp.snd_sum_finsupp_lequiv_prod_finsupp],
  apply finsupp.single_apply_left sum.inr_injective }

@[simp]
lemma prod_apply (i) :
  b.prod b' i = sum.elim (linear_map.inl R M M' ∘ b) (linear_map.inr R M M' ∘ b') i :=
by { ext; cases i; simp only [prod_apply_inl_fst, sum.elim_inl, linear_map.inl_apply,
                              prod_apply_inr_fst, sum.elim_inr, linear_map.inr_apply,
                              prod_apply_inl_snd, prod_apply_inr_snd, comp_app] }

end prod

section no_zero_smul_divisors

-- Can't be an instance because the basis can't be inferred.
protected lemma no_zero_smul_divisors [no_zero_divisors R] (b : basis ι R M) :
  no_zero_smul_divisors R M :=
⟨λ c x hcx, or_iff_not_imp_right.mpr (λ hx, begin
  rw [← b.total_repr x, ← linear_map.map_smul] at hcx,
  have := linear_independent_iff.mp b.linear_independent (c • b.repr x) hcx,
  rw smul_eq_zero at this,
  exact this.resolve_right (λ hr, hx (b.repr.map_eq_zero_iff.mp hr))
end)⟩

protected lemma smul_eq_zero [no_zero_divisors R] (b : basis ι R M) {c : R} {x : M} :
  c • x = 0 ↔ c = 0 ∨ x = 0 :=
@smul_eq_zero _ _ _ _ _ b.no_zero_smul_divisors _ _

end no_zero_smul_divisors

section singleton

/-- `basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`. -/
protected def singleton (ι R : Type*) [unique ι] [semiring R] :
  basis ι R R :=
of_repr
{ to_fun := λ x, finsupp.single (default ι) x,
  inv_fun := λ f, f (default ι),
  left_inv := λ x, by simp,
  right_inv := λ f, finsupp.unique_ext (by simp),
  map_add' := λ x y, by simp,
  map_smul' := λ c x, by simp }

@[simp] lemma singleton_apply (ι R : Type*) [unique ι] [semiring R] (i) :
  basis.singleton ι R i = 1 :=
apply_eq_iff.mpr (by simp [basis.singleton])

@[simp] lemma singleton_repr (ι R : Type*) [unique ι] [semiring R] (x i) :
  (basis.singleton ι R).repr x i = x :=
by simp [basis.singleton, unique.eq_default i]

lemma basis_singleton_iff
  {R M : Type*} [ring R] [nontrivial R] [add_comm_group M] [module R M] [no_zero_smul_divisors R M]
  (ι : Type*) [unique ι] :
  nonempty (basis ι R M) ↔ ∃ x ≠ 0, ∀ y : M, ∃ r : R, r • x = y :=
begin
  fsplit,
  { rintro ⟨b⟩,
    refine ⟨b (default ι), b.linear_independent.ne_zero _, _⟩,
    simpa [span_singleton_eq_top_iff, set.range_unique] using b.span_eq },
  { rintro ⟨x, nz, w⟩,
    refine ⟨of_repr $ linear_equiv.symm
      { to_fun := λ f, f (default ι) • x,
        inv_fun := λ y, finsupp.single (default ι) (w y).some,
        left_inv := λ f, finsupp.unique_ext _,
        right_inv := λ y, _,
        map_add' := λ y z, _,
        map_smul' := λ c y, _ }⟩,
    { rw [finsupp.smul_apply, smul_assoc] },
    { rw [finsupp.add_apply, add_smul] },
    { refine smul_right_injective _ nz _,
      simp only [finsupp.single_eq_same],
      exact (w (f (default ι) • x)).some_spec },
    { simp only [finsupp.single_eq_same],
      exact (w y).some_spec } }
end

end singleton

section empty

variables (M)

/-- If `M` is a subsingleton and `ι` is empty, this is the unique `ι`-indexed basis for `M`. -/
protected def empty [subsingleton M] [is_empty ι] : basis ι R M :=
of_repr 0

instance empty_unique [subsingleton M] [is_empty ι] : unique (basis ι R M) :=
{ default := basis.empty M, uniq := λ ⟨x⟩, congr_arg of_repr $ subsingleton.elim _ _ }

end empty

end basis

section fintype

open basis
open fintype

variables [fintype ι] (b : basis ι R M)

/-- A module over `R` with a finite basis is linearly equivalent to functions from its basis to `R`.
-/
def basis.equiv_fun : M ≃ₗ[R] (ι → R) :=
linear_equiv.trans b.repr
  { to_fun := coe_fn,
    map_add' := finsupp.coe_add,
    map_smul' := finsupp.coe_smul,
    ..finsupp.equiv_fun_on_fintype }

/-- A module over a finite ring that admits a finite basis is finite. -/
def module.fintype_of_fintype [fintype R] : fintype M :=
fintype.of_equiv _ b.equiv_fun.to_equiv.symm

theorem module.card_fintype [fintype R] [fintype M] :
  card M = (card R) ^ (card ι) :=
calc card M = card (ι → R)    : card_congr b.equiv_fun.to_equiv
        ... = card R ^ card ι : card_fun

/-- Given a basis `v` indexed by `ι`, the canonical linear equivalence between `ι → R` and `M` maps
a function `x : ι → R` to the linear combination `∑_i x i • v i`. -/
@[simp] lemma basis.equiv_fun_symm_apply (x : ι → R) :
  b.equiv_fun.symm x = ∑ i, x i • b i :=
by { simp [basis.equiv_fun, finsupp.total_apply, finsupp.sum_fintype],
     refl }

@[simp]
lemma basis.equiv_fun_apply (u : M) : b.equiv_fun u = b.repr u := rfl

lemma basis.sum_equiv_fun (u : M) : ∑ i, b.equiv_fun u i • b i = u :=
begin
  conv_rhs { rw ← b.total_repr u },
  simp [finsupp.total_apply, finsupp.sum_fintype, b.equiv_fun_apply]
end

lemma basis.sum_repr (u : M) : ∑ i, b.repr u i • b i = u :=
b.sum_equiv_fun u

@[simp]
lemma basis.equiv_fun_self (i j : ι) : b.equiv_fun (b i) j = if i = j then 1 else 0 :=
by { rw [b.equiv_fun_apply, b.repr_self_apply] }

/-- Define a basis by mapping each vector `x : M` to its coordinates `e x : ι → R`,
as long as `ι` is finite. -/
def basis.of_equiv_fun (e : M ≃ₗ[R] (ι → R)) : basis ι R M :=
basis.of_repr $ e.trans $ linear_equiv.symm $ finsupp.linear_equiv_fun_on_fintype R

@[simp] lemma basis.of_equiv_fun_repr_apply (e : M ≃ₗ[R] (ι → R)) (x : M) (i : ι) :
  (basis.of_equiv_fun e).repr x i = e x i := rfl

@[simp] lemma basis.coe_of_equiv_fun (e : M ≃ₗ[R] (ι → R)) :
  (basis.of_equiv_fun e : ι → M) = λ i, e.symm (function.update 0 i 1) :=
funext $ λ i, e.injective $ funext $ λ j,
  by simp [basis.of_equiv_fun, ←finsupp.single_eq_pi_single, finsupp.single_eq_update]

variables (S : Type*) [semiring S] [module S M']
variables [smul_comm_class R S M']

@[simp] theorem basis.constr_apply_fintype (f : ι → M') (x : M) :
  (b.constr S f : M → M') x = ∑ i, (b.equiv_fun x i) • f i :=
by simp [b.constr_apply, b.equiv_fun_apply, finsupp.sum_fintype]

end fintype

end module

section comm_semiring

namespace basis

variables [comm_semiring R]
variables [add_comm_monoid M] [module R M] [add_comm_monoid M'] [module R M']
variables (b : basis ι R M) (b' : basis ι' R M')

/-- If `b` is a basis for `M` and `b'` a basis for `M'`,
and `f`, `g` form a bijection between the basis vectors,
`b.equiv' b' f g hf hg hgf hfg` is a linear equivalence `M ≃ₗ[R] M'`, mapping `b i` to `f (b i)`.
-/
def equiv' (f : M → M') (g : M' → M)
  (hf : ∀ i, f (b i) ∈ range b') (hg : ∀ i, g (b' i) ∈ range b)
  (hgf : ∀i, g (f (b i)) = b i) (hfg : ∀i, f (g (b' i)) = b' i) :
  M ≃ₗ[R] M' :=
{ inv_fun := b'.constr R (g ∘ b'),
  left_inv :=
    have (b'.constr R (g ∘ b')).comp (b.constr R (f ∘ b)) = linear_map.id,
    from (b.ext $ λ i, exists.elim (hf i)
      (λ i' hi', by rw [linear_map.comp_apply, b.constr_basis, function.comp_apply, ← hi',
                        b'.constr_basis, function.comp_apply, hi', hgf, linear_map.id_apply])),
    λ x, congr_arg (λ (h : M →ₗ[R] M), h x) this,
  right_inv :=
    have (b.constr R (f ∘ b)).comp (b'.constr R (g ∘ b')) = linear_map.id,
    from (b'.ext $ λ i, exists.elim (hg i)
      (λ i' hi', by rw [linear_map.comp_apply, b'.constr_basis, function.comp_apply, ← hi',
                        b.constr_basis, function.comp_apply, hi', hfg, linear_map.id_apply])),
    λ x, congr_arg (λ (h : M' →ₗ[R] M'), h x) this,
  .. b.constr R (f ∘ b) }

@[simp] lemma equiv'_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι) :
  b.equiv' b' f g hf hg hgf hfg (b i) = f (b i) :=
b.constr_basis R _ _

@[simp] lemma equiv'_symm_apply (f : M → M') (g : M' → M) (hf hg hgf hfg) (i : ι') :
  (b.equiv' b' f g hf hg hgf hfg).symm (b' i) = g (b' i) :=
b'.constr_basis R _ _

lemma sum_repr_mul_repr {ι'} [fintype ι'] (b' : basis ι' R M) (x : M) (i : ι) :
  ∑ (j : ι'), b.repr (b' j) i * b'.repr x j = b.repr x i :=
begin
  conv_rhs { rw [← b'.sum_repr x] },
  simp_rw [linear_equiv.map_sum, linear_equiv.map_smul, finset.sum_apply'],
  refine finset.sum_congr rfl (λ j _, _),
  rw [finsupp.smul_apply, smul_eq_mul, mul_comm]
end

end basis

end comm_semiring

section module

open linear_map

variables {v : ι → M}
variables [ring R] [add_comm_group M] [add_comm_group M'] [add_comm_group M'']
variables [module R M] [module R M'] [module R M'']
variables {c d : R} {x y : M}
variables (b : basis ι R M)

namespace basis

section mk

variables (hli : linear_independent R v) (hsp : span R (range v) = ⊤)

/-- A linear independent family of vectors spanning the whole module is a basis. -/
protected noncomputable def mk : basis ι R M :=
basis.of_repr
{ inv_fun := finsupp.total _ _ _ v,
  left_inv := λ x, hli.total_repr ⟨x, _⟩,
  right_inv := λ x, hli.repr_eq rfl,
  .. hli.repr.comp (linear_map.id.cod_restrict _ (λ h, hsp.symm ▸ submodule.mem_top)) }

@[simp] lemma mk_repr :
  (basis.mk hli hsp).repr x = hli.repr ⟨x, hsp.symm ▸ submodule.mem_top⟩ :=
rfl

lemma mk_apply (i : ι) : basis.mk hli hsp i = v i :=
show finsupp.total _ _ _ v _ = v i, by simp

@[simp] lemma coe_mk : ⇑(basis.mk hli hsp) = v :=
funext (mk_apply _ _)

end mk

section span

variables (hli : linear_independent R v)

/-- A linear independent family of vectors is a basis for their span. -/
protected noncomputable def span : basis ι R (span R (range v)) :=
basis.mk (linear_independent_span hli) $
begin
  rw eq_top_iff,
  intros x _,
  have h₁ : subtype.val '' set.range (λ i, subtype.mk (v i) _) = range v,
  { rw ← set.range_comp },
  have h₂ : map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _)))
    = span R (range v),
  { rw [← span_image, submodule.subtype_eq_val, h₁] },
  have h₃ : (x : M) ∈ map (submodule.subtype _) (span R (set.range (λ i, subtype.mk (v i) _))),
  { rw h₂, apply subtype.mem x },
  rcases mem_map.1 h₃ with ⟨y, hy₁, hy₂⟩,
  have h_x_eq_y : x = y,
  { rw [subtype.ext_iff, ← hy₂], simp },
  rwa h_x_eq_y
end

end span

lemma group_smul_span_eq_top
  {G : Type*} [group G] [distrib_mul_action G R] [distrib_mul_action G M]
  [is_scalar_tower G R M] {v : ι → M} (hv : submodule.span R (set.range v) = ⊤) {w : ι → G} :
  submodule.span R (set.range (w • v)) = ⊤ :=
begin
  rw eq_top_iff,
  intros j hj,
  rw ← hv at hj,
  rw submodule.mem_span at hj ⊢,
  refine λ p hp, hj p (λ u hu, _),
  obtain ⟨i, rfl⟩ := hu,
  have : ((w i)⁻¹ • 1 : R) • w i • v i ∈ p := p.smul_mem ((w i)⁻¹ • 1 : R) (hp ⟨i, rfl⟩),
  rwa [smul_one_smul, inv_smul_smul] at this,
end

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` are elements of a group,
`group_smul` provides the basis corresponding to `w • v`. -/
def group_smul {G : Type*} [group G] [distrib_mul_action G R] [distrib_mul_action G M]
  [is_scalar_tower G R M] [smul_comm_class G R M] (v : basis ι R M) (w : ι → G) :
  basis ι R M :=
@basis.mk ι R M (w • v) _ _ _
  (v.linear_independent.group_smul w) (group_smul_span_eq_top v.span_eq)

lemma group_smul_apply {G : Type*} [group G] [distrib_mul_action G R] [distrib_mul_action G M]
  [is_scalar_tower G R M] [smul_comm_class G R M] {v : basis ι R M} {w : ι → G} (i : ι) :
  v.group_smul w i = (w • v : ι → M) i :=
mk_apply
  (v.linear_independent.group_smul w) (group_smul_span_eq_top v.span_eq) i

lemma units_smul_span_eq_top {v : ι → M} (hv : submodule.span R (set.range v) = ⊤)
  {w : ι → units R} : submodule.span R (set.range (w • v)) = ⊤ :=
group_smul_span_eq_top hv

/-- Given a basis `v` and a map `w` such that for all `i`, `w i` is a unit, `smul_of_is_unit`
provides the basis corresponding to `w • v`. -/
def units_smul (v : basis ι R M) (w : ι → units R) :
  basis ι R M :=
@basis.mk ι R M (w • v) _ _ _
  (v.linear_independent.units_smul w) (units_smul_span_eq_top v.span_eq)

lemma units_smul_apply {v : basis ι R M} {w : ι → units R} (i : ι) :
  v.units_smul w i = w i • v i :=
mk_apply
  (v.linear_independent.units_smul w) (units_smul_span_eq_top v.span_eq) i

/-- A version of `smul_of_units` that uses `is_unit`. -/
def is_unit_smul (v : basis ι R M) {w : ι → R} (hw : ∀ i, is_unit (w i)):
  basis ι R M :=
units_smul v (λ i, (hw i).unit)

lemma is_unit_smul_apply {v : basis ι R M} {w : ι → R} (hw : ∀ i, is_unit (w i)) (i : ι) :
  v.is_unit_smul hw i = w i • v i :=
begin
  convert units_smul_apply i,
  exact (is_unit.unit_spec (hw i)).symm,
end

end basis

end module

section division_ring

variables [division_ring K] [add_comm_group V] [add_comm_group V'] [module K V] [module K V']
variables {v : ι → V} {s t : set V} {x y z : V}

include K

open submodule

namespace basis

section exists_basis

/-- If `s` is a linear independent set of vectors, we can extend it to a basis. -/
noncomputable def extend (hs : linear_independent K (coe : s → V)) :
  basis _ K V :=
basis.mk
  (@linear_independent.restrict_of_comp_subtype _ _ _ id _ _ _ _ (hs.linear_independent_extend _))
  (eq_top_iff.mpr $ set_like.coe_subset_coe.mp $
    by simpa using hs.subset_span_extend (subset_univ s))

lemma extend_apply_self (hs : linear_independent K (coe : s → V))
  (x : hs.extend _) :
  basis.extend hs x = x :=
basis.mk_apply _ _ _

@[simp] lemma coe_extend (hs : linear_independent K (coe : s → V)) :
  ⇑(basis.extend hs) = coe :=
funext (extend_apply_self hs)

lemma range_extend (hs : linear_independent K (coe : s → V)) :
  range (basis.extend hs) = hs.extend (subset_univ _) :=
by rw [coe_extend, subtype.range_coe_subtype, set_of_mem_eq]

/-- If `v` is a linear independent family of vectors, extend it to a basis indexed by a sum type. -/
noncomputable def sum_extend (hs : linear_independent K v) :
  basis (ι ⊕ _) K V :=
let s := set.range v,
    e : ι ≃ s := equiv.of_injective v hs.injective,
    b := hs.to_subtype_range.extend (subset_univ (set.range v)) in
(basis.extend hs.to_subtype_range).reindex $ equiv.symm $
  calc ι ⊕ (b \ s : set V) ≃ s ⊕ (b \ s : set V) : equiv.sum_congr e (equiv.refl _)
  ... ≃ b                   : equiv.set.sum_diff_subset (hs.to_subtype_range.subset_extend _)

lemma subset_extend {s : set V} (hs : linear_independent K (coe : s → V)) :
  s ⊆ hs.extend (set.subset_univ _) :=
hs.subset_extend _

section

variables (K V)

/-- A set used to index `basis.of_vector_space`. -/
noncomputable def of_vector_space_index : set V :=
(linear_independent_empty K V).extend (subset_univ _)

/-- Each vector space has a basis. -/
noncomputable def of_vector_space : basis (of_vector_space_index K V) K V :=
basis.extend (linear_independent_empty K V)

lemma of_vector_space_apply_self (x : of_vector_space_index K V) :
  of_vector_space K V x = x :=
basis.mk_apply _ _ _

@[simp] lemma coe_of_vector_space :
  ⇑(of_vector_space K V) = coe :=
funext (λ x, of_vector_space_apply_self K V x)

lemma of_vector_space_index.linear_independent :
  linear_independent K (coe : of_vector_space_index K V → V) :=
by { convert (of_vector_space K V).linear_independent, ext x, rw of_vector_space_apply_self }

lemma range_of_vector_space :
  range (of_vector_space K V) = of_vector_space_index K V :=
range_extend _

lemma exists_basis : ∃ s : set V, nonempty (basis s K V) :=
⟨of_vector_space_index K V, ⟨of_vector_space K V⟩⟩

end

end exists_basis

end basis

open fintype
variables (K V)

theorem vector_space.card_fintype [fintype K] [fintype V] :
  ∃ n : ℕ, card V = (card K) ^ n :=
⟨card (basis.of_vector_space_index K V), module.card_fintype (basis.of_vector_space K V)⟩

end division_ring

section field

variables [field K] [add_comm_group V] [add_comm_group V'] [module K V] [module K V']
variables {v : ι → V} {s t : set V} {x y z : V}

lemma linear_map.exists_left_inverse_of_injective (f : V →ₗ[K] V')
  (hf_inj : f.ker = ⊥) : ∃g:V' →ₗ V, g.comp f = linear_map.id :=
begin
  let B := basis.of_vector_space_index K V,
  let hB := basis.of_vector_space K V,
  have hB₀ : _ := hB.linear_independent.to_subtype_range,
  have : linear_independent K (λ x, x : f '' B → V'),
  { have h₁ : linear_independent K (λ (x : ↥(⇑f '' range (basis.of_vector_space _ _))), ↑x) :=
         @linear_independent.image_subtype _ _ _ _ _ _ _ _ _ f hB₀
      (show disjoint _ _, by simp [hf_inj]),
    rwa [basis.range_of_vector_space K V] at h₁ },
  let C := this.extend (subset_univ _),
  have BC := this.subset_extend (subset_univ _),
  let hC := basis.extend this,
  haveI : inhabited V := ⟨0⟩,
  refine ⟨hC.constr K (C.restrict (inv_fun f)), hB.ext (λ b, _)⟩,
  rw image_subset_iff at BC,
  have fb_eq : f b = hC ⟨f b, BC b.2⟩,
  { change f b = basis.extend this _,
    rw [basis.extend_apply_self, subtype.coe_mk] },
  dsimp [hB],
  rw [basis.of_vector_space_apply_self, fb_eq, hC.constr_basis],
  exact left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _
end

lemma submodule.exists_is_compl (p : submodule K V) : ∃ q : submodule K V, is_compl p q :=
let ⟨f, hf⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype in
⟨f.ker, linear_map.is_compl_of_proj $ linear_map.ext_iff.1 hf⟩

instance module.submodule.is_complemented : is_complemented (submodule K V) :=
⟨submodule.exists_is_compl⟩

lemma linear_map.exists_right_inverse_of_surjective (f : V →ₗ[K] V')
  (hf_surj : f.range = ⊤) : ∃g:V' →ₗ V, f.comp g = linear_map.id :=
begin
  let C := basis.of_vector_space_index K V',
  let hC := basis.of_vector_space K V',
  haveI : inhabited V := ⟨0⟩,
  use hC.constr K (C.restrict (inv_fun f)),
  refine hC.ext (λ c, _),
  rw [linear_map.comp_apply, hC.constr_basis],
  simp [right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) c]
end

/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
lemma linear_map.exists_extend {p : submodule K V} (f : p →ₗ[K] V') :
  ∃ g : V →ₗ[K] V', g.comp p.subtype = f :=
let ⟨g, hg⟩ := p.subtype.exists_left_inverse_of_injective p.ker_subtype in
⟨f.comp g, by rw [linear_map.comp_assoc, hg, f.comp_id]⟩

open submodule linear_map

/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
lemma submodule.exists_le_ker_of_lt_top (p : submodule K V) (hp : p < ⊤) :
  ∃ f ≠ (0 : V →ₗ[K] K), p ≤ ker f :=
begin
  rcases set_like.exists_of_lt hp with ⟨v, -, hpv⟩, clear hp,
  rcases (linear_pmap.sup_span_singleton ⟨p, 0⟩ v (1 : K) hpv).to_fun.exists_extend with ⟨f, hf⟩,
  refine ⟨f, _, _⟩,
  { rintro rfl, rw [linear_map.zero_comp] at hf,
    have := linear_pmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv 0 p.zero_mem 1,
    simpa using (linear_map.congr_fun hf _).trans this },
  { refine λ x hx, mem_ker.2 _,
    have := linear_pmap.sup_span_singleton_apply_mk ⟨p, 0⟩ v (1 : K) hpv x hx 0,
    simpa using (linear_map.congr_fun hf _).trans this }
end

theorem quotient_prod_linear_equiv (p : submodule K V) :
  nonempty ((p.quotient × p) ≃ₗ[K] V) :=
let ⟨q, hq⟩ := p.exists_is_compl in nonempty.intro $
((quotient_equiv_of_is_compl p q hq).prod (linear_equiv.refl _ _)).trans
  (prod_equiv_of_is_compl q p hq.symm)

end field
