/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import linear_algebra.dimension
import ring_theory.principal_ideal_domain

/-!
# Finite dimensional vector spaces

Definition and basic properties of finite dimensional vector spaces, of their dimensions, and
of linear maps on such spaces.

## Main definitions

Assume `V` is a vector space over a field `K`. There are (at least) three equivalent definitions of
finite-dimensionality of `V`:

- it admits a finite basis.
- it is finitely generated.
- it is noetherian, i.e., every subspace is finitely generated.

We introduce a typeclass `finite_dimensional K V` capturing this property. For ease of transfer of
proof, it is defined using the third point of view, i.e., as `is_noetherian`. However, we prove
that all these points of view are equivalent, with the following lemmas
(in the namespace `finite_dimensional`):

- `exists_is_basis_finite` states that a finite-dimensional vector space has a finite basis
- `of_fintype_basis` states that the existence of a basis indexed by a finite type implies
  finite-dimensionality
- `of_finset_basis` states that the existence of a basis indexed by a `finset` implies
  finite-dimensionality
- `of_finite_basis` states that the existence of a basis indexed by a finite set implies
  finite-dimensionality
- `iff_fg` states that the space is finite-dimensional if and only if it is finitely generated

Also defined is `findim`, the dimension of a finite dimensional space, returning a `nat`,
as opposed to `dim`, which returns a `cardinal`. When the space has infinite dimension, its
`findim` is by convention set to `0`.

Preservation of finite-dimensionality and formulas for the dimension are given for
- submodules
- quotients (for the dimension of a quotient, see `findim_quotient_add_findim`)
- linear equivs, in `linear_equiv.finite_dimensional` and `linear_equiv.findim_eq`
- image under a linear map (the rank-nullity formula is in `findim_range_add_findim_ker`)

Basic properties of linear maps of a finite-dimensional vector space are given. Notably, the
equivalence of injectivity and surjectivity is proved in `linear_map.injective_iff_surjective`,
and the equivalence between left-inverse and right-inverse in `mul_eq_one_comm` and
`comp_eq_id_comm`.

## Implementation notes

Most results are deduced from the corresponding results for the general dimension (as a cardinal),
in `dimension.lean`. Not all results have been ported yet.

One of the characterizations of finite-dimensionality is in terms of finite generation. This
property is currently defined only for submodules, so we express it through the fact that the
maximal submodule (which, as a set, coincides with the whole space) is finitely generated. This is
not very convenient to use, although there are some helper functions. However, this becomes very
convenient when speaking of submodules which are finite-dimensional, as this notion coincides with
the fact that the submodule is finitely generated (as a submodule of the whole space). This
equivalence is proved in `submodule.fg_iff_finite_dimensional`.
-/

universes u v v' w
open_locale classical

open vector_space cardinal submodule module function

variables {K : Type u} {V : Type v} [field K] [add_comm_group V] [vector_space K V]
{V₂ : Type v'} [add_comm_group V₂] [vector_space K V₂]

/-- `finite_dimensional` vector spaces are defined to be noetherian modules.
Use `finite_dimensional.iff_fg` or `finite_dimensional.of_fintype_basis` to prove finite dimension
from a conventional definition. -/
@[reducible] def finite_dimensional (K V : Type*) [field K]
  [add_comm_group V] [vector_space K V] := is_noetherian K V

namespace finite_dimensional

open is_noetherian

/-- A vector space is finite-dimensional if and only if its dimension (as a cardinal) is strictly
less than the first infinite cardinal `omega`. -/
lemma finite_dimensional_iff_dim_lt_omega : finite_dimensional K V ↔ dim K V < omega.{v} :=
begin
  cases exists_is_basis K V with b hb,
  have := is_basis.mk_eq_dim hb,
  simp only [lift_id] at this,
  rw [← this, lt_omega_iff_fintype, ← @set.set_of_mem_eq _ b, ← subtype.range_coe_subtype],
  split,
  { intro, resetI, convert finite_of_linear_independent hb.1, simp },
  { assume hbfinite,
    refine @is_noetherian_of_linear_equiv K (⊤ : submodule K V) V _
      _ _ _ _ (linear_equiv.of_top _ rfl) (id _),
    refine is_noetherian_of_fg_of_noetherian _ ⟨set.finite.to_finset hbfinite, _⟩,
    rw [set.finite.coe_to_finset, ← hb.2], refl }
end

/-- The dimension of a finite-dimensional vector space, as a cardinal, is strictly less than the
first infinite cardinal `omega`. -/
lemma dim_lt_omega (K V : Type*) [field K] [add_comm_group V] [vector_space K V] :
  ∀ [finite_dimensional K V], dim K V < omega.{v} :=
finite_dimensional_iff_dim_lt_omega.1

/-- In a finite dimensional space, there exists a finite basis. A basis is in general given as a
function from an arbitrary type to the vector space. Here, we think of a basis as a set (instead of
a function), and use as parametrizing type this set (and as a function the coercion
  `coe : s → V`).
-/
variables (K V)
lemma exists_is_basis_finite [finite_dimensional K V] :
  ∃ s : set V, (is_basis K (coe : s → V)) ∧ s.finite :=
begin
  cases exists_is_basis K V with s hs,
  exact ⟨s, hs, finite_of_linear_independent hs.1⟩
end

/-- In a finite dimensional space, there exists a finite basis. Provides the basis as a finset.
This is in contrast to `exists_is_basis_finite`, which provides a set and a `set.finite`.
-/
lemma exists_is_basis_finset [finite_dimensional K V] :
  ∃ b : finset V, is_basis K (coe : (↑b : set V) → V) :=
begin
  obtain ⟨s, s_basis, s_finite⟩ := exists_is_basis_finite K V,
  refine ⟨s_finite.to_finset, _⟩,
  rw set.finite.coe_to_finset,
  exact s_basis,
end

/-- A finite dimensional vector space over a finite field is finite -/
noncomputable def fintype_of_fintype [fintype K] [finite_dimensional K V] : fintype V :=
module.fintype_of_fintype (classical.some_spec (finite_dimensional.exists_is_basis_finset K V) : _)

variables {K V}

/-- A vector space is finite-dimensional if and only if it is finitely generated. As the
finitely-generated property is a property of submodules, we formulate this in terms of the
maximal submodule, equal to the whole space as a set by definition.-/
lemma iff_fg :
  finite_dimensional K V ↔ (⊤ : submodule K V).fg :=
begin
  split,
  { introI h,
    rcases exists_is_basis_finite K V with ⟨s, s_basis, s_finite⟩,
    exact ⟨s_finite.to_finset, by { convert s_basis.2, simp }⟩ },
  { rintros ⟨s, hs⟩,
    rw [finite_dimensional_iff_dim_lt_omega, ← dim_top, ← hs],
    exact lt_of_le_of_lt (dim_span_le _) (lt_omega_iff_finite.2 (set.finite_mem_finset s)) }
end

/-- If a vector space has a finite basis, then it is finite-dimensional. -/
lemma of_fintype_basis {ι : Type w} [fintype ι] {b : ι → V} (h : is_basis K b) :
  finite_dimensional K V :=
iff_fg.2 $ ⟨finset.univ.image b, by {convert h.2, simp} ⟩

/-- If a vector space has a basis indexed by elements of a finite set, then it is
finite-dimensional. -/
lemma of_finite_basis {ι} {s : set ι} {b : s → V} (h : is_basis K b) (hs : set.finite s) :
  finite_dimensional K V :=
by haveI := hs.fintype; exact of_fintype_basis h

/-- If a vector space has a finite basis, then it is finite-dimensional, finset style. -/
lemma of_finset_basis {ι} {s : finset ι} {b : (↑s : set ι) → V} (h : is_basis K b) :
  finite_dimensional K V :=
of_finite_basis h s.finite_to_set

/-- A subspace of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_submodule [finite_dimensional K V] (S : submodule K V) :
  finite_dimensional K S :=
finite_dimensional_iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_submodule_le _) (dim_lt_omega K V))

/-- A quotient of a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_quotient [finite_dimensional K V] (S : submodule K V) :
  finite_dimensional K (quotient S) :=
finite_dimensional_iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_quotient_le _) (dim_lt_omega K V))

/-- The dimension of a finite-dimensional vector space as a natural number. Defined by convention to
be `0` if the space is infinite-dimensional. -/
noncomputable def findim (K V : Type*) [field K]
  [add_comm_group V] [vector_space K V] : ℕ :=
if h : dim K V < omega.{v} then classical.some (lt_omega.1 h) else 0

/-- In a finite-dimensional space, its dimension (seen as a cardinal) coincides with its `findim`. -/
lemma findim_eq_dim (K : Type u) (V : Type v) [field K]
  [add_comm_group V] [vector_space K V] [finite_dimensional K V] :
  (findim K V : cardinal.{v}) = dim K V :=
begin
  have : findim K V = classical.some (lt_omega.1 (dim_lt_omega K V)) :=
    dif_pos (dim_lt_omega K V),
  rw this,
  exact (classical.some_spec (lt_omega.1 (dim_lt_omega K V))).symm
end

lemma findim_of_infinite_dimensional {K V : Type*} [field K] [add_comm_group V] [vector_space K V]
  (h : ¬finite_dimensional K V) : findim K V = 0 :=
dif_neg $ mt finite_dimensional_iff_dim_lt_omega.2 h

/-- If a vector space has a finite basis, then its dimension (seen as a cardinal) is equal to the
cardinality of the basis. -/
lemma dim_eq_card_basis {ι : Type w} [fintype ι] {b : ι → V} (h : is_basis K b) :
  dim K V = fintype.card ι :=
by rw [←h.mk_range_eq_dim, cardinal.fintype_card,
       set.card_range_of_injective h.injective]

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. -/
lemma findim_eq_card_basis {ι : Type w} [fintype ι] {b : ι → V} (h : is_basis K b) :
  findim K V = fintype.card ι :=
begin
  haveI : finite_dimensional K V := of_fintype_basis h,
  have := dim_eq_card_basis h,
  rw ← findim_eq_dim at this,
  exact_mod_cast this
end

/-- If a vector space is finite-dimensional, then the cardinality of any basis is equal to its
`findim`. -/
lemma findim_eq_card_basis' [finite_dimensional K V] {ι : Type w} {b : ι → V} (h : is_basis K b) :
  (findim K V : cardinal.{w}) = cardinal.mk ι :=
begin
  rcases exists_is_basis_finite K V with ⟨s, s_basis, s_finite⟩,
  letI: fintype s := s_finite.fintype,
  have A : cardinal.mk s = fintype.card s := fintype_card _,
  have B : findim K V = fintype.card s := findim_eq_card_basis s_basis,
  have C : cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{v w} (cardinal.mk s) :=
    mk_eq_mk_of_basis h s_basis,
  rw [A, ← B, lift_nat_cast] at C,
  have : cardinal.lift.{w v} (cardinal.mk ι) = cardinal.lift.{w v} (findim K V),
    by { simp, exact C },
  exact (lift_inj.mp this).symm
end

/-- If a vector space has a finite basis, then its dimension is equal to the cardinality of the
basis. This lemma uses a `finset` instead of indexed types. -/
lemma findim_eq_card_finset_basis {b : finset V}
  (h : is_basis K (subtype.val : (↑b : set V) -> V)) :
  findim K V = finset.card b :=
by { rw [findim_eq_card_basis h, fintype.subtype_card], intros x, refl }

lemma equiv_fin {ι : Type*} [finite_dimensional K V] {v : ι → V} (hv : is_basis K v) :
  ∃ g : fin (findim K V) ≃ ι, is_basis K (v ∘ g) :=
begin
  have : (cardinal.mk (fin $ findim K V)).lift = (cardinal.mk ι).lift,
  { simp [cardinal.mk_fin (findim K V), ← findim_eq_card_basis' hv] },
  rcases cardinal.lift_mk_eq.mp this with ⟨g⟩,
  exact ⟨g, hv.comp _ g.bijective⟩
end

variables (K V)

lemma fin_basis [finite_dimensional K V] : ∃ v : fin (findim K V) → V, is_basis K v :=
let ⟨B, hB, B_fin⟩ := exists_is_basis_finite K V, ⟨g, hg⟩ := finite_dimensional.equiv_fin hB in
⟨coe ∘ g, hg⟩

variables {K V}

lemma cardinal_mk_le_findim_of_linear_independent
  [finite_dimensional K V] {ι : Type w} {b : ι → V} (h : linear_independent K b) :
  cardinal.mk ι ≤ findim K V :=
begin
  rw ← lift_le.{_ (max v w)},
  simpa [← findim_eq_dim K V] using
    cardinal_lift_le_dim_of_linear_independent.{_ _ _ (max v w)} h
end

lemma fintype_card_le_findim_of_linear_independent
  [finite_dimensional K V] {ι : Type*} [fintype ι] {b : ι → V} (h : linear_independent K b) :
  fintype.card ι ≤ findim K V :=
by simpa [fintype_card] using cardinal_mk_le_findim_of_linear_independent h

lemma finset_card_le_findim_of_linear_independent [finite_dimensional K V] {b : finset V}
  (h : linear_independent K (λ x, x : (↑b : set V) → V)) :
  b.card ≤ findim K V :=
begin
  rw ←fintype.card_coe,
  exact fintype_card_le_findim_of_linear_independent h,
end

lemma lt_omega_of_linear_independent {ι : Type w} [finite_dimensional K V]
  {v : ι → V} (h : linear_independent K v) :
  cardinal.mk ι < cardinal.omega :=
begin
  apply cardinal.lift_lt.1,
  apply lt_of_le_of_lt,
  apply linear_independent_le_dim h,
  rw [←findim_eq_dim, cardinal.lift_omega, cardinal.lift_nat_cast],
  apply cardinal.nat_lt_omega,
end

lemma not_linear_independent_of_infinite {ι : Type w} [inf : infinite ι] [finite_dimensional K V]
  (v : ι → V) : ¬ linear_independent K v :=
begin
  intro h_lin_indep,
  have : ¬ omega ≤ mk ι := not_le.mpr (lt_omega_of_linear_independent h_lin_indep),
  have : omega ≤ mk ι := infinite_iff.mp inf,
  contradiction
end

/-- A finite dimensional space has positive `findim` iff it has a nonzero element. -/
lemma findim_pos_iff_exists_ne_zero [finite_dimensional K V] : 0 < findim K V ↔ ∃ x : V, x ≠ 0 :=
iff.trans (by { rw ← findim_eq_dim, norm_cast }) (@dim_pos_iff_exists_ne_zero K V _ _ _)

/-- A finite dimensional space has positive `findim` iff it is nontrivial. -/
lemma findim_pos_iff [finite_dimensional K V] : 0 < findim K V ↔ nontrivial V :=
iff.trans (by { rw ← findim_eq_dim, norm_cast }) (@dim_pos_iff_nontrivial K V _ _ _)

/-- A nontrivial finite dimensional space has positive `findim`. -/
lemma findim_pos [finite_dimensional K V] [h : nontrivial V] : 0 < findim K V :=
findim_pos_iff.mpr h

section
open_locale big_operators
open finset

/--
If a finset has cardinality larger than the dimension of the space,
then there is a nontrivial linear relation amongst its elements.
-/
lemma exists_nontrivial_relation_of_dim_lt_card
  [finite_dimensional K V] {t : finset V} (h : findim K V < t.card) :
  ∃ f : V → K, ∑ e in t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 :=
begin
  have := mt finset_card_le_findim_of_linear_independent (by { simpa using h }),
  rw linear_dependent_iff at this,
  obtain ⟨s, g, sum, z, zm, nonzero⟩ := this,
  -- Now we have to extend `g` to all of `t`, then to all of `V`.
  let f : V → K := λ x, if h : x ∈ t then if (⟨x, h⟩ : (↑t : set V)) ∈ s then g ⟨x, h⟩ else 0 else 0,
  -- and finally clean up the mess caused by the extension.
  refine ⟨f, _, _⟩,
  { dsimp [f],
    rw ← sum,
    fapply sum_bij_ne_zero (λ v hvt _, (⟨v, hvt⟩ : {v // v ∈ t})),
    { intros v hvt H, dsimp,
      rw [dif_pos hvt] at H,
      contrapose! H,
      rw [if_neg H, zero_smul], },
    { intros _ _ _ _ _ _, exact subtype.mk.inj, },
    { intros b hbs hb,
      use b,
      simpa only [hbs, exists_prop, dif_pos, finset.mk_coe, and_true, if_true, finset.coe_mem,
        eq_self_iff_true, exists_prop_of_true, ne.def] using hb, },
    { intros a h₁, dsimp, rw [dif_pos h₁],
      intro h₂, rw [if_pos], contrapose! h₂,
      rw [if_neg h₂, zero_smul], }, },
  { refine ⟨z, z.2, _⟩, dsimp only [f], erw [dif_pos z.2, if_pos]; rwa [subtype.coe_eta] },
end

/--
If a finset has cardinality larger than `findim + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero.
-/
lemma exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card
  [finite_dimensional K V] {t : finset V} (h : findim K V + 1 < t.card) :
  ∃ f : V → K, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 :=
begin
  -- Pick an element x₀ ∈ t,
  have card_pos : 0 < t.card := lt_trans (nat.succ_pos _) h,
  obtain ⟨x₀, m⟩ := (finset.card_pos.1 card_pos).bex,
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : V ↪ V := ⟨λ x, x - x₀, sub_left_injective⟩,
  let t' := (t.erase x₀).map shift,
  have h' : findim K V < t'.card,
  { simp only [t', card_map, finset.card_erase_of_mem m],
    exact nat.lt_pred_iff.mpr h, },
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_dim_lt_card h',
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e in t, f e = 0`.
  let f : V → K := λ z, if z = x₀ then - ∑ z in (t.erase x₀), g (z - x₀) else g (z - x₀),
  refine ⟨f, _ ,_ ,_⟩,
  -- After this, it's a matter of verifiying the properties,
  -- based on the corresponding properties for `g`.
  { show ∑ (e : V) in t, f e • e = 0,
    -- We prove this by splitting off the `x₀` term of the sum,
    -- which is itself a sum over `t.erase x₀`,
    -- combining the two sums, and
    -- observing that after reindexing we have exactly
    -- ∑ (x : V) in t', g x • x = 0.
    simp only [f],
    conv_lhs { apply_congr, skip, rw [ite_smul], },
    rw [finset.sum_ite],
    conv { congr, congr, apply_congr, simp [filter_eq', m], },
    conv { congr, congr, skip, apply_congr, simp [filter_ne'], },
    rw [sum_singleton, neg_smul, add_comm, ←sub_eq_add_neg, sum_smul, ←sum_sub_distrib],
    simp only [←smul_sub],
    -- At the end we have to reindex the sum, so we use `change` to
    -- express the summand using `shift`.
    change (∑ (x : V) in t.erase x₀, (λ e, g e • e) (shift x)) = 0,
    rw ←sum_map _ shift,
    exact gsum, },
  { show ∑ (e : V) in t, f e = 0,
    -- Again we split off the `x₀` term,
    -- observing that it exactly cancels the other terms.
    rw [← insert_erase m, sum_insert (not_mem_erase x₀ t)],
    dsimp [f],
    rw [if_pos rfl],
    conv_lhs { congr, skip, apply_congr, skip, rw if_neg (show x ≠ x₀, from (mem_erase.mp H).1), },
    exact neg_add_self _, },
  { show ∃ (x : V) (H : x ∈ t), f x ≠ 0,
    -- We can use x₁ + x₀.
    refine ⟨x₁ + x₀, _, _⟩,
    { rw finset.mem_map at x₁_mem,
      rcases x₁_mem with ⟨x₁, x₁_mem, rfl⟩,
      rw mem_erase at x₁_mem,
      simp only [x₁_mem, sub_add_cancel, function.embedding.coe_fn_mk], },
    { dsimp only [f],
      rwa [if_neg, add_sub_cancel],
      rw [add_left_eq_self], rintro rfl,
      simpa only [sub_eq_zero, exists_prop, finset.mem_map, embedding.coe_fn_mk, eq_self_iff_true,
        mem_erase, not_true, exists_eq_right, ne.def, false_and] using x₁_mem, } },
end

section
variables {L : Type*} [linear_ordered_field L]
variables {W : Type v} [add_comm_group W] [vector_space L W]

/--
A slight strengthening of `exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card`
available when working over an ordered field:
we can ensure a positive coefficient, not just a nonzero coefficient.
-/
lemma exists_relation_sum_zero_pos_coefficient_of_dim_succ_lt_card
  [finite_dimensional L W] {t : finset W} (h : findim L W + 1 < t.card) :
  ∃ f : W → L, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, 0 < f x :=
begin
  obtain ⟨f, sum, total, nonzero⟩ := exists_nontrivial_relation_sum_zero_of_dim_succ_lt_card h,
  exact ⟨f, sum, total, exists_pos_of_sum_zero_of_exists_nonzero f total nonzero⟩,
end

end

end

/-- If a submodule has maximal dimension in a finite dimensional space, then it is equal to the
whole space. -/
lemma eq_top_of_findim_eq [finite_dimensional K V] {S : submodule K V}
  (h : findim K S = findim K V) : S = ⊤ :=
begin
  cases exists_is_basis K S with bS hbS,
  have : linear_independent K (subtype.val : (subtype.val '' bS : set V) → V),
    from @linear_independent.image_subtype _ _ _ _ _ _ _ _ _
      (submodule.subtype S) hbS.1 (by simp),
  cases exists_subset_is_basis this with b hb,
  letI : fintype b := classical.choice (finite_of_linear_independent hb.2.1),
  letI : fintype (subtype.val '' bS) := classical.choice (finite_of_linear_independent this),
  letI : fintype bS := classical.choice (finite_of_linear_independent hbS.1),
  have : subtype.val '' bS = b, from set.eq_of_subset_of_card_le hb.1
    (by rw [set.card_image_of_injective _ subtype.val_injective, ← findim_eq_card_basis hbS,
         ← findim_eq_card_basis hb.2, h]; apply_instance),
  erw [← hb.2.2, subtype.range_coe, ← this, ← subtype_eq_val, span_image],
  have := hbS.2,
  erw [subtype.range_coe] at this,
  rw [this, map_top (submodule.subtype S), range_subtype],
end

variable (K)
/-- A field is one-dimensional as a vector space over itself. -/
@[simp] lemma findim_of_field : findim K K = 1 :=
begin
  have := dim_of_field K,
  rw [← findim_eq_dim] at this,
  exact_mod_cast this
end

/-- The vector space of functions on a fintype has finite dimension. -/
instance finite_dimensional_fintype_fun {ι : Type*} [fintype ι] :
  finite_dimensional K (ι → K) :=
by { rw [finite_dimensional_iff_dim_lt_omega, dim_fun'], exact nat_lt_omega _ }

/-- The vector space of functions on a fintype ι has findim equal to the cardinality of ι. -/
@[simp] lemma findim_fintype_fun_eq_card {ι : Type v} [fintype ι] :
  findim K (ι → K) = fintype.card ι :=
begin
  have : vector_space.dim K (ι → K) = fintype.card ι := dim_fun',
  rwa [← findim_eq_dim, nat_cast_inj] at this,
end

/-- The vector space of functions on `fin n` has findim equal to `n`. -/
@[simp] lemma findim_fin_fun {n : ℕ} : findim K (fin n → K) = n :=
by simp

/-- The submodule generated by a finite set is finite-dimensional. -/
theorem span_of_finite {A : set V} (hA : set.finite A) : finite_dimensional K (submodule.span K A) :=
is_noetherian_span_of_finite K hA

/-- The submodule generated by a single element is finite-dimensional. -/
instance (x : V) : finite_dimensional K (K ∙ x) := by {apply span_of_finite, simp}

end finite_dimensional

section zero_dim

open vector_space finite_dimensional

lemma finite_dimensional_of_dim_eq_zero (h : vector_space.dim K V = 0) : finite_dimensional K V :=
by rw [finite_dimensional_iff_dim_lt_omega, h]; exact cardinal.omega_pos

lemma finite_dimensional_of_dim_eq_one (h : vector_space.dim K V = 1) : finite_dimensional K V :=
by rw [finite_dimensional_iff_dim_lt_omega, h]; exact one_lt_omega

lemma findim_eq_zero_of_dim_eq_zero [finite_dimensional K V] (h : vector_space.dim K V = 0) :
  findim K V = 0 :=
begin
  convert findim_eq_dim K V,
  rw h, norm_cast
end

variables (K V)

lemma finite_dimensional_bot : finite_dimensional K (⊥ : submodule K V) :=
finite_dimensional_of_dim_eq_zero $ by simp

@[simp] lemma findim_bot : findim K (⊥ : submodule K V) = 0 :=
begin
  haveI := finite_dimensional_bot K V,
  convert findim_eq_dim K (⊥ : submodule K V),
  rw dim_bot, norm_cast
end

variables {K V}

lemma bot_eq_top_of_dim_eq_zero (h : vector_space.dim K V = 0) : (⊥ : submodule K V) = ⊤ :=
begin
  haveI := finite_dimensional_of_dim_eq_zero h,
  apply eq_top_of_findim_eq,
  rw [findim_bot, findim_eq_zero_of_dim_eq_zero h]
end

@[simp] theorem dim_eq_zero {S : submodule K V} : dim K S = 0 ↔ S = ⊥ :=
⟨λ h, (submodule.eq_bot_iff _).2 $ λ x hx, congr_arg subtype.val $
  ((submodule.eq_bot_iff _).1 $ eq.symm $ bot_eq_top_of_dim_eq_zero h) ⟨x, hx⟩ submodule.mem_top,
λ h, by rw [h, dim_bot]⟩

@[simp] theorem findim_eq_zero {S : submodule K V} [finite_dimensional K S] : findim K S = 0 ↔ S = ⊥ :=
by rw [← dim_eq_zero, ← findim_eq_dim, ← @nat.cast_zero cardinal, cardinal.nat_cast_inj]

end zero_dim

namespace submodule
open finite_dimensional

/-- A submodule is finitely generated if and only if it is finite-dimensional -/
theorem fg_iff_finite_dimensional (s : submodule K V) :
  s.fg ↔ finite_dimensional K s :=
⟨λh, is_noetherian_of_fg_of_noetherian s h,
 λh, by { rw ← map_subtype_top s, exact fg_map (iff_fg.1 h) }⟩

/-- A submodule contained in a finite-dimensional submodule is
finite-dimensional. -/
lemma finite_dimensional_of_le {S₁ S₂ : submodule K V} [finite_dimensional K S₂] (h : S₁ ≤ S₂) :
  finite_dimensional K S₁ :=
finite_dimensional_iff_dim_lt_omega.2 (lt_of_le_of_lt (dim_le_of_submodule _ _ h)
                                                      (dim_lt_omega K S₂))

/-- The inf of two submodules, the first finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_left (S₁ S₂ : submodule K V) [finite_dimensional K S₁] :
  finite_dimensional K (S₁ ⊓ S₂ : submodule K V) :=
finite_dimensional_of_le inf_le_left

/-- The inf of two submodules, the second finite-dimensional, is
finite-dimensional. -/
instance finite_dimensional_inf_right (S₁ S₂ : submodule K V) [finite_dimensional K S₂] :
  finite_dimensional K (S₁ ⊓ S₂ : submodule K V) :=
finite_dimensional_of_le inf_le_right

/-- The sup of two finite-dimensional submodules is
finite-dimensional. -/
instance finite_dimensional_sup (S₁ S₂ : submodule K V) [h₁ : finite_dimensional K S₁]
  [h₂ : finite_dimensional K S₂] : finite_dimensional K (S₁ ⊔ S₂ : submodule K V) :=
begin
  rw ←submodule.fg_iff_finite_dimensional at *,
  exact submodule.fg_sup h₁ h₂
end

/-- In a finite-dimensional vector space, the dimensions of a submodule and of the corresponding
quotient add up to the dimension of the space. -/
theorem findim_quotient_add_findim [finite_dimensional K V] (s : submodule K V) :
  findim K s.quotient + findim K s = findim K V :=
begin
  have := dim_quotient_add_dim s,
  rw [← findim_eq_dim, ← findim_eq_dim, ← findim_eq_dim] at this,
  exact_mod_cast this
end

/-- The dimension of a submodule is bounded by the dimension of the ambient space. -/
lemma findim_le [finite_dimensional K V] (s : submodule K V) : findim K s ≤ findim K V :=
by { rw ← s.findim_quotient_add_findim, exact nat.le_add_left _ _ }

/-- The dimension of a strict submodule is strictly bounded by the dimension of the ambient space. -/
lemma findim_lt [finite_dimensional K V] {s : submodule K V} (h : s < ⊤) :
  findim K s < findim K V :=
begin
  rw [← s.findim_quotient_add_findim, add_comm],
  exact nat.lt_add_of_zero_lt_left _ _ (findim_pos_iff.mpr (quotient.nontrivial_of_lt_top _ h))
end

/-- The dimension of a quotient is bounded by the dimension of the ambient space. -/
lemma findim_quotient_le [finite_dimensional K V] (s : submodule K V) :
  findim K s.quotient ≤ findim K V :=
by { rw ← s.findim_quotient_add_findim, exact nat.le_add_right _ _ }

/-- The sum of the dimensions of s + t and s ∩ t is the sum of the dimensions of s and t -/
theorem dim_sup_add_dim_inf_eq (s t : submodule K V) [finite_dimensional K s]
  [finite_dimensional K t] : findim K ↥(s ⊔ t) + findim K ↥(s ⊓ t) = findim K ↥s + findim K ↥t :=
begin
  have key : dim K ↥(s ⊔ t) + dim K ↥(s ⊓ t) = dim K s + dim K t := dim_sup_add_dim_inf_eq s t,
  repeat { rw ←findim_eq_dim at key },
  norm_cast at key,
  exact key
end

lemma eq_top_of_disjoint [finite_dimensional K V] (s t : submodule K V)
  (hdim : findim K s + findim K t = findim K V)
  (hdisjoint : disjoint s t) : s ⊔ t = ⊤ :=
begin
  have h_findim_inf : findim K ↥(s ⊓ t) = 0,
  { rw [disjoint, le_bot_iff] at hdisjoint,
    rw [hdisjoint, findim_bot] },
  apply eq_top_of_findim_eq,
  rw ←hdim,
  convert s.dim_sup_add_dim_inf_eq t,
  rw h_findim_inf,
  refl,
end

end submodule

namespace linear_equiv
open finite_dimensional

/-- Finite dimensionality is preserved under linear equivalence. -/
protected theorem finite_dimensional (f : V ≃ₗ[K] V₂) [finite_dimensional K V] :
  finite_dimensional K V₂ :=
is_noetherian_of_linear_equiv f

/-- The dimension of a finite dimensional space is preserved under linear equivalence. -/
theorem findim_eq (f : V ≃ₗ[K] V₂) [finite_dimensional K V] :
  findim K V = findim K V₂ :=
begin
  haveI : finite_dimensional K V₂ := f.finite_dimensional,
  simpa [← findim_eq_dim] using f.lift_dim_eq
end

end linear_equiv

namespace finite_dimensional

/--
Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
theorem nonempty_linear_equiv_of_findim_eq [finite_dimensional K V] [finite_dimensional K V₂]
  (cond : findim K V = findim K V₂) : nonempty (V ≃ₗ[K] V₂) :=
nonempty_linear_equiv_of_lift_dim_eq $ by simp only [← findim_eq_dim, cond, lift_nat_cast]

/--
Two finite-dimensional vector spaces are isomorphic if and only if they have the same (finite) dimension.
-/
theorem nonempty_linear_equiv_iff_findim_eq [finite_dimensional K V] [finite_dimensional K V₂] :
   nonempty (V ≃ₗ[K] V₂) ↔ findim K V = findim K V₂ :=
⟨λ ⟨h⟩, h.findim_eq, λ h, nonempty_linear_equiv_of_findim_eq h⟩

section

variables (V V₂)

/--
Two finite-dimensional vector spaces are isomorphic if they have the same (finite) dimension.
-/
noncomputable def linear_equiv.of_findim_eq [finite_dimensional K V] [finite_dimensional K V₂]
  (cond : findim K V = findim K V₂) : V ≃ₗ[K] V₂ :=
classical.choice $ nonempty_linear_equiv_of_findim_eq cond

end

lemma eq_of_le_of_findim_le {S₁ S₂ : submodule K V} [finite_dimensional K S₂] (hle : S₁ ≤ S₂)
  (hd : findim K S₂ ≤ findim K S₁) : S₁ = S₂ :=
begin
  rw ←linear_equiv.findim_eq (submodule.comap_subtype_equiv_of_le hle) at hd,
  exact le_antisymm hle (submodule.comap_subtype_eq_top.1 (eq_top_of_findim_eq
    (le_antisymm (comap (submodule.subtype S₂) S₁).findim_le hd))),
end

/-- If a submodule is less than or equal to a finite-dimensional
submodule with the same dimension, they are equal. -/
lemma eq_of_le_of_findim_eq {S₁ S₂ : submodule K V} [finite_dimensional K S₂] (hle : S₁ ≤ S₂)
  (hd : findim K S₁ = findim K S₂) : S₁ = S₂ :=
eq_of_le_of_findim_le hle hd.ge

end finite_dimensional

namespace linear_map
open finite_dimensional

/-- On a finite-dimensional space, an injective linear map is surjective. -/
lemma surjective_of_injective [finite_dimensional K V] {f : V →ₗ[K] V}
  (hinj : injective f) : surjective f :=
begin
  have h := dim_eq_of_injective _ hinj,
  rw [← findim_eq_dim, ← findim_eq_dim, nat_cast_inj] at h,
  exact range_eq_top.1 (eq_top_of_findim_eq h.symm)
end

/-- On a finite-dimensional space, a linear map is injective if and only if it is surjective. -/
lemma injective_iff_surjective [finite_dimensional K V] {f : V →ₗ[K] V} :
  injective f ↔ surjective f :=
⟨surjective_of_injective,
  λ hsurj, let ⟨g, hg⟩ := f.exists_right_inverse_of_surjective (range_eq_top.2 hsurj) in
  have function.right_inverse g f, from linear_map.ext_iff.1 hg,
  (left_inverse_of_surjective_of_right_inverse
    (surjective_of_injective this.injective) this).injective⟩

lemma ker_eq_bot_iff_range_eq_top [finite_dimensional K V] {f : V →ₗ[K] V} :
  f.ker = ⊥ ↔ f.range = ⊤ :=
by rw [range_eq_top, ker_eq_bot, injective_iff_surjective]

/-- In a finite-dimensional space, if linear maps are inverse to each other on one side then they
are also inverse to each other on the other side. -/
lemma mul_eq_one_of_mul_eq_one [finite_dimensional K V] {f g : V →ₗ[K] V} (hfg : f * g = 1) :
  g * f = 1 :=
have ginj : injective g, from has_left_inverse.injective
  ⟨f, (λ x, show (f * g) x = (1 : V →ₗ[K] V) x, by rw hfg; refl)⟩,
let ⟨i, hi⟩ := g.exists_right_inverse_of_surjective
  (range_eq_top.2 (injective_iff_surjective.1 ginj)) in
have f * (g * i) = f * 1, from congr_arg _ hi,
by rw [← mul_assoc, hfg, one_mul, mul_one] at this; rwa ← this

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
lemma mul_eq_one_comm [finite_dimensional K V] {f g : V →ₗ[K] V} : f * g = 1 ↔ g * f = 1 :=
⟨mul_eq_one_of_mul_eq_one, mul_eq_one_of_mul_eq_one⟩

/-- In a finite-dimensional space, linear maps are inverse to each other on one side if and only if
they are inverse to each other on the other side. -/
lemma comp_eq_id_comm [finite_dimensional K V] {f g : V →ₗ[K] V} : f.comp g = id ↔ g.comp f = id :=
mul_eq_one_comm

/-- The image under an onto linear map of a finite-dimensional space is also finite-dimensional. -/
lemma finite_dimensional_of_surjective [h : finite_dimensional K V]
  (f : V →ₗ[K] V₂) (hf : f.range = ⊤) : finite_dimensional K V₂ :=
is_noetherian_of_surjective V f hf

/-- The range of a linear map defined on a finite-dimensional space is also finite-dimensional. -/
instance finite_dimensional_range [h : finite_dimensional K V] (f : V →ₗ[K] V₂) :
  finite_dimensional K f.range :=
f.quot_ker_equiv_range.finite_dimensional

/-- rank-nullity theorem : the dimensions of the kernel and the range of a linear map add up to
the dimension of the source space. -/
theorem findim_range_add_findim_ker [finite_dimensional K V] (f : V →ₗ[K] V₂) :
  findim K f.range + findim K f.ker = findim K V :=
by { rw [← f.quot_ker_equiv_range.findim_eq], exact submodule.findim_quotient_add_findim _ }

end linear_map

namespace linear_equiv
open finite_dimensional
variables [finite_dimensional K V]

/-- The linear equivalence corresponging to an injective endomorphism. -/
noncomputable def of_injective_endo (f : V →ₗ[K] V) (h_inj : f.ker = ⊥) : V ≃ₗ[K] V :=
(linear_equiv.of_injective f h_inj).trans (linear_equiv.of_top _ (linear_map.ker_eq_bot_iff_range_eq_top.1 h_inj))

lemma of_injective_endo_to_fun (f : V →ₗ[K] V) (h_inj : f.ker = ⊥) :
  (of_injective_endo f h_inj).to_fun = f := rfl

lemma of_injective_endo_right_inv (f : V →ₗ[K] V) (h_inj : f.ker = ⊥) :
  f * (of_injective_endo f h_inj).symm = 1 :=
begin
  ext,
  simp only [linear_map.one_app, linear_map.mul_app],
  change f ((of_injective_endo f h_inj).symm x) = x,
  rw ← linear_equiv.inv_fun_apply (of_injective_endo f h_inj),
  apply (of_injective_endo f h_inj).right_inv,
end

lemma of_injective_endo_left_inv (f : V →ₗ[K] V) (h_inj : f.ker = ⊥) :
  ((of_injective_endo f h_inj).symm : V →ₗ[K] V) * f = 1 :=
begin
  ext,
  simp only [linear_map.one_app, linear_map.mul_app],
  change (of_injective_endo f h_inj).symm (f x) = x,
  rw ← linear_equiv.inv_fun_apply (of_injective_endo f h_inj),
  apply (of_injective_endo f h_inj).left_inv,
end

end linear_equiv

namespace linear_map

lemma is_unit_iff [finite_dimensional K V] (f : V →ₗ[K] V): is_unit f ↔ f.ker = ⊥ :=
begin
  split,
  { intro h_is_unit,
    rcases h_is_unit with ⟨u, hu⟩,
    rw [←hu, linear_map.ker_eq_bot'],
    intros x hx,
    change (1 : V →ₗ[K] V) x = 0,
    rw ← u.inv_val,
    change u.inv (u x) = 0,
    simp [hx] },
  { intro h_inj,
    use ⟨f, (linear_equiv.of_injective_endo f h_inj).symm.to_linear_map,
      linear_equiv.of_injective_endo_right_inv f h_inj, linear_equiv.of_injective_endo_left_inv f h_inj⟩,
    refl }
end

end linear_map

open vector_space finite_dimensional

section top

@[simp]
theorem findim_top : findim K (⊤ : submodule K V) = findim K V :=
by { unfold findim, simp [dim_top] }

end top

namespace linear_map

theorem injective_iff_surjective_of_findim_eq_findim [finite_dimensional K V]
  [finite_dimensional K V₂] (H : findim K V = findim K V₂) {f : V →ₗ[K] V₂} :
  function.injective f ↔ function.surjective f :=
begin
  have := findim_range_add_findim_ker f,
  rw [← ker_eq_bot, ← range_eq_top], refine ⟨λ h, _, λ h, _⟩,
  { rw [h, findim_bot, add_zero, H] at this, exact eq_top_of_findim_eq this },
  { rw [h, findim_top, H] at this, exact findim_eq_zero.1 (add_right_injective _ this) }
end

theorem findim_le_findim_of_injective [finite_dimensional K V] [finite_dimensional K V₂]
  {f : V →ₗ[K] V₂} (hf : function.injective f) : findim K V ≤ findim K V₂ :=
calc  findim K V
    = findim K f.range + findim K f.ker : (findim_range_add_findim_ker f).symm
... = findim K f.range : by rw [ker_eq_bot.2 hf, findim_bot, add_zero]
... ≤ findim K V₂ : submodule.findim_le _

end linear_map

namespace alg_hom

lemma bijective {F : Type*} [field F] {E : Type*} [field E] [algebra F E]
  [finite_dimensional F E] (ϕ : E →ₐ[F] E) : function.bijective ϕ :=
have inj : function.injective ϕ.to_linear_map := ϕ.to_ring_hom.injective,
⟨inj, (linear_map.injective_iff_surjective_of_findim_eq_findim rfl).mp inj⟩

end alg_hom

/-- Bijection between algebra equivalences and algebra homomorphisms -/
noncomputable def alg_equiv_equiv_alg_hom (F : Type u) [field F] (E : Type v) [field E]
  [algebra F E] [finite_dimensional F E] : (E ≃ₐ[F] E) ≃ (E →ₐ[F] E) :=
{ to_fun := λ ϕ, ϕ.to_alg_hom,
  inv_fun := λ ϕ, alg_equiv.of_bijective ϕ ϕ.bijective,
  left_inv := λ _, by {ext, refl},
  right_inv := λ _, by {ext, refl} }

section

/-- An integral domain that is module-finite as an algebra over a field is a field. -/
noncomputable def field_of_finite_dimensional (F K : Type*) [field F] [integral_domain K]
  [algebra F K] [finite_dimensional F K] : field K :=
{ inv := λ x, if H : x = 0 then 0 else classical.some $
    (show function.surjective (algebra.lmul_left F x), from
      linear_map.injective_iff_surjective.1 $ λ _ _, (mul_right_inj' H).1) 1,
  mul_inv_cancel := λ x hx, show x * dite _ _ _ = _, by { rw dif_neg hx,
    exact classical.some_spec ((show function.surjective (algebra.lmul_left F x), from
      linear_map.injective_iff_surjective.1 $ λ _ _, (mul_right_inj' hx).1) 1) },
  inv_zero := dif_pos rfl,
  .. ‹integral_domain K› }

end

namespace submodule

lemma findim_mono [finite_dimensional K V] :
  monotone (λ (s : submodule K V), findim K s) :=
λ s t hst,
calc findim K s = findim K (comap t.subtype s)
  : linear_equiv.findim_eq (comap_subtype_equiv_of_le hst).symm
... ≤ findim K t : submodule.findim_le _

lemma lt_of_le_of_findim_lt_findim {s t : submodule K V}
  (le : s ≤ t) (lt : findim K s < findim K t) : s < t :=
lt_of_le_of_ne le (λ h, ne_of_lt lt (by rw h))

lemma lt_top_of_findim_lt_findim {s : submodule K V}
  (lt : findim K s < findim K V) : s < ⊤ :=
begin
  by_cases fin : (finite_dimensional K V),
  { haveI := fin,
    rw ← @findim_top K V at lt,
    exact lt_of_le_of_findim_lt_findim le_top lt },
  { exfalso,
    have : findim K V = 0 := dif_neg (mt finite_dimensional_iff_dim_lt_omega.mpr fin),
    rw this at lt,
    exact nat.not_lt_zero _ lt }
end

lemma findim_lt_findim_of_lt [finite_dimensional K V] {s t : submodule K V} (hst : s < t) :
  findim K s < findim K t :=
begin
  rw linear_equiv.findim_eq (comap_subtype_equiv_of_le (le_of_lt hst)).symm,
  refine findim_lt (lt_of_le_of_ne le_top _),
  intro h_eq_top,
  rw comap_subtype_eq_top at h_eq_top,
  apply not_le_of_lt hst h_eq_top,
end

end submodule

section span

open submodule

lemma findim_span_le_card (s : set V) [fin : fintype s] :
  findim K (span K s) ≤ s.to_finset.card :=
begin
  haveI := span_of_finite K ⟨fin⟩,
  have : dim K (span K s) ≤ (mk s : cardinal) := dim_span_le s,
  rw [←findim_eq_dim, cardinal.fintype_card, ←set.to_finset_card] at this,
  exact_mod_cast this
end

lemma findim_span_eq_card {ι : Type*} [fintype ι] {b : ι → V}
  (hb : linear_independent K b) :
  findim K (span K (set.range b)) = fintype.card ι :=
begin
  haveI : finite_dimensional K (span K (set.range b)) := span_of_finite K (set.finite_range b),
  have : dim K (span K (set.range b)) = (mk (set.range b) : cardinal) := dim_span hb,
  rwa [←findim_eq_dim, ←lift_inj, mk_range_eq_of_injective hb.injective,
    cardinal.fintype_card, lift_nat_cast, lift_nat_cast, nat_cast_inj] at this,
end

lemma findim_span_set_eq_card (s : set V) [fin : fintype s]
  (hs : linear_independent K (coe : s → V)) :
  findim K (span K s) = s.to_finset.card :=
begin
  haveI := span_of_finite K ⟨fin⟩,
  have : dim K (span K s) = (mk s : cardinal) := dim_span_set hs,
  rw [←findim_eq_dim, cardinal.fintype_card, ←set.to_finset_card] at this,
  exact_mod_cast this
end

lemma span_lt_of_subset_of_card_lt_findim {s : set V} [fintype s] {t : submodule K V}
  (subset : s ⊆ t) (card_lt : s.to_finset.card < findim K t) : span K s < t :=
lt_of_le_of_findim_lt_findim (span_le.mpr subset) (lt_of_le_of_lt (findim_span_le_card _) card_lt)

lemma span_lt_top_of_card_lt_findim {s : set V} [fintype s]
  (card_lt : s.to_finset.card < findim K V) : span K s < ⊤ :=
lt_top_of_findim_lt_findim (lt_of_le_of_lt (findim_span_le_card _) card_lt)

lemma findim_span_singleton {v : V} (hv : v ≠ 0) : findim K (K ∙ v) = 1 :=
begin
  apply le_antisymm,
  { exact findim_span_le_card ({v} : set V) },
  { rw [nat.succ_le_iff, findim_pos_iff],
    use [⟨v, mem_span_singleton_self v⟩, 0],
    simp [hv] }
end

end span

section is_basis

lemma linear_independent_of_span_eq_top_of_card_eq_findim {ι : Type*} [fintype ι] {b : ι → V}
  (span_eq : span K (set.range b) = ⊤) (card_eq : fintype.card ι = findim K V) :
  linear_independent K b :=
linear_independent_iff'.mpr $ λ s g dependent i i_mem_s,
begin
  by_contra gx_ne_zero,
  -- We'll derive a contradiction by showing `b '' (univ \ {i})` of cardinality `n - 1`
  -- spans a vector space of dimension `n`.
  refine ne_of_lt (span_lt_top_of_card_lt_findim
    (show (b '' (set.univ \ {i})).to_finset.card < findim K V, from _)) _,
  { calc (b '' (set.univ \ {i})).to_finset.card = ((set.univ \ {i}).to_finset.image b).card
      : by rw [set.to_finset_card, fintype.card_of_finset]
    ... ≤ (set.univ \ {i}).to_finset.card : finset.card_image_le
    ... = (finset.univ.erase i).card : congr_arg finset.card (finset.ext (by simp [and_comm]))
    ... < finset.univ.card : finset.card_erase_lt_of_mem (finset.mem_univ i)
    ... = findim K V : card_eq },

  -- We already have that `b '' univ` spans the whole space,
  -- so we only need to show that the span of `b '' (univ \ {i})` contains each `b j`.
  refine trans (le_antisymm (span_mono (set.image_subset_range _ _)) (span_le.mpr _)) span_eq,
  rintros _ ⟨j, rfl, rfl⟩,
  -- The case that `j ≠ i` is easy because `b j ∈ b '' (univ \ {i})`.
  by_cases j_eq : j = i,
  swap,
  { refine subset_span ⟨j, (set.mem_diff _).mpr ⟨set.mem_univ _, _⟩, rfl⟩,
    exact mt set.mem_singleton_iff.mp j_eq },

  -- To show `b i ∈ span (b '' (univ \ {i}))`, we use that it's a weighted sum
  -- of the other `b j`s.
  rw [j_eq, mem_coe, show b i = -((g i)⁻¹ • (s.erase i).sum (λ j, g j • b j)), from _],
  { refine submodule.neg_mem _ (smul_mem _ _ (sum_mem _ (λ k hk, _))),
    obtain ⟨k_ne_i, k_mem⟩ := finset.mem_erase.mp hk,
    refine smul_mem _ _ (subset_span ⟨k, _, rfl⟩),
    simpa using k_mem },

  -- To show `b i` is a weighted sum of the other `b j`s, we'll rewrite this sum
  -- to have the form of the assumption `dependent`.
  apply eq_neg_of_add_eq_zero,
  calc b i + (g i)⁻¹ • (s.erase i).sum (λ j, g j • b j)
      = (g i)⁻¹ • (g i • b i + (s.erase i).sum (λ j, g j • b j))
    : by rw [smul_add, ←mul_smul, inv_mul_cancel gx_ne_zero, one_smul]
  ... = (g i)⁻¹ • 0 : congr_arg _ _
  ... = 0           : smul_zero _,
  -- And then it's just a bit of manipulation with finite sums.
  rwa [← finset.insert_erase i_mem_s, finset.sum_insert (finset.not_mem_erase _ _)] at dependent
end

/-- A finite family of vectors is linearly independent if and only if
its cardinality equals the dimension of its span. -/
lemma linear_independent_iff_card_eq_findim_span {ι : Type*} [fintype ι] {b : ι → V} :
  linear_independent K b ↔ fintype.card ι = findim K (span K (set.range b)) :=
begin
  split,
  { intro h,
    exact (findim_span_eq_card h).symm },
  { intro hc,
    let f := (submodule.subtype (span K (set.range b))),
    let b' : ι → span K (set.range b) :=
      λ i, ⟨b i, mem_span.2 (λ p hp, hp (set.mem_range_self _))⟩,
    have hs : span K (set.range b') = ⊤,
    { rw eq_top_iff',
      intro x,
      have h : span K (f '' (set.range b')) = map f (span K (set.range b')) := span_image f,
      have hf : f '' (set.range b') = set.range b, { ext x, simp [set.mem_image, set.mem_range] },
      rw hf at h,
      have hx : (x : V) ∈ span K (set.range b) := x.property,
      conv at hx { congr, skip, rw h },
      simpa [mem_map] using hx },
    have hi : f.ker = ⊥ := ker_subtype _,
    convert (linear_independent_of_span_eq_top_of_card_eq_findim hs hc).map' _ hi }
end

lemma is_basis_of_span_eq_top_of_card_eq_findim {ι : Type*} [fintype ι] {b : ι → V}
  (span_eq : span K (set.range b) = ⊤) (card_eq : fintype.card ι = findim K V) :
  is_basis K b :=
⟨linear_independent_of_span_eq_top_of_card_eq_findim span_eq card_eq, span_eq⟩

lemma finset_is_basis_of_span_eq_top_of_card_eq_findim {s : finset V}
  (span_eq : span K (↑s : set V) = ⊤) (card_eq : s.card = findim K V) :
  is_basis K (coe : (↑s : set V) → V) :=
is_basis_of_span_eq_top_of_card_eq_findim
  ((@subtype.range_coe_subtype _ (λ x, x ∈ s)).symm ▸ span_eq)
  (trans (fintype.card_coe _) card_eq)

lemma set_is_basis_of_span_eq_top_of_card_eq_findim {s : set V} [fintype s]
  (span_eq : span K s = ⊤) (card_eq : s.to_finset.card = findim K V) :
  is_basis K (λ (x : s), (x : V)) :=
is_basis_of_span_eq_top_of_card_eq_findim
  ((@subtype.range_coe_subtype _ s).symm ▸ span_eq)
  (trans s.to_finset_card.symm card_eq)

lemma span_eq_top_of_linear_independent_of_card_eq_findim
  {ι : Type*} [hι : nonempty ι] [fintype ι] {b : ι → V}
  (lin_ind : linear_independent K b) (card_eq : fintype.card ι = findim K V) :
  span K (set.range b) = ⊤ :=
begin
  by_cases fin : (finite_dimensional K V),
  { haveI := fin,
    by_contra ne_top,
    have lt_top : span K (set.range b) < ⊤ := lt_of_le_of_ne le_top ne_top,
    exact ne_of_lt (submodule.findim_lt lt_top) (trans (findim_span_eq_card lin_ind) card_eq) },
  { exfalso,
    apply ne_of_lt (fintype.card_pos_iff.mpr hι),
    symmetry,
    calc fintype.card ι = findim K V : card_eq
                    ... = 0 : dif_neg (mt finite_dimensional_iff_dim_lt_omega.mpr fin) }
end

lemma is_basis_of_linear_independent_of_card_eq_findim
  {ι : Type*} [nonempty ι] [fintype ι] {b : ι → V}
  (lin_ind : linear_independent K b) (card_eq : fintype.card ι = findim K V) :
  is_basis K b :=
⟨lin_ind, span_eq_top_of_linear_independent_of_card_eq_findim lin_ind card_eq⟩

lemma finset_is_basis_of_linear_independent_of_card_eq_findim
  {s : finset V} (hs : s.nonempty)
  (lin_ind : linear_independent K (coe : (↑s : set V) → V)) (card_eq : s.card = findim K V) :
  is_basis K (coe : (↑s : set V) → V) :=
@is_basis_of_linear_independent_of_card_eq_findim _ _ _ _ _ _
  ⟨(⟨hs.some, hs.some_spec⟩ : (↑s : set V))⟩ _ _
  lin_ind
  (trans (fintype.card_coe _) card_eq)

lemma set_is_basis_of_linear_independent_of_card_eq_findim
  {s : set V} [nonempty s] [fintype s]
  (lin_ind : linear_independent K (coe : s → V)) (card_eq : s.to_finset.card = findim K V) :
  is_basis K (coe : s → V) :=
is_basis_of_linear_independent_of_card_eq_findim lin_ind (trans s.to_finset_card.symm card_eq)

end is_basis

section subalgebra_dim
open vector_space
variables {F E : Type*} [field F] [field E] [algebra F E]

lemma subalgebra.dim_eq_one_of_eq_bot {S : subalgebra F E} (h : S = ⊥) : dim F S = 1 :=
begin
  rw [← S.to_submodule_equiv.dim_eq, h,
    (linear_equiv.of_eq ↑(⊥ : subalgebra F E) _ algebra.to_submodule_bot).dim_eq, dim_span_set],
  exacts [mk_singleton _, linear_independent_singleton one_ne_zero]
end

@[simp]
lemma subalgebra.dim_bot : dim F (⊥ : subalgebra F E) = 1 :=
subalgebra.dim_eq_one_of_eq_bot rfl

lemma subalgebra_top_dim_eq_submodule_top_dim :
  dim F (⊤ : subalgebra F E) = dim F (⊤ : submodule F E) :=
by { rw ← algebra.coe_top, refl }

lemma subalgebra_top_findim_eq_submodule_top_findim :
  findim F (⊤ : subalgebra F E) = findim F (⊤ : submodule F E) :=
by { rw ← algebra.coe_top, refl }

lemma subalgebra.dim_top : dim F (⊤ : subalgebra F E) = dim F E :=
by { rw subalgebra_top_dim_eq_submodule_top_dim, exact dim_top }

lemma subalgebra.finite_dimensional_bot : finite_dimensional F (⊥ : subalgebra F E) :=
finite_dimensional_of_dim_eq_one subalgebra.dim_bot

@[simp]
lemma subalgebra.findim_bot : findim F (⊥ : subalgebra F E) = 1 :=
begin
  haveI : finite_dimensional F (⊥ : subalgebra F E) := subalgebra.finite_dimensional_bot,
  have : dim F (⊥ : subalgebra F E) = 1 := subalgebra.dim_bot,
  rw ← findim_eq_dim at this,
  norm_cast at *,
  simp *,
end

lemma subalgebra.findim_eq_one_of_eq_bot {S : subalgebra F E} (h : S = ⊥) : findim F S = 1 :=
by { rw h, exact subalgebra.findim_bot }

lemma subalgebra.eq_bot_of_findim_one {S : subalgebra F E} (h : findim F S = 1) : S = ⊥ :=
begin
  rw eq_bot_iff,
  let b : set S := {1},
  have : fintype b := unique.fintype,
  have b_lin_ind : linear_independent F (coe : b → S) := linear_independent_singleton one_ne_zero,
  have b_card : fintype.card b = 1 := fintype.card_of_subsingleton _,
  obtain ⟨_, b_spans⟩ := set_is_basis_of_linear_independent_of_card_eq_findim
    b_lin_ind (by simp only [*, set.to_finset_card]),
  intros x hx,
  rw [subalgebra.mem_coe, algebra.mem_bot],
  have x_in_span_b : (⟨x, hx⟩ : S) ∈ submodule.span F b,
  { rw subtype.range_coe at b_spans,
    rw b_spans,
    exact submodule.mem_top, },
  obtain ⟨a, ha⟩ := submodule.mem_span_singleton.mp x_in_span_b,
  replace ha : a • 1 = x := by injections with ha,
  exact ⟨a, by rw [← ha, algebra.smul_def, mul_one]⟩,
end

lemma subalgebra.eq_bot_of_dim_one {S : subalgebra F E} (h : dim F S = 1) : S = ⊥ :=
begin
  haveI : finite_dimensional F S := finite_dimensional_of_dim_eq_one h,
  rw ← findim_eq_dim at h,
  norm_cast at h,
  exact subalgebra.eq_bot_of_findim_one h,
end

@[simp]
lemma subalgebra.bot_eq_top_of_dim_eq_one (h : dim F E = 1) : (⊥ : subalgebra F E) = ⊤ :=
begin
  rw [← dim_top, ← subalgebra_top_dim_eq_submodule_top_dim] at h,
  exact eq.symm (subalgebra.eq_bot_of_dim_one h),
end

@[simp]
lemma subalgebra.bot_eq_top_of_findim_eq_one (h : findim F E = 1) : (⊥ : subalgebra F E) = ⊤ :=
begin
  rw [← findim_top, ← subalgebra_top_findim_eq_submodule_top_findim] at h,
  exact eq.symm (subalgebra.eq_bot_of_findim_one h),
end

@[simp]
theorem subalgebra.dim_eq_one_iff {S : subalgebra F E} : dim F S = 1 ↔ S = ⊥ :=
⟨subalgebra.eq_bot_of_dim_one, subalgebra.dim_eq_one_of_eq_bot⟩

@[simp]
theorem subalgebra.findim_eq_one_iff {S : subalgebra F E} : findim F S = 1 ↔ S = ⊥ :=
⟨subalgebra.eq_bot_of_findim_one, subalgebra.findim_eq_one_of_eq_bot⟩

end subalgebra_dim

namespace module
namespace End

lemma exists_ker_pow_eq_ker_pow_succ [finite_dimensional K V] (f : End K V) :
  ∃ (k : ℕ), k ≤ findim K V ∧ (f ^ k).ker = (f ^ k.succ).ker :=
begin
  classical,
  by_contradiction h_contra,
  simp_rw [not_exists, not_and] at h_contra,
  have h_le_ker_pow : ∀ (n : ℕ), n ≤ (findim K V).succ → n ≤ findim K (f ^ n).ker,
  { intros n hn,
    induction n with n ih,
    { exact zero_le (findim _ _) },
    { have h_ker_lt_ker : (f ^ n).ker < (f ^ n.succ).ker,
      { refine lt_of_le_of_ne _ (h_contra n (nat.le_of_succ_le_succ hn)),
        rw pow_succ,
        apply linear_map.ker_le_ker_comp },
      have h_findim_lt_findim : findim K (f ^ n).ker < findim K (f ^ n.succ).ker,
      { apply submodule.findim_lt_findim_of_lt h_ker_lt_ker },
      calc
        n.succ ≤ (findim K ↥(linear_map.ker (f ^ n))).succ :
            nat.succ_le_succ (ih (nat.le_of_succ_le hn))
        ... ≤ findim K ↥(linear_map.ker (f ^ n.succ)) :
            nat.succ_le_of_lt h_findim_lt_findim } },
  have h_le_findim_V : ∀ n, findim K (f ^ n).ker ≤ findim K V :=
    λ n, submodule.findim_le _,
  have h_any_n_lt: ∀ n, n ≤ (findim K V).succ → n ≤ findim K V :=
    λ n hn, (h_le_ker_pow n hn).trans (h_le_findim_V n),
  show false,
    from nat.not_succ_le_self _ (h_any_n_lt (findim K V).succ (findim K V).succ.le_refl),
end

lemma ker_pow_constant {f : End K V} {k : ℕ} (h : (f ^ k).ker = (f ^ k.succ).ker) :
  ∀ m, (f ^ k).ker = (f ^ (k + m)).ker
| 0 := by simp
| (m + 1) :=
  begin
    apply le_antisymm,
    { rw [add_comm, pow_add],
      apply linear_map.ker_le_ker_comp },
    { rw [ker_pow_constant m, add_comm m 1, ←add_assoc, pow_add, pow_add f k m],
      change linear_map.ker ((f ^ (k + 1)).comp (f ^ m)) ≤ linear_map.ker ((f ^ k).comp (f ^ m)),
      rw [linear_map.ker_comp, linear_map.ker_comp, h, nat.add_one],
      exact le_refl _, }
  end

lemma ker_pow_eq_ker_pow_findim_of_le [finite_dimensional K V]
  {f : End K V} {m : ℕ} (hm : findim K V ≤ m) :
  (f ^ m).ker = (f ^ findim K V).ker :=
begin
  obtain ⟨k, h_k_le, hk⟩ :
    ∃ k, k ≤ findim K V ∧ linear_map.ker (f ^ k) = linear_map.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f,
  calc (f ^ m).ker = (f ^ (k + (m - k))).ker :
      by rw nat.add_sub_of_le (h_k_le.trans hm)
    ...  = (f ^ k).ker : by rw ker_pow_constant hk _
    ...  = (f ^ (k + (findim K V - k))).ker : ker_pow_constant hk (findim K V - k)
    ...  = (f ^ findim K V).ker : by rw nat.add_sub_of_le h_k_le
end

lemma ker_pow_le_ker_pow_findim [finite_dimensional K V] (f : End K V) (m : ℕ) :
  (f ^ m).ker ≤ (f ^ findim K V).ker :=
begin
  by_cases h_cases: m < findim K V,
  { rw [←nat.add_sub_of_le (nat.le_of_lt h_cases), add_comm, pow_add],
    apply linear_map.ker_le_ker_comp },
  { rw [ker_pow_eq_ker_pow_findim_of_le (le_of_not_lt h_cases)],
    exact le_refl _ }
end

end End
end module
