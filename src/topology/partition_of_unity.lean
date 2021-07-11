/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import algebra.big_operators.finprod
import topology.urysohns_lemma
import topology.paracompact
import topology.continuous_function.algebra

/-!
# Continuous partition of unity

In this file we define `partition_of_unity (ι X : Type*) [topological_space X] (s : set X := univ)`
to be a continuous partition of unity on `s` indexed by `ι`. More precisely, `f : partition_of_unity
ι X s` is a collection of continuous functions `f i : C(X, ℝ)`, `i : ι`, such that

* supports of `f i` is a locally finite family of sets;
* each `f i` is nonnegative;
* `∑ᶠ i, f i x = 1` for all `x ∈ s`;
* `∑ᶠ i, f i x ≤ 1` for all `x : X`.

In the case `s = univ` the last assumption follows from the previous one but it is convenient to
have this assumption in the case `s ≠ univ`.

We also define a bump function covering,
`bump_covering (ι X : Type*) [topological_space X] (s : set X := univ)`, to be a collection of
functions `f i : C(X, ℝ)`, `i : ι`, such that

* supports of `f i` is a locally finite family of sets;
* each `f i` is nonnegative;
* for each `x ∈ s` there exists `i : ι` such that `f i y = 1` in a neighborhood of `x`.

The term is motivated by the smooth case.

If `f` is a bump function covering indexed by a linearly ordered type, then
`g i x = f i x * ∏ᶠ j < i, (1 - f j x)` is a partition of unity, see
`bump_covering.to_partition_of_unity`. We use `well_ordering_rel j i` instead of `j < i` in the
actual definition to avoid a `[linear_order ι]` assumption.

We say that a partition of unity or a bump function covering `f` is *subordinate* to a family of
sets `U i`, `i : ι`, if the closure of the support of each `f i` is included by `U i`. We use
Urysohn's Lemma to prove that a locally finite open covering of a normal topological space admits a
subordinate bump function covering (hence, a subordinate partition of unity), see
`bump_covering.exists_is_subordinate_of_locally_finite`. If `X` is a paracompact space, then any
open covering admits a locally finite refinement, hence it admits a subordinate bump function
covering and a subordinate partition of unity, see `bump_covering.exists_is_subordinate`.

We also provide two slightly more general versions of these lemmas,
`bump_covering.exists_is_subordinate_of_locally_finite_of_prop` and
`bump_covering.exists_is_subordinate_of_prop`, to be used later in the construction of a smooth
partition of unity.

** Implementation notes

Most (if not all) books only define a partition of unity of the whole space. However, quite a few
proofs only deal with `f i` such that `closure (support (f i))` meets a specific closed subset, and
it is easier to formalize these proofs if we don't have other functions right away.

** Tags

partition of unity, bump function, Urysohn's lemma, normal space, paracompact space
-/

universes u v

open function set filter
open_locale big_operators topological_space classical

noncomputable theory

/-- Continuous partition of unity on a set `s : set X` is a colletion of continuous functions `f i`
such that

* supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there exists
  a neighborhood `U ⊇ x` such that all but finitely many functions `f i` are zero on `U`;
* the functions `f i` are nonnegative;
* the sum `∑ᶠ i, f i x` is equal to one for every `x ∈ s` and is less than or equal to one
  otherwise.

If `X` is a normal paracompact space, then `partition_of_unity.exists_is_subordinate` guarantees
that for every open covering `U : set (set X)` of `s` there exists a partition of unity that is
subordinate to `U`.
-/
structure partition_of_unity (ι X : Type*) [topological_space X] (s : set X := univ) :=
(to_fun : ι → C(X, ℝ))
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(nonneg' : 0 ≤ to_fun)
(sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, to_fun i x = 1)
(sum_le_one' : ∀ x, ∑ᶠ i, to_fun i x ≤ 1)

/-- A `bump_covering ι X s` is an indexed family of functions `f i`, `i : ι`, such that

* supports of `f i` form a locally finite family of sets, i.e., for every point `x : X` there exists
  a neighborhood `U ⊇ x` such that all but finitely many functions `f i` are zero on `U`;
* for all `i`, `x` we have `0 ≤ f i x ≤ 1`;
* each point `x ∈ s` belongs to the interior of `{x | f i x = 1}` for some `i`.

One of the main use cases for a `bump_covering` is to define a `partition_of_unity`, see
`bump_covering.to_partition_of_unity`, but some proofs can directly use a `bump_covering` instead of
a `partition_of_unity`.

If `X` is a normal paracompact space, then `bump_covering.exists_is_subordinate` guarantees that for
every open covering `U : set (set X)` of `s` there exists a `bump_covering` of `s` that is
subordinate to `U`.
-/
structure bump_covering (ι X : Type*) [topological_space X] (s : set X := univ) :=
(to_fun : ι → C(X, ℝ))
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(nonneg' : 0 ≤ to_fun)
(le_one' : to_fun ≤ 1)
(eventually_eq_one' : ∀ x ∈ s, ∃ i, to_fun i =ᶠ[𝓝 x] 1)

variables {ι : Type u} {X : Type v} [topological_space X]

namespace partition_of_unity

variables {s : set X} (f : partition_of_unity ι X s)

instance : has_coe_to_fun (partition_of_unity ι X s) := ⟨_, to_fun⟩

protected lemma locally_finite : locally_finite (λ i, support (f i)) :=
f.locally_finite'

lemma nonneg (i : ι) (x : X) : 0 ≤ f i x := f.nonneg' i x

lemma sum_eq_one {x : X} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 := f.sum_eq_one' x hx

lemma sum_le_one (x : X) : ∑ᶠ i, f i x ≤ 1 := f.sum_le_one' x

lemma sum_nonneg (x : X) : 0 ≤ ∑ᶠ i, f i x := finsum_nonneg $ λ i, f.nonneg i x

lemma le_one (i : ι) (x : X) : f i x ≤ 1 :=
(single_le_finsum i (f.locally_finite.point_finite x) (λ j, f.nonneg j x)).trans (f.sum_le_one x)

/-- A partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same type if
for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def is_subordinate (f : partition_of_unity ι X s) (U : ι → set X) : Prop :=
∀ i, closure (support (f i)) ⊆ U i

end partition_of_unity

namespace bump_covering

variables {s : set X} (f : bump_covering ι X s)

instance : has_coe_to_fun (bump_covering ι X s) := ⟨_, to_fun⟩

protected lemma locally_finite : locally_finite (λ i, support (f i)) :=
f.locally_finite'

protected lemma point_finite (x : X) : finite {i | f i x ≠ 0} :=
f.locally_finite.point_finite x

lemma nonneg (i : ι) (x : X) : 0 ≤ f i x := f.nonneg' i x

lemma le_one (i : ι) (x : X) : f i x ≤ 1 := f.le_one' i x

/-- A `bump_covering` that consists of a single function, defined as an example
for `inhabited` instance. -/
protected def single (i : ι) (s : set X) : bump_covering ι X s :=
{ to_fun := pi.single i 1,
  locally_finite' := λ x,
    begin
      refine ⟨univ, univ_mem_sets, (finite_singleton i).subset _⟩,
      rintro j ⟨x, hx, -⟩,
      contrapose! hx,
      rw [mem_singleton_iff] at hx,
      simp [hx]
    end,
  nonneg' := le_update_iff.2 ⟨λ x, zero_le_one, λ _ _, le_rfl⟩,
  le_one' := update_le_iff.2 ⟨le_rfl, λ _ _ _, zero_le_one⟩,
  eventually_eq_one' := λ x _, ⟨i, by simp⟩ }

instance [inhabited ι] : inhabited (bump_covering ι X s) :=
⟨bump_covering.single (default ι) s⟩

/-- A collection of bump functions `f i` is subordinate to a family of sets `U i` indexed by the
same type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def is_subordinate (f : bump_covering ι X s) (U : ι → set X) : Prop :=
∀ i, closure (support (f i)) ⊆ U i

lemma is_subordinate.mono {f : bump_covering ι X s} {U V : ι → set X} (hU : f.is_subordinate U)
  (hV : ∀ i, U i ⊆ V i) :
  f.is_subordinate V :=
λ i, subset.trans (hU i) (hV i)

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : locally_finite U` can be omitted, see
`bump_covering.exists_is_subordinate`. This version assumes that `p : (X → ℝ) → Prop` is a predicate
that satisfies the Urysohn's lemma, and provides a `bump_covering` such that each function of the
covering satisfies `p`. -/
lemma exists_is_subordinate_of_locally_finite_of_prop [normal_space X] (p : (X → ℝ) → Prop)
  (h01 : ∀ s t, is_closed s → is_closed t → disjoint s t →
    ∃ f : C(X, ℝ), p f ∧ eq_on f 0 s ∧ eq_on f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
  (hs : is_closed s) (U : ι → set X) (ho : ∀ i, is_open (U i)) (hf : locally_finite U)
  (hU : s ⊆ ⋃ i, U i) :
  ∃ f : bump_covering ι X s, (∀ i, p (f i)) ∧ f.is_subordinate U :=
begin
  rcases exists_subset_Union_closure_subset hs ho (λ x _, hf.point_finite x) hU
    with ⟨V, hsV, hVo, hVU⟩,
  have hVU' : ∀ i, V i ⊆ U i, from λ i, subset.trans subset_closure (hVU i),
  rcases exists_subset_Union_closure_subset hs hVo
    (λ x _, (hf.subset hVU').point_finite x) hsV with ⟨W, hsW, hWo, hWV⟩,
  choose f hfp hf0 hf1 hf01
    using λ i, h01 _ _ (is_closed_compl_iff.2 $ hVo i)
      is_closed_closure (disjoint_right.2 $ λ x hx, not_not.2 (hWV i hx)),
  have hsupp : ∀ i, support (f i) ⊆ V i,
    from λ i, support_subset_iff'.2 (hf0 i),
  refine ⟨⟨f, hf.subset (λ i, subset.trans (hsupp i) (hVU' i)),
    λ i x, (hf01 i x).1, λ i x, (hf01 i x).2, λ x hx, _⟩, hfp,
    λ i, subset.trans (closure_mono (hsupp i)) (hVU i)⟩,
  rcases mem_Union.1 (hsW hx) with ⟨i, hi⟩,
  exact ⟨i, ((hf1 i).mono subset_closure).eventually_eq_of_mem ((hWo i).mem_nhds hi)⟩
end

/-- If `X` is a normal topological space and `U i`, `i : ι`, is a locally finite open covering of a
closed set `s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : locally_finite U` can be omitted, see
`bump_covering.exists_is_subordinate`. -/
lemma exists_is_subordinate_of_locally_finite [normal_space X] (hs : is_closed s)
  (U : ι → set X) (ho : ∀ i, is_open (U i)) (hf : locally_finite U)
  (hU : s ⊆ ⋃ i, U i) :
  ∃ f : bump_covering ι X s, f.is_subordinate U :=
let ⟨f, _, hfU⟩ :=
  exists_is_subordinate_of_locally_finite_of_prop (λ _, true)
    (λ s t hs ht hd, (exists_continuous_zero_one_of_closed hs ht hd).imp $ λ f hf, ⟨trivial, hf⟩)
    hs U ho hf hU
in ⟨f, hfU⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. This version assumes that
`p : (X → ℝ) → Prop` is a predicate that satisfies the Urysohn's lemma, and provides a
`bump_covering` such that each function of the covering satisfies `p`. -/
lemma exists_is_subordinate_of_prop [normal_space X] [paracompact_space X] (p : (X → ℝ) → Prop)
  (h01 : ∀ s t, is_closed s → is_closed t → disjoint s t →
    ∃ f : C(X, ℝ), p f ∧ eq_on f 0 s ∧ eq_on f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1)
  (hs : is_closed s) (U : ι → set X) (ho : ∀ i, is_open (U i)) (hU : s ⊆ ⋃ i, U i) :
  ∃ f : bump_covering ι X s, (∀ i, p (f i)) ∧ f.is_subordinate U :=
begin
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩,
  rcases exists_is_subordinate_of_locally_finite_of_prop p h01 hs V hVo hVf hsV with ⟨f, hfp, hf⟩,
  exact ⟨f, hfp, hf.mono hVU⟩
end

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. -/
lemma exists_is_subordinate [normal_space X] [paracompact_space X]
  (hs : is_closed s) (U : ι → set X) (ho : ∀ i, is_open (U i)) (hU : s ⊆ ⋃ i, U i) :
  ∃ f : bump_covering ι X s, f.is_subordinate U :=
begin
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩,
  rcases exists_is_subordinate_of_locally_finite hs V hVo hVf hsV with ⟨f, hf⟩,
  exact ⟨f, hf.mono hVU⟩
end

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : X) (hx : x ∈ s) : ι := (f.eventually_eq_one' x hx).some

lemma eventually_eq_one (x : X) (hx : x ∈ s) : f (f.ind x hx) =ᶠ[𝓝 x] 1 :=
(f.eventually_eq_one' x hx).some_spec

lemma ind_apply (x : X) (hx : x ∈ s) : f (f.ind x hx) x = 1 :=
(f.eventually_eq_one x hx).eq_of_nhds

/-- Partition of unity defined by a `bump_covering`. Use `bump_function.to_partition_of_unity`
instead. -/
def to_pou_fun (i : ι) (x : X) : ℝ :=
f i x * ∏ᶠ j (hj : well_ordering_rel j i), (1 - f j x)

lemma to_pou_fun_zero_of_zero {i : ι} {x : X} (h : f i x = 0) :
  f.to_pou_fun i x = 0 :=
by rw [to_pou_fun, h, zero_mul]

lemma support_to_pou_fun_subset (i : ι) :
  support (f.to_pou_fun i) ⊆ support (f i) :=
 λ x, mt $ f.to_pou_fun_zero_of_zero

lemma to_pou_fun_eq_mul_prod (i : ι) (x : X) (t : finset ι)
  (ht : ∀ j, well_ordering_rel j i → f j x ≠ 0 → j ∈ t) :
  f.to_pou_fun i x = f i x * ∏ j in t.filter (λ j, well_ordering_rel j i), (1 - f j x) :=
begin
  refine congr_arg _ (finprod_cond_eq_prod_of_cond_iff _ (λ j hj, _)),
  rw [ne.def, sub_eq_self] at hj,
  rw [finset.mem_filter, iff.comm, and_iff_right_iff_imp],
  exact flip (ht j) hj
end

lemma sum_to_pou_fun_eq (x : X) :
  ∑ᶠ i, f.to_pou_fun i x = 1 - ∏ᶠ i, (1 - f i x) :=
begin
  set s := (f.point_finite x).to_finset,
  have hs : (s : set ι) = {i | f i x ≠ 0} := finite.coe_to_finset _,
  have A : support (λ i, to_pou_fun f i x) ⊆ s,
  { rw hs,
    exact λ i hi, f.support_to_pou_fun_subset i hi },
  have B : mul_support (λ i, 1 - f i x) ⊆ s,
  { rw [hs, mul_support_one_sub], exact λ i, id },
  letI : linear_order ι := linear_order_of_STO' well_ordering_rel,
  rw [finsum_eq_sum_of_support_subset _ A, finprod_eq_prod_of_mul_support_subset _ B,
    finset.prod_one_sub_ordered, sub_sub_cancel],
  refine finset.sum_congr rfl (λ i hi, _),
  convert f.to_pou_fun_eq_mul_prod _ _ _ (λ j hji hj, _),
  rwa finite.mem_to_finset
end

lemma exists_finset_to_pou_fun_eventually_eq (i : ι) (x : X) :
  ∃ t : finset ι, f.to_pou_fun i =ᶠ[𝓝 x]
    f i * ∏ j in t.filter (λ j, well_ordering_rel j i), (1 - f j) :=
begin
  rcases f.locally_finite x with ⟨U, hU, hf⟩,
  use hf.to_finset,
  filter_upwards [hU],
  intros y hyU,
  simp only [pi.mul_apply, finset.prod_apply],
  apply to_pou_fun_eq_mul_prod,
  intros j hji hj,
  exact hf.mem_to_finset.2 ⟨y, ⟨hj, hyU⟩⟩
end

lemma continuous_to_pou_fun (i : ι) : continuous (f.to_pou_fun i) :=
begin
  refine ((f i).continuous.mul $
    continuous_finprod_cond (λ j _, continuous_const.sub (f j).continuous) _),
  simp only [mul_support_one_sub],
  exact f.locally_finite
end

/-- The partition of unity defined by a `bump_covering`. -/
def to_partition_of_unity : partition_of_unity ι X s :=
{ to_fun := λ i, ⟨f.to_pou_fun i, f.continuous_to_pou_fun i⟩,
  locally_finite' := f.locally_finite.subset f.support_to_pou_fun_subset,
  nonneg' := λ i x, mul_nonneg (f.nonneg i x)
    (finprod_cond_nonneg $ λ j hj, sub_nonneg.2 $ f.le_one j x),
  sum_eq_one' := λ x hx,
    begin
      simp only [continuous_map.coe_mk, sum_to_pou_fun_eq, sub_eq_self],
      apply finprod_eq_zero (λ i, 1 - f i x) (f.ind x hx),
      { simp only [f.ind_apply x hx, sub_self] },
      { rw mul_support_one_sub, exact f.point_finite x }
    end,
  sum_le_one' := λ x,
    begin
      simp only [continuous_map.coe_mk, sum_to_pou_fun_eq, sub_le_self_iff],
      exact finprod_nonneg (λ i, sub_nonneg.2 $ f.le_one i x)
    end }

lemma to_partition_of_unity_apply (i : ι) (x : X) :
  f.to_partition_of_unity i x = f i x * ∏ᶠ j (hj : well_ordering_rel j i), (1 - f j x) :=
rfl

lemma to_partition_of_unity_eq_mul_prod (i : ι) (x : X) (t : finset ι)
  (ht : ∀ j, well_ordering_rel j i → f j x ≠ 0 → j ∈ t) :
  f.to_partition_of_unity i x = f i x * ∏ j in t.filter (λ j, well_ordering_rel j i), (1 - f j x) :=
f.to_pou_fun_eq_mul_prod i x t ht

lemma exists_finset_to_partition_of_unity_eventually_eq (i : ι) (x : X) :
  ∃ t : finset ι, f.to_partition_of_unity i =ᶠ[𝓝 x]
    f i * ∏ j in t.filter (λ j, well_ordering_rel j i), (1 - f j) :=
f.exists_finset_to_pou_fun_eventually_eq i x

lemma to_partition_of_unity_zero_of_zero {i : ι} {x : X} (h : f i x = 0) :
  f.to_partition_of_unity i x = 0 :=
f.to_pou_fun_zero_of_zero h

lemma support_to_partition_of_unity_subset (i : ι) :
  support (f.to_partition_of_unity i) ⊆ support (f i) :=
f.support_to_pou_fun_subset i

lemma sum_to_partition_of_unity_eq (x : X) :
  ∑ᶠ i, f.to_partition_of_unity i x = 1 - ∏ᶠ i, (1 - f i x) :=
f.sum_to_pou_fun_eq x

lemma is_subordinate.to_partition_of_unity {f : bump_covering ι X s} {U : ι → set X}
  (h : f.is_subordinate U) :
  f.to_partition_of_unity.is_subordinate U :=
λ i, subset.trans (closure_mono $ f.support_to_partition_of_unity_subset i) (h i)

end bump_covering

namespace partition_of_unity

variables {s : set X}

instance [inhabited ι] : inhabited (partition_of_unity ι X s) :=
⟨(default (bump_covering ι X s)).to_partition_of_unity⟩

/-- If `X` is a normal topological space and `U` is a locally finite open covering of a closed set
`s`, then there exists a `partition_of_unity ι X s` that is subordinate to `U`. If `X` is a
paracompact space, then the assumption `hf : locally_finite U` can be omitted, see
`bump_covering.exists_is_subordinate`. -/
lemma exists_is_subordinate_of_locally_finite [normal_space X] (hs : is_closed s)
  (U : ι → set X) (ho : ∀ i, is_open (U i)) (hf : locally_finite U)
  (hU : s ⊆ ⋃ i, U i) :
  ∃ f : partition_of_unity ι X s, f.is_subordinate U :=
let ⟨f, hf⟩ := bump_covering.exists_is_subordinate_of_locally_finite hs U ho hf hU
in ⟨f.to_partition_of_unity, hf.to_partition_of_unity⟩

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `partition_of_unity ι X s` that is subordinate to `U`. -/
lemma exists_is_subordinate [normal_space X] [paracompact_space X] (hs : is_closed s)
  (U : ι → set X) (ho : ∀ i, is_open (U i)) (hU : s ⊆ ⋃ i, U i) :
  ∃ f : partition_of_unity ι X s, f.is_subordinate U :=
let ⟨f, hf⟩ := bump_covering.exists_is_subordinate hs U ho hU
in ⟨f.to_partition_of_unity, hf.to_partition_of_unity⟩

end partition_of_unity
