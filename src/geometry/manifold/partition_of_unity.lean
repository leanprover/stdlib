/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import geometry.manifold.bump_function
import topology.partition_of_unity

/-!
# Smooth partition of unity

In this file we define two structures, `smooth_bump_covering` and `smooth_partition_of_unity`. Both
structures describe coverings of a set by a locally finite family of supports of smooth functions
with some additional properties. The former structure is mostly useful as an intermediate step in
the construction of a smooth partition of unity but some proofs that traditionally deal with a
partition of unity can use a `smooth_bump_covering` as well.

Given a real manifold `M` and its subset `s`, a `smooth_bump_covering I M s` is a collection of
`smooth_bump_function`s `f i` indexed by `i : f.ι` such that

* center of each `f i` belongs to `s`;
* the family of sets `support (f i)` is locally finite;
* for each `x ∈ s`, there exists `i : f.ι` such that `f i =ᶠ[𝓝 x] 1`.
In the same settings, a `smooth_partition_of_unity ι I M s` is a collection of smooth nonnegative
functions `f i : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯`, `i : ι`, such that

* the family of sets `support (f i)` is locally finite;
* for each `x ∈ s`, the sum `∑ᶠ i, f i x` equals one;
* for each `x`, the sum `∑ᶠ i, f i x` is less than or equal to one.

We say that `f : smooth_bump_covering I M s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `closure (support (f i)) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.

We prove that on a smooth finitely dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering I M s`
subordinate to `U`. Then we use this fact to prove a similar statement about smooth partitions of
unity.

## TODO

* Build a framework for to transfer local definitions to global using partition of unity and use it
  to define, e.g., the integral of a differential form over a manifold.

## Tags

smooth bump function, partition of unity
-/

universes uι uE uH uM

open function filter finite_dimensional set
open_locale topological_space manifold classical filter big_operators

noncomputable theory

variables {ι : Type uι}
{E : Type uE} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
{H : Type uH} [topological_space H] (I : model_with_corners ℝ E H)
{M : Type uM} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

/-!
### Covering by supports of smooth bump functions

In this section we define `smooth_bump_covering I M s` to be a collection of `smooth_bump_function`s
such that their supports is a locally finite family of sets and for each `x ∈ s` some function `f i`
from the collection is equal to `1` in a neighborhood of `x`. A covering of this type is useful to
construct a smooth partition of unity and can be used instead of a partition of unity in some
proofs.

We prove that on a smooth finite dimensional real manifold with `σ`-compact Hausdorff topology,
for any `U : M → set M` such that `∀ x ∈ s, U x ∈ 𝓝 x` there exists a `smooth_bump_covering I M s`
subordinate to `U`. Then we use this fact to prove a version of the Whitney embedding theorem: any
compact real manifold can be embedded into `ℝ^n` for large enough `n`.
-/

variables (ι M)

/-- We say that a collection of `smooth_bump_function`s is a `smooth_bump_covering` of a set `s` if

* `(f i).c ∈ s` for all `i`;
* the family `λ i, support (f i)` is locally finite;
* for each point `x ∈ s` there exists `i` such that `f i =ᶠ[𝓝 x] 1`;
  in other words, `x` belongs to the interior of `{y | f i y = 1}`;

If `M` is a finite dimensional real manifold which is a sigma-compact Hausdorff topological space,
then a choice of `smooth_bump_covering` is available as `smooth_bump_covering.choice_set`, see also
`smooth_bump_covering.choice` for the case `s = univ` and
`smooth_bump_covering.exists_is_subordinate` for a lemma providing a covering subordinate to a given
`U : M → set M`.

This covering can be used, e.g., to construct a partition of unity and to prove the weak
Whitney embedding theorem. -/
structure smooth_bump_covering (s : set M := univ) :=
(ι : Type uM)
(c : ι → M)
(to_fun : Π i, smooth_bump_function I (c i))
(c_mem' : ∀ i, c i ∈ s)
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(eventually_eq_one' : ∀ x ∈ s, ∃ i, to_fun i =ᶠ[𝓝 x] 1)

/-- We say that that a collection of functions form a smooth partition of unity on a set `s` if

* all functions are infinitely smooth and nonnegative;
* the family `λ i, support (f i)` is locally finite;
* for all `x ∈ s` the sum `∑ᶠ i, f i x` equals one;
* for all `x`, the sum `∑ᶠ i, f i x` is less than or equal to one. -/
structure smooth_partition_of_unity (s : set M := univ) :=
(to_fun : ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯)
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(nonneg' : ∀ i x, 0 ≤ to_fun i x)
(sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, to_fun i x = 1)
(sum_le_one' : ∀ x, ∑ᶠ i, to_fun i x ≤ 1)

variables {ι I M}

namespace smooth_partition_of_unity

variables {s : set M} (f : smooth_partition_of_unity ι I M s)

instance {s : set M} : has_coe_to_fun (smooth_partition_of_unity ι I M s) :=
⟨λ _, ι → C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, smooth_partition_of_unity.to_fun⟩

protected lemma locally_finite : locally_finite (λ i, support (f i)) :=
f.locally_finite'

lemma nonneg (i : ι) (x : M) : 0 ≤ f i x := f.nonneg' i x

lemma sum_eq_one {x} (hx : x ∈ s) : ∑ᶠ i, f i x = 1 := f.sum_eq_one' x hx

lemma sum_le_one (x : M) : ∑ᶠ i, f i x ≤ 1 := f.sum_le_one' x

/-- Reinterpret a smooth partition of unity as a continuous partition of unity. -/
def to_partition_of_unity : partition_of_unity ι M s :=
{ to_fun := λ i, f i, .. f }

lemma smooth_sum : smooth I 𝓘(ℝ) (λ x, ∑ᶠ i, f i x) :=
smooth_finsum (λ i, (f i).smooth) f.locally_finite

lemma le_one (i : ι) (x : M) : f i x ≤ 1 := f.to_partition_of_unity.le_one i x

lemma sum_nonneg (x : M) : 0 ≤ ∑ᶠ i, f i x := f.to_partition_of_unity.sum_nonneg x

/-- A smooth partition of unity `f i` is subordinate to a family of sets `U i` indexed by the same
type if for each `i` the closure of the support of `f i` is a subset of `U i`. -/
def is_subordinate (f : smooth_partition_of_unity ι I M s) (U : ι → set M) :=
∀ i, closure (support (f i)) ⊆ U i

@[simp] lemma is_subordinate_to_partition_of_unity {f : smooth_partition_of_unity ι I M s}
  {U : ι → set M} :
  f.to_partition_of_unity.is_subordinate U ↔ f.is_subordinate U :=
iff.rfl

alias is_subordinate_to_partition_of_unity ↔
  _ smooth_partition_of_unity.is_subordinate.to_partition_of_unity

end smooth_partition_of_unity

namespace bump_covering

-- Repeat variables to drop two of them
lemma smooth_to_partition_of_unity {E : Type uE} [normed_group E] [normed_space ℝ E]
  {H : Type uH} [topological_space H] {I : model_with_corners ℝ E H}
  {M : Type uM} [topological_space M] [charted_space H M] {s : set M}
  (f : bump_covering ι M s) (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) (i : ι) :
  smooth I 𝓘(ℝ) (f.to_partition_of_unity i) :=
(hf i).mul $ smooth_finprod_cond (λ j _, smooth_const.sub (hf j)) $
  by { simp only [mul_support_one_sub], exact f.locally_finite }

variables {s : set M}

/-- A `bump_covering` such that all functions in this covering are smooth generates a smooth
partition of unity. -/
def to_smooth_partition_of_unity (f : bump_covering ι M s) (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) :
  smooth_partition_of_unity ι I M s :=
{ to_fun := λ i, ⟨f.to_partition_of_unity i, f.smooth_to_partition_of_unity hf i⟩,
  .. f.to_partition_of_unity }

@[simp] lemma to_smooth_partition_of_unity_to_partition_of_unity (f : bump_covering ι M s)
  (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) :
  (f.to_smooth_partition_of_unity hf).to_partition_of_unity = f.to_partition_of_unity :=
rfl

@[simp] lemma coe_to_smooth_partition_of_unity (f : bump_covering ι M s)
  (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) (i : ι) :
  ⇑(f.to_smooth_partition_of_unity hf i) = f.to_partition_of_unity i :=
rfl

lemma is_subordinate.to_smooth_partition_of_unity {f : bump_covering ι M s}
  {U : ι → set M} (h : f.is_subordinate U) (hf : ∀ i, smooth I 𝓘(ℝ) (f i)) :
  (f.to_smooth_partition_of_unity hf).is_subordinate U :=
h.to_partition_of_unity

end bump_covering

namespace smooth_bump_covering

variables {s : set M} {U : M → set M} (fs : smooth_bump_covering I M s) {I}

instance : has_coe_to_fun (smooth_bump_covering I M s) := ⟨_, to_fun⟩

@[simp] lemma coe_mk (ι : Type uM) (c : ι → M) (to_fun : Π i, smooth_bump_function I (c i))
  (h₁ h₂ h₃) : ⇑(mk ι c to_fun h₁ h₂ h₃ : smooth_bump_covering I M s) = to_fun :=
rfl

/-- 
We say that `f : smooth_bump_covering I M s` is *subordinate* to a map `U : M → set M` if for each
index `i`, we have `closure (support (f i)) ⊆ U (f i).c`. This notion is a bit more general than
being subordinate to an open covering of `M`, because we make no assumption about the way `U x`
depends on `x`.
-/
def is_subordinate {s : set M} (f : smooth_bump_covering I M s) (U : M → set M) :=
∀ i, closure (support $ f i) ⊆ U (f.c i)

lemma is_subordinate.support_subset {fs : smooth_bump_covering I M s} {U : M → set M}
  (h : fs.is_subordinate U) (i : fs.ι) :
  support (fs i) ⊆ U (fs.c i) :=
subset.trans subset_closure (h i)

variable (I)

/-- Let `M` be a smooth manifold with corners modelled on a finite dimensional real vector space.
Suppose also that `M` is a Hausdorff `σ`-compact topological space. Let `s` be a closed set
in `M` and `U : M → set M` be a collection of sets such that `U x ∈ 𝓝 x` for every `x ∈ s`.
Then there exists a smooth bump covering of `s` that is subordinate to `U`. -/
lemma exists_is_subordinate [t2_space M] [sigma_compact_space M] (hs : is_closed s)
  (hU : ∀ x ∈ s, U x ∈ 𝓝 x) :
  ∃ f : smooth_bump_covering I M s, f.is_subordinate U :=
begin
  -- First we deduce some missing instances
  haveI : locally_compact_space H := I.locally_compact,
  haveI : locally_compact_space M := charted_space.locally_compact H,
  haveI : normal_space M := normal_of_paracompact_t2,
  -- Next we choose a covering by supports of smooth bump functions
  have hB := λ x hx, smooth_bump_function.nhds_basis_support I (hU x hx),
  rcases refinement_of_locally_compact_sigma_compact_of_nhds_basis_set hs hB
    with ⟨ι, c, f, hf, hsub', hfin⟩, choose hcs hfU using hf,
  /- Then we use the shrinking lemma to get a covering by smaller open -/
  rcases exists_subset_Union_closed_subset hs (λ i, (f i).open_support)
    (λ x hx, hfin.point_finite x) hsub' with ⟨V, hsV, hVc, hVf⟩,
  choose r hrR hr using λ i, (f i).exists_r_pos_lt_subset_ball (hVc i) (hVf i),
  refine ⟨⟨ι, c, λ i, (f i).update_r (r i) (hrR i), hcs, _, λ x hx, _⟩, λ i, _⟩,
  { simpa only [smooth_bump_function.support_update_r] },
  { refine (mem_Union.1 $ hsV hx).imp (λ i hi, _),
    exact ((f i).update_r _ _).eventually_eq_one_of_dist_lt
      ((f i).support_subset_source $ hVf _ hi) (hr i hi).2 },
  { simpa only [coe_mk, smooth_bump_function.support_update_r] using hfU i }
end

/-- Choice of a covering of a closed set `s` by supports of smooth bump functions. -/
def choice_set [t2_space M] [sigma_compact_space M] (s : set M) (hs : is_closed s) :
  smooth_bump_covering I M s :=
(exists_is_subordinate I hs (λ x hx, univ_mem_sets)).some

instance [t2_space M] [sigma_compact_space M] {s : set M} [is_closed s] :
  inhabited (smooth_bump_covering I M s) :=
⟨choice_set I s ‹_›⟩

variable (M)

/-- Choice of a covering of a manifold by supports of smooth bump functions. -/
def choice [t2_space M] [sigma_compact_space M] :
  smooth_bump_covering I M :=
choice_set I univ is_closed_univ

variables {I M}

protected lemma locally_finite : locally_finite (λ i, support (fs i)) := fs.locally_finite'

protected lemma point_finite (x : M) : {i | fs i x ≠ 0}.finite :=
fs.locally_finite.point_finite x

lemma mem_chart_at_source_of_eq_one {i : fs.ι} {x : M} (h : fs i x = 1) :
  x ∈ (chart_at H (fs.c i)).source :=
(fs i).support_subset_source $ by simp [h]

lemma mem_ext_chart_at_source_of_eq_one {i : fs.ι} {x : M} (h : fs i x = 1) :
  x ∈ (ext_chart_at I (fs.c i)).source :=
by { rw ext_chart_at_source, exact fs.mem_chart_at_source_of_eq_one h }

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : M) (hx : x ∈ s) : fs.ι := (fs.eventually_eq_one' x hx).some

lemma eventually_eq_one (x : M) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
(fs.eventually_eq_one' x hx).some_spec

lemma apply_ind (x : M) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
(fs.eventually_eq_one x hx).eq_of_nhds

lemma mem_support_ind (x : M) (hx : x ∈ s) : x ∈ support (fs $ fs.ind x hx) :=
by simp [fs.apply_ind x hx]

lemma mem_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (chart_at H (fs.c (fs.ind x hx))).source :=
fs.mem_chart_at_source_of_eq_one (fs.apply_ind x hx)

lemma mem_ext_chart_at_ind_source (x : M) (hx : x ∈ s) :
  x ∈ (ext_chart_at I (fs.c (fs.ind x hx))).source :=
fs.mem_ext_chart_at_source_of_eq_one (fs.apply_ind x hx)

instance fintype_ι_of_compact [compact_space M] : fintype fs.ι :=
fs.locally_finite.fintype_of_compact $ λ i, (fs i).nonempty_support

variable [t2_space M]

/-- Reinterpret a `smooth_bump_covering` as a continuous `bump_covering`. -/
def to_bump_covering : bump_covering fs.ι M s :=
{ to_fun := λ i, ⟨fs i, (fs i).continuous⟩,
  locally_finite' := fs.locally_finite,
  nonneg' := λ i x, (fs i).nonneg,
  le_one' := λ i x, (fs i).le_one,
  eventually_eq_one' := fs.eventually_eq_one' }

@[simp] lemma is_subordinate_to_bump_covering {f : smooth_bump_covering I M s} {U : M → set M} :
  f.to_bump_covering.is_subordinate (λ i, U (f.c i)) ↔ f.is_subordinate U :=
iff.rfl

alias is_subordinate_to_bump_covering ↔
  _ smooth_bump_covering.is_subordinate.to_bump_covering

/-- Every `smooth_bump_covering` defines a smooth partition of unity. -/
def to_smooth_partition_of_unity : smooth_partition_of_unity fs.ι I M s :=
fs.to_bump_covering.to_smooth_partition_of_unity (λ i, (fs i).smooth)

lemma to_smooth_partition_of_unity_apply (i : fs.ι) (x : M) :
  fs.to_smooth_partition_of_unity i x = fs i x * ∏ᶠ j (hj : well_ordering_rel j i), (1 - fs j x) :=
rfl

lemma to_smooth_partition_of_unity_eq_mul_prod (i : fs.ι) (x : M) (t : finset fs.ι)
  (ht : ∀ j, well_ordering_rel j i → fs j x ≠ 0 → j ∈ t) :
  fs.to_smooth_partition_of_unity i x =
    fs i x * ∏ j in t.filter (λ j, well_ordering_rel j i), (1 - fs j x) :=
fs.to_bump_covering.to_partition_of_unity_eq_mul_prod i x t ht

lemma exists_finset_to_smooth_partition_of_unity_eventually_eq (i : fs.ι) (x : M) :
  ∃ t : finset fs.ι, fs.to_smooth_partition_of_unity i =ᶠ[𝓝 x]
    fs i * ∏ j in t.filter (λ j, well_ordering_rel j i), (1 - fs j) :=
fs.to_bump_covering.exists_finset_to_partition_of_unity_eventually_eq i x

lemma to_smooth_partition_of_unity_zero_of_zero {i : fs.ι} {x : M} (h : fs i x = 0) :
  fs.to_smooth_partition_of_unity i x = 0 :=
fs.to_bump_covering.to_partition_of_unity_zero_of_zero h

lemma support_to_smooth_partition_of_unity_subset (i : fs.ι) :
  support (fs.to_smooth_partition_of_unity i) ⊆ support (fs i) :=
fs.to_bump_covering.support_to_partition_of_unity_subset i

lemma is_subordinate.to_smooth_partition_of_unity {f : smooth_bump_covering I M s} {U : M → set M}
  (h : f.is_subordinate U) :
  f.to_smooth_partition_of_unity.is_subordinate (λ i, U (f.c i)) :=
h.to_bump_covering.to_partition_of_unity

lemma sum_to_smooth_partition_of_unity_eq (x : M) :
  ∑ᶠ i, fs.to_smooth_partition_of_unity i x = 1 - ∏ᶠ i, (1 - fs i x) :=
fs.to_bump_covering.sum_to_partition_of_unity_eq x

end smooth_bump_covering

variable (I)

/-- Given two disjoint closed sets in a Hausdorff σ-compact finite dimensional manifold, there
exists an infinitely smooth function that is equal to `0` on one of them and is equal to one on the
other. -/
lemma exists_smooth_zero_one_of_closed [t2_space M] [sigma_compact_space M] {s t : set M}
  (hs : is_closed s) (ht : is_closed t) (hd : disjoint s t) :
  ∃ f : C^∞⟮I, M; 𝓘(ℝ), ℝ⟯, eq_on f 0 s ∧ eq_on f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
begin
  have : ∀ x ∈ t, sᶜ ∈ 𝓝 x, from λ x hx, hs.is_open_compl.mem_nhds (disjoint_right.1 hd hx),
  rcases smooth_bump_covering.exists_is_subordinate I ht this with ⟨f, hf⟩,
  set g := f.to_smooth_partition_of_unity,
  refine ⟨⟨_, g.smooth_sum⟩, λ x hx, _, λ x, g.sum_eq_one, λ x, ⟨g.sum_nonneg x, g.sum_le_one x⟩⟩,
  suffices : ∀ i, g i x = 0,
    by simp only [this, times_cont_mdiff_map.coe_fn_mk, finsum_zero, pi.zero_apply],
  refine λ i, f.to_smooth_partition_of_unity_zero_of_zero _,
  exact nmem_support.1 (subset_compl_comm.1 (hf.support_subset i) hx)
end

variable {I}

namespace smooth_partition_of_unity

variables [t2_space M] [sigma_compact_space M]

/-- If `X` is a paracompact normal topological space and `U` is an open covering of a closed set
`s`, then there exists a `bump_covering ι X s` that is subordinate to `U`. -/
lemma exists_is_subordinate {s : set M} (hs : is_closed s) (U : ι → set M) (ho : ∀ i, is_open (U i))
  (hU : s ⊆ ⋃ i, U i) :
  ∃ f : smooth_partition_of_unity ι I M s, f.is_subordinate U :=
begin
  haveI : locally_compact_space H := I.locally_compact,
  haveI : locally_compact_space M := charted_space.locally_compact H,
  haveI : normal_space M := normal_of_paracompact_t2,
  rcases bump_covering.exists_is_subordinate_of_prop (smooth I 𝓘(ℝ)) _ hs U ho hU
    with ⟨f, hf, hfU⟩,
  { exact ⟨f.to_smooth_partition_of_unity hf, hfU.to_smooth_partition_of_unity hf⟩ },
  { intros s t hs ht hd,
    rcases exists_smooth_zero_one_of_closed I hs ht hd with ⟨f, hf⟩,
    exact ⟨f, f.smooth, hf⟩ }
end

instance {s : set M} [is_closed s] :
  inhabited (smooth_partition_of_unity s I M s) :=
⟨(exists_is_subordinate ‹_› (λ _ : s, univ) (λ _, is_open_univ)
  (λ x hx, mem_Union.2 ⟨⟨x, hx⟩, mem_univ x⟩)).some⟩

end smooth_partition_of_unity
