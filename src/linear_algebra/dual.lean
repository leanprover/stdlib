/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle
-/
import linear_algebra.finite_dimensional
noncomputable theory

/-!
# Dual vector spaces

The dual space of an R-module M is the R-module of linear maps `M → R`.

## Main definitions

* `dual R M` defines the dual space of M over R.
* Given a basis for a K-vector space `V`, `is_basis.to_dual` produces a map from `V` to `dual K V`.
* Given families of vectors `e` and `ε`, `dual_pair e ε` states that these families have the
  characteristic properties of a basis and a dual.

## Main results

* `to_dual_equiv` : the dual space is linearly equivalent to the primal space.
* `dual_pair.is_basis` and `dual_pair.eq_dual`: if `e` and `ε` form a dual pair, `e` is a basis and
  `ε` is its dual basis.

## Notation

We sometimes use `V'` as local notation for `dual K V`.

-/

namespace module
variables (R : Type*) (M : Type*)
variables [comm_ring R] [add_comm_group M] [module R M]

/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
@[derive [add_comm_group, module R]] def dual := M →ₗ[R] R

namespace dual

instance : inhabited (dual R M) := by dunfold dual; apply_instance

instance : has_coe_to_fun (dual R M) := ⟨_, linear_map.to_fun⟩

/-- Maps a module M to the dual of the dual of M. See `vector_space.erange_coe` and
`vector_space.eval_equiv`. -/
def eval : M →ₗ[R] (dual R (dual R M)) := linear_map.flip linear_map.id

@[simp] lemma eval_apply (v : M) (a : dual R M) : eval R M v a = a v :=
begin
  dunfold eval,
  rw [linear_map.flip_apply, linear_map.id_apply]
end

variables {R M} {M' : Type*} [add_comm_group M'] [module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`dual R M' →ₗ[R] dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] (dual R M' →ₗ[R] dual R M) :=
(linear_map.llcomp R M M' R).flip

lemma transpose_apply (u : M →ₗ[R] M') (l : dual R M') : transpose u l = l.comp u := rfl

variables {M'' : Type*} [add_comm_group M''] [module R M'']

lemma transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
  transpose (u.comp v) = (transpose v).comp (transpose u) := rfl

end dual
end module

namespace is_basis
universes u v w
variables {K : Type u} {V : Type v} {ι : Type w}
variables [field K] [add_comm_group V] [vector_space K V]
open vector_space module module.dual submodule linear_map cardinal function

variables [de : decidable_eq ι]
variables (B : ι → V) (h : is_basis K B)

include de h

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def to_dual : V →ₗ[K] module.dual K V :=
h.constr $ λ v, h.constr $ λ w, if w = v then 1 else 0

variable {B}

lemma to_dual_apply (i j : ι) :
  h.to_dual B (B i) (B j) = if i = j then 1 else 0 :=
by { erw [constr_basis h, constr_basis h], ac_refl }

@[simp] lemma to_dual_total_left (f : ι →₀ K) (i : ι) :
  h.to_dual B (finsupp.total ι V K B f) (B i) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum, linear_map.sum_apply],
  simp_rw [linear_map.map_smul, linear_map.smul_apply, to_dual_apply, smul_eq_mul,
           mul_boole, finset.sum_ite_eq'],
  split_ifs with h,
  { refl },
  { rw finsupp.not_mem_support_iff.mp h }
end

@[simp] lemma to_dual_total_right (f : ι →₀ K) (i : ι) :
  h.to_dual B (B i) (finsupp.total ι V K B f) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum],
  simp_rw [linear_map.map_smul, to_dual_apply, smul_eq_mul, mul_boole, finset.sum_ite_eq],
  split_ifs with h,
  { refl },
  { rw finsupp.not_mem_support_iff.mp h }
end

lemma to_dual_apply_left (v : V) (i : ι) : h.to_dual B v (B i) = h.repr v i :=
by rw [← h.to_dual_total_left, h.total_repr]

lemma to_dual_apply_right (i : ι) (v : V) : h.to_dual B (B i) v = h.repr v i :=
by rw [← h.to_dual_total_right, h.total_repr]

variable (B)

/-- `h.to_dual_flip v` is the linear map sending `w` to `h.to_dual w v`. -/
def to_dual_flip (v : V) : (V →ₗ[K] K) := (h.to_dual B).flip v

variable {B}

omit de h
-- TODO: unify this with `finsupp.lapply`.
/-- Evaluation of finitely supported functions at a fixed point `i`, as a `K`-linear map. -/
def eval_finsupp_at (i : ι) : (ι →₀ K) →ₗ[K] K :=
{ to_fun    := λ f, f i,
  map_add'  := by intros; rw finsupp.add_apply,
  map_smul' := by intros; rw finsupp.smul_apply }
include h

/-- `h.coord_fun i` sends vectors to their `i`'th coordinate with respect to the basis `h`. -/
def coord_fun (i : ι) : (V →ₗ[K] K) := linear_map.comp (eval_finsupp_at i) h.repr

lemma coord_fun_eq_repr (v : V) (i : ι) : h.coord_fun i v = h.repr v i := rfl

include de

-- TODO: this lemma should be called something like `to_dual_flip_apply`
lemma to_dual_swap_eq_to_dual (v w : V) : h.to_dual_flip B v w = h.to_dual B w v := rfl

lemma to_dual_eq_repr (v : V) (i : ι) : h.to_dual B v (B i) = h.repr v i :=
h.to_dual_apply_left v i

lemma to_dual_eq_equiv_fun [fintype ι] (v : V) (i : ι) : h.to_dual B v (B i) = h.equiv_fun v i :=
by rw [h.equiv_fun_apply, to_dual_eq_repr]

lemma to_dual_inj (v : V) (a : h.to_dual B v = 0) : v = 0 :=
begin
  rw [← mem_bot K, ← h.repr_ker, mem_ker],
  apply finsupp.ext,
  intro b,
  rw [←to_dual_eq_repr _ _ _, a],
  refl
end

theorem to_dual_ker : (h.to_dual B).ker = ⊥ :=
ker_eq_bot'.mpr h.to_dual_inj

theorem to_dual_range [fin : fintype ι] : (h.to_dual B).range = ⊤ :=
begin
  rw eq_top_iff',
  intro f,
  rw linear_map.mem_range,
  let lin_comb : ι →₀ K := finsupp.on_finset fin.elems (λ i, f.to_fun (B i)) _,
  { use finsupp.total ι V K B lin_comb,
    apply h.ext,
    { intros i,
      rw [h.to_dual_eq_repr _ i, repr_total h],
      { refl },
      { rw [finsupp.mem_supported],
        exact λ _ _, set.mem_univ _ } } },
  { intros a _,
    apply fin.complete }
end

/-- Maps a basis for `V` to a basis for the dual space. -/
def dual_basis : ι → dual K V := λ i, h.to_dual B (B i)

theorem dual_lin_independent : linear_independent K h.dual_basis :=
h.1.map' _ (to_dual_ker _)

@[simp] lemma dual_basis_apply_self (i j : ι) :
  h.dual_basis i (B j) = if i = j then 1 else 0 :=
h.to_dual_apply i j

variable (B)

/-- A vector space is linearly equivalent to its dual space. -/
def to_dual_equiv [fintype ι] : V ≃ₗ[K] (dual K V) :=
linear_equiv.of_bijective (h.to_dual B) h.to_dual_ker h.to_dual_range

variable {B}

theorem dual_basis_is_basis [fintype ι] : is_basis K h.dual_basis :=
(h.to_dual_equiv B).is_basis h

@[simp] lemma total_dual_basis [fintype ι] (f : ι →₀ K) (i : ι) :
  finsupp.total ι (dual K V) K h.dual_basis f (B i) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum_fintype, linear_map.sum_apply],
  { simp_rw [smul_apply, smul_eq_mul, dual_basis_apply_self, mul_boole,
             finset.sum_ite_eq', if_pos (finset.mem_univ i)] },
  { intro, rw zero_smul },
end

lemma dual_basis_repr [fintype ι] (l : dual K V) (i : ι) :
  h.dual_basis_is_basis.repr l i = l (B i) :=
by rw [← total_dual_basis h, is_basis.total_repr h.dual_basis_is_basis l ]

lemma dual_basis_equiv_fun [fintype ι] (l : dual K V) (i : ι) :
  h.dual_basis_is_basis.equiv_fun l i = l (B i) :=
by rw [is_basis.equiv_fun_apply, dual_basis_repr]

lemma dual_basis_apply [fintype ι] (i : ι) (v : V) : h.dual_basis i v = h.equiv_fun v i :=
h.to_dual_apply_right i v

@[simp] lemma to_dual_to_dual [fintype ι] :
  (h.dual_basis_is_basis.to_dual _).comp (h.to_dual B) = eval K V :=
begin
  refine h.ext (λ i, h.dual_basis_is_basis.ext (λ j, _)),
  suffices : @ite _ (classical.prop_decidable _) K 1 0 = @ite _ (de j i) K 1 0,
    by simpa [h.dual_basis_is_basis.to_dual_apply_left, h.dual_basis_repr, h.to_dual_apply_right],
  split_ifs; refl
end

omit de

theorem dual_dim_eq [fintype ι] :
  cardinal.lift.{v u} (dim K V) = dim K (dual K V) :=
begin
  classical,
  have := linear_equiv.dim_eq_lift (h.to_dual_equiv B),
  simp only [cardinal.lift_umax] at this,
  rw [this, ← cardinal.lift_umax],
  apply cardinal.lift_id,
end

end is_basis

namespace vector_space

universes u v
variables {K : Type u} {V : Type v}
variables [field K] [add_comm_group V] [vector_space K V]
open module module.dual submodule linear_map cardinal is_basis finite_dimensional

theorem eval_ker : (eval K V).ker = ⊥ :=
begin
  classical,
  rw ker_eq_bot',
  intros v h,
  rw linear_map.ext_iff at h,
  by_contradiction H,
  rcases exists_subset_is_basis (linear_independent_singleton H) with ⟨b, hv, hb⟩,
  swap 4, assumption,
  have hv' : v = (coe : b → V) ⟨v, hv (set.mem_singleton v)⟩ := rfl,
  let hx := h (hb.to_dual _ v),
  rw [eval_apply, hv', to_dual_apply, if_pos rfl, zero_apply] at hx,
  exact one_ne_zero hx
end

theorem dual_dim_eq [finite_dimensional K V] :
  cardinal.lift.{v u} (dim K V) = dim K (dual K V) :=
begin
  classical,
  rcases exists_is_basis_fintype (dim_lt_omega K V) with ⟨b, hb, ⟨hf⟩⟩,
  resetI,
  exact hb.dual_dim_eq
end


lemma erange_coe [finite_dimensional K V] : (eval K V).range = ⊤ :=
begin
  classical,
  rcases exists_is_basis_fintype (dim_lt_omega K V) with ⟨b, hb, ⟨hf⟩⟩,
  unfreezingI { rw [← hb.to_dual_to_dual, range_comp, hb.to_dual_range, map_top, to_dual_range _] },
  apply_instance
end

/-- A vector space is linearly equivalent to the dual of its dual space. -/
def eval_equiv [finite_dimensional K V] : V ≃ₗ[K] dual K (dual K V) :=
linear_equiv.of_bijective (eval K V) eval_ker (erange_coe)

end vector_space

section dual_pair

open vector_space module module.dual linear_map function

universes u v w
variables {K : Type u} {V : Type v} {ι : Type w} [decidable_eq ι]
variables [field K] [add_comm_group V] [vector_space K V]

local notation `V'` := dual K V

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
@[nolint has_inhabited_instance]
structure dual_pair (e : ι → V) (ε : ι → V') :=
(eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0)
(total : ∀ {v : V}, (∀ i, ε i v = 0) → v = 0)
[finite : ∀ v : V, fintype {i | ε i v ≠ 0}]

end dual_pair

namespace dual_pair

open vector_space module module.dual linear_map function

universes u v w
variables {K : Type u} {V : Type v} {ι : Type w} [dι : decidable_eq ι]
variables [field K] [add_comm_group V] [vector_space K V]
variables {e : ι → V} {ε : ι → dual K V} (h : dual_pair e ε)

include h

/-- The coefficients of `v` on the basis `e` -/
def coeffs (v : V) : ι →₀ K :=
{ to_fun := λ i, ε i v,
  support := by { haveI := h.finite v, exact {i : ι | ε i v ≠ 0}.to_finset },
  mem_support_to_fun := by {intro i, rw set.mem_to_finset, exact iff.rfl } }


@[simp] lemma coeffs_apply (v : V) (i : ι) : h.coeffs v i = ε i v := rfl

omit h
/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `finsupp.total _ V K e l` -/
def lc (e : ι → V) (l : ι →₀ K) : V := l.sum (λ (i : ι) (a : K), a • (e i))

include h

lemma dual_lc (l : ι →₀ K) (i : ι) : ε i (dual_pair.lc e l) = l i :=
begin
  erw linear_map.map_sum,
  simp only [h.eval, map_smul, smul_eq_mul],
  rw finset.sum_eq_single i,
  { simp },
  { intros q q_in q_ne,
    simp [q_ne.symm] },
  { intro p_not_in,
    simp [finsupp.not_mem_support_iff.1 p_not_in] },
end

@[simp]
lemma coeffs_lc (l : ι →₀ K) : h.coeffs (dual_pair.lc e l) = l :=
by { ext i, rw [h.coeffs_apply, h.dual_lc] }

/-- For any v : V n, \sum_{p ∈ Q n} (ε p v) • e p = v -/
lemma decomposition (v : V) : dual_pair.lc e (h.coeffs v) = v :=
begin
  refine eq_of_sub_eq_zero (h.total _),
  intros i,
  simp [-sub_eq_add_neg, linear_map.map_sub, h.dual_lc, sub_eq_zero_iff_eq]
end

lemma mem_of_mem_span {H : set ι} {x : V} (hmem : x ∈ submodule.span K (e '' H)) :
  ∀ i : ι, ε i x ≠ 0 → i ∈ H :=
begin
  intros i hi,
  rcases (finsupp.mem_span_iff_total _).mp hmem with ⟨l, supp_l, sum_l⟩,
  change dual_pair.lc e l = x at sum_l,
  rw finsupp.mem_supported' at supp_l,
  apply classical.by_contradiction,
  intro i_not,
  apply hi,
  rw ← sum_l,
  simpa [h.dual_lc] using supp_l i i_not
end

lemma is_basis : is_basis K e :=
begin
  split,
  { rw linear_independent_iff,
    intros l H,
    change dual_pair.lc e l = 0 at H,
    ext i,
    apply_fun ε i at H,
    simpa [h.dual_lc] using H },
  { rw submodule.eq_top_iff',
    intro v,
    rw [← set.image_univ, finsupp.mem_span_iff_total],
    exact ⟨h.coeffs v, by simp, h.decomposition v⟩ },
end

lemma eq_dual : ε = is_basis.dual_basis h.is_basis :=
begin
  funext i,
  refine h.is_basis.ext (λ _, _),
  erw [is_basis.to_dual_apply, h.eval]
end

end dual_pair
