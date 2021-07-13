/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle
-/
import linear_algebra.finite_dimensional
import linear_algebra.projection

/-!
# Dual vector spaces

The dual space of an R-module M is the R-module of linear maps `M → R`.

## Main definitions

* `dual R M` defines the dual space of M over R.
* Given a basis for an `R`-module `M`, `basis.to_dual` produces a map from `M` to `dual R M`.
* Given families of vectors `e` and `ε`, `dual_pair e ε` states that these families have the
  characteristic properties of a basis and a dual.
* `dual_annihilator W` is the submodule of `dual R M` where every element annihilates `W`.

## Main results

* `to_dual_equiv` : the linear equivalence between the dual module and primal module,
  given a finite basis.
* `dual_pair.basis` and `dual_pair.eq_dual`: if `e` and `ε` form a dual pair, `e` is a basis and
  `ε` is its dual basis.
* `quot_equiv_annihilator`: the quotient by a subspace is isomorphic to its dual annihilator.

## Notation

We sometimes use `V'` as local notation for `dual K V`.

## TODO

Erdös-Kaplansky theorem about the dimension of a dual vector space in case of infinite dimension.
-/

noncomputable theory

namespace module

variables (R : Type*) (M : Type*)
variables [comm_semiring R] [add_comm_monoid M] [module R M]

/-- The dual space of an R-module M is the R-module of linear maps `M → R`. -/
@[derive [add_comm_monoid, module R]] def dual := M →ₗ[R] R

instance {S : Type*} [comm_ring S] {N : Type*} [add_comm_group N] [module S N] :
  add_comm_group (dual S N) := by {unfold dual, apply_instance}

namespace dual

instance : inhabited (dual R M) := by dunfold dual; apply_instance

instance : has_coe_to_fun (dual R M) := ⟨_, linear_map.to_fun⟩

/-- Maps a module M to the dual of the dual of M. See `module.erange_coe` and
`module.eval_equiv`. -/
def eval : M →ₗ[R] (dual R (dual R M)) := linear_map.flip linear_map.id

@[simp] lemma eval_apply (v : M) (a : dual R M) : eval R M v a = a v :=
begin
  dunfold eval,
  rw [linear_map.flip_apply, linear_map.id_apply]
end

variables {R M} {M' : Type*} [add_comm_monoid M'] [module R M']

/-- The transposition of linear maps, as a linear map from `M →ₗ[R] M'` to
`dual R M' →ₗ[R] dual R M`. -/
def transpose : (M →ₗ[R] M') →ₗ[R] (dual R M' →ₗ[R] dual R M) :=
(linear_map.llcomp R M M' R).flip

lemma transpose_apply (u : M →ₗ[R] M') (l : dual R M') : transpose u l = l.comp u := rfl

variables {M'' : Type*} [add_comm_monoid M''] [module R M'']

lemma transpose_comp (u : M' →ₗ[R] M'') (v : M →ₗ[R] M') :
  transpose (u.comp v) = (transpose v).comp (transpose u) := rfl

end dual

end module

namespace basis

universes u v w

open module module.dual submodule linear_map cardinal function

variables {R M K V ι : Type*}

section comm_semiring

variables [comm_semiring R] [add_comm_monoid M] [module R M] [decidable_eq ι]
variables (b : basis ι R M)

/-- The linear map from a vector space equipped with basis to its dual vector space,
taking basis elements to corresponding dual basis elements. -/
def to_dual : M →ₗ[R] module.dual R M :=
b.constr ℕ $ λ v, b.constr ℕ $ λ w, if w = v then (1 : R) else 0

lemma to_dual_apply (i j : ι) :
  b.to_dual (b i) (b j) = if i = j then 1 else 0 :=
by { erw [constr_basis b, constr_basis b], ac_refl }

@[simp] lemma to_dual_total_left (f : ι →₀ R) (i : ι) :
  b.to_dual (finsupp.total ι M R b f) (b i) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum, linear_map.sum_apply],
  simp_rw [linear_map.map_smul, linear_map.smul_apply, to_dual_apply, smul_eq_mul,
           mul_boole, finset.sum_ite_eq'],
  split_ifs with h,
  { refl },
  { rw finsupp.not_mem_support_iff.mp h }
end

@[simp] lemma to_dual_total_right (f : ι →₀ R) (i : ι) :
  b.to_dual (b i) (finsupp.total ι M R b f) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum, linear_map.map_sum],
  simp_rw [linear_map.map_smul, to_dual_apply, smul_eq_mul, mul_boole, finset.sum_ite_eq],
  split_ifs with h,
  { refl },
  { rw finsupp.not_mem_support_iff.mp h }
end

lemma to_dual_apply_left (m : M) (i : ι) : b.to_dual m (b i) = b.repr m i :=
by rw [← b.to_dual_total_left, b.total_repr]

lemma to_dual_apply_right (i : ι) (m : M) : b.to_dual (b i) m = b.repr m i :=
by rw [← b.to_dual_total_right, b.total_repr]

lemma coe_to_dual_self (i : ι) : b.to_dual (b i) = b.coord i :=
by { ext, apply to_dual_apply_right }

/-- `h.to_dual_flip v` is the linear map sending `w` to `h.to_dual w v`. -/
def to_dual_flip (m : M) : (M →ₗ[R] R) := b.to_dual.flip m

lemma to_dual_flip_apply (m₁ m₂ : M) : b.to_dual_flip m₁ m₂ = b.to_dual m₂ m₁ := rfl

lemma to_dual_eq_repr (m : M) (i : ι) : b.to_dual m (b i) = b.repr m i :=
b.to_dual_apply_left m i

lemma to_dual_eq_equiv_fun [fintype ι] (m : M) (i : ι) : b.to_dual m (b i) = b.equiv_fun m i :=
by rw [b.equiv_fun_apply, to_dual_eq_repr]

lemma to_dual_inj (m : M) (a : b.to_dual m = 0) : m = 0 :=
begin
  rw [← mem_bot R, ← b.repr.ker, mem_ker, linear_equiv.coe_coe],
  apply finsupp.ext,
  intro b,
  rw [← to_dual_eq_repr, a],
  refl
end

theorem to_dual_ker : b.to_dual.ker = ⊥ :=
ker_eq_bot'.mpr b.to_dual_inj

theorem to_dual_range [fin : fintype ι] : b.to_dual.range = ⊤ :=
begin
  rw eq_top_iff',
  intro f,
  rw linear_map.mem_range,
  let lin_comb : ι →₀ R := finsupp.on_finset fin.elems (λ i, f.to_fun (b i)) _,
  { use finsupp.total ι M R b lin_comb,
    apply b.ext,
    { intros i,
      rw [b.to_dual_eq_repr _ i, repr_total b],
      { refl } } },
  { intros a _,
    apply fin.complete }
end

end comm_semiring

section comm_ring

variables [comm_ring R] [add_comm_group M] [module R M] [decidable_eq ι]
variables (b : basis ι R M)

/-- A vector space is linearly equivalent to its dual space. -/
@[simps]
def to_dual_equiv [fintype ι] : M ≃ₗ[R] (dual R M) :=
linear_equiv.of_bijective b.to_dual b.to_dual_ker b.to_dual_range

/-- Maps a basis for `V` to a basis for the dual space. -/
def dual_basis [fintype ι] : basis ι R (dual R M) :=
b.map b.to_dual_equiv

-- We use `j = i` to match `basis.repr_self`
lemma dual_basis_apply_self [fintype ι] (i j : ι) :
  b.dual_basis i (b j) = if j = i then 1 else 0 :=
by { convert b.to_dual_apply i j using 2, rw @eq_comm _ j i }

lemma total_dual_basis [fintype ι] (f : ι →₀ R) (i : ι) :
  finsupp.total ι (dual R M) R b.dual_basis f (b i) = f i :=
begin
  rw [finsupp.total_apply, finsupp.sum_fintype, linear_map.sum_apply],
  { simp_rw [linear_map.smul_apply, smul_eq_mul, dual_basis_apply_self, mul_boole,
      finset.sum_ite_eq, if_pos (finset.mem_univ i)] },
  { intro, rw zero_smul },
end

lemma dual_basis_repr [fintype ι] (l : dual R M) (i : ι) :
  b.dual_basis.repr l i = l (b i) :=
by rw [← total_dual_basis b, basis.total_repr b.dual_basis l]

lemma dual_basis_equiv_fun [fintype ι] (l : dual R M) (i : ι) :
  b.dual_basis.equiv_fun l i = l (b i) :=
by rw [basis.equiv_fun_apply, dual_basis_repr]

lemma dual_basis_apply [fintype ι] (i : ι) (m : M) : b.dual_basis i m = b.repr m i :=
b.to_dual_apply_right i m

@[simp] lemma coe_dual_basis [fintype ι] :
  ⇑b.dual_basis = b.coord :=
by { ext i x, apply dual_basis_apply }

@[simp] lemma to_dual_to_dual [fintype ι] :
  b.dual_basis.to_dual.comp b.to_dual = dual.eval R M :=
begin
  refine b.ext (λ i, b.dual_basis.ext (λ j, _)),
  rw [linear_map.comp_apply, to_dual_apply_left, coe_to_dual_self, ← coe_dual_basis,
      dual.eval_apply, basis.repr_self, finsupp.single_apply, dual_basis_apply_self]
end

theorem eval_ker {ι : Type*} (b : basis ι R M) :
  (dual.eval R M).ker = ⊥ :=
begin
  rw ker_eq_bot',
  intros m hm,
  simp_rw [linear_map.ext_iff, dual.eval_apply, zero_apply] at hm,
  exact (basis.forall_coord_eq_zero_iff _).mp (λ i, hm (b.coord i))
end

lemma eval_range {ι : Type*} [fintype ι] (b : basis ι R M) :
  (eval R M).range = ⊤ :=
begin
  classical,
  rw [← b.to_dual_to_dual, range_comp, b.to_dual_range, map_top, to_dual_range _],
  apply_instance
end

/-- A module with a basis is linearly equivalent to the dual of its dual space. -/
def eval_equiv  {ι : Type*} [fintype ι] (b : basis ι R M) : M ≃ₗ[R] dual R (dual R M) :=
linear_equiv.of_bijective (eval R M) b.eval_ker b.eval_range

@[simp] lemma eval_equiv_to_linear_map {ι : Type*} [fintype ι] (b : basis ι R M) :
  (b.eval_equiv).to_linear_map = dual.eval R M := rfl

end comm_ring

/-- `simp` normal form version of `total_dual_basis` -/
@[simp] lemma total_coord [comm_ring R] [add_comm_group M] [module R M] [fintype ι]
  (b : basis ι R M) (f : ι →₀ R) (i : ι) :
  finsupp.total ι (dual R M) R b.coord f (b i) = f i :=
by { haveI := classical.dec_eq ι, rw [← coe_dual_basis, total_dual_basis] }

-- TODO(jmc): generalize to rings, once `module.rank` is generalized
theorem dual_dim_eq [field K] [add_comm_group V] [module K V] [fintype ι] (b : basis ι K V) :
  cardinal.lift (module.rank K V) = module.rank K (dual K V) :=
begin
  classical,
  have := linear_equiv.dim_eq_lift b.to_dual_equiv,
  simp only [cardinal.lift_umax] at this,
  rw [this, ← cardinal.lift_umax],
  apply cardinal.lift_id,
end

end basis

namespace module

variables {K V : Type*}
variables [field K] [add_comm_group V] [module K V]
open module module.dual submodule linear_map cardinal basis finite_dimensional

theorem eval_ker : (eval K V).ker = ⊥ :=
by { classical, exact (basis.of_vector_space K V).eval_ker }

-- TODO(jmc): generalize to rings, once `module.rank` is generalized
theorem dual_dim_eq [finite_dimensional K V] :
  cardinal.lift (module.rank K V) = module.rank K (dual K V) :=
(basis.of_vector_space K V).dual_dim_eq

lemma erange_coe [finite_dimensional K V] : (eval K V).range = ⊤ :=
by { classical, exact (basis.of_vector_space K V).eval_range }

variables (K V)

/-- A vector space is linearly equivalent to the dual of its dual space. -/
def eval_equiv [finite_dimensional K V] : V ≃ₗ[K] dual K (dual K V) :=
linear_equiv.of_bijective (eval K V) eval_ker (erange_coe)

variables {K V}

@[simp] lemma eval_equiv_to_linear_map [finite_dimensional K V] :
  (eval_equiv K V).to_linear_map = dual.eval K V := rfl

end module

section dual_pair

open module

variables {R M ι : Type*}
variables [comm_ring R] [add_comm_group M] [module R M] [decidable_eq ι]

/-- `e` and `ε` have characteristic properties of a basis and its dual -/
@[nolint has_inhabited_instance]
structure dual_pair (e : ι → M) (ε : ι → (dual R M)) :=
(eval : ∀ i j : ι, ε i (e j) = if i = j then 1 else 0)
(total : ∀ {m : M}, (∀ i, ε i m = 0) → m = 0)
[finite : ∀ m : M, fintype {i | ε i m ≠ 0}]

end dual_pair

namespace dual_pair

open module module.dual linear_map function

variables {R M ι : Type*}
variables [comm_ring R] [add_comm_group M] [module R M]
variables {e : ι → M} {ε : ι → dual R M}

/-- The coefficients of `v` on the basis `e` -/
def coeffs [decidable_eq ι] (h : dual_pair e ε) (m : M) : ι →₀ R :=
{ to_fun := λ i, ε i m,
  support := by { haveI := h.finite m, exact {i : ι | ε i m ≠ 0}.to_finset },
  mem_support_to_fun := by {intro i, rw set.mem_to_finset, exact iff.rfl } }

@[simp] lemma coeffs_apply [decidable_eq ι] (h : dual_pair e ε) (m : M) (i : ι) :
  h.coeffs m i = ε i m := rfl

/-- linear combinations of elements of `e`.
This is a convenient abbreviation for `finsupp.total _ M R e l` -/
def lc {ι} (e : ι → M) (l : ι →₀ R) : M := l.sum (λ (i : ι) (a : R), a • (e i))

lemma lc_def (e : ι → M) (l : ι →₀ R) : lc e l = finsupp.total _ _ _ e l := rfl

variables [decidable_eq ι] (h : dual_pair e ε)
include h

lemma dual_lc (l : ι →₀ R) (i : ι) : ε i (dual_pair.lc e l) = l i :=
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
lemma coeffs_lc (l : ι →₀ R) : h.coeffs (dual_pair.lc e l) = l :=
by { ext i, rw [h.coeffs_apply, h.dual_lc] }

/-- For any m : M n, \sum_{p ∈ Q n} (ε p m) • e p = m -/
@[simp]
lemma lc_coeffs (m : M) : dual_pair.lc e (h.coeffs m) = m :=
begin
  refine eq_of_sub_eq_zero (h.total _),
  intros i,
  simp [-sub_eq_add_neg, linear_map.map_sub, h.dual_lc, sub_eq_zero]
end

/-- `(h : dual_pair e ε).basis` shows the family of vectors `e` forms a basis. -/
@[simps]
def basis : basis ι R M :=
basis.of_repr
{ to_fun := coeffs h,
  inv_fun := lc e,
  left_inv := lc_coeffs h,
  right_inv := coeffs_lc h,
  map_add' := λ v w, by { ext i, exact (ε i).map_add v w },
  map_smul' := λ c v, by { ext i, exact (ε i).map_smul c v } }

@[simp] lemma coe_basis : ⇑h.basis = e :=
by { ext i, rw basis.apply_eq_iff, ext j,
     rw [h.basis_repr_apply, coeffs_apply, h.eval, finsupp.single_apply],
     convert if_congr eq_comm rfl rfl } -- `convert` to get rid of a `decidable_eq` mismatch

lemma mem_of_mem_span {H : set ι} {x : M} (hmem : x ∈ submodule.span R (e '' H)) :
  ∀ i : ι, ε i x ≠ 0 → i ∈ H :=
begin
  intros i hi,
  rcases (finsupp.mem_span_image_iff_total _).mp hmem with ⟨l, supp_l, rfl⟩,
  apply not_imp_comm.mp ((finsupp.mem_supported' _ _).mp supp_l i),
  rwa [← lc_def, h.dual_lc] at hi
end

lemma coe_dual_basis [fintype ι] : ⇑h.basis.dual_basis = ε :=
funext (λ i, h.basis.ext (λ j, by rw [h.basis.dual_basis_apply_self, h.coe_basis, h.eval,
                                      if_congr eq_comm rfl rfl]))

end dual_pair

namespace submodule

universes u v w

variables {R : Type u} {M : Type v} [comm_semiring R] [add_comm_monoid M] [module R M]
variable {W : submodule R M}

/-- The `dual_restrict` of a submodule `W` of `M` is the linear map from the
  dual of `M` to the dual of `W` such that the domain of each linear map is
  restricted to `W`. -/
def dual_restrict (W : submodule R M) :
  module.dual R M →ₗ[R] module.dual R W :=
linear_map.dom_restrict' W

@[simp] lemma dual_restrict_apply
  (W : submodule R M) (φ : module.dual R M) (x : W) :
  W.dual_restrict φ x = φ (x : M) := rfl

/-- The `dual_annihilator` of a submodule `W` is the set of linear maps `φ` such
  that `φ w = 0` for all `w ∈ W`. -/
def dual_annihilator (W : submodule R M) : submodule R $ module.dual R M :=
W.dual_restrict.ker

@[simp] lemma mem_dual_annihilator (φ : module.dual R M) :
  φ ∈ W.dual_annihilator ↔ ∀ w ∈ W, φ w = 0 :=
begin
  refine linear_map.mem_ker.trans _,
  simp_rw [linear_map.ext_iff, dual_restrict_apply],
  exact ⟨λ h w hw, h ⟨w, hw⟩, λ h w, h w.1 w.2⟩
end

lemma dual_restrict_ker_eq_dual_annihilator (W : submodule R M) :
  W.dual_restrict.ker = W.dual_annihilator :=
rfl

lemma dual_annihilator_sup_eq_inf_dual_annihilator (U V : submodule R M) :
  (U ⊔ V).dual_annihilator = U.dual_annihilator ⊓ V.dual_annihilator :=
begin
  ext φ,
  rw [mem_inf, mem_dual_annihilator, mem_dual_annihilator, mem_dual_annihilator],
  split; intro h,
  { refine ⟨_, _⟩;
    intros x hx,
    exact h x (mem_sup.2 ⟨x, hx, 0, zero_mem _, add_zero _⟩),
    exact h x (mem_sup.2 ⟨0, zero_mem _, x, hx, zero_add _⟩) },
  { simp_rw mem_sup,
    rintro _ ⟨x, hx, y, hy, rfl⟩,
    rw [linear_map.map_add, h.1 _ hx, h.2 _ hy, add_zero] }
end

/-- The pullback of a submodule in the dual space along the evaluation map. -/
def dual_annihilator_comap (Φ : submodule R (module.dual R M)) : submodule R M :=
Φ.dual_annihilator.comap (module.dual.eval R M)

lemma mem_dual_annihilator_comap_iff {Φ : submodule R (module.dual R M)} (x : M) :
  x ∈ Φ.dual_annihilator_comap ↔ ∀ φ ∈ Φ, (φ x : R) = 0 :=
by simp_rw [dual_annihilator_comap, mem_comap, mem_dual_annihilator, module.dual.eval_apply]

end submodule

namespace subspace

open submodule linear_map

universes u v w

-- We work in vector spaces because `exists_is_compl` only hold for vector spaces
variables {K : Type u} {V : Type v} [field K] [add_comm_group V] [module K V]

/-- Given a subspace `W` of `V` and an element of its dual `φ`, `dual_lift W φ` is
the natural extension of `φ` to an element of the dual of `V`.
That is, `dual_lift W φ` sends `w ∈ W` to `φ x` and `x` in the complement of `W` to `0`. -/
noncomputable def dual_lift (W : subspace K V) :
  module.dual K W →ₗ[K] module.dual K V :=
let h := classical.indefinite_description _ W.exists_is_compl in
  (linear_map.of_is_compl_prod h.2).comp (linear_map.inl _ _ _)

variable {W : subspace K V}

@[simp] lemma dual_lift_of_subtype {φ : module.dual K W} (w : W) :
  W.dual_lift φ (w : V) = φ w :=
by { erw of_is_compl_left_apply _ w, refl }

lemma dual_lift_of_mem {φ : module.dual K W} {w : V} (hw : w ∈ W) :
  W.dual_lift φ w = φ ⟨w, hw⟩ :=
dual_lift_of_subtype ⟨w, hw⟩

@[simp] lemma dual_restrict_comp_dual_lift (W : subspace K V) :
  W.dual_restrict.comp W.dual_lift = 1 :=
by { ext φ x, simp }

lemma dual_restrict_left_inverse (W : subspace K V) :
  function.left_inverse W.dual_restrict W.dual_lift :=
λ x, show W.dual_restrict.comp W.dual_lift x = x,
  by { rw [dual_restrict_comp_dual_lift], refl }

lemma dual_lift_right_inverse (W : subspace K V) :
  function.right_inverse W.dual_lift W.dual_restrict :=
W.dual_restrict_left_inverse

lemma dual_restrict_surjective :
  function.surjective W.dual_restrict :=
W.dual_lift_right_inverse.surjective

lemma dual_lift_injective : function.injective W.dual_lift :=
W.dual_restrict_left_inverse.injective

/-- The quotient by the `dual_annihilator` of a subspace is isomorphic to the
  dual of that subspace. -/
noncomputable def quot_annihilator_equiv (W : subspace K V) :
  W.dual_annihilator.quotient ≃ₗ[K] module.dual K W :=
(quot_equiv_of_eq _ _ W.dual_restrict_ker_eq_dual_annihilator).symm.trans $
  W.dual_restrict.quot_ker_equiv_of_surjective dual_restrict_surjective

/-- The natural isomorphism forom the dual of a subspace `W` to `W.dual_lift.range`. -/
noncomputable def dual_equiv_dual (W : subspace K V) :
  module.dual K W ≃ₗ[K] W.dual_lift.range :=
linear_equiv.of_injective _ $ ker_eq_bot.2 dual_lift_injective

lemma dual_equiv_dual_def (W : subspace K V) :
  W.dual_equiv_dual.to_linear_map = W.dual_lift.range_restrict := rfl

@[simp] lemma dual_equiv_dual_apply (φ : module.dual K W) :
  W.dual_equiv_dual φ = ⟨W.dual_lift φ, mem_range.2 ⟨φ, rfl⟩⟩ := rfl

section

open_locale classical

open finite_dimensional

variables {V₁ : Type*} [add_comm_group V₁] [module K V₁]

instance [H : finite_dimensional K V] : finite_dimensional K (module.dual K V) :=
linear_equiv.finite_dimensional (basis.of_vector_space K V).to_dual_equiv

variables [finite_dimensional K V] [finite_dimensional K V₁]

@[simp] lemma dual_finrank_eq :
  finrank K (module.dual K V) = finrank K V :=
linear_equiv.finrank_eq (basis.of_vector_space K V).to_dual_equiv.symm

/-- The quotient by the dual is isomorphic to its dual annihilator.  -/
noncomputable def quot_dual_equiv_annihilator (W : subspace K V) :
  W.dual_lift.range.quotient ≃ₗ[K] W.dual_annihilator :=
linear_equiv.quot_equiv_of_quot_equiv $
  linear_equiv.trans W.quot_annihilator_equiv W.dual_equiv_dual

/-- The quotient by a subspace is isomorphic to its dual annihilator. -/
noncomputable def quot_equiv_annihilator (W : subspace K V) :
  W.quotient ≃ₗ[K] W.dual_annihilator :=
begin
  refine linear_equiv.trans _ W.quot_dual_equiv_annihilator,
  refine linear_equiv.quot_equiv_of_equiv _ (basis.of_vector_space K V).to_dual_equiv,
  exact (basis.of_vector_space K W).to_dual_equiv.trans W.dual_equiv_dual
end

open finite_dimensional

@[simp]
lemma finrank_dual_annihilator_comap_eq {Φ : subspace K (module.dual K V)} :
  finrank K Φ.dual_annihilator_comap = finrank K Φ.dual_annihilator :=
begin
  rw [submodule.dual_annihilator_comap, ← module.eval_equiv_to_linear_map],
  exact linear_equiv.finrank_eq (linear_equiv.of_submodule' _ _),
end

lemma finrank_add_finrank_dual_annihilator_comap_eq
  (W : subspace K (module.dual K V)) :
  finrank K W + finrank K W.dual_annihilator_comap = finrank K V :=
begin
  rw [finrank_dual_annihilator_comap_eq, W.quot_equiv_annihilator.finrank_eq.symm, add_comm,
      submodule.finrank_quotient_add_finrank, subspace.dual_finrank_eq],
end

end

end subspace

variables {R : Type*} [comm_ring R] {M₁ : Type*} {M₂ : Type*}
variables [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]

open module

/-- Given a linear map `f : M₁ →ₗ[R] M₂`, `f.dual_map` is the linear map between the dual of
`M₂` and `M₁` such that it maps the functional `φ` to `φ ∘ f`. -/
def linear_map.dual_map (f : M₁ →ₗ[R] M₂) : dual R M₂ →ₗ[R] dual R M₁ :=
linear_map.lcomp R R f

@[simp] lemma linear_map.dual_map_apply (f : M₁ →ₗ[R] M₂) (g : dual R M₂) (x : M₁) :
  f.dual_map g x = g (f x) :=
linear_map.lcomp_apply f g x

@[simp] lemma linear_map.dual_map_id :
  (linear_map.id : M₁ →ₗ[R] M₁).dual_map = linear_map.id :=
by { ext, refl }

lemma linear_map.dual_map_comp_dual_map {M₃ : Type*} [add_comm_group M₃] [module R M₃]
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) :
  f.dual_map.comp g.dual_map = (g.comp f).dual_map :=
rfl

/-- The `linear_equiv` version of `linear_map.dual_map`. -/
def linear_equiv.dual_map (f : M₁ ≃ₗ[R] M₂) : dual R M₂ ≃ₗ[R] dual R M₁ :=
{ inv_fun := f.symm.to_linear_map.dual_map,
  left_inv :=
    begin
      intro φ, ext x,
      simp only [linear_map.dual_map_apply, linear_equiv.coe_to_linear_map,
                 linear_map.to_fun_eq_coe, linear_equiv.apply_symm_apply]
    end,
  right_inv :=
    begin
      intro φ, ext x,
      simp only [linear_map.dual_map_apply, linear_equiv.coe_to_linear_map,
                 linear_map.to_fun_eq_coe, linear_equiv.symm_apply_apply]
    end,
  .. f.to_linear_map.dual_map }

@[simp] lemma linear_equiv.dual_map_apply (f : M₁ ≃ₗ[R] M₂) (g : dual R M₂) (x : M₁) :
  f.dual_map g x = g (f x) :=
linear_map.lcomp_apply f g x

@[simp] lemma linear_equiv.dual_map_refl :
  (linear_equiv.refl R M₁).dual_map = linear_equiv.refl R (dual R M₁) :=
by { ext, refl }

@[simp] lemma linear_equiv.dual_map_symm {f : M₁ ≃ₗ[R] M₂} :
  (linear_equiv.dual_map f).symm = linear_equiv.dual_map f.symm := rfl

lemma linear_equiv.dual_map_trans {M₃ : Type*} [add_comm_group M₃] [module R M₃]
  (f : M₁ ≃ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₃) :
  g.dual_map.trans f.dual_map = (f.trans g).dual_map :=
rfl

namespace linear_map

variable (f : M₁ →ₗ[R] M₂)

lemma ker_dual_map_eq_dual_annihilator_range :
  f.dual_map.ker = f.range.dual_annihilator :=
begin
  ext φ, split; intro hφ,
  { rw mem_ker at hφ,
    rw submodule.mem_dual_annihilator,
    rintro y ⟨x, rfl⟩,
    rw [← dual_map_apply, hφ, zero_apply] },
  { ext x,
    rw dual_map_apply,
    rw submodule.mem_dual_annihilator at hφ,
    exact hφ (f x) ⟨x, rfl⟩ }
end

lemma range_dual_map_le_dual_annihilator_ker :
  f.dual_map.range ≤ f.ker.dual_annihilator :=
begin
  rintro _ ⟨ψ, rfl⟩,
  simp_rw [submodule.mem_dual_annihilator, mem_ker],
  rintro x hx,
  rw [dual_map_apply, hx, map_zero]
end

section finite_dimensional

variables {K : Type*} [field K] {V₁ : Type*} {V₂ : Type*}
variables [add_comm_group V₁] [module K V₁] [add_comm_group V₂] [module K V₂]

open finite_dimensional

variable [finite_dimensional K V₂]

@[simp] lemma finrank_range_dual_map_eq_finrank_range (f : V₁ →ₗ[K] V₂) :
  finrank K f.dual_map.range = finrank K f.range :=
begin
  have := submodule.finrank_quotient_add_finrank f.range,
  rw [(subspace.quot_equiv_annihilator f.range).finrank_eq,
      ← ker_dual_map_eq_dual_annihilator_range] at this,
  conv_rhs at this { rw ← subspace.dual_finrank_eq },
  refine add_left_injective (finrank K f.dual_map.ker) _,
  change _ + _ = _ + _,
  rw [finrank_range_add_finrank_ker f.dual_map, add_comm, this],
end

lemma range_dual_map_eq_dual_annihilator_ker [finite_dimensional K V₁] (f : V₁ →ₗ[K] V₂) :
  f.dual_map.range = f.ker.dual_annihilator :=
begin
  refine eq_of_le_of_finrank_eq f.range_dual_map_le_dual_annihilator_ker _,
  have := submodule.finrank_quotient_add_finrank f.ker,
  rw (subspace.quot_equiv_annihilator f.ker).finrank_eq at this,
  refine add_left_injective (finrank K f.ker) _,
  simp_rw [this, finrank_range_dual_map_eq_finrank_range],
  exact finrank_range_add_finrank_ker f,
end

end finite_dimensional

end linear_map
