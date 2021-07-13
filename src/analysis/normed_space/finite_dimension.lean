/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.normed_space.operator_norm
import analysis.normed_space.add_torsor
import topology.bases
import linear_algebra.finite_dimensional

/-!
# Finite dimensional normed spaces over complete fields

Over a complete nondiscrete field, in finite dimension, all norms are equivalent and all linear maps
are continuous. Moreover, a finite-dimensional subspace is always complete and closed.

## Main results:

* `linear_map.continuous_of_finite_dimensional` : a linear map on a finite-dimensional space over a
  complete field is continuous.
* `finite_dimensional.complete` : a finite-dimensional space over a complete field is complete. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution.
* `submodule.closed_of_finite_dimensional` : a finite-dimensional subspace over a complete field is
  closed
* `finite_dimensional.proper` : a finite-dimensional space over a proper field is proper. This
  is not registered as an instance, as the field would be an unknown metavariable in typeclass
  resolution. It is however registered as an instance for `𝕜 = ℝ` and `𝕜 = ℂ`. As properness
  implies completeness, there is no need to also register `finite_dimensional.complete` on `ℝ` or
  `ℂ`.

## Implementation notes

The fact that all norms are equivalent is not written explicitly, as it would mean having two norms
on a single space, which is not the way type classes work. However, if one has a
finite-dimensional vector space `E` with a norm, and a copy `E'` of this type with another norm,
then the identities from `E` to `E'` and from `E'`to `E` are continuous thanks to
`linear_map.continuous_of_finite_dimensional`. This gives the desired norm equivalence.
-/

universes u v w x

open set finite_dimensional topological_space filter
open_locale classical big_operators filter topological_space

noncomputable theory

/-- A linear map on `ι → 𝕜` (where `ι` is a fintype) is continuous -/
lemma linear_map.continuous_on_pi {ι : Type w} [fintype ι] {𝕜 : Type u} [normed_field 𝕜]
  {E : Type v}  [add_comm_group E] [module 𝕜 E] [topological_space E]
  [topological_add_group E] [has_continuous_smul 𝕜 E] (f : (ι → 𝕜) →ₗ[𝕜] E) : continuous f :=
begin
  -- for the proof, write `f` in the standard basis, and use that each coordinate is a continuous
  -- function.
  have : (f : (ι → 𝕜) → E) =
         (λx, ∑ i : ι, x i • (f (λj, if i = j then 1 else 0))),
    by { ext x, exact f.pi_apply_eq_sum_univ x },
  rw this,
  refine continuous_finset_sum _ (λi hi, _),
  exact (continuous_apply i).smul continuous_const
end

section complete_field

variables {𝕜 : Type u} [nondiscrete_normed_field 𝕜]
{E : Type v} [normed_group E] [normed_space 𝕜 E]
{F : Type w} [normed_group F] [normed_space 𝕜 F]
{F' : Type x} [add_comm_group F'] [module 𝕜 F'] [topological_space F']
[topological_add_group F'] [has_continuous_smul 𝕜 F']
[complete_space 𝕜]

/-- In finite dimension over a complete field, the canonical identification (in terms of a basis)
with `𝕜^n` together with its sup norm is continuous. This is the nontrivial part in the fact that
all norms are equivalent in finite dimension.

This statement is superceded by the fact that every linear map on a finite-dimensional space is
continuous, in `linear_map.continuous_of_finite_dimensional`. -/
lemma continuous_equiv_fun_basis {ι : Type v} [fintype ι] (ξ : basis ι 𝕜 E) :
  continuous ξ.equiv_fun :=
begin
  unfreezingI { induction hn : fintype.card ι with n IH generalizing ι E },
  { apply linear_map.continuous_of_bound _ 0 (λx, _),
    have : ξ.equiv_fun x = 0,
      by { ext i, exact (fintype.card_eq_zero_iff.1 hn).elim i },
    change ∥ξ.equiv_fun x∥ ≤ 0 * ∥x∥,
    rw this,
    simp [norm_nonneg] },
  { haveI : finite_dimensional 𝕜 E := of_fintype_basis ξ,
    -- first step: thanks to the inductive assumption, any n-dimensional subspace is equivalent
    -- to a standard space of dimension n, hence it is complete and therefore closed.
    have H₁ : ∀s : submodule 𝕜 E, finrank 𝕜 s = n → is_closed (s : set E),
    { assume s s_dim,
      let b := basis.of_vector_space 𝕜 s,
      have U : uniform_embedding b.equiv_fun.symm.to_equiv,
      { have : fintype.card (basis.of_vector_space_index 𝕜 s) = n,
          by { rw ← s_dim, exact (finrank_eq_card_basis b).symm },
        have : continuous b.equiv_fun := IH b this,
        exact b.equiv_fun.symm.uniform_embedding (linear_map.continuous_on_pi _) this },
      have : is_complete (s : set E),
        from complete_space_coe_iff_is_complete.1 ((complete_space_congr U).1 (by apply_instance)),
      exact this.is_closed },
    -- second step: any linear form is continuous, as its kernel is closed by the first step
    have H₂ : ∀f : E →ₗ[𝕜] 𝕜, continuous f,
    { assume f,
      have : finrank 𝕜 f.ker = n ∨ finrank 𝕜 f.ker = n.succ,
      { have Z := f.finrank_range_add_finrank_ker,
        rw [finrank_eq_card_basis ξ, hn] at Z,
        by_cases H : finrank 𝕜 f.range = 0,
        { right,
          rw H at Z,
          simpa using Z },
        { left,
          have : finrank 𝕜 f.range = 1,
          { refine le_antisymm _ (zero_lt_iff.mpr H),
            simpa [finrank_of_field] using f.range.finrank_le },
          rw [this, add_comm, nat.add_one] at Z,
          exact nat.succ.inj Z } },
      have : is_closed (f.ker : set E),
      { cases this,
        { exact H₁ _ this },
        { have : f.ker = ⊤,
            by { apply eq_top_of_finrank_eq, rw [finrank_eq_card_basis ξ, hn, this] },
          simp [this] } },
      exact linear_map.continuous_iff_is_closed_ker.2 this },
    -- third step: applying the continuity to the linear form corresponding to a coefficient in the
    -- basis decomposition, deduce that all such coefficients are controlled in terms of the norm
    have : ∀i:ι, ∃C, 0 ≤ C ∧ ∀(x:E), ∥ξ.equiv_fun x i∥ ≤ C * ∥x∥,
    { assume i,
      let f : E →ₗ[𝕜] 𝕜 := (linear_map.proj i).comp ξ.equiv_fun,
      let f' : E →L[𝕜] 𝕜 := { cont := H₂ f, ..f },
      exact ⟨∥f'∥, norm_nonneg _, λx, continuous_linear_map.le_op_norm f' x⟩ },
    -- fourth step: combine the bound on each coefficient to get a global bound and the continuity
    choose C0 hC0 using this,
    let C := ∑ i, C0 i,
    have C_nonneg : 0 ≤ C := finset.sum_nonneg (λi hi, (hC0 i).1),
    have C0_le : ∀i, C0 i ≤ C :=
      λi, finset.single_le_sum (λj hj, (hC0 j).1) (finset.mem_univ _),
    apply linear_map.continuous_of_bound _ C (λx, _),
    rw pi_semi_norm_le_iff,
    { exact λi, le_trans ((hC0 i).2 x) (mul_le_mul_of_nonneg_right (C0_le i) (norm_nonneg _)) },
    { exact mul_nonneg C_nonneg (norm_nonneg _) } }
end

/-- Any linear map on a finite dimensional space over a complete field is continuous. -/
theorem linear_map.continuous_of_finite_dimensional [finite_dimensional 𝕜 E] (f : E →ₗ[𝕜] F') :
  continuous f :=
begin
  -- for the proof, go to a model vector space `b → 𝕜` thanks to `continuous_equiv_fun_basis`, and
  -- argue that all linear maps there are continuous.
  let b := basis.of_vector_space 𝕜 E,
  have A : continuous b.equiv_fun :=
    continuous_equiv_fun_basis b,
  have B : continuous (f.comp (b.equiv_fun.symm : (basis.of_vector_space_index 𝕜 E → 𝕜) →ₗ[𝕜] E)) :=
    linear_map.continuous_on_pi _,
  have : continuous ((f.comp (b.equiv_fun.symm : (basis.of_vector_space_index 𝕜 E → 𝕜) →ₗ[𝕜] E))
                      ∘ b.equiv_fun) := B.comp A,
  convert this,
  ext x,
  dsimp,
  rw [basis.equiv_fun_symm_apply, basis.sum_repr]
end

theorem affine_map.continuous_of_finite_dimensional {PE PF : Type*}
  [metric_space PE] [normed_add_torsor E PE] [metric_space PF] [normed_add_torsor F PF]
  [finite_dimensional 𝕜 E] (f : PE →ᵃ[𝕜] PF) : continuous f :=
affine_map.continuous_linear_iff.1 f.linear.continuous_of_finite_dimensional

namespace linear_map

variables [finite_dimensional 𝕜 E]

/-- The continuous linear map induced by a linear map on a finite dimensional space -/
def to_continuous_linear_map : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F' :=
{ to_fun := λ f, ⟨f, f.continuous_of_finite_dimensional⟩,
  inv_fun := coe,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl,
  left_inv := λ f, rfl,
  right_inv := λ f, continuous_linear_map.coe_injective rfl }

@[simp] lemma coe_to_continuous_linear_map' (f : E →ₗ[𝕜] F') :
  ⇑f.to_continuous_linear_map = f := rfl

@[simp] lemma coe_to_continuous_linear_map (f : E →ₗ[𝕜] F') :
  (f.to_continuous_linear_map : E →ₗ[𝕜] F') = f := rfl

@[simp] lemma coe_to_continuous_linear_map_symm :
  ⇑(to_continuous_linear_map : (E →ₗ[𝕜] F') ≃ₗ[𝕜] E →L[𝕜] F').symm = coe := rfl

end linear_map

/-- The continuous linear equivalence induced by a linear equivalence on a finite dimensional
space. -/
def linear_equiv.to_continuous_linear_equiv [finite_dimensional 𝕜 E] (e : E ≃ₗ[𝕜] F) : E ≃L[𝕜] F :=
{ continuous_to_fun := e.to_linear_map.continuous_of_finite_dimensional,
  continuous_inv_fun := begin
    haveI : finite_dimensional 𝕜 F := e.finite_dimensional,
    exact e.symm.to_linear_map.continuous_of_finite_dimensional
  end,
  ..e }

lemma linear_map.exists_antilipschitz_with [finite_dimensional 𝕜 E] (f : E →ₗ[𝕜] F)
  (hf : f.ker = ⊥) : ∃ K > 0, antilipschitz_with K f :=
begin
  cases subsingleton_or_nontrivial E; resetI,
  { exact ⟨1, zero_lt_one, antilipschitz_with.of_subsingleton⟩ },
  { let e : E ≃L[𝕜] f.range := (linear_equiv.of_injective f hf).to_continuous_linear_equiv,
    exact ⟨_, e.nnnorm_symm_pos, e.antilipschitz⟩ }
end

protected lemma linear_independent.eventually {ι} [fintype ι] {f : ι → E}
  (hf : linear_independent 𝕜 f) : ∀ᶠ g in 𝓝 f, linear_independent 𝕜 g :=
begin
  simp only [fintype.linear_independent_iff'] at hf ⊢,
  rcases linear_map.exists_antilipschitz_with _ hf with ⟨K, K0, hK⟩,
  have : tendsto (λ g : ι → E, ∑ i, ∥g i - f i∥) (𝓝 f) (𝓝 $ ∑ i, ∥f i - f i∥),
    from tendsto_finset_sum _ (λ i hi, tendsto.norm $
      ((continuous_apply i).tendsto _).sub tendsto_const_nhds),
  simp only [sub_self, norm_zero, finset.sum_const_zero] at this,
  refine (this.eventually (gt_mem_nhds $ inv_pos.2 K0)).mono (λ g hg, _),
  replace hg : ∑ i, nnnorm (g i - f i) < K⁻¹, by { rw ← nnreal.coe_lt_coe, push_cast, exact hg },
  rw linear_map.ker_eq_bot,
  refine (hK.add_sub_lipschitz_with (lipschitz_with.of_dist_le_mul $ λ v u, _) hg).injective,
  simp only [dist_eq_norm, linear_map.lsum_apply, pi.sub_apply, linear_map.sum_apply,
    linear_map.comp_apply, linear_map.proj_apply, linear_map.smul_right_apply, linear_map.id_apply,
    ← finset.sum_sub_distrib, ← smul_sub, ← sub_smul, nnreal.coe_sum, coe_nnnorm, finset.sum_mul],
  refine norm_sum_le_of_le _ (λ i _, _),
  rw [norm_smul, mul_comm],
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (v - u) i) (norm_nonneg _)
end

lemma is_open_set_of_linear_independent {ι : Type*} [fintype ι] :
  is_open {f : ι → E | linear_independent 𝕜 f} :=
is_open_iff_mem_nhds.2 $ λ f, linear_independent.eventually

lemma is_open_set_of_nat_le_rank (n : ℕ) : is_open {f : E →L[𝕜] F | ↑n ≤ rank (f : E →ₗ[𝕜] F)} :=
begin
  simp only [le_rank_iff_exists_linear_independent_finset, set_of_exists, ← exists_prop],
  refine is_open_bUnion (λ t ht, _),
  have : continuous (λ f : E →L[𝕜] F, (λ x : (t : set E), f x)),
    from continuous_pi (λ x, (continuous_linear_map.apply 𝕜 F (x : E)).continuous),
  exact is_open_set_of_linear_independent.preimage this
end

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if they have the same
(finite) dimension. -/
theorem finite_dimensional.nonempty_continuous_linear_equiv_of_finrank_eq
  [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] (cond : finrank 𝕜 E = finrank 𝕜 F) :
  nonempty (E ≃L[𝕜] F) :=
(nonempty_linear_equiv_of_finrank_eq cond).map linear_equiv.to_continuous_linear_equiv

/-- Two finite-dimensional normed spaces are continuously linearly equivalent if and only if they
have the same (finite) dimension. -/
theorem finite_dimensional.nonempty_continuous_linear_equiv_iff_finrank_eq
  [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F] :
   nonempty (E ≃L[𝕜] F) ↔ finrank 𝕜 E = finrank 𝕜 F :=
⟨ λ ⟨h⟩, h.to_linear_equiv.finrank_eq,
  λ h, finite_dimensional.nonempty_continuous_linear_equiv_of_finrank_eq h ⟩

/-- A continuous linear equivalence between two finite-dimensional normed spaces of the same
(finite) dimension. -/
def continuous_linear_equiv.of_finrank_eq [finite_dimensional 𝕜 E] [finite_dimensional 𝕜 F]
  (cond : finrank 𝕜 E = finrank 𝕜 F) :
  E ≃L[𝕜] F :=
(linear_equiv.of_finrank_eq E F cond).to_continuous_linear_equiv

variables {ι : Type*} [fintype ι]

/-- Construct a continuous linear map given the value at a finite basis. -/
def basis.constrL (v : basis ι 𝕜 E) (f : ι → F) :
  E →L[𝕜] F :=
by haveI : finite_dimensional 𝕜 E := finite_dimensional.of_fintype_basis v;
  exact (v.constr 𝕜 f).to_continuous_linear_map

@[simp, norm_cast] lemma basis.coe_constrL (v : basis ι 𝕜 E) (f : ι → F) :
  (v.constrL f : E →ₗ[𝕜] F) = v.constr 𝕜 f := rfl

/-- The continuous linear equivalence between a vector space over `𝕜` with a finite basis and
functions from its basis indexing type to `𝕜`. -/
def basis.equiv_funL (v : basis ι 𝕜 E) : E ≃L[𝕜] (ι → 𝕜) :=
{ continuous_to_fun := begin
    haveI : finite_dimensional 𝕜 E := finite_dimensional.of_fintype_basis v,
    apply linear_map.continuous_of_finite_dimensional,
  end,
  continuous_inv_fun := begin
    change continuous v.equiv_fun.symm.to_fun,
    apply linear_map.continuous_of_finite_dimensional,
  end,
  ..v.equiv_fun }


@[simp] lemma basis.constrL_apply (v : basis ι 𝕜 E) (f : ι → F) (e : E) :
  (v.constrL f) e = ∑ i, (v.equiv_fun e i) • f i :=
v.constr_apply_fintype 𝕜 _ _

@[simp] lemma basis.constrL_basis (v : basis ι 𝕜 E) (f : ι → F) (i : ι) :
  (v.constrL f) (v i) = f i :=
v.constr_basis 𝕜 _ _

lemma basis.sup_norm_le_norm (v : basis ι 𝕜 E) :
  ∃ C > (0 : ℝ), ∀ e : E, ∑ i, ∥v.equiv_fun e i∥ ≤ C * ∥e∥ :=
begin
  set φ := v.equiv_funL.to_continuous_linear_map,
  set C := ∥φ∥ * (fintype.card ι),
  use [max C 1, lt_of_lt_of_le (zero_lt_one) (le_max_right C 1)],
  intros e,
  calc ∑ i, ∥φ e i∥ ≤ ∑ i : ι, ∥φ e∥ : by { apply finset.sum_le_sum,
                                           exact λ i hi, norm_le_pi_norm (φ e) i }
  ... = ∥φ e∥*(fintype.card ι) : by simpa only [mul_comm, finset.sum_const, nsmul_eq_mul]
  ... ≤ ∥φ∥ * ∥e∥ * (fintype.card ι) : mul_le_mul_of_nonneg_right (φ.le_op_norm e)
                                                                 (fintype.card ι).cast_nonneg
  ... = ∥φ∥ * (fintype.card ι) * ∥e∥ : by ring
  ... ≤ max C 1 * ∥e∥ :  mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
end

lemma basis.op_norm_le  {ι : Type*} [fintype ι] (v : basis ι 𝕜 E) :
  ∃ C > (0 : ℝ), ∀ {u : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ∥u (v i)∥ ≤ M) → ∥u∥ ≤ C*M :=
begin
  obtain ⟨C, C_pos, hC⟩ : ∃ C > (0 : ℝ), ∀ (e : E), ∑ i, ∥v.equiv_fun e i∥ ≤ C * ∥e∥,
    from v.sup_norm_le_norm,
  use [C, C_pos],
  intros u M hM hu,
  apply u.op_norm_le_bound (mul_nonneg (le_of_lt C_pos) hM),
  intros e,
  calc
  ∥u e∥ = ∥u (∑ i, v.equiv_fun e i • v i)∥ :   by rw [v.sum_equiv_fun]
  ... = ∥∑ i, (v.equiv_fun e i) • (u $ v i)∥ : by simp [u.map_sum, linear_map.map_smul]
  ... ≤ ∑ i, ∥(v.equiv_fun e i) • (u $ v i)∥ : norm_sum_le _ _
  ... = ∑ i, ∥v.equiv_fun e i∥ * ∥u (v i)∥ :   by simp only [norm_smul]
  ... ≤ ∑ i, ∥v.equiv_fun e i∥ * M : finset.sum_le_sum (λ i hi,
                                                  mul_le_mul_of_nonneg_left (hu i) (norm_nonneg _))
  ... = (∑ i, ∥v.equiv_fun e i∥) * M : finset.sum_mul.symm
  ... ≤ C * ∥e∥ * M : mul_le_mul_of_nonneg_right (hC e) hM
  ... = C * M * ∥e∥ : by ring
end

instance [finite_dimensional 𝕜 E] [second_countable_topology F] :
  second_countable_topology (E →L[𝕜] F) :=
begin
  set d := finite_dimensional.finrank 𝕜 E,
  suffices :
    ∀ ε > (0 : ℝ), ∃ n : (E →L[𝕜] F) → fin d → ℕ, ∀ (f g : E →L[𝕜] F), n f = n g → dist f g ≤ ε,
  from metric.second_countable_of_countable_discretization
    (λ ε ε_pos, ⟨fin d → ℕ, by apply_instance, this ε ε_pos⟩),
  intros ε ε_pos,
  obtain ⟨u : ℕ → F, hu : dense_range u⟩ := exists_dense_seq F,
  let v := finite_dimensional.fin_basis 𝕜 E,
  obtain ⟨C : ℝ, C_pos : 0 < C,
          hC : ∀ {φ : E →L[𝕜] F} {M : ℝ}, 0 ≤ M → (∀ i, ∥φ (v i)∥ ≤ M) → ∥φ∥ ≤ C * M⟩ :=
    v.op_norm_le,
  have h_2C : 0 < 2*C := mul_pos zero_lt_two C_pos,
  have hε2C : 0 < ε/(2*C) := div_pos ε_pos h_2C,
  have : ∀ φ : E →L[𝕜] F, ∃ n : fin d → ℕ, ∥φ - (v.constrL $ u ∘ n)∥ ≤ ε/2,
  { intros φ,
    have : ∀ i, ∃ n, ∥φ (v i) - u n∥ ≤ ε/(2*C),
    { simp only [norm_sub_rev],
      intro i,
      have : φ (v i) ∈ closure (range u) := hu _,
      obtain ⟨n, hn⟩ : ∃ n, ∥u n - φ (v i)∥ < ε / (2 * C),
      { rw mem_closure_iff_nhds_basis metric.nhds_basis_ball at this,
        specialize this (ε/(2*C)) hε2C,
        simpa [dist_eq_norm] },
      exact ⟨n, le_of_lt hn⟩ },
    choose n hn using this,
    use n,
    replace hn : ∀ i : fin d, ∥(φ - (v.constrL $ u ∘ n)) (v i)∥ ≤ ε / (2 * C), by simp [hn],
    have : C * (ε / (2 * C)) = ε/2,
    { rw [eq_div_iff (two_ne_zero : (2 : ℝ) ≠ 0), mul_comm, ← mul_assoc,
          mul_div_cancel' _ (ne_of_gt h_2C)] },
    specialize hC (le_of_lt hε2C) hn,
    rwa this at hC },
  choose n hn using this,
  set Φ := λ φ : E →L[𝕜] F, (v.constrL $ u ∘ (n φ)),
  change ∀ z, dist z (Φ z) ≤ ε/2 at hn,
  use n,
  intros x y hxy,
  calc dist x y ≤ dist x (Φ x) + dist (Φ x) y : dist_triangle _ _ _
  ... = dist x (Φ x) + dist y (Φ y) : by simp [Φ, hxy, dist_comm]
  ... ≤ ε : by linarith [hn x, hn y]
end

/-- Any finite-dimensional vector space over a complete field is complete.
We do not register this as an instance to avoid an instance loop when trying to prove the
completeness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
variables (𝕜 E)
lemma finite_dimensional.complete [finite_dimensional 𝕜 E] : complete_space E :=
begin
  set e := continuous_linear_equiv.of_finrank_eq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm,
  have : uniform_embedding e.to_linear_equiv.to_equiv.symm := e.symm.uniform_embedding,
  exact (complete_space_congr this).1 (by apply_instance)
end

variables {𝕜 E}
/-- A finite-dimensional subspace is complete. -/
lemma submodule.complete_of_finite_dimensional (s : submodule 𝕜 E) [finite_dimensional 𝕜 s] :
  is_complete (s : set E) :=
complete_space_coe_iff_is_complete.1 (finite_dimensional.complete 𝕜 s)

/-- A finite-dimensional subspace is closed. -/
lemma submodule.closed_of_finite_dimensional (s : submodule 𝕜 E) [finite_dimensional 𝕜 s] :
  is_closed (s : set E) :=
s.complete_of_finite_dimensional.is_closed

lemma continuous_linear_map.exists_right_inverse_of_surjective [finite_dimensional 𝕜 F]
  (f : E →L[𝕜] F) (hf : f.range = ⊤) :
  ∃ g : F →L[𝕜] E, f.comp g = continuous_linear_map.id 𝕜 F :=
let ⟨g, hg⟩ := (f : E →ₗ[𝕜] F).exists_right_inverse_of_surjective hf in
⟨g.to_continuous_linear_map, continuous_linear_map.ext $ linear_map.ext_iff.1 hg⟩

lemma closed_embedding_smul_left {c : E} (hc : c ≠ 0) : closed_embedding (λ x : 𝕜, x • c) :=
begin
  haveI : finite_dimensional 𝕜 (𝕜 ∙ c) :=
    finite_dimensional.span_of_finite 𝕜 (finite_singleton c),
  have m1 : closed_embedding (coe : (𝕜 ∙ c) → E) :=
  (𝕜 ∙ c).closed_of_finite_dimensional.closed_embedding_subtype_coe,
  have m2 : closed_embedding
    (linear_equiv.to_span_nonzero_singleton 𝕜 E c hc : 𝕜 → 𝕜 ∙ c) :=
  (continuous_linear_equiv.to_span_nonzero_singleton 𝕜 c hc).to_homeomorph.closed_embedding,
  exact m1.comp m2
end

/- `smul` is a closed map in the first argument. -/
lemma is_closed_map_smul_left (c : E) : is_closed_map (λ x : 𝕜, x • c) :=
begin
  by_cases hc : c = 0,
  { simp_rw [hc, smul_zero], exact is_closed_map_const },
  { exact (closed_embedding_smul_left hc).is_closed_map }
end

end complete_field

section proper_field
variables (𝕜 : Type u) [nondiscrete_normed_field 𝕜]
(E : Type v) [normed_group E] [normed_space 𝕜 E] [proper_space 𝕜]

/-- Any finite-dimensional vector space over a proper field is proper.
We do not register this as an instance to avoid an instance loop when trying to prove the
properness of `𝕜`, and the search for `𝕜` as an unknown metavariable. Declare the instance
explicitly when needed. -/
lemma finite_dimensional.proper [finite_dimensional 𝕜 E] : proper_space E :=
begin
  set e := continuous_linear_equiv.of_finrank_eq (@finrank_fin_fun 𝕜 _ (finrank 𝕜 E)).symm,
  exact e.symm.antilipschitz.proper_space e.symm.continuous e.symm.surjective
end

end proper_field

/- Over the real numbers, we can register the previous statement as an instance as it will not
cause problems in instance resolution since the properness of `ℝ` is already known. -/
instance finite_dimensional.proper_real
  (E : Type u) [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E] : proper_space E :=
finite_dimensional.proper ℝ E

attribute [instance, priority 900] finite_dimensional.proper_real

/-- In a finite dimensional vector space over `ℝ`, the series `∑ x, ∥f x∥` is unconditionally
summable if and only if the series `∑ x, f x` is unconditionally summable. One implication holds in
any complete normed space, while the other holds only in finite dimensional spaces. -/
lemma summable_norm_iff {α E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  {f : α → E} : summable (λ x, ∥f x∥) ↔ summable f :=
begin
  refine ⟨summable_of_summable_norm, λ hf, _⟩,
  -- First we use a finite basis to reduce the problem to the case `E = fin N → ℝ`
  suffices : ∀ {N : ℕ} {g : α → fin N → ℝ}, summable g → summable (λ x, ∥g x∥),
  { obtain v := fin_basis ℝ E,
    set e := v.equiv_funL,
    have : summable (λ x, ∥e (f x)∥) := this (e.summable.2 hf),
    refine summable_of_norm_bounded _ (this.mul_left
      ↑(nnnorm (e.symm : (fin (finrank ℝ E) → ℝ) →L[ℝ] E))) (λ i, _),
    simpa using (e.symm : (fin (finrank ℝ E) → ℝ) →L[ℝ] E).le_op_norm (e $ f i) },
  unfreezingI { clear_dependent E },
  -- Now we deal with `g : α → fin N → ℝ`
  intros N g hg,
  have : ∀ i, summable (λ x, ∥g x i∥) := λ i, (pi.summable.1 hg i).abs,
  refine summable_of_norm_bounded _ (summable_sum (λ i (hi : i ∈ finset.univ), this i)) (λ x, _),
  rw [norm_norm, pi_norm_le_iff],
  { refine λ i, finset.single_le_sum (λ i hi, _) (finset.mem_univ i),
    exact norm_nonneg (g x i) },
  { exact finset.sum_nonneg (λ _ _, norm_nonneg _) }
end
