/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.mean_inequalities
import analysis.normed_space.inner_product

/-!
# `L^p` distance on finite products of metric spaces
Given finitely many metric spaces, one can put the max distance on their product, but there is also
a whole family of natural distances, indexed by a real parameter `p ∈ [1, ∞)`, that also induce
the product topology. We define them in this file. The distance on `Π i, α i` is given by
$$
d(x, y) = \left(\sum d(x_i, y_i)^p\right)^{1/p}.
$$

We give instances of this construction for emetric spaces, metric spaces, normed groups and normed
spaces.

To avoid conflicting instances, all these are defined on a copy of the original Pi type, named
`pi_Lp p hp α`, where `hp : 1 ≤ p`. This assumption is included in the definition of the type
to make sure that it is always available to typeclass inference to construct the instances.

We ensure that the topology and uniform structure on `pi_Lp p hp α` are (defeq to) the product
topology and product uniformity, to be able to use freely continuity statements for the coordinate
functions, for instance.

In the specific case of the `L^2`-norm, we show that we get an inner product space.

We define `euclidean_space 𝕜 n` to be `pi_Lp 2 _ (n → 𝕜)` for any `fintype n`, i.e., the space
from functions to `n` to `𝕜` with the `L^2` norm, and register several instances on it
(notably that it is a finite-dimensional inner product space).


## Implementation notes

We only deal with the `L^p` distance on a product of finitely many metric spaces, which may be
distinct. A closely related construction is the `L^p` norm on the space of
functions from a measure space to a normed space, where the norm is
$$
\left(\int ∥f (x)∥^p dμ\right)^{1/p}.
$$
However, the topology induced by this construction is not the product topology, this only
defines a seminorm (as almost everywhere zero functions have zero `L^p` norm), and some functions
have infinite `L^p` norm. All these subtleties are not present in the case of finitely many
metric spaces (which corresponds to the basis which is a finite space with the counting measure),
hence it is worth devoting a file to this specific case which is particularly well behaved.
The general case is not yet formalized in mathlib.

To prove that the topology (and the uniform structure) on a finite product with the `L^p` distance
are the same as those coming from the `L^∞` distance, we could argue that the `L^p` and `L^∞` norms
are equivalent on `ℝ^n` for abstract (norm equivalence) reasons. Instead, we give a more explicit
(easy) proof which provides a comparison between these two norms with explicit constants.

We also set up the theory for `pseudo_emetric_space` and `pseudo_metric_space`.
-/

open real set filter is_R_or_C
open_locale big_operators uniformity topological_space nnreal ennreal

noncomputable theory

variables {ι : Type*}

/-- A copy of a Pi type, on which we will put the `L^p` distance. Since the Pi type itself is
already endowed with the `L^∞` distance, we need the type synonym to avoid confusing typeclass
resolution. Also, we let it depend on `p`, to get a whole family of type on which we can put
different distances, and we provide the assumption `hp` in the definition, to make it available
to typeclass resolution when it looks for a distance on `pi_Lp p hp α`. -/
@[nolint unused_arguments]
def pi_Lp {ι : Type*} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*) : Type* := Π (i : ι), α i

instance {ι : Type*} (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*) [∀ i, inhabited (α i)] :
  inhabited (pi_Lp p hp α) :=
⟨λ i, default (α i)⟩

namespace pi_Lp

variables (p : ℝ) (hp : 1 ≤ p) (α : ι → Type*) (β : ι → Type*)

/-- Canonical bijection between `pi_Lp p hp α` and the original Pi type. We introduce it to be able
to compare the `L^p` and `L^∞` distances through it. -/
protected def equiv : pi_Lp p hp α ≃ Π (i : ι), α i :=
equiv.refl _

section
/-!
### The uniformity on finite `L^p` products is the product uniformity

In this section, we put the `L^p` edistance on `pi_Lp p hp α`, and we check that the uniformity
coming from this edistance coincides with the product uniformity, by showing that the canonical
map to the Pi type (with the `L^∞` distance) is a uniform embedding, as it is both Lipschitz and
antiLipschitz.

We only register this emetric space structure as a temporary instance, as the true instance (to be
registered later) will have as uniformity exactly the product uniformity, instead of the one coming
from the edistance (which is equal to it, but not defeq). See Note [forgetful inheritance]
explaining why having definitionally the right uniformity is often important.
-/

variables [∀ i, emetric_space (α i)] [∀ i, pseudo_emetric_space (β i)] [fintype ι]

/-- Endowing the space `pi_Lp p hp β` with the `L^p` pseudoedistance. This definition is not
satisfactory, as it does not register the fact that the topology and the uniform structure coincide
with the product one. Therefore, we do not register it as an instance. Using this as a temporary
pseudoemetric space instance, we will show that the uniform structure is equal (but not defeq) to
the product one, and then register an instance in which we replace the uniform structure by the
product one using this pseudoemetric space and `pseudo_emetric_space.replace_uniformity`. -/
def pseudo_emetric_aux : pseudo_emetric_space (pi_Lp p hp β) :=
have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
{ edist          := λ f g, (∑ (i : ι), (edist (f i) (g i)) ^ p) ^ (1/p),
  edist_self     := λ f, by simp [edist, ennreal.zero_rpow_of_pos pos,
                                  ennreal.zero_rpow_of_pos (inv_pos.2 pos)],
  edist_comm     := λ f g, by simp [edist, edist_comm],
  edist_triangle := λ f g h, calc
    (∑ (i : ι), edist (f i) (h i) ^ p) ^ (1 / p) ≤
    (∑ (i : ι), (edist (f i) (g i) + edist (g i) (h i)) ^ p) ^ (1 / p) :
    begin
      apply ennreal.rpow_le_rpow _ (one_div_nonneg.2 $ le_of_lt pos),
      refine finset.sum_le_sum (λ i hi, _),
      exact ennreal.rpow_le_rpow (edist_triangle _ _ _) (le_trans zero_le_one hp)
    end
    ... ≤
    (∑ (i : ι), edist (f i) (g i) ^ p) ^ (1 / p) + (∑ (i : ι), edist (g i) (h i) ^ p) ^ (1 / p) :
      ennreal.Lp_add_le _ _ _ hp }

/-- Endowing the space `pi_Lp p hp α` with the `L^p` edistance. This definition is not satisfactory,
as it does not register the fact that the topology and the uniform structure coincide with the
product one. Therefore, we do not register it as an instance. Using this as a temporary emetric
space instance, we will show that the uniform structure is equal (but not defeq) to the product one,
and then register an instance in which we replace the uniform structure by the product one using
this emetric space and `emetric_space.replace_uniformity`. -/
def emetric_aux : emetric_space (pi_Lp p hp α) :=
{ eq_of_edist_eq_zero := λ f g hfg,
  begin
    have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
    letI h := pseudo_emetric_aux p hp α,
    have h : edist f g = (∑ (i : ι), (edist (f i) (g i)) ^ p) ^ (1/p) := rfl,
    simp [h, ennreal.rpow_eq_zero_iff, pos, asymm pos, finset.sum_eq_zero_iff_of_nonneg] at hfg,
    exact funext hfg
  end,
  ..pseudo_emetric_aux p hp α }

local attribute [instance] pi_Lp.emetric_aux pi_Lp.pseudo_emetric_aux

lemma lipschitz_with_equiv : lipschitz_with 1 (pi_Lp.equiv p hp β) :=
begin
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  have cancel : p * (1/p) = 1 := mul_div_cancel' 1 (ne_of_gt pos),
  assume x y,
  simp only [edist, forall_prop_of_true, one_mul, finset.mem_univ, finset.sup_le_iff,
             ennreal.coe_one],
  assume i,
  calc
  edist (x i) (y i) = (edist (x i) (y i) ^ p) ^ (1/p) :
    by simp [← ennreal.rpow_mul, cancel, -one_div]
  ... ≤ (∑ (i : ι), edist (x i) (y i) ^ p) ^ (1 / p) :
  begin
    apply ennreal.rpow_le_rpow _ (one_div_nonneg.2 $ le_of_lt pos),
    exact finset.single_le_sum (λ i hi, (bot_le : (0 : ℝ≥0∞) ≤ _)) (finset.mem_univ i)
  end
end

lemma antilipschitz_with_equiv :
  antilipschitz_with ((fintype.card ι : ℝ≥0) ^ (1/p)) (pi_Lp.equiv p hp β) :=
begin
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  have nonneg : 0 ≤ 1 / p := one_div_nonneg.2 (le_of_lt pos),
  have cancel : p * (1/p) = 1 := mul_div_cancel' 1 (ne_of_gt pos),
  assume x y,
  simp [edist, -one_div],
  calc (∑ (i : ι), edist (x i) (y i) ^ p) ^ (1 / p) ≤
  (∑ (i : ι), edist (pi_Lp.equiv p hp β x) (pi_Lp.equiv p hp β y) ^ p) ^ (1 / p) :
  begin
    apply ennreal.rpow_le_rpow _ nonneg,
    apply finset.sum_le_sum (λ i hi, _),
    apply ennreal.rpow_le_rpow _ (le_of_lt pos),
    exact finset.le_sup (finset.mem_univ i)
  end
  ... = (((fintype.card ι : ℝ≥0)) ^ (1/p) : ℝ≥0) *
    edist (pi_Lp.equiv p hp β x) (pi_Lp.equiv p hp β y) :
  begin
    simp only [nsmul_eq_mul, finset.card_univ, ennreal.rpow_one, finset.sum_const,
      ennreal.mul_rpow_of_nonneg _ _ nonneg, ←ennreal.rpow_mul, cancel],
    have : (fintype.card ι : ℝ≥0∞) = (fintype.card ι : ℝ≥0) :=
      (ennreal.coe_nat (fintype.card ι)).symm,
    rw [this, ennreal.coe_rpow_of_nonneg _ nonneg]
  end
end

lemma aux_uniformity_eq :
  𝓤 (pi_Lp p hp β) = @uniformity _ (Pi.uniform_space _) :=
begin
  have A : uniform_inducing (pi_Lp.equiv p hp β) :=
    (antilipschitz_with_equiv p hp β).uniform_inducing
    (lipschitz_with_equiv p hp β).uniform_continuous,
  have : (λ (x : pi_Lp p hp β × pi_Lp p hp β),
    ((pi_Lp.equiv p hp β) x.fst, (pi_Lp.equiv p hp β) x.snd)) = id,
    by ext i; refl,
  rw [← A.comap_uniformity, this, comap_id]
end

end

/-! ### Instances on finite `L^p` products -/

instance uniform_space [∀ i, uniform_space (β i)] : uniform_space (pi_Lp p hp β) :=
Pi.uniform_space _

variable [fintype ι]

/-- pseudoemetric space instance on the product of finitely many pseudoemetric spaces, using the
`L^p` pseudoedistance, and having as uniformity the product uniformity. -/
instance [∀ i, pseudo_emetric_space (β i)] : pseudo_emetric_space (pi_Lp p hp β) :=
(pseudo_emetric_aux p hp β).replace_uniformity (aux_uniformity_eq p hp β).symm

/-- emetric space instance on the product of finitely many emetric spaces, using the `L^p`
edistance, and having as uniformity the product uniformity. -/
instance [∀ i, emetric_space (α i)] : emetric_space (pi_Lp p hp α) :=
(emetric_aux p hp α).replace_uniformity (aux_uniformity_eq p hp α).symm

protected lemma edist {p : ℝ} {hp : 1 ≤ p} {β : ι → Type*}
  [∀ i, pseudo_emetric_space (β i)] (x y : pi_Lp p hp β) :
  edist x y = (∑ (i : ι), (edist (x i) (y i)) ^ p) ^ (1/p) := rfl

/-- pseudometric space instance on the product of finitely many psuedometric spaces, using the
`L^p` distance, and having as uniformity the product uniformity. -/
instance [∀ i, pseudo_metric_space (β i)] : pseudo_metric_space (pi_Lp p hp β) :=
begin
  /- we construct the instance from the pseudo emetric space instance to avoid checking again that
  the uniformity is the same as the product uniformity, but we register nevertheless a nice formula
  for the distance -/
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  refine pseudo_emetric_space.to_pseudo_metric_space_of_dist
    (λf g, (∑ (i : ι), (dist (f i) (g i)) ^ p) ^ (1/p)) (λ f g, _) (λ f g, _),
  { simp [pi_Lp.edist, ennreal.rpow_eq_top_iff, asymm pos, pos,
          ennreal.sum_eq_top_iff, edist_ne_top] },
  { have A : ∀ (i : ι), i ∈ (finset.univ : finset ι) → edist (f i) (g i) ^ p < ⊤ :=
      λ i hi, by simp [lt_top_iff_ne_top, edist_ne_top, le_of_lt pos],
    simp [dist, -one_div, pi_Lp.edist, ← ennreal.to_real_rpow,
          ennreal.to_real_sum A, dist_edist] }
end

/-- metric space instance on the product of finitely many metric spaces, using the `L^p` distance,
and having as uniformity the product uniformity. -/
instance [∀ i, metric_space (α i)] : metric_space (pi_Lp p hp α) :=
begin
  /- we construct the instance from the emetric space instance to avoid checking again that the
  uniformity is the same as the product uniformity, but we register nevertheless a nice formula
  for the distance -/
  have pos : 0 < p := lt_of_lt_of_le zero_lt_one hp,
  refine emetric_space.to_metric_space_of_dist
    (λf g, (∑ (i : ι), (dist (f i) (g i)) ^ p) ^ (1/p)) (λ f g, _) (λ f g, _),
  { simp [pi_Lp.edist, ennreal.rpow_eq_top_iff, asymm pos, pos,
          ennreal.sum_eq_top_iff, edist_ne_top] },
  { have A : ∀ (i : ι), i ∈ (finset.univ : finset ι) → edist (f i) (g i) ^ p < ⊤ :=
      λ i hi, by simp [lt_top_iff_ne_top, edist_ne_top, le_of_lt pos],
    simp [dist, -one_div, pi_Lp.edist, ← ennreal.to_real_rpow,
          ennreal.to_real_sum A, dist_edist] }
end

protected lemma dist {p : ℝ} {hp : 1 ≤ p} {β : ι → Type*}
  [∀ i, pseudo_metric_space (β i)] (x y : pi_Lp p hp β) :
  dist x y = (∑ (i : ι), (dist (x i) (y i)) ^ p) ^ (1/p) := rfl

/-- seminormed group instance on the product of finitely many normed groups, using the `L^p`
norm. -/
instance semi_normed_group [∀i, semi_normed_group (β i)] : semi_normed_group (pi_Lp p hp β) :=
{ norm := λf, (∑ (i : ι), norm (f i) ^ p) ^ (1/p),
  dist_eq := λ x y, by { simp [pi_Lp.dist, dist_eq_norm, sub_eq_add_neg] },
  .. pi.add_comm_group }

/-- normed group instance on the product of finitely many normed groups, using the `L^p` norm. -/
instance normed_group [∀i, normed_group (α i)] : normed_group (pi_Lp p hp α) :=
{ ..pi_Lp.semi_normed_group p hp α }

lemma norm_eq {p : ℝ} {hp : 1 ≤ p} {β : ι → Type*}
  [∀i, semi_normed_group (β i)] (f : pi_Lp p hp β) :
  ∥f∥ = (∑ (i : ι), ∥f i∥ ^ p) ^ (1/p) := rfl

lemma norm_eq_of_nat {p : ℝ} {hp : 1 ≤ p} {β : ι → Type*}
  [∀i, semi_normed_group (β i)] (n : ℕ) (h : p = n) (f : pi_Lp p hp β) :
  ∥f∥ = (∑ (i : ι), ∥f i∥ ^ n) ^ (1/(n : ℝ)) :=
by simp [norm_eq, h, real.sqrt_eq_rpow, ←real.rpow_nat_cast]

variables (𝕜 : Type*) [normed_field 𝕜]

/-- The product of finitely many seminormed spaces is a seminormed space, with the `L^p` norm. -/
instance normed_space [∀i, semi_normed_group (β i)] [∀i, normed_space 𝕜 (β i)] :
  normed_space 𝕜 (pi_Lp p hp β) :=
{ norm_smul_le :=
  begin
    assume c f,
    have : p * (1 / p) = 1 := mul_div_cancel' 1 (ne_of_gt (lt_of_lt_of_le zero_lt_one hp)),
    simp only [pi_Lp.norm_eq, norm_smul, mul_rpow, norm_nonneg, ←finset.mul_sum, pi.smul_apply],
    rw [mul_rpow (rpow_nonneg_of_nonneg (norm_nonneg _) _), ← rpow_mul (norm_nonneg _),
        this, rpow_one],
    exact finset.sum_nonneg (λ i hi, rpow_nonneg_of_nonneg (norm_nonneg _) _)
  end,
  .. pi.module ι β 𝕜 }

/-- The product of finitely many normed spaces is a normed space, with the `L^p` norm. -/
instance normed_space [∀i, normed_group (α i)] [∀i, normed_space 𝕜 (α i)] :
  normed_space 𝕜 (pi_Lp p hp α) :=
{ ..pi_Lp.normed_space p hp α 𝕜 }

/- Register simplification lemmas for the applications of `pi_Lp` elements, as the usual lemmas
for Pi types will not trigger. -/
variables {𝕜 p hp α}
[∀i, semi_normed_group (β i)] [∀i, normed_space 𝕜 (β i)] (c : 𝕜) (x y : pi_Lp p hp β) (i : ι)

@[simp] lemma add_apply : (x + y) i = x i + y i := rfl
@[simp] lemma sub_apply : (x - y) i = x i - y i := rfl
@[simp] lemma smul_apply : (c • x) i = c • x i := rfl
@[simp] lemma neg_apply : (-x) i = - (x i) := rfl

end pi_Lp

section

/-! ### Inner product space structure on product spaces -/

variables {𝕜 : Type*} [is_R_or_C 𝕜] {E : Type*} [inner_product_space 𝕜 E]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `pi_Lp 2 one_le_two f` for the product space, which is endowed with the `L^2` norm.
-/
instance pi_Lp.inner_product_space {ι : Type*} [fintype ι] (f : ι → Type*)
  [Π i, inner_product_space 𝕜 (f i)] : inner_product_space 𝕜 (pi_Lp 2 one_le_two f) :=
{ inner := λ x y, ∑ i, inner (x i) (y i),
  norm_sq_eq_inner :=
  begin
    intro x,
    have h₁ : ∑ (i : ι), ∥x i∥ ^ (2 : ℕ) = ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { apply finset.sum_congr rfl,
      intros j hj,
      simp [←rpow_nat_cast] },
    have h₂ : 0 ≤ ∑ (i : ι), ∥x i∥ ^ (2 : ℝ),
    { rw [←h₁],
      exact finset.sum_nonneg (λ j (hj : j ∈ finset.univ), pow_nonneg (norm_nonneg (x j)) 2) },
    simp [norm, add_monoid_hom.map_sum, ←norm_sq_eq_inner],
    rw [←rpow_nat_cast ((∑ (i : ι), ∥x i∥ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) 2],
    rw [←rpow_mul h₂],
    norm_num [h₁],
  end,
  conj_sym :=
  begin
    intros x y,
    unfold inner,
    rw [←finset.sum_hom finset.univ conj],
    apply finset.sum_congr rfl,
    rintros z -,
    apply inner_conj_sym,
    apply_instance
  end,
  add_left := λ x y z,
    show ∑ i, inner (x i + y i) (z i) = ∑ i, inner (x i) (z i) + ∑ i, inner (y i) (z i),
    by simp only [inner_add_left, finset.sum_add_distrib],
  smul_left := λ x y r,
    show ∑ (i : ι), inner (r • x i) (y i) = (conj r) * ∑ i, inner (x i) (y i),
    by simp only [finset.mul_sum, inner_smul_left] }

@[simp] lemma pi_Lp.inner_apply {ι : Type*} [fintype ι] {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x y : pi_Lp 2 one_le_two f) :
  ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
rfl

lemma pi_Lp.norm_eq_of_L2 {ι : Type*} [fintype ι] {f : ι → Type*}
  [Π i, inner_product_space 𝕜 (f i)] (x : pi_Lp 2 one_le_two f) :
  ∥x∥ = sqrt (∑ (i : ι), ∥x i∥ ^ 2) :=
by { rw [pi_Lp.norm_eq_of_nat 2]; simp [sqrt_eq_rpow] }


/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `euclidean_space 𝕜 (fin n)`. -/
@[reducible, nolint unused_arguments]
def euclidean_space (𝕜 : Type*) [is_R_or_C 𝕜]
  (n : Type*) [fintype n] : Type* := pi_Lp 2 one_le_two (λ (i : n), 𝕜)

lemma euclidean_space.norm_eq {𝕜 : Type*} [is_R_or_C 𝕜] {n : Type*} [fintype n]
  (x : euclidean_space 𝕜 n) : ∥x∥ = real.sqrt (∑ (i : n), ∥x i∥ ^ 2) :=
pi_Lp.norm_eq_of_L2 x

section
local attribute [reducible] pi_Lp

variables [fintype ι]

instance : finite_dimensional 𝕜 (euclidean_space 𝕜 ι) := by apply_instance
instance : inner_product_space 𝕜 (euclidean_space 𝕜 ι) := by apply_instance

@[simp] lemma finrank_euclidean_space :
  finite_dimensional.finrank 𝕜 (euclidean_space 𝕜 ι) = fintype.card ι := by simp

lemma finrank_euclidean_space_fin {n : ℕ} :
  finite_dimensional.finrank 𝕜 (euclidean_space 𝕜 (fin n)) = n := by simp

/-- An orthonormal basis on a fintype `ι` for an inner product space induces an isometry with
`euclidean_space 𝕜 ι`. -/
def basis.isometry_euclidean_of_orthonormal
  (v : basis ι 𝕜 E) (hv : orthonormal 𝕜 v) :
  E ≃ₗᵢ[𝕜] (euclidean_space 𝕜 ι) :=
v.equiv_fun.isometry_of_inner
begin
  intros x y,
  let p : euclidean_space 𝕜 ι := v.equiv_fun x,
  let q : euclidean_space 𝕜 ι := v.equiv_fun y,
  have key : ⟪p, q⟫ = ⟪∑ i, p i • v i, ∑ i, q i • v i⟫,
  { simp [sum_inner, inner_smul_left, hv.inner_right_fintype] },
  convert key,
  { rw [← v.equiv_fun.symm_apply_apply x, v.equiv_fun_symm_apply] },
  { rw [← v.equiv_fun.symm_apply_apply y, v.equiv_fun_symm_apply] }
end

end

/-- `ℂ` is isometric to `ℝ²` with the Euclidean inner product. -/
def complex.isometry_euclidean : ℂ ≃ₗᵢ[ℝ] (euclidean_space ℝ (fin 2)) :=
complex.basis_one_I.isometry_euclidean_of_orthonormal
begin
  rw orthonormal_iff_ite,
  intros i, fin_cases i;
  intros j; fin_cases j;
  simp [real_inner_eq_re_inner]
end

@[simp] lemma complex.isometry_euclidean_symm_apply (x : euclidean_space ℝ (fin 2)) :
  complex.isometry_euclidean.symm x = (x 0) + (x 1) * I :=
begin
  convert complex.basis_one_I.equiv_fun_symm_apply x,
  { simpa },
  { simp },
end

lemma complex.isometry_euclidean_proj_eq_self (z : ℂ) :
  ↑(complex.isometry_euclidean z 0) + ↑(complex.isometry_euclidean z 1) * (I : ℂ) = z :=
by rw [← complex.isometry_euclidean_symm_apply (complex.isometry_euclidean z),
  complex.isometry_euclidean.symm_apply_apply z]

@[simp] lemma complex.isometry_euclidean_apply_zero (z : ℂ) :
  complex.isometry_euclidean z 0 = z.re :=
by { conv_rhs { rw ← complex.isometry_euclidean_proj_eq_self z }, simp }

@[simp] lemma complex.isometry_euclidean_apply_one (z : ℂ) :
  complex.isometry_euclidean z 1 = z.im :=
by { conv_rhs { rw ← complex.isometry_euclidean_proj_eq_self z }, simp }

open finite_dimensional

/-- Given a natural number `n` equal to the `finrank` of a finite-dimensional inner product space,
there exists an isometry from the space to `euclidean_space 𝕜 (fin n)`. -/
def linear_isometry_equiv.of_inner_product_space
  [finite_dimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n) :
  E ≃ₗᵢ[𝕜] (euclidean_space 𝕜 (fin n)) :=
(fin_orthonormal_basis hn).isometry_euclidean_of_orthonormal (fin_orthonormal_basis_orthonormal hn)

local attribute [instance] finite_dimensional_of_finrank_eq_succ

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`euclidean_space 𝕜 (fin n)`. -/
def linear_isometry_equiv.from_orthogonal_span_singleton
  (n : ℕ) [fact (finrank 𝕜 E = n + 1)] {v : E} (hv : v ≠ 0) :
  (𝕜 ∙ v)ᗮ ≃ₗᵢ[𝕜] (euclidean_space 𝕜 (fin n)) :=
linear_isometry_equiv.of_inner_product_space (finrank_orthogonal_span_singleton hv)

end
