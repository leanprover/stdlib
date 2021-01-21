/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
import measure_theory.simple_func_dense
import topology.sequences

/-!
# Bochner integral

The Bochner integral extends the definition of the Lebesgue integral to functions that map from a
measure space into a Banach space (complete normed vector space). It is constructed here by
extending the integral on simple functions.

## Main definitions

The Bochner integral is defined following these steps:

1. Define the integral on simple functions of the type `simple_func α E` (notation : `α →ₛ E`)
  where `E` is a real normed space.

  (See `simple_func.bintegral` and section `bintegral` for details. Also see `simple_func.integral`
  for the integral on simple functions of the type `simple_func α ennreal`.)

2. Use `α →ₛ E` to cut out the simple functions from L1 functions, and define integral
  on these. The type of simple functions in L1 space is written as `α →₁ₛ[μ] E`.

3. Show that the embedding of `α →₁ₛ[μ] E` into L1 is a dense and uniform one.

4. Show that the integral defined on `α →₁ₛ[μ] E` is a continuous linear map.

5. Define the Bochner integral on L1 functions by extending the integral on integrable simple
  functions `α →₁ₛ[μ] E` using `continuous_linear_map.extend`. Define the Bochner integral on
  functions as the Bochner integral of its equivalence class in L1 space.

## Main statements

1. Basic properties of the Bochner integral on functions of type `α → E`, where `α` is a measure
   space and `E` is a real normed space.

  * `integral_zero`                  : `∫ 0 ∂μ = 0`
  * `integral_add`                   : `∫ x, f x + g x ∂μ = ∫ x, f ∂μ + ∫ x, g x ∂μ`
  * `integral_neg`                   : `∫ x, - f x ∂μ = - ∫ x, f x ∂μ`
  * `integral_sub`                   : `∫ x, f x - g x ∂μ = ∫ x, f x ∂μ - ∫ x, g x ∂μ`
  * `integral_smul`                  : `∫ x, r • f x ∂μ = r • ∫ x, f x ∂μ`
  * `integral_congr_ae`              : `f =ᵐ[μ] g → ∫ x, f x ∂μ = ∫ x, g x ∂μ`
  * `norm_integral_le_integral_norm` : `∥∫ x, f x ∂μ∥ ≤ ∫ x, ∥f x∥ ∂μ`

2. Basic properties of the Bochner integral on functions of type `α → ℝ`, where `α` is a measure
  space.

  * `integral_nonneg_of_ae` : `0 ≤ᵐ[μ] f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos_of_ae` : `f ≤ᵐ[μ] 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono_ae`      : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`
  * `integral_nonneg`       : `0 ≤ f → 0 ≤ ∫ x, f x ∂μ`
  * `integral_nonpos`       : `f ≤ 0 → ∫ x, f x ∂μ ≤ 0`
  * `integral_mono`         : `f ≤ᵐ[μ] g → ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ`

3. Propositions connecting the Bochner integral with the integral on `ennreal`-valued functions,
   which is called `lintegral` and has the notation `∫⁻`.

  * `integral_eq_lintegral_max_sub_lintegral_min` : `∫ x, f x ∂μ = ∫⁻ x, f⁺ x ∂μ - ∫⁻ x, f⁻ x ∂μ`,
    where `f⁺` is the positive part of `f` and `f⁻` is the negative part of `f`.
  * `integral_eq_lintegral_of_nonneg_ae`          : `0 ≤ᵐ[μ] f → ∫ x, f x ∂μ = ∫⁻ x, f x ∂μ`

4. `tendsto_integral_of_dominated_convergence` : the Lebesgue dominated convergence theorem

## Notes

Some tips on how to prove a proposition if the API for the Bochner integral is not enough so that
you need to unfold the definition of the Bochner integral and go back to simple functions.

One method is to use the theorem `integrable.induction` in the file `set_integral`, which allows
you to prove something for an arbitrary measurable + integrable function.

Another method is using the following steps.
See `integral_eq_lintegral_max_sub_lintegral_min` for a complicated example, which proves that
`∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, with the first integral sign being the Bochner integral of a real-valued
function `f : α → ℝ`, and second and third integral sign being the integral on ennreal-valued
functions (called `lintegral`). The proof of `integral_eq_lintegral_max_sub_lintegral_min` is
scattered in sections with the name `pos_part`.

Here are the usual steps of proving that a property `p`, say `∫ f = ∫⁻ f⁺ - ∫⁻ f⁻`, holds for all
functions :

1. First go to the `L¹` space.

   For example, if you see `ennreal.to_real (∫⁻ a, ennreal.of_real $ ∥f a∥)`, that is the norm of
   `f` in `L¹` space. Rewrite using `l1.norm_of_fun_eq_lintegral_norm`.

2. Show that the set `{f ∈ L¹ | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}` is closed in `L¹` using `is_closed_eq`.

3. Show that the property holds for all simple functions `s` in `L¹` space.

   Typically, you need to convert various notions to their `simple_func` counterpart, using lemmas
   like `l1.integral_coe_eq_integral`.

4. Since simple functions are dense in `L¹`,
```
univ = closure {s simple}
     = closure {s simple | ∫ s = ∫⁻ s⁺ - ∫⁻ s⁻} : the property holds for all simple functions
     ⊆ closure {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻}
     = {f | ∫ f = ∫⁻ f⁺ - ∫⁻ f⁻} : closure of a closed set is itself
```
Use `is_closed_property` or `dense_range.induction_on` for this argument.

## Notations

* `α →ₛ E`  : simple functions (defined in `measure_theory/integration`)
* `α →₁[μ] E` : functions in L1 space, i.e., equivalence classes of integrable functions (defined in
                `measure_theory/l1_space`)
* `α →₁ₛ[μ] E` : simple functions in L1 space, i.e., equivalence classes of integrable simple
                 functions

Note : `ₛ` is typed using `\_s`. Sometimes it shows as a box if font is missing.

## Tags

Bochner integral, simple function, function space, Lebesgue dominated convergence theorem

-/

noncomputable theory
open_locale classical topological_space big_operators nnreal

namespace measure_theory

variables {α E : Type*} [measurable_space α] [linear_order E] [has_zero E]

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section pos_part

/-- Positive part of a simple function. -/
def pos_part (f : α →ₛ E) : α →ₛ E := f.map (λb, max b 0)

/-- Negative part of a simple function. -/
def neg_part [has_neg E] (f : α →ₛ E) : α →ₛ E := pos_part (-f)

lemma pos_part_map_norm (f : α →ₛ ℝ) : (pos_part f).map norm = pos_part f :=
begin
  ext,
  rw [map_apply, real.norm_eq_abs, abs_of_nonneg],
  rw [pos_part, map_apply],
  exact le_max_right _ _
end

lemma neg_part_map_norm (f : α →ₛ ℝ) : (neg_part f).map norm = neg_part f :=
by { rw neg_part, exact pos_part_map_norm _ }

lemma pos_part_sub_neg_part (f : α →ₛ ℝ) : f.pos_part - f.neg_part = f :=
begin
  simp only [pos_part, neg_part],
  ext a,
  rw coe_sub,
  exact max_zero_sub_eq_self (f a)
end

end pos_part

end simple_func

end measure_theory

namespace measure_theory
open set filter topological_space ennreal emetric

variables {α E F : Type*} [measurable_space α]

local infixr ` →ₛ `:25 := simple_func

namespace simple_func

section integral
/-!
### The Bochner integral of simple functions

Define the Bochner integral of simple functions of the type `α →ₛ β` where `β` is a normed group,
and prove basic property of this integral.
-/
open finset

variables [normed_group E] [measurable_space E] [normed_group F]
variables {μ : measure α}

/-- For simple functions with a `normed_group` as codomain, being integrable is the same as having
    finite volume support. -/
lemma integrable_iff_fin_meas_supp {f : α →ₛ E} {μ : measure α} :
  integrable f μ ↔ f.fin_meas_supp μ :=
calc integrable f μ ↔ ∫⁻ x, f.map (coe ∘ nnnorm : E → ennreal) x ∂μ < ⊤ :
  and_iff_right f.ae_measurable
... ↔ (f.map (coe ∘ nnnorm : E → ennreal)).lintegral μ < ⊤ : by rw lintegral_eq_lintegral
... ↔ (f.map (coe ∘ nnnorm : E → ennreal)).fin_meas_supp μ : iff.symm $
  fin_meas_supp.iff_lintegral_lt_top $ eventually_of_forall $ λ x, coe_lt_top
... ↔ _ : fin_meas_supp.map_iff $ λ b, coe_eq_zero.trans nnnorm_eq_zero

lemma fin_meas_supp.integrable {f : α →ₛ E} (h : f.fin_meas_supp μ) : integrable f μ :=
integrable_iff_fin_meas_supp.2 h

lemma integrable_pair [measurable_space F] {f : α →ₛ E} {g : α →ₛ F} :
  integrable f μ → integrable g μ → integrable (pair f g) μ :=
by simpa only [integrable_iff_fin_meas_supp] using fin_meas_supp.pair

variables [normed_space ℝ F]

/-- Bochner integral of simple functions whose codomain is a real `normed_space`. -/
def integral (μ : measure α) (f : α →ₛ F) : F :=
∑ x in f.range, (ennreal.to_real (μ (f ⁻¹' {x}))) • x

lemma integral_eq_sum_filter (f : α →ₛ F) (μ) :
  f.integral μ = ∑ x in f.range.filter (λ x, x ≠ 0), (ennreal.to_real (μ (f ⁻¹' {x}))) • x :=
eq.symm $ sum_filter_of_ne $ λ x _, mt $ λ h0, h0.symm ▸ smul_zero _

/-- The Bochner integral is equal to a sum over any set that includes `f.range` (except `0`). -/
lemma integral_eq_sum_of_subset {f : α →ₛ F} {μ : measure α} {s : finset F}
  (hs : f.range.filter (λ x, x ≠ 0) ⊆ s) : f.integral μ = ∑ x in s, (μ (f ⁻¹' {x})).to_real • x :=
begin
  rw [simple_func.integral_eq_sum_filter, finset.sum_subset hs],
  rintro x - hx, rw [finset.mem_filter, not_and_distrib, ne.def, not_not] at hx,
  rcases hx with hx|rfl; [skip, simp],
  rw [simple_func.mem_range] at hx, rw [preimage_eq_empty]; simp [disjoint_singleton_left, hx]
end

/-- Calculate the integral of `g ∘ f : α →ₛ F`, where `f` is an integrable function from `α` to `E`
    and `g` is a function from `E` to `F`. We require `g 0 = 0` so that `g ∘ f` is integrable. -/
lemma map_integral (f : α →ₛ E) (g : E → F) (hf : integrable f μ) (hg : g 0 = 0) :
  (f.map g).integral μ = ∑ x in f.range, (ennreal.to_real (μ (f ⁻¹' {x}))) • (g x) :=
begin
  -- We start as in the proof of `map_lintegral`
  simp only [integral, range_map],
  refine finset.sum_image' _ (assume b hb, _),
  rcases mem_range.1 hb with ⟨a, rfl⟩,
  rw [map_preimage_singleton, ← sum_measure_preimage_singleton _
    (λ _ _, f.is_measurable_preimage _)],
  -- Now we use `hf : integrable f μ` to show that `ennreal.to_real` is additive.
  by_cases ha : g (f a) = 0,
  { simp only [ha, smul_zero],
    refine (sum_eq_zero $ λ x hx, _).symm,
    simp only [mem_filter] at hx,
    simp [hx.2] },
  { rw [to_real_sum, sum_smul],
    { refine sum_congr rfl (λ x hx, _),
      simp only [mem_filter] at hx,
      rw [hx.2] },
    { intros x hx,
      simp only [mem_filter] at hx,
      refine (integrable_iff_fin_meas_supp.1 hf).meas_preimage_singleton_ne_zero _,
      exact λ h0, ha (hx.2 ▸ h0.symm ▸ hg) } },
end

/-- `simple_func.integral` and `simple_func.lintegral` agree when the integrand has type
    `α →ₛ ennreal`. But since `ennreal` is not a `normed_space`, we need some form of coercion.
    See `integral_eq_lintegral` for a simpler version. -/
lemma integral_eq_lintegral' {f : α →ₛ E} {g : E → ennreal} (hf : integrable f μ) (hg0 : g 0 = 0)
  (hgt : ∀b, g b < ⊤):
  (f.map (ennreal.to_real ∘ g)).integral μ = ennreal.to_real (∫⁻ a, g (f a) ∂μ) :=
begin
  have hf' : f.fin_meas_supp μ := integrable_iff_fin_meas_supp.1 hf,
  simp only [← map_apply g f, lintegral_eq_lintegral],
  rw [map_integral f _ hf, map_lintegral, ennreal.to_real_sum],
  { refine finset.sum_congr rfl (λb hb, _),
    rw [smul_eq_mul, to_real_mul, mul_comm] },
  { assume a ha,
    by_cases a0 : a = 0,
    { rw [a0, hg0, zero_mul], exact with_top.zero_lt_top },
    { apply mul_lt_top (hgt a) (hf'.meas_preimage_singleton_ne_zero a0) } },
  { simp [hg0] }
end

variables [normed_space ℝ E]

lemma integral_congr {f g : α →ₛ E} (hf : integrable f μ) (h : f =ᵐ[μ] g):
  f.integral μ = g.integral μ :=
show ((pair f g).map prod.fst).integral μ = ((pair f g).map prod.snd).integral μ, from
begin
  have inte := integrable_pair hf (hf.congr h),
  rw [map_integral (pair f g) _ inte prod.fst_zero, map_integral (pair f g) _ inte prod.snd_zero],
  refine finset.sum_congr rfl (assume p hp, _),
  rcases mem_range.1 hp with ⟨a, rfl⟩,
  by_cases eq : f a = g a,
  { dsimp only [pair_apply], rw eq },
  { have : μ ((pair f g) ⁻¹' {(f a, g a)}) = 0,
    { refine measure_mono_null (assume a' ha', _) h,
      simp only [set.mem_preimage, mem_singleton_iff, pair_apply, prod.mk.inj_iff] at ha',
      show f a' ≠ g a',
      rwa [ha'.1, ha'.2] },
    simp only [this, pair_apply, zero_smul, ennreal.zero_to_real] },
end

/-- `simple_func.bintegral` and `simple_func.integral` agree when the integrand has type
    `α →ₛ ennreal`. But since `ennreal` is not a `normed_space`, we need some form of coercion. -/
lemma integral_eq_lintegral {f : α →ₛ ℝ} (hf : integrable f μ) (h_pos : 0 ≤ᵐ[μ] f) :
  f.integral μ = ennreal.to_real (∫⁻ a, ennreal.of_real (f a) ∂μ) :=
begin
  have : f =ᵐ[μ] f.map (ennreal.to_real ∘ ennreal.of_real) :=
    h_pos.mono (λ a h, (ennreal.to_real_of_real h).symm),
  rw [← integral_eq_lintegral' hf],
  { exact integral_congr hf this },
  { exact ennreal.of_real_zero },
  { assume b, rw ennreal.lt_top_iff_ne_top, exact ennreal.of_real_ne_top }
end

lemma integral_add {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ) :
  integral μ (f + g) = integral μ f + integral μ g :=
calc integral μ (f + g) = ∑ x in (pair f g).range,
       ennreal.to_real (μ ((pair f g) ⁻¹' {x})) • (x.fst + x.snd) :
begin
  rw [add_eq_map₂, map_integral (pair f g)],
  { exact integrable_pair hf hg },
  { simp only [add_zero, prod.fst_zero, prod.snd_zero] }
end
... = ∑ x in (pair f g).range,
        (ennreal.to_real (μ ((pair f g) ⁻¹' {x})) • x.fst +
         ennreal.to_real (μ ((pair f g) ⁻¹' {x})) • x.snd) :
  finset.sum_congr rfl $ assume a ha, smul_add _ _ _
... = ∑ x in (pair f g).range,
        ennreal.to_real (μ ((pair f g) ⁻¹' {x})) • x.fst +
      ∑ x in (pair f g).range,
        ennreal.to_real (μ ((pair f g) ⁻¹' {x})) • x.snd :
  by rw finset.sum_add_distrib
... = ((pair f g).map prod.fst).integral μ + ((pair f g).map prod.snd).integral μ :
begin
  rw [map_integral (pair f g), map_integral (pair f g)],
  { exact integrable_pair hf hg }, { refl },
  { exact integrable_pair hf hg }, { refl }
end
... = integral μ f + integral μ g : rfl

lemma integral_neg {f : α →ₛ E} (hf : integrable f μ) : integral μ (-f) = - integral μ f :=
calc integral μ (-f) = integral μ (f.map (has_neg.neg)) : rfl
  ... = - integral μ f :
  begin
    rw [map_integral f _ hf neg_zero, integral, ← sum_neg_distrib],
    refine finset.sum_congr rfl (λx h, smul_neg _ _),
  end

lemma integral_sub [borel_space E] {f g : α →ₛ E} (hf : integrable f μ) (hg : integrable g μ) :
  integral μ (f - g) = integral μ f - integral μ g :=
begin
  rw [sub_eq_add_neg, integral_add hf, integral_neg hg, sub_eq_add_neg],
  exact hg.neg
end

lemma integral_smul (r : ℝ) {f : α →ₛ E} (hf : integrable f μ) :
  integral μ (r • f) = r • integral μ f :=
calc integral μ (r • f) = ∑ x in f.range, ennreal.to_real (μ (f ⁻¹' {x})) • r • x :
  by rw [smul_eq_map r f, map_integral f _ hf (smul_zero _)]
... = ∑ x in f.range, ((ennreal.to_real (μ (f ⁻¹' {x}))) * r) • x :
  finset.sum_congr rfl $ λb hb, by apply smul_smul
... = r • integral μ f :
by simp only [integral, smul_sum, smul_smul, mul_comm]

lemma norm_integral_le_integral_norm (f : α →ₛ E) (hf : integrable f μ) :
  ∥f.integral μ∥ ≤ (f.map norm).integral μ :=
begin
  rw [map_integral f norm hf norm_zero, integral],
  calc ∥∑ x in f.range, ennreal.to_real (μ (f ⁻¹' {x})) • x∥ ≤
       ∑ x in f.range, ∥ennreal.to_real (μ (f ⁻¹' {x})) • x∥ :
    norm_sum_le _ _
    ... = ∑ x in f.range, ennreal.to_real (μ (f ⁻¹' {x})) • ∥x∥ :
    begin
      refine finset.sum_congr rfl (λb hb, _),
      rw [norm_smul, smul_eq_mul, real.norm_eq_abs, abs_of_nonneg to_real_nonneg]
    end
end

lemma integral_add_measure {ν} (f : α →ₛ E) (hf : integrable f (μ + ν)) :
  f.integral (μ + ν) = f.integral μ + f.integral ν :=
begin
  simp only [integral_eq_sum_filter, ← sum_add_distrib, ← add_smul, measure.add_apply],
  refine sum_congr rfl (λ x hx, _),
  rw [to_real_add];
    refine ne_of_lt ((integrable_iff_fin_meas_supp.1 _).meas_preimage_singleton_ne_zero
      (mem_filter.1 hx).2),
  exacts [hf.left_of_add_measure, hf.right_of_add_measure]
end

end integral

end simple_func

namespace l1

open ae_eq_fun

variables
  [normed_group E] [second_countable_topology E] [measurable_space E] [borel_space E]
  [normed_group F] [second_countable_topology F] [measurable_space F] [borel_space F]
  {μ : measure α}

variables (α E μ)

-- We use `Type*` instead of `add_subgroup` because otherwise we loose dot notation.
/-- `l1.simple_func` is a subspace of L1 consisting of equivalence classes of an integrable simple
    function. -/
def simple_func : Type* :=
↥({ carrier := {f : α →₁[μ] E | ∃ (s : α →ₛ E), (ae_eq_fun.mk s s.ae_measurable : α →ₘ[μ] E) = f},
  zero_mem' := ⟨0, rfl⟩,
  add_mem' := λ f g ⟨s, hs⟩ ⟨t, ht⟩,
    ⟨s + t, by simp only [coe_add, ← hs, ← ht, mk_add_mk, ← simple_func.coe_add]⟩,
  neg_mem' := λ f ⟨s, hs⟩, ⟨-s, by simp only [coe_neg, ← hs, neg_mk, ← simple_func.coe_neg]⟩ } :
  add_subgroup (α →₁[μ] E))

variables {α E μ}

notation α ` →₁ₛ[`:25 μ `] ` E := measure_theory.l1.simple_func α E μ

namespace simple_func

section instances
/-! Simple functions in L1 space form a `normed_space`. -/

instance : has_coe (α →₁ₛ[μ] E) (α →₁[μ] E) := coe_subtype
instance : has_coe_to_fun (α →₁ₛ[μ] E) := ⟨λ f, α → E, λ f, ⇑(f : α →₁[μ] E)⟩

@[simp, norm_cast] lemma coe_coe (f : α →₁ₛ[μ] E) : ⇑(f : α →₁[μ] E) = f := rfl
protected lemma eq {f g : α →₁ₛ[μ] E} : (f : α →₁[μ] E) = (g : α →₁[μ] E) → f = g := subtype.eq
protected lemma eq' {f g : α →₁ₛ[μ] E} : (f : α →ₘ[μ] E) = (g : α →ₘ[μ] E) → f = g :=
subtype.eq ∘ subtype.eq

@[norm_cast] protected lemma eq_iff {f g : α →₁ₛ[μ] E} : (f : α →₁[μ] E) = g ↔ f = g :=
subtype.ext_iff.symm

@[norm_cast] protected lemma eq_iff' {f g : α →₁ₛ[μ] E} : (f : α →ₘ[μ] E) = g ↔ f = g :=
iff.intro (simple_func.eq') (congr_arg _)

/-- L1 simple functions forms a `emetric_space`, with the emetric being inherited from L1 space,
  i.e., `edist f g = ∫⁻ a, edist (f a) (g a)`.
  Not declared as an instance as `α →₁ₛ[μ] β` will only be useful in the construction of the Bochner
  integral. -/
protected def emetric_space  : emetric_space (α →₁ₛ[μ] E) := subtype.emetric_space

/-- L1 simple functions forms a `metric_space`, with the metric being inherited from L1 space,
  i.e., `dist f g = ennreal.to_real (∫⁻ a, edist (f a) (g a)`).
  Not declared as an instance as `α →₁ₛ[μ] β` will only be useful in the construction of the Bochner
  integral. -/
protected def metric_space : metric_space (α →₁ₛ[μ] E) := subtype.metric_space

local attribute [instance] simple_func.metric_space simple_func.emetric_space

/-- Functions `α →₁ₛ[μ] E` form an additive commutative group. -/
local attribute [instance, priority 10000]
protected def add_comm_group : add_comm_group (α →₁ₛ[μ] E) := add_subgroup.to_add_comm_group _

instance : inhabited (α →₁ₛ[μ] E) := ⟨0⟩

@[simp, norm_cast]
lemma coe_zero : ((0 : α →₁ₛ[μ] E) : α →₁[μ] E) = 0 := rfl
@[simp, norm_cast]
lemma coe_add (f g : α →₁ₛ[μ] E) : ((f + g : α →₁ₛ[μ] E) : α →₁[μ] E) = f + g := rfl
@[simp, norm_cast]
lemma coe_neg (f : α →₁ₛ[μ] E) : ((-f : α →₁ₛ[μ] E) : α →₁[μ] E) = -f := rfl
@[simp, norm_cast]
lemma coe_sub (f g : α →₁ₛ[μ] E) : ((f - g : α →₁ₛ[μ] E) : α →₁[μ] E) = f - g := rfl

@[simp] lemma edist_eq (f g : α →₁ₛ[μ] E) : edist f g = edist (f : α →₁[μ] E) (g : α →₁[μ] E) := rfl
@[simp] lemma dist_eq (f g : α →₁ₛ[μ] E) : dist f g = dist (f : α →₁[μ] E) (g : α →₁[μ] E) := rfl

/-- The norm on `α →₁ₛ[μ] E` is inherited from L1 space. That is, `∥f∥ = ∫⁻ a, edist (f a) 0`.
  Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the Bochner
  integral. -/
protected def has_norm : has_norm (α →₁ₛ[μ] E) := ⟨λf, ∥(f : α →₁[μ] E)∥⟩

local attribute [instance] simple_func.has_norm

lemma norm_eq (f : α →₁ₛ[μ] E) : ∥f∥ = ∥(f : α →₁[μ] E)∥ := rfl
lemma norm_eq' (f : α →₁ₛ[μ] E) : ∥f∥ = ennreal.to_real (edist (f : α →ₘ[μ] E) 0) := rfl

/-- Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the
Bochner integral. -/
protected def normed_group : normed_group (α →₁ₛ[μ] E) :=
normed_group.of_add_dist (λ x, rfl) $ by
  { intros, simp only [dist_eq, coe_add, l1.dist_eq, l1.coe_add], rw edist_add_right }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

/-- Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the
Bochner integral. -/
protected def has_scalar : has_scalar 𝕜 (α →₁ₛ[μ] E) := ⟨λk f, ⟨k • f,
begin
  rcases f with ⟨f, ⟨s, hs⟩⟩,
  use k • s,
  rw [coe_smul, subtype.coe_mk, ← hs], refl
end ⟩⟩

local attribute [instance, priority 10000] simple_func.has_scalar

@[simp, norm_cast] lemma coe_smul (c : 𝕜) (f : α →₁ₛ[μ] E) :
  ((c • f : α →₁ₛ[μ] E) : α →₁[μ] E) = c • (f : α →₁[μ] E) := rfl

/-- Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the
  Bochner integral. -/
protected def semimodule : semimodule 𝕜 (α →₁ₛ[μ] E) :=
{ one_smul  := λf, simple_func.eq (by { simp only [coe_smul], exact one_smul _ _ }),
  mul_smul  := λx y f, simple_func.eq (by { simp only [coe_smul], exact mul_smul _ _ _ }),
  smul_add  := λx f g, simple_func.eq (by { simp only [coe_smul, coe_add], exact smul_add _ _ _ }),
  smul_zero := λx, simple_func.eq (by { simp only [coe_zero, coe_smul], exact smul_zero _ }),
  add_smul  := λx y f, simple_func.eq (by { simp only [coe_smul], exact add_smul _ _ _ }),
  zero_smul := λf, simple_func.eq (by { simp only [coe_smul], exact zero_smul _ _ }) }

local attribute [instance] simple_func.normed_group simple_func.semimodule

/-- Not declared as an instance as `α →₁ₛ[μ] E` will only be useful in the construction of the
Bochner integral. -/
protected def normed_space : normed_space 𝕜 (α →₁ₛ[μ] E) :=
⟨ λc f, by { rw [norm_eq, norm_eq, coe_smul, norm_smul] } ⟩

end instances

local attribute [instance] simple_func.normed_group simple_func.normed_space

section of_simple_func

/-- Construct the equivalence class `[f]` of an integrable simple function `f`. -/
@[reducible] def of_simple_func (f : α →ₛ E) (hf : integrable f μ) : (α →₁ₛ[μ] E) :=
⟨l1.of_fun f hf, ⟨f, rfl⟩⟩

lemma of_simple_func_eq_of_fun (f : α →ₛ E) (hf : integrable f μ) :
  (of_simple_func f hf : α →₁[μ] E) = l1.of_fun f hf := rfl

lemma of_simple_func_eq_mk (f : α →ₛ E) (hf : integrable f μ) :
  (of_simple_func f hf : α →ₘ[μ] E) = ae_eq_fun.mk f f.ae_measurable := rfl

lemma of_simple_func_zero : of_simple_func (0 : α →ₛ E) (integrable_zero α E μ) = 0 := rfl

lemma of_simple_func_add (f g : α →ₛ E) (hf : integrable f μ) (hg : integrable g μ) :
  of_simple_func (f + g) (hf.add hg) = of_simple_func f hf + of_simple_func g hg := rfl

lemma of_simple_func_neg (f : α →ₛ E) (hf : integrable f μ) :
  of_simple_func (-f) hf.neg = -of_simple_func f hf := rfl

lemma of_simple_func_sub (f g : α →ₛ E) (hf : integrable f μ) (hg : integrable g μ) :
  of_simple_func (f - g) (hf.sub hg) = of_simple_func f hf - of_simple_func g hg :=
by { simp only [sub_eq_add_neg, ← of_simple_func_neg, ← of_simple_func_add], refl }

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma of_simple_func_smul (f : α →ₛ E) (hf : integrable f μ) (c : 𝕜) :
  of_simple_func (c • f) (hf.smul c) = c • of_simple_func f hf := rfl

lemma norm_of_simple_func (f : α →ₛ E) (hf : integrable f μ) :
  ∥of_simple_func f hf∥ = ennreal.to_real (∫⁻ a, edist (f a) 0 ∂μ) :=
rfl

end of_simple_func

section to_simple_func

/-- Find a representative of a `l1.simple_func`. -/
def to_simple_func (f : α →₁ₛ[μ] E) : α →ₛ E := classical.some f.2

/-- `f.to_simple_func` is measurable. -/
protected lemma measurable (f : α →₁ₛ[μ] E) : measurable f.to_simple_func :=
f.to_simple_func.measurable

protected lemma ae_measurable (f : α →₁ₛ[μ] E) : ae_measurable f.to_simple_func μ :=
f.measurable.ae_measurable

/-- `f.to_simple_func` is integrable. -/
protected lemma integrable (f : α →₁ₛ[μ] E) : integrable f.to_simple_func μ :=
let h := classical.some_spec f.2 in (integrable_mk f.ae_measurable).1 $ h.symm ▸ (f : α →₁[μ] E).2

lemma of_simple_func_to_simple_func (f : α →₁ₛ[μ] E) :
  of_simple_func (f.to_simple_func) f.integrable = f :=
by { rw ← simple_func.eq_iff', exact classical.some_spec f.2 }

lemma to_simple_func_of_simple_func (f : α →ₛ E) (hfi : integrable f μ) :
  (of_simple_func f hfi).to_simple_func =ᵐ[μ] f :=
by { rw ← mk_eq_mk, exact classical.some_spec (of_simple_func f hfi).2 }

lemma to_simple_func_eq_to_fun (f : α →₁ₛ[μ] E) : f.to_simple_func =ᵐ[μ] f :=
begin
  rw [← of_fun_eq_of_fun f.to_simple_func f f.integrable (f : α →₁[μ] E).integrable, ← l1.eq_iff],
  simp only [of_fun_eq_mk, ← coe_coe, mk_to_fun],
  exact classical.some_spec f.coe_prop
end

variables (α E)
lemma zero_to_simple_func : (0 : α →₁ₛ[μ] E).to_simple_func =ᵐ[μ] 0 :=
begin
  filter_upwards [to_simple_func_eq_to_fun (0 : α →₁ₛ[μ] E), l1.zero_to_fun α E],
  assume a h₁ h₂,
  rwa h₁,
end
variables {α E}

lemma add_to_simple_func (f g : α →₁ₛ[μ] E) :
  (f + g).to_simple_func =ᵐ[μ] f.to_simple_func + g.to_simple_func :=
begin
  filter_upwards [to_simple_func_eq_to_fun (f + g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, l1.add_to_fun (f : α →₁[μ] E) g],
  assume a,
  simp only [← coe_coe, coe_add, pi.add_apply],
  iterate 4 { assume h, rw h }
end

lemma neg_to_simple_func (f : α →₁ₛ[μ] E) : (-f).to_simple_func =ᵐ[μ] - f.to_simple_func :=
begin
  filter_upwards [to_simple_func_eq_to_fun (-f), to_simple_func_eq_to_fun f,
    l1.neg_to_fun (f : α →₁[μ] E)],
  assume a,
  simp only [pi.neg_apply, coe_neg, ← coe_coe],
  repeat { assume h, rw h }
end

lemma sub_to_simple_func (f g : α →₁ₛ[μ] E) :
  (f - g).to_simple_func =ᵐ[μ] f.to_simple_func - g.to_simple_func :=
begin
  filter_upwards [to_simple_func_eq_to_fun (f - g), to_simple_func_eq_to_fun f,
    to_simple_func_eq_to_fun g, l1.sub_to_fun (f : α →₁[μ] E) g],
  assume a,
  simp only [coe_sub, pi.sub_apply, ← coe_coe],
  repeat { assume h, rw h }
end

variables {𝕜 : Type*} [normed_field 𝕜] [normed_space 𝕜 E]

lemma smul_to_simple_func (k : 𝕜) (f : α →₁ₛ[μ] E) :
  (k • f).to_simple_func =ᵐ[μ] k • f.to_simple_func :=
begin
  filter_upwards [to_simple_func_eq_to_fun (k • f), to_simple_func_eq_to_fun f,
    l1.smul_to_fun k (f : α →₁[μ] E)],
  assume a,
  simp only [pi.smul_apply, coe_smul, ← coe_coe],
  repeat { assume h, rw h }
end

lemma lintegral_edist_to_simple_func_lt_top (f g : α →₁ₛ[μ] E) :
  ∫⁻ (x : α), edist ((to_simple_func f) x) ((to_simple_func g) x) ∂μ < ⊤ :=
begin
  rw lintegral_rw₂ (to_simple_func_eq_to_fun f) (to_simple_func_eq_to_fun g),
  exact lintegral_edist_to_fun_lt_top _ _
end

lemma dist_to_simple_func (f g : α →₁ₛ[μ] E) : dist f g =
  ennreal.to_real (∫⁻ x, edist (f.to_simple_func x) (g.to_simple_func x) ∂μ) :=
begin
  rw [dist_eq, l1.dist_to_fun, ennreal.to_real_eq_to_real],
  { rw lintegral_rw₂, repeat { exact ae_eq_symm (to_simple_func_eq_to_fun _) } },
  { exact l1.lintegral_edist_to_fun_lt_top _ _ },
  { exact lintegral_edist_to_simple_func_lt_top _ _ }
end

lemma norm_to_simple_func (f : α →₁ₛ[μ] E) :
  ∥f∥ = ennreal.to_real (∫⁻ (a : α), nnnorm ((to_simple_func f) a) ∂μ) :=
calc ∥f∥ =
  ennreal.to_real (∫⁻x, edist (f.to_simple_func x) ((0 : α →₁ₛ[μ] E).to_simple_func x) ∂μ) :
begin
  rw [← dist_zero_right, dist_to_simple_func]
end
... = ennreal.to_real (∫⁻ (x : α), (coe ∘ nnnorm) (f.to_simple_func x) ∂μ) :
begin
  rw lintegral_nnnorm_eq_lintegral_edist,
  have : ∫⁻ x, edist ((to_simple_func f) x) ((to_simple_func (0 : α →₁ₛ[μ] E)) x) ∂μ =
    ∫⁻ x, edist ((to_simple_func f) x) 0 ∂μ,
  { refine lintegral_congr_ae ((zero_to_simple_func α E).mono (λ a h, _)),
    rw [h, pi.zero_apply] },
  rw [ennreal.to_real_eq_to_real],
  { exact this },
  { exact lintegral_edist_to_simple_func_lt_top _ _ },
  { rw ← this, exact lintegral_edist_to_simple_func_lt_top _ _ }
end

lemma norm_eq_integral (f : α →₁ₛ[μ] E) : ∥f∥ = (f.to_simple_func.map norm).integral μ :=
-- calc ∥f∥ = ennreal.to_real (∫⁻ (x : α), (coe ∘ nnnorm) (f.to_simple_func x) ∂μ) :
--   by { rw norm_to_simple_func }
-- ... = (f.to_simple_func.map norm).integral μ :
begin
  rw [norm_to_simple_func, simple_func.integral_eq_lintegral],
  { simp only [simple_func.map_apply, of_real_norm_eq_coe_nnnorm] },
  { exact f.integrable.norm },
  { exact eventually_of_forall (λ x, norm_nonneg _) }
end

end to_simple_func

section coe_to_l1

protected lemma uniform_continuous : uniform_continuous (coe : (α →₁ₛ[μ] E) → (α →₁[μ] E)) :=
uniform_continuous_comap

protected lemma uniform_embedding : uniform_embedding (coe : (α →₁ₛ[μ] E) → (α →₁[μ] E)) :=
uniform_embedding_comap subtype.val_injective

protected lemma uniform_inducing : uniform_inducing (coe : (α →₁ₛ[μ] E) → (α →₁[μ] E)) :=
simple_func.uniform_embedding.to_uniform_inducing

protected lemma dense_embedding : dense_embedding (coe : (α →₁ₛ[μ] E) → (α →₁[μ] E)) :=
begin
  apply simple_func.uniform_embedding.dense_embedding,
  rintros ⟨f, hfi⟩,
  have A : ae_eq_fun.mk f f.ae_measurable = f := mk_coe_fn _,
  rw mem_closure_iff_seq_limit,
  have hfi' := integrable_coe_fn.2 hfi,
  refine ⟨λ n, ↑(of_simple_func (simple_func.approx_on f f.measurable univ 0 trivial n)
    (simple_func.integrable_approx_on_univ f.measurable hfi' n)), λ n, mem_range_self _, _⟩,
  simp only [tendsto_iff_edist_tendsto_0, of_fun_eq_mk, subtype.coe_mk, edist_eq],
  dsimp,
  conv in (edist _ _) { congr, skip, rw ← A },
  simpa only [edist_mk_mk] using simple_func.tendsto_approx_on_univ_l1_edist f.measurable hfi'
end

protected lemma dense_inducing : dense_inducing (coe : (α →₁ₛ[μ] E) → (α →₁[μ] E)) :=
simple_func.dense_embedding.to_dense_inducing

protected lemma dense_range : dense_range (coe : (α →₁ₛ[μ] E) → (α →₁[μ] E)) :=
simple_func.dense_inducing.dense

variables (𝕜 : Type*) [normed_field 𝕜] [normed_space 𝕜 E]

variables (α E)

/-- The uniform and dense embedding of L1 simple functions into L1 functions. -/
def coe_to_l1 : (α →₁ₛ[μ] E) →L[𝕜] (α →₁[μ] E) :=
{ to_fun := (coe : (α →₁ₛ[μ] E) → (α →₁[μ] E)),
  map_add' := λf g, rfl,
  map_smul' := λk f, rfl,
  cont := l1.simple_func.uniform_continuous.continuous, }

variables {α E 𝕜}

end coe_to_l1

section pos_part

/-- Positive part of a simple function in L1 space.  -/
def pos_part (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ := ⟨l1.pos_part (f : α →₁[μ] ℝ),
begin
  rcases f with ⟨f, s, hsf⟩,
  use s.pos_part,
  simp only [subtype.coe_mk, l1.coe_pos_part, ← hsf, ae_eq_fun.pos_part_mk, simple_func.pos_part,
    simple_func.coe_map]
end ⟩

/-- Negative part of a simple function in L1 space. -/
def neg_part (f : α →₁ₛ[μ] ℝ) : α →₁ₛ[μ] ℝ := pos_part (-f)

@[norm_cast]
lemma coe_pos_part (f : α →₁ₛ[μ] ℝ) : (f.pos_part : α →₁[μ] ℝ) = (f : α →₁[μ] ℝ).pos_part := rfl

@[norm_cast]
lemma coe_neg_part (f : α →₁ₛ[μ] ℝ) : (f.neg_part : α →₁[μ] ℝ) = (f : α →₁[μ] ℝ).neg_part := rfl

end pos_part

section simple_func_integral
/-! Define the Bochner integral on `α →₁ₛ[μ] E` and prove basic properties of this integral. -/

variables [normed_space ℝ E]

/-- The Bochner integral over simple functions in l1 space. -/
def integral (f : α →₁ₛ[μ] E) : E := (f.to_simple_func).integral μ

lemma integral_eq_integral (f : α →₁ₛ[μ] E) : integral f = (f.to_simple_func).integral μ := rfl

lemma integral_eq_lintegral {f : α →₁ₛ[μ] ℝ} (h_pos : 0 ≤ᵐ[μ] f.to_simple_func) :
  integral f = ennreal.to_real (∫⁻ a, ennreal.of_real (f.to_simple_func a) ∂μ) :=
by rw [integral, simple_func.integral_eq_lintegral f.integrable h_pos]

lemma integral_congr {f g : α →₁ₛ[μ] E} (h : f.to_simple_func =ᵐ[μ] g.to_simple_func) :
  integral f = integral g :=
simple_func.integral_congr f.integrable h

lemma integral_add (f g : α →₁ₛ[μ] E) : integral (f + g) = integral f + integral g :=
begin
  simp only [integral],
  rw ← simple_func.integral_add f.integrable g.integrable,
  apply measure_theory.simple_func.integral_congr (f + g).integrable,
  apply add_to_simple_func
end

lemma integral_smul (r : ℝ) (f : α →₁ₛ[μ] E) : integral (r • f) = r • integral f :=
begin
  simp only [integral],
  rw ← simple_func.integral_smul _ f.integrable,
  apply measure_theory.simple_func.integral_congr (r • f).integrable,
  apply smul_to_simple_func
end

lemma norm_integral_le_norm (f : α →₁ₛ[μ] E) : ∥ integral f ∥ ≤ ∥f∥ :=
begin
  rw [integral, norm_eq_integral],
  exact f.to_simple_func.norm_integral_le_integral_norm f.integrable
end

/-- The Bochner integral over simple functions in l1 space as a continuous linear map. -/
def integral_clm : (α →₁ₛ[μ] E) →L[ℝ] E :=
linear_map.mk_continuous ⟨integral, integral_add, integral_smul⟩
  1 (λf, le_trans (norm_integral_le_norm _) $ by rw one_mul)

local notation `Integral` := @integral_clm α E _ _ _ _ _ μ _

open continuous_linear_map

lemma norm_Integral_le_one : ∥Integral∥ ≤ 1 :=
linear_map.mk_continuous_norm_le _ (zero_le_one) _

section pos_part

lemma pos_part_to_simple_func (f : α →₁ₛ[μ] ℝ) :
  f.pos_part.to_simple_func =ᵐ[μ] f.to_simple_func.pos_part :=
begin
  have eq : ∀ a, f.to_simple_func.pos_part a = max (f.to_simple_func a) 0 := λa, rfl,
  have ae_eq : ∀ᵐ a ∂μ, f.pos_part.to_simple_func a = max (f.to_simple_func a) 0,
  { filter_upwards [to_simple_func_eq_to_fun f.pos_part, pos_part_to_fun (f : α →₁[μ] ℝ),
      to_simple_func_eq_to_fun f],
    assume a h₁ h₂ h₃,
    rw [h₁, ← coe_coe, coe_pos_part, h₂, coe_coe, ← h₃] },
  refine ae_eq.mono (assume a h, _),
  rw [h, eq]
end

lemma neg_part_to_simple_func (f : α →₁ₛ[μ] ℝ) :
  f.neg_part.to_simple_func =ᵐ[μ] f.to_simple_func.neg_part :=
begin
  rw [simple_func.neg_part, measure_theory.simple_func.neg_part],
  filter_upwards [pos_part_to_simple_func (-f), neg_to_simple_func f],
  assume a h₁ h₂,
  rw h₁,
  show max _ _ = max _ _,
  rw h₂,
  refl
end

lemma integral_eq_norm_pos_part_sub (f : α →₁ₛ[μ] ℝ) : f.integral = ∥f.pos_part∥ - ∥f.neg_part∥ :=
begin
  -- Convert things in `L¹` to their `simple_func` counterpart
  have ae_eq₁ : f.to_simple_func.pos_part =ᵐ[μ] (f.pos_part).to_simple_func.map norm,
  { filter_upwards [pos_part_to_simple_func f],
    assume a h,
    rw [simple_func.map_apply, h],
    conv_lhs { rw [← simple_func.pos_part_map_norm, simple_func.map_apply] } },
  -- Convert things in `L¹` to their `simple_func` counterpart
  have ae_eq₂ : f.to_simple_func.neg_part =ᵐ[μ] (f.neg_part).to_simple_func.map norm,
  { filter_upwards [neg_part_to_simple_func f],
    assume a h,
    rw [simple_func.map_apply, h],
    conv_lhs { rw [← simple_func.neg_part_map_norm, simple_func.map_apply] } },
  -- Convert things in `L¹` to their `simple_func` counterpart
  have ae_eq : ∀ᵐ a ∂μ, f.to_simple_func.pos_part a - f.to_simple_func.neg_part a =
    (f.pos_part).to_simple_func.map norm a - (f.neg_part).to_simple_func.map norm a,
  { filter_upwards [ae_eq₁, ae_eq₂],
    assume a h₁ h₂,
    rw [h₁, h₂] },
  rw [integral, norm_eq_integral, norm_eq_integral, ← simple_func.integral_sub],
  { show f.to_simple_func.integral μ =
      ((f.pos_part.to_simple_func).map norm - f.neg_part.to_simple_func.map norm).integral μ,
    apply measure_theory.simple_func.integral_congr f.integrable,
    filter_upwards [ae_eq₁, ae_eq₂],
    assume a h₁ h₂, show _ = _ - _,
    rw [← h₁, ← h₂],
    have := f.to_simple_func.pos_part_sub_neg_part,
    conv_lhs {rw ← this},
    refl },
  { exact f.integrable.max_zero.congr ae_eq₁ },
  { exact f.integrable.neg.max_zero.congr ae_eq₂ }
end

end pos_part

end simple_func_integral

end simple_func

open simple_func

variables [normed_space ℝ E] [normed_space ℝ F] [complete_space E]

section integration_in_l1

local notation `to_l1` := coe_to_l1 α E ℝ
local attribute [instance] simple_func.normed_group simple_func.normed_space

open continuous_linear_map

/-- The Bochner integral in l1 space as a continuous linear map. -/
def integral_clm : (α →₁[μ] E) →L[ℝ] E :=
  integral_clm.extend to_l1 simple_func.dense_range simple_func.uniform_inducing

/-- The Bochner integral in l1 space -/
def integral (f : α →₁[μ] E) : E := integral_clm f

lemma integral_eq (f : α →₁[μ] E) : integral f = integral_clm f := rfl

@[norm_cast] lemma simple_func.integral_l1_eq_integral (f : α →₁ₛ[μ] E) :
  integral (f : α →₁[μ] E) = f.integral :=
uniformly_extend_of_ind simple_func.uniform_inducing simple_func.dense_range
  simple_func.integral_clm.uniform_continuous _

variables (α E)
@[simp] lemma integral_zero : integral (0 : α →₁[μ] E) = 0 :=
map_zero integral_clm
variables {α E}

lemma integral_add (f g : α →₁[μ] E) : integral (f + g) = integral f + integral g :=
map_add integral_clm f g

lemma integral_neg (f : α →₁[μ] E) : integral (-f) = - integral f :=
map_neg integral_clm f

lemma integral_sub (f g : α →₁[μ] E) : integral (f - g) = integral f - integral g :=
map_sub integral_clm f g

lemma integral_smul (r : ℝ) (f : α →₁[μ] E) : integral (r • f) = r • integral f :=
map_smul r integral_clm f

local notation `Integral` := @integral_clm α E _ _ _ _ _ μ _ _
local notation `sIntegral` := @simple_func.integral_clm α E _ _ _ _ _ μ _

lemma norm_Integral_le_one : ∥Integral∥ ≤ 1 :=
calc ∥Integral∥ ≤ (1 : ℝ≥0) * ∥sIntegral∥ :
  op_norm_extend_le _ _ _ $ λs, by {rw [nnreal.coe_one, one_mul], refl}
  ... = ∥sIntegral∥ : one_mul _
  ... ≤ 1 : norm_Integral_le_one

lemma norm_integral_le (f : α →₁[μ] E) : ∥integral f∥ ≤ ∥f∥ :=
calc ∥integral f∥ = ∥Integral f∥ : rfl
  ... ≤ ∥Integral∥ * ∥f∥ : le_op_norm _ _
  ... ≤ 1 * ∥f∥ : mul_le_mul_of_nonneg_right norm_Integral_le_one $ norm_nonneg _
  ... = ∥f∥ : one_mul _

@[continuity]
lemma continuous_integral : continuous (λ (f : α →₁[μ] E), f.integral) :=
by simp [l1.integral, l1.integral_clm.continuous]

section pos_part

lemma integral_eq_norm_pos_part_sub (f : α →₁[μ] ℝ) : integral f = ∥pos_part f∥ - ∥neg_part f∥ :=
begin
  -- Use `is_closed_property` and `is_closed_eq`
  refine @is_closed_property _ _ _ (coe : (α →₁ₛ[μ] ℝ) → (α →₁[μ] ℝ))
    (λ f : α →₁[μ] ℝ, integral f = ∥pos_part f∥ - ∥neg_part f∥)
    l1.simple_func.dense_range (is_closed_eq _ _) _ f,
  { exact cont _ },
  { refine continuous.sub (continuous_norm.comp l1.continuous_pos_part)
      (continuous_norm.comp l1.continuous_neg_part) },
  -- Show that the property holds for all simple functions in the `L¹` space.
  { assume s,
    norm_cast,
    rw [← simple_func.norm_eq, ← simple_func.norm_eq],
    exact simple_func.integral_eq_norm_pos_part_sub _}
end

end pos_part

end integration_in_l1

end l1

variables [normed_group E] [second_countable_topology E] [normed_space ℝ E] [complete_space E]
  [measurable_space E] [borel_space E]
          [normed_group F] [second_countable_topology F] [normed_space ℝ F] [complete_space F]
  [measurable_space F] [borel_space F]

/-- The Bochner integral -/
def integral (μ : measure α) (f : α → E) : E :=
if hf : integrable f μ then (l1.of_fun f hf).integral else 0

/-! In the notation for integrals, an expression like `∫ x, g ∥x∥ ∂μ` will not be parsed correctly,
  and needs parentheses. We do not set the binding power of `r` to `0`, because then
  `∫ x, f x = 0` will be parsed incorrectly. -/
notation `∫` binders `, ` r:(scoped:60 f, f) ` ∂` μ:70 := integral μ r
notation `∫` binders `, ` r:(scoped:60 f, integral volume f) := r
notation `∫` binders ` in ` s `, ` r:(scoped:60 f, f) ` ∂` μ:70 := integral (measure.restrict μ s) r
notation `∫` binders ` in ` s `, ` r:(scoped:60 f, integral (measure.restrict volume s) f) := r

section properties

open continuous_linear_map measure_theory.simple_func

variables {f g : α → E} {μ : measure α}

lemma integral_eq (f : α → E) (hf : integrable f μ) :
  ∫ a, f a ∂μ = (l1.of_fun f hf).integral :=
dif_pos hf

lemma l1.integral_eq_integral (f : α →₁[μ] E) : f.integral = ∫ a, f a ∂μ :=
by rw [integral_eq, l1.of_fun_to_fun]

lemma integral_undef (h : ¬ integrable f μ) : ∫ a, f a ∂μ = 0 :=
dif_neg h

lemma integral_non_ae_measurable (h : ¬ ae_measurable f μ) : ∫ a, f a ∂μ = 0 :=
integral_undef $ not_and_of_not_left _ h

variables (α E)

lemma integral_zero : ∫ a : α, (0:E) ∂μ = 0 :=
by rw [integral_eq, l1.of_fun_zero, l1.integral_zero]

@[simp] lemma integral_zero' : integral μ (0 : α → E) = 0 :=
integral_zero α E

variables {α E}

lemma integral_add (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
by { rw [integral_eq, integral_eq f hf, integral_eq g hg, ← l1.integral_add, ← l1.of_fun_add],
     refl }

lemma integral_add' (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
integral_add hf hg

lemma integral_neg (f : α → E) : ∫ a, -f a ∂μ = - ∫ a, f a ∂μ :=
begin
  by_cases hf : integrable f μ,
  { rw [integral_eq f hf, integral_eq (λa, - f a) hf.neg, ← l1.integral_neg, ← l1.of_fun_neg],
    refl },
  { rw [integral_undef hf, integral_undef, neg_zero], rwa [← integrable_neg_iff] at hf }
end

lemma integral_neg' (f : α → E) : ∫ a, (-f) a ∂μ = - ∫ a, f a ∂μ :=
integral_neg f

lemma integral_sub (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
by { simp only [sub_eq_add_neg, ← integral_neg], exact integral_add hf hg.neg }

lemma integral_sub' (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ :=
integral_sub hf hg

lemma integral_smul (r : ℝ) (f : α → E) : ∫ a, r • (f a) ∂μ = r • ∫ a, f a ∂μ :=
begin
  by_cases hf : integrable f μ,
  { rw [integral_eq f hf, integral_eq (λa, r • (f a)), l1.of_fun_smul, l1.integral_smul] },
  { by_cases hr : r = 0,
    { simp only [hr, measure_theory.integral_zero, zero_smul] },
    have hf' : ¬ integrable (λ x, r • f x) μ,
    { change ¬ integrable (r • f) μ, rwa [integrable_smul_iff hr f] },
    rw [integral_undef hf, integral_undef hf', smul_zero] }
end

lemma integral_mul_left (r : ℝ) (f : α → ℝ) : ∫ a, r * (f a) ∂μ = r * ∫ a, f a ∂μ :=
integral_smul r f

lemma integral_mul_right (r : ℝ) (f : α → ℝ) : ∫ a, (f a) * r ∂μ = ∫ a, f a ∂μ * r :=
by { simp only [mul_comm], exact integral_mul_left r f }

lemma integral_div (r : ℝ) (f : α → ℝ) : ∫ a, (f a) / r ∂μ = ∫ a, f a ∂μ / r :=
integral_mul_right r⁻¹ f

lemma integral_congr_ae (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ :=
begin
  by_cases hfi : integrable f μ,
  { have hgi : integrable g μ := hfi.congr h,
    rw [integral_eq f hfi, integral_eq g hgi, (l1.of_fun_eq_of_fun f g hfi hgi).2 h] },
  { have hgi : ¬ integrable g μ, { rw integrable_congr h at hfi, exact hfi },
    rw [integral_undef hfi, integral_undef hgi] },
end

@[simp] lemma l1.integral_of_fun_eq_integral {f : α → E} (hf : integrable f μ) :
  ∫ a, (l1.of_fun f hf) a ∂μ = ∫ a, f a ∂μ :=
integral_congr_ae (l1.to_fun_of_fun f hf)

@[continuity]
lemma continuous_integral : continuous (λ (f : α →₁[μ] E), ∫ a, f a ∂μ) :=
by { simp only [← l1.integral_eq_integral], exact l1.continuous_integral }

lemma norm_integral_le_lintegral_norm (f : α → E) :
  ∥∫ a, f a ∂μ∥ ≤ ennreal.to_real (∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ) :=
begin
  by_cases hf : integrable f μ,
  { rw [integral_eq f hf, ← l1.norm_of_fun_eq_lintegral_norm f hf], exact l1.norm_integral_le _ },
  { rw [integral_undef hf, norm_zero], exact to_real_nonneg }
end

lemma ennnorm_integral_le_lintegral_ennnorm (f : α → E) :
  (nnnorm (∫ a, f a ∂μ) : ennreal) ≤ ∫⁻ a, (nnnorm (f a)) ∂μ :=
by { simp_rw [← of_real_norm_eq_coe_nnnorm], apply ennreal.of_real_le_of_le_to_real,
  exact norm_integral_le_lintegral_norm f }

lemma integral_eq_zero_of_ae {f : α → E} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0 :=
if hfm : ae_measurable f μ then by simp [integral_congr_ae hf, integral_zero]
else integral_non_ae_measurable hfm

/-- If `f` has finite integral, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
lemma has_finite_integral.tendsto_set_integral_nhds_zero {ι} {f : α → E}
  (hf : has_finite_integral f μ) {l : filter ι} {s : ι → set α}
  (hs : tendsto (μ ∘ s) l (𝓝 0)) :
  tendsto (λ i, ∫ x in s i, f x ∂μ) l (𝓝 0) :=
begin
  rw [tendsto_zero_iff_norm_tendsto_zero],
  simp_rw [← coe_nnnorm, ← nnreal.coe_zero, nnreal.tendsto_coe, ← ennreal.tendsto_coe,
    ennreal.coe_zero],
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_set_lintegral_zero hf hs) (λ i, zero_le _)
    (λ i, ennnorm_integral_le_lintegral_ennnorm _)
end

/-- If `f` is integrable, then `∫ x in s, f x ∂μ` is absolutely continuous in `s`: it tends
to zero as `μ s` tends to zero. -/
lemma integrable.tendsto_set_integral_nhds_zero {ι} {f : α → E}
  (hf : integrable f μ) {l : filter ι} {s : ι → set α} (hs : tendsto (μ ∘ s) l (𝓝 0)) :
  tendsto (λ i, ∫ x in s i, f x ∂μ) l (𝓝 0) :=
hf.2.tendsto_set_integral_nhds_zero hs

/-- If `F i → f` in `L1`, then `∫ x, F i x ∂μ → ∫ x, f x∂μ`. -/
lemma tendsto_integral_of_l1 {ι} (f : α → E) (hfi : integrable f μ)
  {F : ι → α → E} {l : filter ι} (hFi : ∀ᶠ i in l, integrable (F i) μ)
  (hF : tendsto (λ i, ∫⁻ x, edist (F i x) (f x) ∂μ) l (𝓝 0)) :
  tendsto (λ i, ∫ x, F i x ∂μ) l (𝓝 $ ∫ x, f x ∂μ) :=
begin
  rw [tendsto_iff_norm_tendsto_zero],
  replace hF : tendsto (λ i, ennreal.to_real $ ∫⁻ x, edist (F i x) (f x) ∂μ) l (𝓝 0) :=
    (ennreal.tendsto_to_real zero_ne_top).comp hF,
  refine squeeze_zero_norm' (hFi.mp $ hFi.mono $ λ i hFi hFm, _) hF,
  simp only [norm_norm, ← integral_sub hFi hfi, edist_dist, dist_eq_norm],
  apply norm_integral_le_lintegral_norm
end

/-- Lebesgue dominated convergence theorem provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their integrals. -/
theorem tendsto_integral_of_dominated_convergence {F : ℕ → α → E} {f : α → E} (bound : α → ℝ)
  (F_measurable : ∀ n, ae_measurable (F n) μ)
  (f_measurable : ae_measurable f μ)
  (bound_integrable : integrable bound μ)
  (h_bound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) at_top (𝓝 (f a))) :
  tendsto (λn, ∫ a, F n a ∂μ) at_top (𝓝 $ ∫ a, f a ∂μ) :=
begin
  /- To show `(∫ a, F n a) --> (∫ f)`, suffices to show `∥∫ a, F n a - ∫ f∥ --> 0` -/
  rw tendsto_iff_norm_tendsto_zero,
  /- But `0 ≤ ∥∫ a, F n a - ∫ f∥ = ∥∫ a, (F n a - f a) ∥ ≤ ∫ a, ∥F n a - f a∥, and thus we apply the
    sandwich theorem and prove that `∫ a, ∥F n a - f a∥ --> 0` -/
  have lintegral_norm_tendsto_zero :
    tendsto (λn, ennreal.to_real $ ∫⁻ a, (ennreal.of_real ∥F n a - f a∥) ∂μ) at_top (𝓝 0) :=
  (tendsto_to_real zero_ne_top).comp
    (tendsto_lintegral_norm_of_dominated_convergence
      F_measurable f_measurable bound_integrable.has_finite_integral h_bound h_lim),
  -- Use the sandwich theorem
  refine squeeze_zero (λ n, norm_nonneg _) _ lintegral_norm_tendsto_zero,
  -- Show `∥∫ a, F n a - ∫ f∥ ≤ ∫ a, ∥F n a - f a∥` for all `n`
  { assume n,
    have h₁ : integrable (F n) μ := bound_integrable.mono' (F_measurable n) (h_bound _),
    have h₂ : integrable f μ :=
    ⟨f_measurable, has_finite_integral_of_dominated_convergence
      bound_integrable.has_finite_integral h_bound h_lim⟩,
    rw ← integral_sub h₁ h₂,
    exact norm_integral_le_lintegral_norm _ }
end

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
lemma tendsto_integral_filter_of_dominated_convergence {ι} {l : filter ι}
  {F : ι → α → E} {f : α → E} (bound : α → ℝ)
  (hl_cb : l.is_countably_generated)
  (hF_meas : ∀ᶠ n in l, ae_measurable (F n) μ)
  (f_measurable : ae_measurable f μ)
  (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (bound_integrable : integrable bound μ)
  (h_lim : ∀ᵐ a ∂μ, tendsto (λ n, F n a) l (𝓝 (f a))) :
  tendsto (λn, ∫ a, F n a ∂μ) l (𝓝 $ ∫ a, f a ∂μ) :=
begin
  rw hl_cb.tendsto_iff_seq_tendsto,
  { intros x xl,
    have hxl, { rw tendsto_at_top' at xl, exact xl },
    have h := inter_mem_sets hF_meas h_bound,
    replace h := hxl _ h,
    rcases h with ⟨k, h⟩,
    rw ← tendsto_add_at_top_iff_nat k,
    refine tendsto_integral_of_dominated_convergence _ _ _ _ _ _,
    { exact bound },
    { intro, refine (h _ _).1, exact nat.le_add_left _ _ },
    { assumption },
    { assumption },
    { intro, refine (h _ _).2, exact nat.le_add_left _ _ },
    { filter_upwards [h_lim],
      assume a h_lim,
      apply @tendsto.comp _ _ _ (λn, x (n + k)) (λn, F n a),
      { assumption },
      rw tendsto_add_at_top_iff_nat,
      assumption } },
end

/-- The Bochner integral of a real-valued function `f : α → ℝ` is the difference between the
  integral of the positive part of `f` and the integral of the negative part of `f`.  -/
lemma integral_eq_lintegral_max_sub_lintegral_min {f : α → ℝ} (hf : integrable f μ) :
  ∫ a, f a ∂μ =
  ennreal.to_real (∫⁻ a, (ennreal.of_real $ max (f a) 0) ∂μ) -
  ennreal.to_real (∫⁻ a, (ennreal.of_real $ - min (f a) 0) ∂μ) :=
let f₁ : α →₁[μ] ℝ := l1.of_fun f hf in
-- Go to the `L¹` space
have eq₁ : ennreal.to_real (∫⁻ a, (ennreal.of_real $ max (f a) 0) ∂μ) = ∥l1.pos_part f₁∥ :=
begin
  rw l1.norm_eq_norm_to_fun,
  congr' 1,
  apply lintegral_congr_ae,
  filter_upwards [l1.pos_part_to_fun f₁, l1.to_fun_of_fun f hf],
  assume a h₁ h₂,
  rw [h₁, h₂, real.norm_eq_abs, abs_of_nonneg],
  exact le_max_right _ _
end,
-- Go to the `L¹` space
have eq₂ : ennreal.to_real (∫⁻ a, (ennreal.of_real $ -min (f a) 0) ∂μ)  = ∥l1.neg_part f₁∥ :=
begin
  rw l1.norm_eq_norm_to_fun,
  congr' 1,
  apply lintegral_congr_ae,
  filter_upwards [l1.neg_part_to_fun_eq_min f₁, l1.to_fun_of_fun f hf],
  assume a h₁ h₂,
  rw [h₁, h₂, real.norm_eq_abs, abs_of_nonneg],
  rw [neg_nonneg],
  exact min_le_right _ _
end,
begin
  rw [eq₁, eq₂, integral, dif_pos],
  exact l1.integral_eq_norm_pos_part_sub _
end

lemma integral_eq_lintegral_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfm : ae_measurable f μ) :
  ∫ a, f a ∂μ = ennreal.to_real (∫⁻ a, (ennreal.of_real $ f a) ∂μ) :=
begin
  by_cases hfi : integrable f μ,
  { rw integral_eq_lintegral_max_sub_lintegral_min hfi,
    have h_min : ∫⁻ a, ennreal.of_real (-min (f a) 0) ∂μ = 0,
    { rw lintegral_eq_zero_iff',
      { refine hf.mono _,
        simp only [pi.zero_apply],
        assume a h,
        simp only [min_eq_right h, neg_zero, ennreal.of_real_zero] },
      { exact measurable_of_real.comp_ae_measurable (measurable_id.neg.comp_ae_measurable
          $ hfm.min ae_measurable_const) } },
    have h_max : ∫⁻ a, ennreal.of_real (max (f a) 0) ∂μ = ∫⁻ a, ennreal.of_real (f a) ∂μ,
    { refine lintegral_congr_ae (hf.mono (λ a h, _)),
      rw [pi.zero_apply] at h,
      rw max_eq_left h },
    rw [h_min, h_max, zero_to_real, _root_.sub_zero] },
  { rw integral_undef hfi,
    simp_rw [integrable, hfm, has_finite_integral_iff_norm, lt_top_iff_ne_top, ne.def, true_and,
      not_not] at hfi,
    have : ∫⁻ (a : α), ennreal.of_real (f a) ∂μ = ∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ,
    { refine lintegral_congr_ae (hf.mono $ assume a h, _),
      rw [real.norm_eq_abs, abs_of_nonneg h] },
    rw [this, hfi], refl }
end

lemma integral_nonneg_of_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ a, f a ∂μ :=
begin
  by_cases hfm : ae_measurable f μ,
  { rw integral_eq_lintegral_of_nonneg_ae hf hfm, exact to_real_nonneg },
  { rw integral_non_ae_measurable hfm }
end

lemma lintegral_coe_eq_integral (f : α → ℝ≥0) (hfi : integrable (λ x, (f x : real)) μ) :
  ∫⁻ a, f a ∂μ = ennreal.of_real ∫ a, f a ∂μ :=
begin
  simp_rw [integral_eq_lintegral_of_nonneg_ae (eventually_of_forall (λ x, (f x).coe_nonneg))
    hfi.ae_measurable, ← ennreal.coe_nnreal_eq], rw [ennreal.of_real_to_real],
  rw [← lt_top_iff_ne_top], convert hfi.has_finite_integral, ext1 x, rw [real.nnnorm_coe_eq_self]
end

lemma integral_to_real {f : α → ennreal} (hfm : ae_measurable f μ) (hf : ∀ᵐ x ∂μ, f x < ⊤) :
  ∫ a, (f a).to_real ∂μ = (∫⁻ a, f a ∂μ).to_real :=
begin
  rw [integral_eq_lintegral_of_nonneg_ae _ hfm.to_real],
  { rw lintegral_congr_ae, refine hf.mp (eventually_of_forall _),
    intros x hx, rw [lt_top_iff_ne_top] at hx, simp [hx] },
  { exact (eventually_of_forall $ λ x, ennreal.to_real_nonneg) }
end

lemma integral_nonneg {f : α → ℝ} (hf : 0 ≤ f) : 0 ≤ ∫ a, f a ∂μ :=
integral_nonneg_of_ae $ eventually_of_forall hf

lemma integral_nonpos_of_ae {f : α → ℝ} (hf : f ≤ᵐ[μ] 0) : ∫ a, f a ∂μ ≤ 0 :=
begin
  have hf : 0 ≤ᵐ[μ] (-f) := hf.mono (assume a h, by rwa [pi.neg_apply, pi.zero_apply, neg_nonneg]),
  have : 0 ≤ ∫ a, -f a ∂μ := integral_nonneg_of_ae hf,
  rwa [integral_neg, neg_nonneg] at this,
end

lemma integral_nonpos {f : α → ℝ} (hf : f ≤ 0) : ∫ a, f a ∂μ ≤ 0 :=
integral_nonpos_of_ae $ eventually_of_forall hf

lemma integral_eq_zero_iff_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : integrable f μ) :
  ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
by simp_rw [integral_eq_lintegral_of_nonneg_ae hf hfi.1, ennreal.to_real_eq_zero_iff,
  lintegral_eq_zero_iff' (ennreal.measurable_of_real.comp_ae_measurable hfi.1),
  ← ennreal.not_lt_top, ← has_finite_integral_iff_of_real hf, hfi.2, not_true, or_false,
  ← hf.le_iff_eq, filter.eventually_eq, filter.eventually_le, (∘), pi.zero_apply,
  ennreal.of_real_eq_zero]

lemma integral_eq_zero_iff_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : integrable f μ) :
  ∫ x, f x ∂μ = 0 ↔ f =ᵐ[μ] 0 :=
integral_eq_zero_iff_of_nonneg_ae (eventually_of_forall hf) hfi

lemma integral_pos_iff_support_of_nonneg_ae {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hfi : integrable f μ) :
  (0 < ∫ x, f x ∂μ) ↔ 0 < μ (function.support f) :=
by simp_rw [(integral_nonneg_of_ae hf).lt_iff_ne, pos_iff_ne_zero, ne.def, @eq_comm ℝ 0,
  integral_eq_zero_iff_of_nonneg_ae hf hfi, filter.eventually_eq, ae_iff, pi.zero_apply,
  function.support]

lemma integral_pos_iff_support_of_nonneg {f : α → ℝ} (hf : 0 ≤ f) (hfi : integrable f μ) :
  (0 < ∫ x, f x ∂μ) ↔ 0 < μ (function.support f) :=
integral_pos_iff_support_of_nonneg_ae (eventually_of_forall hf) hfi

section normed_group
variables {H : Type*} [normed_group H] [second_countable_topology H] [measurable_space H]
          [borel_space H]

lemma l1.norm_eq_integral_norm (f : α →₁[μ] H) : ∥f∥ = ∫ a, ∥f a∥ ∂μ :=
by rw [l1.norm_eq_norm_to_fun,
       integral_eq_lintegral_of_nonneg_ae (eventually_of_forall $ by simp [norm_nonneg])
       (continuous_norm.measurable.comp_ae_measurable f.ae_measurable)]

lemma l1.norm_of_fun_eq_integral_norm {f : α → H} (hf : integrable f μ) :
  ∥ l1.of_fun f hf ∥ = ∫ a, ∥f a∥ ∂μ :=
begin
  rw l1.norm_eq_integral_norm,
  refine integral_congr_ae _,
  apply (l1.to_fun_of_fun f hf).mono,
  intros a ha,
  simp [ha]
end

end normed_group

lemma integral_mono_ae {f g : α → ℝ} (hf : integrable f μ) (hg : integrable g μ) (h : f ≤ᵐ[μ] g) :
  ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
le_of_sub_nonneg $ integral_sub hg hf ▸ integral_nonneg_of_ae $ h.mono (λ a, sub_nonneg_of_le)

lemma integral_mono {f g : α → ℝ} (hf : integrable f μ) (hg : integrable g μ) (h : f ≤ g) :
  ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
integral_mono_ae hf hg $ eventually_of_forall h

lemma integral_mono_of_nonneg {f g : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hgi : integrable g μ)
  (h : f ≤ᵐ[μ] g) : ∫ a, f a ∂μ ≤ ∫ a, g a ∂μ :=
begin
  by_cases hfm : ae_measurable f μ,
  { refine integral_mono_ae ⟨hfm, _⟩ hgi h,
    refine (hgi.has_finite_integral.mono $ h.mp $ hf.mono $ λ x hf hfg, _),
    simpa [real.norm_eq_abs, abs_of_nonneg hf, abs_of_nonneg (le_trans hf hfg)] },
  { rw [integral_non_ae_measurable hfm],
    exact integral_nonneg_of_ae (hf.trans h) }
end

lemma norm_integral_le_integral_norm (f : α → E) : ∥(∫ a, f a ∂μ)∥ ≤ ∫ a, ∥f a∥ ∂μ :=
have le_ae : ∀ᵐ a ∂μ, 0 ≤ ∥f a∥ := eventually_of_forall (λa, norm_nonneg _),
classical.by_cases
( λh : ae_measurable f μ,
  calc ∥∫ a, f a ∂μ∥ ≤ ennreal.to_real (∫⁻ a, (ennreal.of_real ∥f a∥) ∂μ) :
      norm_integral_le_lintegral_norm _
    ... = ∫ a, ∥f a∥ ∂μ : (integral_eq_lintegral_of_nonneg_ae le_ae $ ae_measurable.norm h).symm )
( λh : ¬ae_measurable f μ,
  begin
    rw [integral_non_ae_measurable h, norm_zero],
    exact integral_nonneg_of_ae le_ae
  end )

lemma norm_integral_le_of_norm_le {f : α → E} {g : α → ℝ} (hg : integrable g μ)
  (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ g x) : ∥∫ x, f x ∂μ∥ ≤ ∫ x, g x ∂μ :=
calc ∥∫ x, f x ∂μ∥ ≤ ∫ x, ∥f x∥ ∂μ : norm_integral_le_integral_norm f
               ... ≤ ∫ x, g x ∂μ   :
  integral_mono_of_nonneg (eventually_of_forall $ λ x, norm_nonneg _) hg h

lemma integral_finset_sum {ι} (s : finset ι) {f : ι → α → E} (hf : ∀ i, integrable (f i) μ) :
  ∫ a, ∑ i in s, f i a ∂μ = ∑ i in s, ∫ a, f i a ∂μ :=
begin
  refine finset.induction_on s _ _,
  { simp only [integral_zero, finset.sum_empty] },
  { assume i s his ih,
    simp only [his, finset.sum_insert, not_false_iff],
    rw [integral_add (hf _) (integrable_finset_sum s hf), ih] }
end

lemma simple_func.integral_eq_integral (f : α →ₛ E) (hfi : integrable f μ) :
  f.integral μ = ∫ x, f x ∂μ :=
begin
  rw [integral_eq f hfi, ← l1.simple_func.of_simple_func_eq_of_fun,
    l1.simple_func.integral_l1_eq_integral, l1.simple_func.integral_eq_integral],
  exact simple_func.integral_congr hfi (l1.simple_func.to_simple_func_of_simple_func _ _).symm
end

@[simp] lemma integral_const (c : E) : ∫ x : α, c ∂μ = (μ univ).to_real • c :=
begin
  by_cases hμ : μ univ < ⊤,
  { haveI : finite_measure μ := ⟨hμ⟩,
    calc ∫ x : α, c ∂μ = (simple_func.const α c).integral μ :
      ((simple_func.const α c).integral_eq_integral (integrable_const _)).symm
    ... = _ : _,
    rw [simple_func.integral],
    by_cases ha : nonempty α,
    { resetI, simp [preimage_const_of_mem] },
    { simp [μ.eq_zero_of_not_nonempty ha] } },
  { by_cases hc : c = 0,
    { simp [hc, integral_zero] },
    { have : ¬integrable (λ x : α, c) μ,
      { simp only [integrable_const_iff, not_or_distrib],
        exact ⟨hc, hμ⟩ },
      simp only [not_lt, top_le_iff] at hμ,
      simp [integral_undef, *] } }
end

lemma norm_integral_le_of_norm_le_const [finite_measure μ] {f : α → E} {C : ℝ}
  (h : ∀ᵐ x ∂μ, ∥f x∥ ≤ C) :
  ∥∫ x, f x ∂μ∥ ≤ C * (μ univ).to_real :=
calc ∥∫ x, f x ∂μ∥ ≤ ∫ x, C ∂μ : norm_integral_le_of_norm_le (integrable_const C) h
               ... = C * (μ univ).to_real : by rw [integral_const, smul_eq_mul, mul_comm]

lemma tendsto_integral_approx_on_univ_of_measurable
  {f : α → E} (fmeas : measurable f) (hf : integrable f μ) :
  tendsto (λ n, (simple_func.approx_on f fmeas univ 0 trivial n).integral μ) at_top
    (𝓝 $ ∫ x, f x ∂μ) :=
begin
  have : tendsto (λ n, ∫ x, simple_func.approx_on f fmeas univ 0 trivial n x ∂μ)
    at_top (𝓝 $ ∫ x, f x ∂μ) :=
    tendsto_integral_of_l1 _ hf
      (eventually_of_forall $ simple_func.integrable_approx_on_univ fmeas hf)
      (simple_func.tendsto_approx_on_univ_l1_edist fmeas hf),
  simpa only [simple_func.integral_eq_integral, simple_func.integrable_approx_on_univ fmeas hf]
end

variable {ν : measure α}

private lemma integral_add_measure_of_measurable
  {f : α → E} (fmeas : measurable f) (hμ : integrable f μ) (hν : integrable f ν) :
  ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν :=
begin
  have hfi := hμ.add_measure hν,
  refine tendsto_nhds_unique (tendsto_integral_approx_on_univ_of_measurable fmeas hfi) _,
  simpa only [simple_func.integral_add_measure _
    (simple_func.integrable_approx_on_univ fmeas hfi _)]
    using (tendsto_integral_approx_on_univ_of_measurable fmeas hμ).add
      (tendsto_integral_approx_on_univ_of_measurable fmeas hν)
end

lemma integral_add_measure {f : α → E} (hμ : integrable f μ) (hν : integrable f ν) :
  ∫ x, f x ∂(μ + ν) = ∫ x, f x ∂μ + ∫ x, f x ∂ν :=
begin
  have h : ae_measurable f (μ + ν) := hμ.ae_measurable.add_measure hν.ae_measurable,
  let g := h.mk f,
  have A : f =ᵐ[μ + ν] g := h.ae_eq_mk,
  have B : f =ᵐ[μ] g := A.filter_mono (ae_mono (measure.le_add_right (le_refl μ))),
  have C : f =ᵐ[ν] g := A.filter_mono (ae_mono (measure.le_add_left (le_refl ν))),
  calc ∫ x, f x ∂(μ + ν) = ∫ x, g x ∂(μ + ν) : integral_congr_ae A
  ... = ∫ x, g x ∂μ + ∫ x, g x ∂ν :
    integral_add_measure_of_measurable h.measurable_mk ((integrable_congr B).1 hμ)
      ((integrable_congr C).1 hν)
  ... = ∫ x, f x ∂μ + ∫ x, f x ∂ν :
    by { congr' 1, { exact integral_congr_ae B.symm }, { exact integral_congr_ae C.symm } }
end

@[simp] lemma integral_zero_measure (f : α → E) : ∫ x, f x ∂0 = 0 :=
norm_le_zero_iff.1 $ le_trans (norm_integral_le_lintegral_norm f) $ by simp

private lemma integral_smul_measure_aux {f : α → E} {c : ennreal}
  (h0 : 0 < c) (hc : c < ⊤) (fmeas : measurable f) (hfi : integrable f μ) :
  ∫ x, f x ∂(c • μ) = c.to_real • ∫ x, f x ∂μ :=
begin
  refine tendsto_nhds_unique _
    (tendsto_const_nhds.smul (tendsto_integral_approx_on_univ_of_measurable fmeas hfi)),
  convert tendsto_integral_approx_on_univ_of_measurable fmeas (hfi.smul_measure hc),
  simp only [simple_func.integral, measure.smul_apply, finset.smul_sum, smul_smul,
    ennreal.to_real_mul]
end

@[simp] lemma integral_smul_measure (f : α → E) (c : ennreal) :
  ∫ x, f x ∂(c • μ) = c.to_real • ∫ x, f x ∂μ :=
begin
  -- First we consider “degenerate” cases:
  -- `c = 0`
  rcases (zero_le c).eq_or_lt with rfl|h0, { simp },
  -- `f` is not almost everywhere measurable
  by_cases hfm : ae_measurable f μ, swap,
  { have : ¬ (ae_measurable f (c • μ)), by simpa [ne_of_gt h0] using hfm,
    simp [integral_non_ae_measurable, hfm, this] },
  -- `c = ⊤`
  rcases (le_top : c ≤ ⊤).eq_or_lt with rfl|hc,
  { rw [ennreal.top_to_real, zero_smul],
    by_cases hf : f =ᵐ[μ] 0,
    { have : f =ᵐ[⊤ • μ] 0 := ae_smul_measure hf ⊤,
      exact integral_eq_zero_of_ae this },
    { apply integral_undef,
      rw [integrable, has_finite_integral, iff_true_intro (hfm.smul_measure ⊤), true_and,
          lintegral_smul_measure, top_mul, if_neg],
      { apply lt_irrefl },
      { rw [lintegral_eq_zero_iff' hfm.ennnorm],
        refine λ h, hf (h.mono $ λ x, _),
        simp } } },
  -- `f` is not integrable and `0 < c < ⊤`
  by_cases hfi : integrable f μ, swap,
  { rw [integral_undef hfi, smul_zero],
    refine integral_undef (mt (λ h, _) hfi),
    convert h.smul_measure (ennreal.inv_lt_top.2 h0),
    rw [smul_smul, ennreal.inv_mul_cancel (ne_of_gt h0) (ne_of_lt hc), one_smul] },
  -- Main case: `0 < c < ⊤`, `f` is almost everywhere measurable and integrable
  let g := hfm.mk f,
  calc ∫ x, f x ∂(c • μ) = ∫ x, g x ∂(c • μ) : integral_congr_ae $ ae_smul_measure hfm.ae_eq_mk c
  ... = c.to_real • ∫ x, g x ∂μ :
    integral_smul_measure_aux h0 hc hfm.measurable_mk $ hfi.congr hfm.ae_eq_mk
  ... = c.to_real • ∫ x, f x ∂μ :
    by { congr' 1, exact integral_congr_ae (hfm.ae_eq_mk.symm) }
end

lemma integral_map_of_measurable {β} [measurable_space β] {φ : α → β} (hφ : measurable φ)
  {f : β → E} (hfm : measurable f) :
  ∫ y, f y ∂(measure.map φ μ) = ∫ x, f (φ x) ∂μ :=
begin
  by_cases hfi : integrable f (measure.map φ μ), swap,
  { rw [integral_undef hfi, integral_undef],
    rwa [← integrable_map_measure hfm.ae_measurable hφ] },
  refine tendsto_nhds_unique (tendsto_integral_approx_on_univ_of_measurable hfm hfi) _,
  convert tendsto_integral_approx_on_univ_of_measurable (hfm.comp hφ)
    ((integrable_map_measure hfm.ae_measurable hφ).1 hfi),
  ext1 i,
  simp only [simple_func.approx_on_comp, simple_func.integral, measure.map_apply, hφ,
    simple_func.is_measurable_preimage, ← preimage_comp, simple_func.coe_comp],
  refine (finset.sum_subset (simple_func.range_comp_subset_range _ hφ) (λ y _ hy, _)).symm,
  rw [simple_func.mem_range, ← set.preimage_singleton_eq_empty, simple_func.coe_comp] at hy,
  simp [hy]
end

lemma integral_map {β} [measurable_space β] {φ : α → β} (hφ : measurable φ)
  {f : β → E} (hfm : ae_measurable f (measure.map φ μ)) :
  ∫ y, f y ∂(measure.map φ μ) = ∫ x, f (φ x) ∂μ :=
let g := hfm.mk f in calc
∫ y, f y ∂(measure.map φ μ) = ∫ y, g y ∂(measure.map φ μ) : integral_congr_ae hfm.ae_eq_mk
... = ∫ x, g (φ x) ∂μ : integral_map_of_measurable hφ hfm.measurable_mk
... = ∫ x, f (φ x) ∂μ : integral_congr_ae $ ae_eq_comp hφ (hfm.ae_eq_mk).symm

lemma integral_dirac' (f : α → E) (a : α) (hfm : measurable f) :
  ∫ x, f x ∂(measure.dirac a) = f a :=
calc ∫ x, f x ∂(measure.dirac a) = ∫ x, f a ∂(measure.dirac a) :
  integral_congr_ae $ ae_eq_dirac' hfm
... = f a : by simp [measure.dirac_apply_of_mem]

lemma integral_dirac [measurable_singleton_class α] (f : α → E) (a : α) :
  ∫ x, f x ∂(measure.dirac a) = f a :=
calc ∫ x, f x ∂(measure.dirac a) = ∫ x, f a ∂(measure.dirac a) :
  integral_congr_ae $ ae_eq_dirac f
... = f a : by simp [measure.dirac_apply_of_mem]

end properties

mk_simp_attribute integral_simps "Simp set for integral rules."

attribute [integral_simps] integral_neg integral_smul l1.integral_add l1.integral_sub
  l1.integral_smul l1.integral_neg

attribute [irreducible] integral l1.integral

end measure_theory
