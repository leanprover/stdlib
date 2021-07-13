/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import analysis.normed_space.multilinear

/-!
# Continuous linear maps

This file defines a class stating that a map between normed vector spaces is (bi)linear and
continuous.
Instead of asking for continuity, the definition takes the equivalent condition that `∥f x∥` is
bounded by a multiple of `∥x∥`. Hence the "bounded" in the name refers to `∥f x∥/∥x∥` rather than
`∥f x∥` itself.

## Main declarations

* `is_bounded_linear_map`: Class stating that a map `f : E → F` is linear and continuous, but
  through the simpler to provide statement that `∥ f x ∥` is bounded by a multiple of `∥ x ∥`.
  Effectively an unbundled version of `continuous_linear_map`, albeit the name disparity.
* `is_bounded_bilinear_map`! Class stating that a map `f : E × F → G` is bilinear and continuous,
  but through the simpler to provide statement that `∥f (x, y)∥` is bounded by a multiple of
  `∥x∥ * ∥y∥`
* `is_bounded_bilinear_map.linear_deriv`: Derivative of a continuous bilinear map as a linear map.
* `is_bounded_bilinear_map.deriv`: Derivative of a continuous bilinear map as a continuous linear
  map. The proof that it is indeed the derivative is `is_bounded_bilinear_map.has_fderiv_at` in
  `analysis.calculus.fderiv`.
* `linear_map.norm_apply_of_isometry`: A linear isometry preserves the norm.

## Notes

The main use of this file is `is_bounded_bilinear_map`. The file `analysis.normed_space.multilinear`
already expands the theory of multilinear maps, but the `2`-variables case is sufficiently simpler
to currently deserve its own treatment.

`is_bounded_linear_map` should in most cases be replaced by a bundled `continuous_linear_map`. The
latter is developed in `analysis.normed_space.operator_norm`.
-/

noncomputable theory
open_locale classical big_operators topological_space

open filter (tendsto) metric

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
          {E : Type*} [normed_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_group F] [normed_space 𝕜 F]
          {G : Type*} [normed_group G] [normed_space 𝕜 G]


/-- A function `f` satisfies `is_bounded_linear_map 𝕜 f` if it is linear and satisfies the
inequality `∥ f x ∥ ≤ M * ∥ x ∥` for some positive constant `M`. -/
structure is_bounded_linear_map (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F] (f : E → F)
  extends is_linear_map 𝕜 f : Prop :=
(bound : ∃ M, 0 < M ∧ ∀ x : E, ∥ f x ∥ ≤ M * ∥ x ∥)

lemma is_linear_map.with_bound
  {f : E → F} (hf : is_linear_map 𝕜 f) (M : ℝ) (h : ∀ x : E, ∥ f x ∥ ≤ M * ∥ x ∥) :
  is_bounded_linear_map 𝕜 f :=
⟨ hf, classical.by_cases
  (assume : M ≤ 0, ⟨1, zero_lt_one, λ x,
    (h x).trans $ mul_le_mul_of_nonneg_right (this.trans zero_le_one) (norm_nonneg x)⟩)
  (assume : ¬ M ≤ 0, ⟨M, lt_of_not_ge this, h⟩)⟩

/-- A continuous linear map satisfies `is_bounded_linear_map` -/
lemma continuous_linear_map.is_bounded_linear_map (f : E →L[𝕜] F) : is_bounded_linear_map 𝕜 f :=
{ bound := f.bound,
  ..f.to_linear_map.is_linear }

namespace is_bounded_linear_map

/-- Construct a linear map from a function `f` satisfying `is_bounded_linear_map 𝕜 f`. -/
def to_linear_map (f : E → F) (h : is_bounded_linear_map 𝕜 f) : E →ₗ[𝕜] F :=
(is_linear_map.mk' _ h.to_is_linear_map)

/-- Construct a continuous linear map from is_bounded_linear_map -/
def to_continuous_linear_map {f : E → F} (hf : is_bounded_linear_map 𝕜 f) : E →L[𝕜] F :=
{ cont := let ⟨C, Cpos, hC⟩ := hf.bound in linear_map.continuous_of_bound _ C hC,
  ..to_linear_map f hf}

lemma zero : is_bounded_linear_map 𝕜 (λ (x:E), (0:F)) :=
(0 : E →ₗ F).is_linear.with_bound 0 $ by simp [le_refl]

lemma id : is_bounded_linear_map 𝕜 (λ (x:E), x) :=
linear_map.id.is_linear.with_bound 1 $ by simp [le_refl]

lemma fst : is_bounded_linear_map 𝕜 (λ x : E × F, x.1) :=
begin
  refine (linear_map.fst 𝕜 E F).is_linear.with_bound 1 (λ x, _),
  rw one_mul,
  exact le_max_left _ _
end

lemma snd : is_bounded_linear_map 𝕜 (λ x : E × F, x.2) :=
begin
  refine (linear_map.snd 𝕜 E F).is_linear.with_bound 1 (λ x, _),
  rw one_mul,
  exact le_max_right _ _
end

variables {f g : E → F}

lemma smul (c : 𝕜) (hf : is_bounded_linear_map 𝕜 f) :
  is_bounded_linear_map 𝕜 (c • f) :=
let ⟨hlf, M, hMp, hM⟩ := hf in
(c • hlf.mk' f).is_linear.with_bound (∥c∥ * M) $ λ x,
  calc ∥c • f x∥ = ∥c∥ * ∥f x∥ : norm_smul c (f x)
  ... ≤ ∥c∥ * (M * ∥x∥)        : mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  ... = (∥c∥ * M) * ∥x∥        : (mul_assoc _ _ _).symm

lemma neg (hf : is_bounded_linear_map 𝕜 f) :
  is_bounded_linear_map 𝕜 (λ e, -f e) :=
begin
  rw show (λ e, -f e) = (λ e, (-1 : 𝕜) • f e), { funext, simp },
  exact smul (-1) hf
end

lemma add (hf : is_bounded_linear_map 𝕜 f) (hg : is_bounded_linear_map 𝕜 g) :
  is_bounded_linear_map 𝕜 (λ e, f e + g e) :=
let ⟨hlf, Mf, hMfp, hMf⟩ := hf in
let ⟨hlg, Mg, hMgp, hMg⟩ := hg in
(hlf.mk' _ + hlg.mk' _).is_linear.with_bound (Mf + Mg) $ λ x,
  calc ∥f x + g x∥ ≤ Mf * ∥x∥ + Mg * ∥x∥ : norm_add_le_of_le (hMf x) (hMg x)
               ... ≤ (Mf + Mg) * ∥x∥     : by rw add_mul

lemma sub (hf : is_bounded_linear_map 𝕜 f) (hg : is_bounded_linear_map 𝕜 g) :
  is_bounded_linear_map 𝕜 (λ e, f e - g e) :=
by simpa [sub_eq_add_neg] using add hf (neg hg)

lemma comp {g : F → G}
  (hg : is_bounded_linear_map 𝕜 g) (hf : is_bounded_linear_map 𝕜 f) :
  is_bounded_linear_map 𝕜 (g ∘ f) :=
(hg.to_continuous_linear_map.comp hf.to_continuous_linear_map).is_bounded_linear_map

protected lemma tendsto (x : E) (hf : is_bounded_linear_map 𝕜 f) :
  tendsto f (𝓝 x) (𝓝 (f x)) :=
let ⟨hf, M, hMp, hM⟩ := hf in
tendsto_iff_norm_tendsto_zero.2 $
  squeeze_zero (λ e, norm_nonneg _)
    (λ e,
      calc ∥f e - f x∥ = ∥hf.mk' f (e - x)∥ : by rw (hf.mk' _).map_sub e x; refl
                   ... ≤ M * ∥e - x∥        : hM (e - x))
    (suffices tendsto (λ (e : E), M * ∥e - x∥) (𝓝 x) (𝓝 (M * 0)), by simpa,
      tendsto_const_nhds.mul (tendsto_norm_sub_self _))

lemma continuous (hf : is_bounded_linear_map 𝕜 f) : continuous f :=
continuous_iff_continuous_at.2 $ λ _, hf.tendsto _

lemma lim_zero_bounded_linear_map (hf : is_bounded_linear_map 𝕜 f) :
  tendsto f (𝓝 0) (𝓝 0) :=
(hf.1.mk' _).map_zero ▸ continuous_iff_continuous_at.1 hf.continuous 0

section
open asymptotics filter

theorem is_O_id {f : E → F} (h : is_bounded_linear_map 𝕜 f) (l : filter E) :
  is_O f (λ x, x) l :=
let ⟨M, hMp, hM⟩ := h.bound in is_O.of_bound _ (mem_sets_of_superset univ_mem_sets (λ x _, hM x))

theorem is_O_comp {E : Type*} {g : F → G} (hg : is_bounded_linear_map 𝕜 g)
  {f : E → F} (l : filter E) : is_O (λ x', g (f x')) f l :=
(hg.is_O_id ⊤).comp_tendsto le_top

theorem is_O_sub {f : E → F} (h : is_bounded_linear_map 𝕜 f)
  (l : filter E) (x : E) : is_O (λ x', f (x' - x)) (λ x', x' - x) l :=
is_O_comp h l

end

end is_bounded_linear_map

section
variables {ι : Type*} [decidable_eq ι] [fintype ι]

/-- Taking the cartesian product of two continuous multilinear maps
is a bounded linear operation. -/
lemma is_bounded_linear_map_prod_multilinear
  {E : ι → Type*} [∀ i, normed_group (E i)] [∀ i, normed_space 𝕜 (E i)] :
  is_bounded_linear_map 𝕜
  (λ p : (continuous_multilinear_map 𝕜 E F) × (continuous_multilinear_map 𝕜 E G), p.1.prod p.2) :=
{ map_add := λ p₁ p₂, by { ext1 m, refl },
  map_smul := λ c p, by { ext1 m, refl },
  bound := ⟨1, zero_lt_one, λ p, begin
    rw one_mul,
    apply continuous_multilinear_map.op_norm_le_bound _ (norm_nonneg _) (λ m, _),
    rw [continuous_multilinear_map.prod_apply, norm_prod_le_iff],
    split,
    { exact (p.1.le_op_norm m).trans
        (mul_le_mul_of_nonneg_right (norm_fst_le p) (finset.prod_nonneg (λ i hi, norm_nonneg _))) },
    { exact (p.2.le_op_norm m).trans
        (mul_le_mul_of_nonneg_right (norm_snd_le p) (finset.prod_nonneg (λ i hi, norm_nonneg _))) },
  end⟩ }

/-- Given a fixed continuous linear map `g`, associating to a continuous multilinear map `f` the
continuous multilinear map `f (g m₁, ..., g mₙ)` is a bounded linear operation. -/
lemma is_bounded_linear_map_continuous_multilinear_map_comp_linear (g : G →L[𝕜] E) :
  is_bounded_linear_map 𝕜 (λ f : continuous_multilinear_map 𝕜 (λ (i : ι), E) F,
    f.comp_continuous_linear_map (λ _, g)) :=
begin
  refine is_linear_map.with_bound ⟨λ f₁ f₂, by { ext m, refl }, λ c f, by { ext m, refl }⟩
    (∥g∥ ^ (fintype.card ι)) (λ f, _),
  apply continuous_multilinear_map.op_norm_le_bound _ _ (λ m, _),
  { apply_rules [mul_nonneg, pow_nonneg, norm_nonneg] },
  calc ∥f (g ∘ m)∥ ≤
    ∥f∥ * ∏ i, ∥g (m i)∥ : f.le_op_norm _
    ... ≤ ∥f∥ * ∏ i, (∥g∥ * ∥m i∥) : begin
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _),
      exact finset.prod_le_prod (λ i hi, norm_nonneg _) (λ i hi, g.le_op_norm _)
    end
    ... = ∥g∥ ^ fintype.card ι * ∥f∥ * ∏ i, ∥m i∥ :
      by { simp [finset.prod_mul_distrib, finset.card_univ], ring }
end

end

section bilinear_map

variable (𝕜)

/-- A map `f : E × F → G` satisfies `is_bounded_bilinear_map 𝕜 f` if it is bilinear and
continuous. -/
structure is_bounded_bilinear_map (f : E × F → G) : Prop :=
(add_left   : ∀ (x₁ x₂ : E) (y : F), f (x₁ + x₂, y) = f (x₁, y) + f (x₂, y))
(smul_left  : ∀ (c : 𝕜) (x : E) (y : F), f (c • x, y) = c • f (x, y))
(add_right  : ∀ (x : E) (y₁ y₂ : F), f (x, y₁ + y₂) = f (x, y₁) + f (x, y₂))
(smul_right : ∀ (c : 𝕜) (x : E) (y : F), f (x, c • y) = c • f (x,y))
(bound      : ∃ C > 0, ∀ (x : E) (y : F), ∥f (x, y)∥ ≤ C * ∥x∥ * ∥y∥)

variable {𝕜}
variable {f : E × F → G}

lemma continuous_linear_map.is_bounded_bilinear_map (f : E →L[𝕜] F →L[𝕜] G) :
  is_bounded_bilinear_map 𝕜 (λ x : E × F, f x.1 x.2) :=
{ add_left := λ x₁ x₂ y, by rw [f.map_add, continuous_linear_map.add_apply],
  smul_left := λ c x y, by rw [f.map_smul _, continuous_linear_map.smul_apply],
  add_right := λ x, (f x).map_add,
  smul_right := λ c x y, (f x).map_smul c y,
  bound := ⟨max ∥f∥ 1, zero_lt_one.trans_le (le_max_right _ _),
    λ x y, (f.le_op_norm₂ x y).trans $
      by apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, le_max_left]⟩ }

protected lemma is_bounded_bilinear_map.is_O (h : is_bounded_bilinear_map 𝕜 f) :
  asymptotics.is_O f (λ p : E × F, ∥p.1∥ * ∥p.2∥) ⊤ :=
let ⟨C, Cpos, hC⟩ := h.bound in asymptotics.is_O.of_bound _ $
filter.eventually_of_forall $ λ ⟨x, y⟩, by simpa [mul_assoc] using hC x y

lemma is_bounded_bilinear_map.is_O_comp {α : Type*} (H : is_bounded_bilinear_map 𝕜 f)
  {g : α → E} {h : α → F} {l : filter α} :
  asymptotics.is_O (λ x, f (g x, h x)) (λ x, ∥g x∥ * ∥h x∥) l :=
H.is_O.comp_tendsto le_top

protected lemma is_bounded_bilinear_map.is_O' (h : is_bounded_bilinear_map 𝕜 f) :
  asymptotics.is_O f (λ p : E × F, ∥p∥ * ∥p∥) ⊤ :=
h.is_O.trans (asymptotics.is_O_fst_prod'.norm_norm.mul asymptotics.is_O_snd_prod'.norm_norm)

lemma is_bounded_bilinear_map.map_sub_left (h : is_bounded_bilinear_map 𝕜 f) {x y : E} {z : F} :
  f (x - y, z) = f (x, z) - f(y, z) :=
calc f (x - y, z) = f (x + (-1 : 𝕜) • y, z) : by simp [sub_eq_add_neg]
... = f (x, z) + (-1 : 𝕜) • f (y, z) : by simp only [h.add_left, h.smul_left]
... = f (x, z) - f (y, z) : by simp [sub_eq_add_neg]

lemma is_bounded_bilinear_map.map_sub_right (h : is_bounded_bilinear_map 𝕜 f) {x : E} {y z : F} :
  f (x, y - z) = f (x, y) - f (x, z) :=
calc f (x, y - z) = f (x, y + (-1 : 𝕜) • z) : by simp [sub_eq_add_neg]
... = f (x, y) + (-1 : 𝕜) • f (x, z) : by simp only [h.add_right, h.smul_right]
... = f (x, y) - f (x, z) : by simp [sub_eq_add_neg]

lemma is_bounded_bilinear_map.is_bounded_linear_map_left (h : is_bounded_bilinear_map 𝕜 f) (y : F) :
  is_bounded_linear_map 𝕜 (λ x, f (x, y)) :=
{ map_add  := λ x x', h.add_left _ _ _,
  map_smul := λ c x, h.smul_left _ _ _,
  bound    := begin
    rcases h.bound with ⟨C, C_pos, hC⟩,
    refine ⟨C * (∥y∥ + 1), mul_pos C_pos (lt_of_lt_of_le (zero_lt_one) (by simp)), λ x, _⟩,
    have : ∥y∥ ≤ ∥y∥ + 1, by simp [zero_le_one],
    calc ∥f (x, y)∥ ≤ C * ∥x∥ * ∥y∥ : hC x y
    ... ≤ C * ∥x∥ * (∥y∥ + 1) :
      by apply_rules [norm_nonneg, mul_le_mul_of_nonneg_left, le_of_lt C_pos, mul_nonneg]
    ... = C * (∥y∥ + 1) * ∥x∥ : by ring
  end }

lemma is_bounded_bilinear_map.is_bounded_linear_map_right
  (h : is_bounded_bilinear_map 𝕜 f) (x : E) :
  is_bounded_linear_map 𝕜 (λ y, f (x, y)) :=
{ map_add  := λ y y', h.add_right _ _ _,
  map_smul := λ c y, h.smul_right _ _ _,
  bound    := begin
    rcases h.bound with ⟨C, C_pos, hC⟩,
    refine ⟨C * (∥x∥ + 1), mul_pos C_pos (lt_of_lt_of_le (zero_lt_one) (by simp)), λ y, _⟩,
    have : ∥x∥ ≤ ∥x∥ + 1, by simp [zero_le_one],
    calc ∥f (x, y)∥ ≤ C * ∥x∥ * ∥y∥ : hC x y
    ... ≤ C * (∥x∥ + 1) * ∥y∥ :
      by apply_rules [mul_le_mul_of_nonneg_right, norm_nonneg, mul_le_mul_of_nonneg_left,
                      le_of_lt C_pos]
  end }

lemma is_bounded_bilinear_map_smul {𝕜' : Type*} [normed_field 𝕜']
  [normed_algebra 𝕜 𝕜'] {E : Type*} [normed_group E] [normed_space 𝕜 E] [normed_space 𝕜' E]
  [is_scalar_tower 𝕜 𝕜' E] :
  is_bounded_bilinear_map 𝕜 (λ (p : 𝕜' × E), p.1 • p.2) :=
{ add_left   := add_smul,
  smul_left  := λ c x y, by simp [smul_assoc],
  add_right  := smul_add,
  smul_right := λ c x y, by simp [smul_assoc, smul_algebra_smul_comm],
  bound      := ⟨1, zero_lt_one, λ x y, by simp [norm_smul] ⟩ }

lemma is_bounded_bilinear_map_mul :
  is_bounded_bilinear_map 𝕜 (λ (p : 𝕜 × 𝕜), p.1 * p.2) :=
by simp_rw ← smul_eq_mul; exact is_bounded_bilinear_map_smul

lemma is_bounded_bilinear_map_comp :
  is_bounded_bilinear_map 𝕜 (λ (p : (E →L[𝕜] F) × (F →L[𝕜] G)), p.2.comp p.1) :=
{ add_left := λ x₁ x₂ y, begin
      ext z,
      change y (x₁ z + x₂ z) = y (x₁ z) + y (x₂ z),
      rw y.map_add
    end,
  smul_left := λ c x y, begin
      ext z,
      change y (c • (x z)) = c • y (x z),
      rw continuous_linear_map.map_smul
    end,
  add_right := λ x y₁ y₂, rfl,
  smul_right := λ c x y, rfl,
  bound := ⟨1, zero_lt_one, λ x y, calc
    ∥continuous_linear_map.comp ((x, y).snd) ((x, y).fst)∥
      ≤ ∥y∥ * ∥x∥ : continuous_linear_map.op_norm_comp_le _ _
    ... = 1 * ∥x∥ * ∥ y∥ : by ring ⟩ }

lemma continuous_linear_map.is_bounded_linear_map_comp_left (g : F →L[𝕜] G) :
  is_bounded_linear_map 𝕜 (λ (f : E →L[𝕜] F), continuous_linear_map.comp g f) :=
is_bounded_bilinear_map_comp.is_bounded_linear_map_left _

lemma continuous_linear_map.is_bounded_linear_map_comp_right (f : E →L[𝕜] F) :
  is_bounded_linear_map 𝕜 (λ (g : F →L[𝕜] G), continuous_linear_map.comp g f) :=
is_bounded_bilinear_map_comp.is_bounded_linear_map_right _

lemma is_bounded_bilinear_map_apply :
  is_bounded_bilinear_map 𝕜 (λ p : (E →L[𝕜] F) × E, p.1 p.2) :=
{ add_left   := by simp,
  smul_left  := by simp,
  add_right  := by simp,
  smul_right := by simp,
  bound      := ⟨1, zero_lt_one, by simp [continuous_linear_map.le_op_norm]⟩ }

/-- The function `continuous_linear_map.smul_right`, associating to a continuous linear map
`f : E → 𝕜` and a scalar `c : F` the tensor product `f ⊗ c` as a continuous linear map from `E` to
`F`, is a bounded bilinear map. -/
lemma is_bounded_bilinear_map_smul_right :
  is_bounded_bilinear_map 𝕜
    (λ p, (continuous_linear_map.smul_right : (E →L[𝕜] 𝕜) → F → (E →L[𝕜] F)) p.1 p.2) :=
{ add_left   := λ m₁ m₂ f, by { ext z, simp [add_smul] },
  smul_left  := λ c m f, by { ext z, simp [mul_smul] },
  add_right  := λ m f₁ f₂, by { ext z, simp [smul_add] },
  smul_right := λ c m f, by { ext z, simp [smul_smul, mul_comm] },
  bound      := ⟨1, zero_lt_one, λ m f, by simp⟩ }

/-- The composition of a continuous linear map with a continuous multilinear map is a bounded
bilinear operation. -/
lemma is_bounded_bilinear_map_comp_multilinear {ι : Type*} {E : ι → Type*}
[decidable_eq ι] [fintype ι] [∀ i, normed_group (E i)] [∀ i, normed_space 𝕜 (E i)] :
  is_bounded_bilinear_map 𝕜 (λ p : (F →L[𝕜] G) × (continuous_multilinear_map 𝕜 E F),
    p.1.comp_continuous_multilinear_map p.2) :=
{ add_left   := λ g₁ g₂ f, by { ext m, refl },
  smul_left  := λ c g f, by { ext m, refl },
  add_right  := λ g f₁ f₂, by { ext m, simp },
  smul_right := λ c g f, by { ext m, simp },
  bound      := ⟨1, zero_lt_one, λ g f, begin
    apply continuous_multilinear_map.op_norm_le_bound _ _ (λ m, _),
    { apply_rules [mul_nonneg, zero_le_one, norm_nonneg] },
    calc ∥g (f m)∥ ≤ ∥g∥ * ∥f m∥ : g.le_op_norm _
    ... ≤ ∥g∥ * (∥f∥ * ∏ i, ∥m i∥) :
      mul_le_mul_of_nonneg_left (f.le_op_norm _) (norm_nonneg _)
    ... = 1 * ∥g∥ * ∥f∥ * ∏ i, ∥m i∥ : by ring
    end⟩ }

/-- Definition of the derivative of a bilinear map `f`, given at a point `p` by
`q ↦ f(p.1, q.2) + f(q.1, p.2)` as in the standard formula for the derivative of a product.
We define this function here as a linear map `E × F →ₗ[𝕜] G`, then `is_bounded_bilinear_map.deriv`
strengthens it to a continuous linear map `E × F →L[𝕜] G`.
``. -/
def is_bounded_bilinear_map.linear_deriv (h : is_bounded_bilinear_map 𝕜 f) (p : E × F) :
  E × F →ₗ[𝕜] G :=
{ to_fun := λ q, f (p.1, q.2) + f (q.1, p.2),
  map_add' := λ q₁ q₂, begin
    change f (p.1, q₁.2 + q₂.2) + f (q₁.1 + q₂.1, p.2) =
      f (p.1, q₁.2) + f (q₁.1, p.2) + (f (p.1, q₂.2) + f (q₂.1, p.2)),
    simp [h.add_left, h.add_right], abel
  end,
  map_smul' := λ c q, begin
    change f (p.1, c • q.2) + f (c • q.1, p.2) = c • (f (p.1, q.2) + f (q.1, p.2)),
    simp [h.smul_left, h.smul_right, smul_add]
  end }

/-- The derivative of a bounded bilinear map at a point `p : E × F`, as a continuous linear map
from `E × F` to `G`. The statement that this is indeed the derivative of `f` is
`is_bounded_bilinear_map.has_fderiv_at` in `analysis.calculus.fderiv`. -/
def is_bounded_bilinear_map.deriv (h : is_bounded_bilinear_map 𝕜 f) (p : E × F) : E × F →L[𝕜] G :=
(h.linear_deriv p).mk_continuous_of_exists_bound $ begin
  rcases h.bound with ⟨C, Cpos, hC⟩,
  refine ⟨C * ∥p.1∥ + C * ∥p.2∥, λ q, _⟩,
  calc ∥f (p.1, q.2) + f (q.1, p.2)∥
    ≤ C * ∥p.1∥ * ∥q.2∥ + C * ∥q.1∥ * ∥p.2∥ : norm_add_le_of_le (hC _ _) (hC _ _)
  ... ≤ C * ∥p.1∥ * ∥q∥ + C * ∥q∥ * ∥p.2∥ : begin
      apply add_le_add,
      exact mul_le_mul_of_nonneg_left
        (le_max_right _ _) (mul_nonneg (le_of_lt Cpos) (norm_nonneg _)),
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (le_of_lt Cpos),
  end
  ... = (C * ∥p.1∥ + C * ∥p.2∥) * ∥q∥ : by ring
end

@[simp] lemma is_bounded_bilinear_map_deriv_coe (h : is_bounded_bilinear_map 𝕜 f) (p q : E × F) :
  h.deriv p q = f (p.1, q.2) + f (q.1, p.2) := rfl

variables (𝕜)

/-- The function `lmul_left_right : 𝕜' × 𝕜' → (𝕜' →L[𝕜] 𝕜')` is a bounded bilinear map. -/
lemma continuous_linear_map.lmul_left_right_is_bounded_bilinear
  (𝕜' : Type*) [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] :
  is_bounded_bilinear_map 𝕜 (λ p : 𝕜' × 𝕜', continuous_linear_map.lmul_left_right 𝕜 𝕜' p.1 p.2) :=
(continuous_linear_map.lmul_left_right 𝕜 𝕜').is_bounded_bilinear_map

variables {𝕜}

/-- Given a bounded bilinear map `f`, the map associating to a point `p` the derivative of `f` at
`p` is itself a bounded linear map. -/
lemma is_bounded_bilinear_map.is_bounded_linear_map_deriv (h : is_bounded_bilinear_map 𝕜 f) :
  is_bounded_linear_map 𝕜 (λ p : E × F, h.deriv p) :=
begin
  rcases h.bound with ⟨C, Cpos : 0 < C, hC⟩,
  refine is_linear_map.with_bound ⟨λ p₁ p₂, _, λ c p, _⟩ (C + C) (λ p, _),
  { ext; simp [h.add_left, h.add_right]; abel },
  { ext; simp [h.smul_left, h.smul_right, smul_add] },
  { refine continuous_linear_map.op_norm_le_bound _
      (mul_nonneg (add_nonneg Cpos.le Cpos.le) (norm_nonneg _)) (λ q, _),
    calc ∥f (p.1, q.2) + f (q.1, p.2)∥
      ≤ C * ∥p.1∥ * ∥q.2∥ + C * ∥q.1∥ * ∥p.2∥ : norm_add_le_of_le (hC _ _) (hC _ _)
    ... ≤ C * ∥p∥ * ∥q∥ + C * ∥q∥ * ∥p∥ : by apply_rules [add_le_add, mul_le_mul, norm_nonneg,
      Cpos.le, le_refl, le_max_left, le_max_right, mul_nonneg]
    ... = (C + C) * ∥p∥ * ∥q∥ : by ring },
end

end bilinear_map

/-- A linear isometry preserves the norm. -/
lemma linear_map.norm_apply_of_isometry (f : E →ₗ[𝕜] F) {x : E} (hf : isometry f) : ∥f x∥ = ∥x∥ :=
by { simp_rw [←dist_zero_right, ←f.map_zero], exact isometry.dist_eq hf _ _ }

/-- Construct a continuous linear equiv from
a linear map that is also an isometry with full range. -/
def continuous_linear_equiv.of_isometry (f : E →ₗ[𝕜] F) (hf : isometry f) (hfr : f.range = ⊤) :
  E ≃L[𝕜] F :=
continuous_linear_equiv.of_homothety
(linear_equiv.of_bijective f (linear_map.ker_eq_bot.mpr (isometry.injective hf)) hfr)
1 zero_lt_one (λ _, by simp [one_mul, f.norm_apply_of_isometry hf])
