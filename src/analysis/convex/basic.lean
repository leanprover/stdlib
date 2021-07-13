/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import data.set.intervals.ord_connected
import data.set.intervals.image_preimage
import data.complex.module
import linear_algebra.affine_space.affine_map
import algebra.module.ordered
import order.closure

/-!
# Convex sets and functions on real vector spaces

In a real vector space, we define the following objects and properties.

* `segment x y` is the closed segment joining `x` and `y`.
* `open_segment x y` is the open segment joining `x` and `y`.
* A set `s` is `convex` if for any two points `x y ∈ s` it includes `segment x y`;
* A function `f : E → β` is `convex_on` a set `s` if `s` is itself a convex set, and for any two
  points `x y ∈ s` the segment joining `(x, f x)` to `(y, f y)` is (non-strictly) above the graph
  of `f`; equivalently, `convex_on f s` means that the epigraph
  `{p : E × β | p.1 ∈ s ∧ f p.1 ≤ p.2}` is a convex set;
* Center mass of a finite set of points with prescribed weights.
* Convex hull of a set `s` is the minimal convex set that includes `s`.
* Standard simplex `std_simplex ι [fintype ι]` is the intersection of the positive quadrant with
  the hyperplane `s.sum = 1` in the space `ι → ℝ`.

We also provide various equivalent versions of the definitions above, prove that some specific sets
are convex, and prove Jensen's inequality.

Note: To define convexity for functions `f : E → β`, we need `β` to be an ordered vector space,
defined using the instance `ordered_module ℝ β`.

## Notations

We use the following local notations:

* `I = Icc (0:ℝ) 1`;
* `[x, y] = segment x y`.

They are defined using `local notation`, so they are not available outside of this file.

## Implementation notes

`convex_hull` is defined as a closure operator. This gives access to the `closure_operator` API
while the impact on writing code is minimal as `convex_hull s` is automatically elaborated as
`⇑convex_hull s`.
-/

universes u' u v v' w x

variables {E : Type u} {F : Type v} {ι : Type w} {ι' : Type x} {α : Type v'}
  [add_comm_group E] [module ℝ E] [add_comm_group F] [module ℝ F]
  [linear_ordered_field α]
  {s : set E}

open set linear_map
open_locale classical big_operators

local notation `I` := (Icc 0 1 : set ℝ)

section sets

/-! ### Segment -/

/-- Segments in a vector space. -/
def segment (x y : E) : set E :=
{z : E | ∃ (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1), a • x + b • y = z}

local notation `[`x `, ` y `]` := segment x y

lemma segment_symm (x y : E) : [x, y] = [y, x] :=
set.ext $ λ z,
⟨λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
  λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

lemma left_mem_segment (x y : E) : x ∈ [x, y] :=
⟨1, 0, zero_le_one, le_refl 0, add_zero 1, by rw [zero_smul, one_smul, add_zero]⟩

lemma right_mem_segment (x y : E) : y ∈ [x, y] :=
segment_symm y x ▸ left_mem_segment y x

lemma segment_same (x : E) : [x, x] = {x} :=
set.ext $ λ z, ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
  by simpa only [(add_smul _ _ _).symm, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
  λ h, mem_singleton_iff.1 h ▸ left_mem_segment z z⟩

lemma segment_eq_image (x y : E) : [x, y] = (λ θ : ℝ, (1 - θ) • x + θ • y) '' I :=
set.ext $ λ z,
  ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
    ⟨b, ⟨hb, hab ▸ le_add_of_nonneg_left ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel]⟩,
    λ ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩, ⟨1-θ, θ, sub_nonneg.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

lemma segment_eq_image' (x y : E) : [x, y] = (λ (θ : ℝ), x + θ • (y - x)) '' I :=
by { convert segment_eq_image x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

lemma segment_eq_image₂ (x y : E) :
  [x, y] = (λ p : ℝ×ℝ, p.1 • x + p.2 • y) '' {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 = 1} :=
by simp only [segment, image, prod.exists, mem_set_of_eq, exists_prop, and_assoc]

lemma segment_eq_Icc {a b : ℝ} (h : a ≤ b) : [a, b] = Icc a b :=
begin
  rw [segment_eq_image'],
  show (((+) a) ∘ (λ t, t * (b - a))) '' Icc 0 1 = Icc a b,
  rw [image_comp, image_mul_right_Icc (@zero_le_one ℝ _) (sub_nonneg.2 h), image_const_add_Icc],
  simp
end

lemma segment_eq_Icc' (a b : ℝ) : [a, b] = Icc (min a b) (max a b) :=
by cases le_total a b; [skip, rw segment_symm]; simp [segment_eq_Icc, *]

lemma segment_eq_interval (a b : ℝ) : segment a b = interval a b :=
segment_eq_Icc' _ _

lemma mem_segment_translate (a : E) {x b c} : a + x ∈ [a + b, a + c] ↔ x ∈ [b, c] :=
begin
  rw [segment_eq_image', segment_eq_image'],
  refine exists_congr (λ θ, and_congr iff.rfl _),
  simp only [add_sub_add_left_eq_sub, add_assoc, add_right_inj]
end

lemma segment_translate_preimage (a b c : E) : (λ x, a + x) ⁻¹' [a + b, a + c] = [b, c] :=
set.ext $ λ x, mem_segment_translate a

lemma segment_translate_image (a b c : E) : (λx, a + x) '' [b, c] = [a + b, a + c] :=
segment_translate_preimage a b c ▸ image_preimage_eq _ $ add_left_surjective a

lemma segment_image (f : E →ₗ[ℝ] F) (a b : E) : f '' [a, b] = [f a, f b] :=
set.ext (λ x, by simp [segment_eq_image])

/-- Open segment in a vector space. Note that `open_segment x x = {x}` instead of being `∅`. -/
def open_segment (x y : E) : set E :=
{z : E | ∃ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1), a • x + b • y = z}

lemma open_segment_subset_segment (x y : E) :
  open_segment x y ⊆ [x, y] :=
λ z ⟨a, b, ha, hb, hab, hz⟩, ⟨a, b, ha.le, hb.le, hab, hz⟩

lemma mem_open_segment_of_ne_left_right {x y z : E} (hx : x ≠ z) (hy : y ≠ z) (hz : z ∈ [x, y]) :
  z ∈ open_segment x y :=
begin
  obtain ⟨a, b, ha, hb, hab, hz⟩ := hz,
  by_cases ha' : a ≠ 0,
  by_cases hb' : b ≠ 0,
  { exact ⟨a, b, ha.lt_of_ne (ne.symm ha'), hb.lt_of_ne (ne.symm hb'), hab, hz⟩ },
  all_goals { simp only [*, add_zero, not_not, one_smul, zero_smul, zero_add] at * }
end

lemma open_segment_symm (x y : E) :
  open_segment x y = open_segment y x :=
set.ext $ λ z,
⟨λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩,
  λ ⟨a, b, ha, hb, hab, H⟩, ⟨b, a, hb, ha, (add_comm _ _).trans hab, (add_comm _ _).trans H⟩⟩

@[simp] lemma open_segment_same (x : E) :
  open_segment x x = {x} :=
set.ext $ λ z, ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
  by simpa only [← add_smul, mem_singleton_iff, hab, one_smul, eq_comm] using hz,
  λ h, mem_singleton_iff.1 h ▸ ⟨1/2, 1/2, one_half_pos, one_half_pos, add_halves 1,
    by rw [←add_smul, add_halves, one_smul]⟩⟩

@[simp] lemma left_mem_open_segment_iff {x y : E} :
  x ∈ open_segment x y ↔ x = y :=
begin
  split,
  { rintro ⟨a, b, ha, hb, hab, hx⟩,
    refine smul_left_injective _ hb.ne' ((add_right_inj (a • x)).1 _),
    rw [hx, ←add_smul, hab, one_smul] },
  rintro rfl,
  simp only [open_segment_same, mem_singleton],
end

@[simp] lemma right_mem_open_segment_iff {x y : E} :
  y ∈ open_segment x y ↔ x = y :=
by rw [open_segment_symm, left_mem_open_segment_iff, eq_comm]

lemma open_segment_eq_image (x y : E) :
  open_segment x y = (λ (θ : ℝ), (1 - θ) • x + θ • y) '' (Ioo 0 1 : set ℝ) :=
set.ext $ λ z,
  ⟨λ ⟨a, b, ha, hb, hab, hz⟩,
    ⟨b, ⟨hb, hab ▸ lt_add_of_pos_left _ ha⟩, hab ▸ hz ▸ by simp only [add_sub_cancel]⟩,
    λ ⟨θ, ⟨hθ₀, hθ₁⟩, hz⟩, ⟨1 - θ, θ, sub_pos.2 hθ₁, hθ₀, sub_add_cancel _ _, hz⟩⟩

lemma open_segment_eq_image' (x y : E) :
  open_segment x y = (λ (θ : ℝ), x + θ • (y - x)) '' (Ioo 0 1 : set ℝ) :=
by { convert open_segment_eq_image x y, ext θ, simp only [smul_sub, sub_smul, one_smul], abel }

lemma open_segment_eq_image₂ (x y : E) :
  open_segment x y = (λ p:ℝ×ℝ, p.1 • x + p.2 • y) '' {p | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1} :=
by simp only [open_segment, image, prod.exists, mem_set_of_eq, exists_prop, and_assoc]

@[simp] lemma open_segment_eq_Ioo {a b : ℝ} (h : a < b) :
  open_segment a b = Ioo a b :=
begin
  rw open_segment_eq_image',
  show (((+) a) ∘ (λ t, t * (b - a))) '' Ioo 0 1 = Ioo a b,
  rw [image_comp, image_mul_right_Ioo _ _ (sub_pos.2 h), image_const_add_Ioo],
  simp
end

lemma open_segment_eq_Ioo' {a b : ℝ} (hab : a ≠ b) :
  open_segment a b = Ioo (min a b) (max a b) :=
begin
  cases le_total a b,
  { rw open_segment_eq_Ioo (h.lt_of_ne hab),
    simp * },
  rw [open_segment_symm, open_segment_eq_Ioo (h.lt_of_ne hab.symm)],
  simp *,
end

@[simp] lemma mem_open_segment_translate (a : E) {x b c : E} :
  a + x ∈ open_segment (a + b) (a + c)  ↔ x ∈ open_segment b c :=
begin
  rw [open_segment_eq_image', open_segment_eq_image'],
  refine exists_congr (λ θ, and_congr iff.rfl _),
  simp only [add_sub_add_left_eq_sub, add_assoc, add_right_inj],
end

@[simp] lemma open_segment_translate_preimage (a b c : E) :
  (λ x, a + x) ⁻¹' open_segment (a + b) (a + c) = open_segment b c :=
set.ext $ λ x, mem_open_segment_translate a

lemma open_segment_translate_image (a b c : E) :
  (λ x, a + x) '' open_segment b c = open_segment (a + b) (a + c) :=
open_segment_translate_preimage a b c ▸ image_preimage_eq _ $ add_left_surjective a

@[simp] lemma open_segment_image (f : E →ₗ[ℝ] F) (a b : E) :
  f '' open_segment a b = open_segment (f a) (f b) :=
set.ext (λ x, by simp [open_segment_eq_image])

/-! ### Convexity of sets -/

/-- Convexity of sets. -/
def convex (s : set E) :=
∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
  a • x + b • y ∈ s

lemma convex_iff_forall_pos :
  convex s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 → a • x + b • y ∈ s :=
begin
  refine ⟨λ h x y hx hy a b ha hb hab, h hx hy (le_of_lt ha) (le_of_lt hb) hab, _⟩,
  intros h x y hx hy a b ha hb hab,
  cases eq_or_lt_of_le ha with ha ha,
  { subst a, rw [zero_add] at hab, simp [hab, hy] },
  cases eq_or_lt_of_le hb with hb hb,
  { subst b, rw [add_zero] at hab, simp [hab, hx] },
  exact h hx hy ha hb hab
end

lemma convex_iff_segment_subset :
  convex s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → [x, y] ⊆ s :=
by simp only [convex, segment_eq_image₂, subset_def, ball_image_iff, prod.forall,
  mem_set_of_eq, and_imp]

lemma convex_iff_open_segment_subset :
  convex s ↔ ∀ ⦃x y⦄, x ∈ s → y ∈ s → open_segment x y ⊆ s :=
by simp only [convex_iff_forall_pos, open_segment_eq_image₂, subset_def, ball_image_iff,
  prod.forall, mem_set_of_eq, and_imp]

lemma convex.segment_subset (h : convex s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) : [x, y] ⊆ s :=
convex_iff_segment_subset.1 h hx hy

lemma convex.open_segment_subset (h : convex s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
  open_segment x y ⊆ s :=
convex_iff_open_segment_subset.1 h hx hy

lemma convex.add_smul_sub_mem (h : convex s) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
  {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ s :=
begin
  apply h.segment_subset hx hy,
  rw segment_eq_image',
  apply mem_image_of_mem,
  exact ht
end

lemma convex.add_smul_mem (h : convex s) {x y : E} (hx : x ∈ s) (hy : x + y ∈ s)
  {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : x + t • y ∈ s :=
by { convert h.add_smul_sub_mem hx hy ht, abel }

lemma convex.smul_mem_of_zero_mem (h : convex s) {x : E} (zero_mem : (0:E) ∈ s) (hx : x ∈ s)
  {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • x ∈ s :=
by simpa using h.add_smul_mem zero_mem (by simpa using hx) ht

lemma convex.mem_smul_of_zero_mem (h : convex s) {x : E} (zero_mem : (0:E) ∈ s) (hx : x ∈ s)
  {t : ℝ} (ht : t ∈ Ici (1 : ℝ)) : x ∈ t • s :=
begin
  rw mem_smul_set_iff_inv_smul_mem,
  apply h.smul_mem_of_zero_mem zero_mem hx ⟨inv_nonneg.2 (zero_le_one.trans ht), inv_le_one ht⟩,
  exact ne_of_gt (zero_lt_one.trans_le ht),
end

/-- Alternative definition of set convexity, in terms of pointwise set operations. -/
lemma convex_iff_pointwise_add_subset:
  convex s ↔ ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 → a • s + b • s ⊆ s :=
iff.intro
  begin
    rintros hA a b ha hb hab w ⟨au, bv, ⟨u, hu, rfl⟩, ⟨v, hv, rfl⟩, rfl⟩,
    exact hA hu hv ha hb hab
  end
  (λ h x y hx hy a b ha hb hab,
    (h ha hb hab) (set.add_mem_add ⟨_, hx, rfl⟩ ⟨_, hy, rfl⟩))

/-- Alternative definition of set convexity, using division. -/
lemma convex_iff_div:
  convex s ↔ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄,
    0 ≤ a → 0 ≤ b → 0 < a + b → (a/(a+b)) • x + (b/(a+b)) • y ∈ s :=
⟨begin
  assume h x y hx hy a b ha hb hab,
  apply h hx hy,
  have ha', from mul_le_mul_of_nonneg_left ha (le_of_lt (inv_pos.2 hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at ha',
  have hb', from mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.2 hab)),
  rwa [mul_zero, ←div_eq_inv_mul] at hb',
  rw [←add_div],
  exact div_self (ne_of_lt hab).symm
end,
begin
  assume h x y hx hy a b ha hb hab,
  have h', from h hx hy ha hb,
  rw [hab, div_one, div_one] at h',
  exact h' zero_lt_one
end⟩

/-! ### Examples of convex sets -/

lemma convex_empty : convex (∅ : set E) :=  by finish

lemma convex_singleton (c : E) : convex ({c} : set E) :=
begin
  intros x y hx hy a b ha hb hab,
  rw [set.eq_of_mem_singleton hx, set.eq_of_mem_singleton hy, ←add_smul, hab, one_smul],
  exact mem_singleton c
end

lemma convex_univ : convex (set.univ : set E) := λ _ _ _ _ _ _ _ _ _, trivial

lemma convex.inter {t : set E} (hs: convex s) (ht: convex t) : convex (s ∩ t) :=
λ x y (hx : x ∈ s ∩ t) (hy : y ∈ s ∩ t) a b (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1),
  ⟨hs hx.left hy.left ha hb hab, ht hx.right hy.right ha hb hab⟩

lemma convex_sInter {S : set (set E)} (h : ∀ s ∈ S, convex s) : convex (⋂₀ S) :=
assume x y hx hy a b ha hb hab s hs,
h s hs (hx s hs) (hy s hs) ha hb hab

lemma convex_Inter {ι : Sort*} {s : ι → set E} (h : ∀ i : ι, convex (s i)) : convex (⋂ i, s i) :=
(sInter_range s) ▸ convex_sInter $ forall_range_iff.2 h

lemma convex.prod {s : set E} {t : set F} (hs : convex s) (ht : convex t) :
  convex (s.prod t) :=
begin
  intros x y hx hy a b ha hb hab,
  apply mem_prod.2,
  exact ⟨hs (mem_prod.1 hx).1 (mem_prod.1 hy).1 ha hb hab,
        ht (mem_prod.1 hx).2 (mem_prod.1 hy).2 ha hb hab⟩
end

lemma directed.convex_Union {ι : Sort*} {s : ι → set E} (hdir : directed has_subset.subset s)
  (hc : ∀ ⦃i : ι⦄, convex (s i)) :
  convex (⋃ i, s i) :=
begin
  rintro x y hx hy a b ha hb hab,
  rw mem_Union at ⊢ hx hy,
  obtain ⟨i, hx⟩ := hx,
  obtain ⟨j, hy⟩ := hy,
  obtain ⟨k, hik, hjk⟩ := hdir i j,
  exact ⟨k, hc (hik hx) (hjk hy) ha hb hab⟩,
end

lemma directed_on.convex_sUnion {c : set (set E)} (hdir : directed_on has_subset.subset c)
  (hc : ∀ ⦃A : set E⦄, A ∈ c → convex A) :
  convex (⋃₀c) :=
begin
  rw sUnion_eq_Union,
  exact (directed_on_iff_directed.1 hdir).convex_Union (λ A, hc A.2),
end

lemma convex.combo_to_vadd {a b : ℝ} {x y : E} (h : a + b = 1) :
  a • x + b • y = b • (y - x) + x :=
calc
  a • x + b • y = (b • y - b • x) + (a • x + b • x) : by abel
            ... = b • (y - x) + (a + b) • x         : by rw [smul_sub, add_smul]
            ... = b • (y - x) + (1 : ℝ) • x         : by rw [h]
            ... = b • (y - x) + x                   : by rw [one_smul]

/--
Applying an affine map to an affine combination of two points yields
an affine combination of the images.
-/
lemma convex.combo_affine_apply {a b : ℝ} {x y : E} {f : E →ᵃ[ℝ] F} (h : a + b = 1) :
  f (a • x + b • y) = a • f x + b • f y :=
begin
  simp only [convex.combo_to_vadd h, ← vsub_eq_sub],
  exact f.apply_line_map _ _ _,
end

/-- The preimage of a convex set under an affine map is convex. -/
lemma convex.affine_preimage (f : E →ᵃ[ℝ] F) {s : set F} (hs : convex s) :
  convex (f ⁻¹' s) :=
begin
  intros x y xs ys a b ha hb hab,
  rw [mem_preimage, convex.combo_affine_apply hab],
  exact hs xs ys ha hb hab,
end

/-- The image of a convex set under an affine map is convex. -/
lemma convex.affine_image (f : E →ᵃ[ℝ] F) {s : set E} (hs : convex s) :
  convex (f '' s) :=
begin
  rintros x y ⟨x', ⟨hx', hx'f⟩⟩ ⟨y', ⟨hy', hy'f⟩⟩ a b ha hb hab,
  refine ⟨a • x' + b • y', ⟨hs hx' hy' ha hb hab, _⟩⟩,
  rw [convex.combo_affine_apply hab, hx'f, hy'f]
end

lemma convex.linear_image (hs : convex s) (f : E →ₗ[ℝ] F) : convex (image f s) :=
hs.affine_image f.to_affine_map

lemma convex.is_linear_image (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) :
  convex (f '' s) :=
hs.linear_image $ hf.mk' f

lemma convex.linear_preimage {s : set F} (hs : convex s) (f : E →ₗ[ℝ] F) :
  convex (preimage f s) :=
hs.affine_preimage f.to_affine_map

lemma convex.is_linear_preimage {s : set F} (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) :
  convex (preimage f s) :=
hs.linear_preimage $ hf.mk' f

lemma convex.neg (hs : convex s) : convex ((λ z, -z) '' s) :=
hs.is_linear_image is_linear_map.is_linear_map_neg

lemma convex.neg_preimage (hs : convex s) : convex ((λ z, -z) ⁻¹' s) :=
hs.is_linear_preimage is_linear_map.is_linear_map_neg

lemma convex.smul (c : ℝ) (hs : convex s) : convex (c • s) :=
hs.linear_image (linear_map.lsmul _ _ c)

lemma convex.smul_preimage (c : ℝ) (hs : convex s) : convex ((λ z, c • z) ⁻¹' s) :=
hs.linear_preimage (linear_map.lsmul _ _ c)

lemma convex.add {t : set E}  (hs : convex s) (ht : convex t) : convex (s + t) :=
by { rw ← add_image_prod, exact (hs.prod ht).is_linear_image is_linear_map.is_linear_map_add }

lemma convex.sub {t : set E}  (hs : convex s) (ht : convex t) :
  convex ((λx : E × E, x.1 - x.2) '' (s.prod t)) :=
(hs.prod ht).is_linear_image is_linear_map.is_linear_map_sub

lemma convex.translate (hs : convex s) (z : E) : convex ((λx, z + x) '' s) :=
hs.affine_image $ affine_map.const ℝ E z +ᵥ affine_map.id ℝ E

/-- The translation of a convex set is also convex. -/
lemma convex.translate_preimage_right (hs : convex s) (a : E) : convex ((λ z, a + z) ⁻¹' s) :=
hs.affine_preimage $ affine_map.const ℝ E a +ᵥ affine_map.id ℝ E

/-- The translation of a convex set is also convex. -/
lemma convex.translate_preimage_left (hs : convex s) (a : E) : convex ((λ z, z + a) ⁻¹' s) :=
by simpa only [add_comm] using hs.translate_preimage_right a

lemma convex.affinity (hs : convex s) (z : E) (c : ℝ) : convex ((λx, z + c • x) '' s) :=
hs.affine_image $ affine_map.const ℝ E z +ᵥ c • affine_map.id ℝ E

lemma real.convex_iff_ord_connected {s : set ℝ} : convex s ↔ ord_connected s :=
begin
  simp only [convex_iff_segment_subset, segment_eq_interval, ord_connected_iff_interval_subset],
  exact forall_congr (λ x, forall_swap)
end

alias real.convex_iff_ord_connected ↔ convex.ord_connected set.ord_connected.convex

lemma convex_Iio (r : ℝ) : convex (Iio r) := ord_connected_Iio.convex
lemma convex_Ioi (r : ℝ) : convex (Ioi r) := ord_connected_Ioi.convex
lemma convex_Iic (r : ℝ) : convex (Iic r) := ord_connected_Iic.convex
lemma convex_Ici (r : ℝ) : convex (Ici r) := ord_connected_Ici.convex
lemma convex_Ioo (r s : ℝ) : convex (Ioo r s) := ord_connected_Ioo.convex
lemma convex_Ico (r s : ℝ) : convex (Ico r s) := ord_connected_Ico.convex
lemma convex_Ioc (r : ℝ) (s : ℝ) : convex (Ioc r s) := ord_connected_Ioc.convex
lemma convex_Icc (r : ℝ) (s : ℝ) : convex (Icc r s) := ord_connected_Icc.convex
lemma convex_interval (r : ℝ) (s : ℝ) : convex (interval r s) := ord_connected_interval.convex

lemma convex_segment (a b : E) : convex [a, b] :=
begin
  have : (λ (t : ℝ), a + t • (b - a)) = (λ z : E, a + z) ∘ (λ t : ℝ, t • (b - a)) := rfl,
  rw [segment_eq_image', this, image_comp],
  refine ((convex_Icc _ _).is_linear_image _).translate _,
  exact is_linear_map.is_linear_map_smul' _
end

lemma convex_open_segment (a b : E) : convex (open_segment a b) :=
begin
  have : (λ (t : ℝ), a + t • (b - a)) = (λ z : E, a + z) ∘ (λ t : ℝ, t • (b - a)) := rfl,
  rw [open_segment_eq_image', this, image_comp],
  refine ((convex_Ioo _ _).is_linear_image _).translate _,
  exact is_linear_map.is_linear_map_smul' _,
end

lemma convex_halfspace_lt {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w < r} :=
(convex_Iio r).is_linear_preimage h

lemma convex_halfspace_le {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w ≤ r} :=
(convex_Iic r).is_linear_preimage h

lemma convex_halfspace_gt {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | r < f w} :=
(convex_Ioi r).is_linear_preimage h

lemma convex_halfspace_ge {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | r ≤ f w} :=
(convex_Ici r).is_linear_preimage h

lemma convex_hyperplane {f : E → ℝ} (h : is_linear_map ℝ f) (r : ℝ) :
  convex {w | f w = r} :=
begin
  show convex (f ⁻¹' {p | p = r}),
  rw set_of_eq_eq_singleton,
  exact (convex_singleton r).is_linear_preimage h
end

lemma convex_halfspace_re_lt (r : ℝ) : convex {c : ℂ | c.re < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_le (r : ℝ) : convex {c : ℂ | c.re ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_gt (r : ℝ) : convex {c : ℂ | r < c.re } :=
convex_halfspace_gt (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_re_lge (r : ℝ) : convex {c : ℂ | r ≤ c.re} :=
convex_halfspace_ge (is_linear_map.mk complex.add_re complex.smul_re) _

lemma convex_halfspace_im_lt (r : ℝ) : convex {c : ℂ | c.im < r} :=
convex_halfspace_lt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_le (r : ℝ) : convex {c : ℂ | c.im ≤ r} :=
convex_halfspace_le (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_gt (r : ℝ) : convex {c : ℂ | r < c.im } :=
convex_halfspace_gt (is_linear_map.mk complex.add_im complex.smul_im) _

lemma convex_halfspace_im_lge (r : ℝ) : convex {c : ℂ | r ≤ c.im} :=
convex_halfspace_ge (is_linear_map.mk complex.add_im complex.smul_im) _

/-! ### Convex combinations in intervals -/

lemma convex.combo_self (a : α) {x y : α} (h : x + y = 1) : a = x * a + y * a :=
calc
  a   = 1 * a         : by rw [one_mul]
  ... = (x + y) * a   : by rw [h]
  ... = x * a + y * a : by rw [add_mul]

/--
If `x` is in an `Ioo`, it can be expressed as a convex combination of the endpoints.
-/
lemma convex.mem_Ioo {a b x : α} (h : a < b) :
  x ∈ Ioo a b ↔ ∃ (x_a x_b : α), 0 < x_a ∧ 0 < x_b ∧ x_a + x_b = 1 ∧ x_a * a + x_b * b = x :=
begin
  split,
  { rintros ⟨h_ax, h_bx⟩,
    by_cases hab : ¬a < b,
    { exfalso; exact hab h },
    { refine ⟨(b-x) / (b-a), (x-a) / (b-a), _⟩,
      refine ⟨div_pos (by linarith) (by linarith), div_pos (by linarith) (by linarith),_,_⟩;
      { field_simp [show b - a ≠ 0, by linarith], ring } } },
  { rw [mem_Ioo],
    rintros ⟨xa, xb, ⟨hxa, hxb, hxaxb, h₂⟩⟩,
    rw [←h₂],
    exact ⟨by nlinarith [convex.combo_self a hxaxb], by nlinarith [convex.combo_self b hxaxb]⟩ }
end

/-- If `x` is in an `Ioc`, it can be expressed as a convex combination of the endpoints. -/
lemma convex.mem_Ioc {a b x : α} (h : a < b) :
  x ∈ Ioc a b ↔ ∃ (x_a x_b : α), 0 ≤ x_a ∧ 0 < x_b ∧ x_a + x_b = 1 ∧ x_a * a + x_b * b = x :=
begin
  split,
  { rintros ⟨h_ax, h_bx⟩,
    by_cases h_x : x = b,
    { exact ⟨0, 1, by linarith, by linarith, by ring, by {rw [h_x], ring}⟩ },
    { rcases (convex.mem_Ioo h).mp ⟨h_ax, lt_of_le_of_ne h_bx h_x⟩ with ⟨x_a, x_b, Ioo_case⟩,
      exact ⟨x_a, x_b, by linarith, Ioo_case.2⟩ } },
  { rw [mem_Ioc],
    rintros ⟨xa, xb, ⟨hxa, hxb, hxaxb, h₂⟩⟩,
    rw [←h₂],
    exact ⟨by nlinarith [convex.combo_self a hxaxb], by nlinarith [convex.combo_self b hxaxb]⟩ }
end

/-- If `x` is in an `Ico`, it can be expressed as a convex combination of the endpoints. -/
lemma convex.mem_Ico {a b x : α} (h : a < b) :
  x ∈ Ico a b ↔ ∃ (x_a x_b : α), 0 < x_a ∧ 0 ≤ x_b ∧ x_a + x_b = 1 ∧ x_a * a + x_b * b = x :=
begin
  split,
  { rintros ⟨h_ax, h_bx⟩,
    by_cases h_x : x = a,
    { exact ⟨1, 0, by linarith, by linarith, by ring, by {rw [h_x], ring}⟩ },
    { rcases (convex.mem_Ioo h).mp ⟨lt_of_le_of_ne h_ax (ne.symm h_x), h_bx⟩
              with ⟨x_a, x_b, Ioo_case⟩,
      exact ⟨x_a, x_b, Ioo_case.1, by linarith, (Ioo_case.2).2⟩ } },
  { rw [mem_Ico],
    rintros ⟨xa, xb, ⟨hxa, hxb, hxaxb, h₂⟩⟩,
    rw [←h₂],
    exact ⟨by nlinarith [convex.combo_self a hxaxb], by nlinarith [convex.combo_self b hxaxb]⟩ }
end

/-- If `x` is in an `Icc`, it can be expressed as a convex combination of the endpoints. -/
lemma convex.mem_Icc {a b x : α} (h : a ≤ b) :
  x ∈ Icc a b ↔ ∃ (x_a x_b : α), 0 ≤ x_a ∧ 0 ≤ x_b ∧ x_a + x_b = 1 ∧ x_a * a + x_b * b = x :=
begin
  split,
  { intro x_in_I,
    rw [Icc, mem_set_of_eq] at x_in_I,
    rcases x_in_I with ⟨h_ax, h_bx⟩,
    by_cases hab' : a = b,
    { exact ⟨0, 1, le_refl 0, by linarith, by ring, by linarith⟩ },
    change a ≠ b at hab',
    replace h : a < b, exact lt_of_le_of_ne h hab',
    by_cases h_x : x = a,
    { exact ⟨1, 0, by linarith, by linarith, by ring, by {rw [h_x], ring}⟩ },
    { rcases (convex.mem_Ioc h).mp ⟨lt_of_le_of_ne h_ax (ne.symm h_x), h_bx⟩
              with ⟨x_a, x_b, Ioo_case⟩,
      exact ⟨x_a, x_b, Ioo_case.1, by linarith, (Ioo_case.2).2⟩ } },
  { rw [mem_Icc],
    rintros ⟨xa, xb, ⟨hxa, hxb, hxaxb, h₂⟩⟩,
    rw [←h₂],
    exact ⟨by nlinarith [convex.combo_self a hxaxb], by nlinarith [convex.combo_self b hxaxb]⟩ }
end


section submodule

open submodule

lemma submodule.convex (K : submodule ℝ E) : convex (↑K : set E) :=
by { repeat {intro}, refine add_mem _ (smul_mem _ _ _) (smul_mem _ _ _); assumption }

lemma subspace.convex (K : subspace ℝ E) : convex (↑K : set E) := K.convex

end submodule

end sets

/-! ### Convex and concave functions -/

section functions

variables {β : Type*} [ordered_add_comm_monoid β] [module ℝ β]

local notation `[`x `, ` y `]` := segment x y

/-- Convexity of functions -/
def convex_on (s : set E) (f : E → β) : Prop :=
  convex s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y

/-- Concavity of functions -/
def concave_on (s : set E) (f : E → β) : Prop :=
  convex s ∧
  ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y ≤ f (a • x + b • y)

section
variables [ordered_module ℝ β]

/-- A function `f` is concave iff `-f` is convex. -/
@[simp] lemma neg_convex_on_iff {γ : Type*} [ordered_add_comm_group γ] [module ℝ γ]
  (s : set E) (f : E → γ) : convex_on s (-f) ↔ concave_on s f :=
begin
  split,
  { rintros ⟨hconv, h⟩,
    refine ⟨hconv, _⟩,
    intros x y xs ys a b ha hb hab,
    specialize h xs ys ha hb hab,
    simp [neg_apply, neg_le, add_comm] at h,
    exact h },
  { rintros ⟨hconv, h⟩,
    refine ⟨hconv, _⟩,
    intros x y xs ys a b ha hb hab,
    specialize h xs ys ha hb hab,
    simp [neg_apply, neg_le, add_comm, h] }
end

/-- A function `f` is concave iff `-f` is convex. -/
@[simp] lemma neg_concave_on_iff {γ : Type*} [ordered_add_comm_group γ] [module ℝ γ]
  (s : set E) (f : E → γ) : concave_on s (-f) ↔ convex_on s f:=
by rw [← neg_convex_on_iff s (-f), neg_neg f]

end

lemma convex_on_id {s : set ℝ} (hs : convex s) : convex_on s id := ⟨hs, by { intros, refl }⟩

lemma concave_on_id {s : set ℝ} (hs : convex s) : concave_on s id := ⟨hs, by { intros, refl }⟩

lemma convex_on_const (c : β) (hs : convex s) : convex_on s (λ x:E, c) :=
⟨hs, by { intros, simp only [← add_smul, *, one_smul] }⟩

lemma concave_on_const (c : β) (hs : convex s) : concave_on s (λ x:E, c) :=
@convex_on_const _ _ _ _ (order_dual β) _ _ c hs

variables {t : set E}

lemma convex_on_iff_div {f : E → β} :
  convex_on s f ↔ convex s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀  ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
    f ((a/(a+b)) • x + (b/(a+b)) • y) ≤ (a/(a+b)) • f x + (b/(a+b)) • f y :=
and_congr iff.rfl
⟨begin
  intros h x y hx hy a b ha hb hab,
  apply h hx hy (div_nonneg ha $ le_of_lt hab) (div_nonneg hb $ le_of_lt hab),
  rw [←add_div],
  exact div_self (ne_of_gt hab)
end,
begin
  intros h x y hx hy a b ha hb hab,
  simpa [hab, zero_lt_one] using h hx hy ha hb,
end⟩

lemma concave_on_iff_div {f : E → β} :
  concave_on s f ↔ convex s ∧ ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → ∀  ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → 0 < a + b →
    (a/(a+b)) • f x + (b/(a+b)) • f y ≤ f ((a/(a+b)) • x + (b/(a+b)) • y) :=
@convex_on_iff_div _ _ _ _ (order_dual β) _ _ _

/-- For a function on a convex set in a linear ordered space, in order to prove that it is convex
it suffices to verify the inequality `f (a • x + b • y) ≤ a • f x + b • f y` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.convex_on_of_lt {f : E → β} [linear_order E] (hs : convex s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y) : convex_on s f :=
begin
  use hs,
  intros x y hx hy a b ha hb hab,
  wlog hxy : x<=y using [x y a b, y x b a],
  { exact le_total _ _ },
  { cases eq_or_lt_of_le hxy with hxy hxy,
      by { subst y, rw [← add_smul, ← add_smul, hab, one_smul, one_smul] },
    cases eq_or_lt_of_le ha with ha ha,
      by { subst a, rw [zero_add] at hab, subst b, simp },
    cases eq_or_lt_of_le hb with hb hb,
      by { subst b, rw [add_zero] at hab, subst a, simp },
    exact hf hx hy hxy ha hb hab }
end

/-- For a function on a convex set in a linear ordered space, in order to prove that it is concave
it suffices to verify the inequality `a • f x + b • f y ≤ f (a • x + b • y)` only for `x < y`
and positive `a`, `b`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.concave_on_of_lt {f : E → β} [linear_order E] (hs : convex s)
  (hf : ∀ ⦃x y : E⦄, x ∈ s → y ∈ s → x < y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
     a • f x + b • f y ≤ f (a • x + b • y)) : concave_on s f :=
@linear_order.convex_on_of_lt _ _ _ _ (order_dual β) _ _ f _ hs hf

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x<y<z`
the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is convex on `D`. This way of proving convexity
of a function is used in the proof of convexity of a function with a monotone derivative. -/
lemma convex_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ}
  (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
  convex_on s f :=
linear_order.convex_on_of_lt hs
begin
  assume x z hx hz hxz a b ha hb hab,
  let y := a * x + b * z,
  have hxy : x < y,
  { rw [← one_mul x, ← hab, add_mul],
    exact add_lt_add_left ((mul_lt_mul_left hb).2 hxz) _ },
  have hyz : y < z,
  { rw [← one_mul z, ← hab, add_mul],
    exact add_lt_add_right ((mul_lt_mul_left ha).2 hxz) _ },
  have : (f y - f x) * (z - y) ≤ (f z - f y) * (y - x),
    from (div_le_div_iff (sub_pos.2 hxy) (sub_pos.2 hyz)).1 (hf hx hz hxy hyz),
  have A : z - y + (y - x) = z - x, by abel,
  have B : 0 < z - x, from sub_pos.2 (lt_trans hxy hyz),
  rw [sub_mul, sub_mul, sub_le_iff_le_add', ← add_sub_assoc, le_sub_iff_add_le, ← mul_add, A,
    ← le_div_iff B, add_div, mul_div_assoc, mul_div_assoc,
    mul_comm (f x), mul_comm (f z)] at this,
  rw [eq_comm, ← sub_eq_iff_eq_add] at hab; subst a,
  convert this; symmetry; simp only [div_eq_iff (ne_of_gt B), y]; ring
end

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is convex on `D`, then for any three
points `x<y<z`, the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`. -/
lemma convex_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : convex_on s f)
  {x y z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
begin
  have h₁ : 0 < y - x := by linarith,
  have h₂ : 0 < z - y := by linarith,
  have h₃ : 0 < z - x := by linarith,
  suffices : f y / (y - x) + f y / (z - y) ≤ f x / (y - x) + f z / (z - y),
    by { ring_nf at this ⊢, linarith },
  set a := (z - y) / (z - x),
  set b := (y - x) / (z - x),
  have heqz : a • x + b • z = y, by { field_simp, rw div_eq_iff; [ring, linarith], },
  have key, from
    hf.2 hx hz
      (show 0 ≤ a, by apply div_nonneg; linarith)
      (show 0 ≤ b, by apply div_nonneg; linarith)
      (show a + b = 1, by { field_simp, rw div_eq_iff; [ring, linarith], }),
  rw heqz at key,
  replace key := mul_le_mul_of_nonneg_left key (le_of_lt h₃),
  field_simp [ne_of_gt h₁, ne_of_gt h₂, ne_of_gt h₃, mul_comm (z - x) _] at key ⊢,
  rw div_le_div_right,
  { linarith, },
  { nlinarith, },
end

/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is convex on `D` iff for any three
points `x<y<z` the slope of the secant line of `f` on `[x, y]` is less than or equal to the slope
of the secant line of `f` on `[x, z]`. -/
lemma convex_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} :
  convex_on s f ↔
  (∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :=
⟨convex_on.slope_mono_adjacent, convex_on_real_of_slope_mono_adjacent hs⟩

/-- For a function `f` defined on a convex subset `D` of `ℝ`, if for any three points `x<y<z`
the slope of the secant line of `f` on `[x, y]` is greater than or equal to the slope
of the secant line of `f` on `[x, z]`, then `f` is concave on `D`. -/
lemma concave_on_real_of_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ}
  (hf : ∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) : concave_on s f :=
begin
  rw [←neg_convex_on_iff],
  apply convex_on_real_of_slope_mono_adjacent hs,
  intros x y z xs zs xy yz,
  rw [←neg_le_neg_iff, ←neg_div, ←neg_div, neg_sub, neg_sub],
  simp only [hf xs zs xy yz, neg_sub_neg, pi.neg_apply],
end

/-- For a function `f` defined on a subset `D` of `ℝ`, if `f` is concave on `D`, then for any three
points `x<y<z`, the slope of the secant line of `f` on `[x, y]` is greater than or equal to the
slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on.slope_mono_adjacent {s : set ℝ} {f : ℝ → ℝ} (hf : concave_on s f)
  {x y z : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
  (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
begin
  rw [←neg_le_neg_iff, ←neg_div, ←neg_div, neg_sub, neg_sub],
  rw [←neg_sub_neg (f y), ←neg_sub_neg (f z)],
  simp_rw [←pi.neg_apply],
  rw [←neg_convex_on_iff] at hf,
  apply convex_on.slope_mono_adjacent hf; assumption,
end

/-- For a function `f` defined on a convex subset `D` of `ℝ`, `f` is concave on `D` iff for any
three points `x<y<z` the slope of the secant line of `f` on `[x, y]` is greater than or equal to
the slope of the secant line of `f` on `[x, z]`. -/
lemma concave_on_real_iff_slope_mono_adjacent {s : set ℝ} (hs : convex s) {f : ℝ → ℝ} :
  concave_on s f ↔
  (∀ {x y z : ℝ}, x ∈ s → z ∈ s → x < y → y < z →
    (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :=
⟨concave_on.slope_mono_adjacent, concave_on_real_of_slope_mono_adjacent hs⟩

lemma convex_on.subset {f : E → β} (h_convex_on : convex_on t f)
  (h_subset : s ⊆ t) (h_convex : convex s) : convex_on s f :=
begin
  apply and.intro h_convex,
  intros x y hx hy,
  exact h_convex_on.2 (h_subset hx) (h_subset hy),
end

lemma concave_on.subset {f : E → β} (h_concave_on : concave_on t f)
  (h_subset : s ⊆ t) (h_convex : convex s) : concave_on s f :=
@convex_on.subset _ _ _ _ (order_dual β) _ _ t f h_concave_on h_subset h_convex

lemma convex_on.add {f g : E → β} (hf : convex_on s f) (hg : convex_on s g) :
  convex_on s (λx, f x + g x) :=
begin
  apply and.intro hf.1,
  intros x y hx hy a b ha hb hab,
  calc
    f (a • x + b • y) + g (a • x + b • y) ≤ (a • f x + b • f y) + (a • g x + b • g y)
      : add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)
    ... = a • f x + a • g x + b • f y + b • g y : by abel
    ... = a • (f x + g x) + b • (f y + g y) : by simp [smul_add, add_assoc]
end

lemma concave_on.add {f g : E → β} (hf : concave_on s f) (hg : concave_on s g) :
  concave_on s (λx, f x + g x) :=
@convex_on.add _ _ _ _ (order_dual β) _ _ f g hf hg

lemma convex_on.smul [ordered_module ℝ β] {f : E → β} {c : ℝ} (hc : 0 ≤ c)
  (hf : convex_on s f) : convex_on s (λx, c • f x) :=
begin
  apply and.intro hf.1,
  intros x y hx hy a b ha hb hab,
  calc
    c • f (a • x + b • y) ≤ c • (a • f x + b • f y)
      : smul_le_smul_of_nonneg (hf.2 hx hy ha hb hab) hc
    ... = a • (c • f x) + b • (c • f y) : by simp only [smul_add, smul_comm c]
end

lemma concave_on.smul [ordered_module ℝ β] {f : E → β} {c : ℝ} (hc : 0 ≤ c)
  (hf : concave_on s f) : concave_on s (λx, c • f x) :=
@convex_on.smul _ _ _ _ (order_dual β) _ _ _ f c hc hf

section linear_order
variables {γ : Type*} [linear_ordered_add_comm_group γ] [module ℝ γ] [ordered_module ℝ γ]
  {f : E → γ}

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment' (hf : convex_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  f (a • x + b • y) ≤ max (f x) (f y) :=
calc
  f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • max (f x) (f y) + b • max (f x) (f y) :
    add_le_add (smul_le_smul_of_nonneg (le_max_left _ _) ha)
      (smul_le_smul_of_nonneg (le_max_right _ _) hb)
  ... = max (f x) (f y) : by rw [←add_smul, hab, one_smul]

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment' (hf : concave_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
  min (f x) (f y) ≤ f (a • x + b • y) :=
@convex_on.le_on_segment' _ _ _ _ (order_dual γ) _ _ _ f hf x y a b hx hy ha hb hab

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment (hf : convex_on s f) {x y z : E}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x, y]) :
  f z ≤ max (f x) (f y) :=
let ⟨a, b, ha, hb, hab, hz⟩ := hz in hz ▸ hf.le_on_segment' hx hy ha hb hab

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment {γ : Type*}
  [linear_ordered_add_comm_group γ] [module ℝ γ] [ordered_module ℝ γ]
  {f : E → γ} (hf : concave_on s f) {x y z : E}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x, y]) :
    min (f x) (f y) ≤ f z :=
@convex_on.le_on_segment _ _ _ _ (order_dual γ) _ _ _ f hf x y z hx hy hz

-- could be shown without contradiction but yeah
lemma convex_on.le_left_of_right_le' (hf : convex_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1)
  (hxy : f y ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f x :=
begin
  apply le_of_not_lt (λ h, lt_irrefl (f (a • x + b • y)) _),
  calc
    f (a • x + b • y)
        ≤ a • f x + b • f y : hf.2 hx hy ha.le hb hab
    ... < a • f (a • x + b • y) + b • f (a • x + b • y)
        : add_lt_add_of_lt_of_le (smul_lt_smul_of_pos h ha) (smul_le_smul_of_nonneg hxy hb)
    ... = f (a • x + b • y) : by rw [←add_smul, hab, one_smul],
end

lemma concave_on.left_le_of_le_right' (hf : concave_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1)
  (hxy : f (a • x + b • y) ≤ f y) :
  f x ≤ f (a • x + b • y) :=
@convex_on.le_left_of_right_le' _ _ _ _ (order_dual γ) _ _ _ f hf x y a b hx hy ha hb hab hxy

lemma convex_on.le_right_of_left_le' (hf : convex_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hxy : f x ≤ f (a • x + b • y)) :
  f (a • x + b • y) ≤ f y :=
begin
  rw add_comm at ⊢ hab hxy,
  exact hf.le_left_of_right_le' hy hx hb ha hab hxy,
end

lemma concave_on.le_right_of_left_le' (hf : concave_on s f) {x y : E} {a b : ℝ}
  (hx : x ∈ s) (hy : y ∈ s) (ha : 0 ≤ a) (hb : 0 < b) (hab : a + b = 1)
  (hxy : f (a • x + b • y) ≤ f x) :
  f y ≤ f (a • x + b • y) :=
@convex_on.le_right_of_left_le' _ _ _ _ (order_dual γ) _ _ _ f hf x y a b hx hy ha hb hab hxy

lemma convex_on.le_left_of_right_le (hf : convex_on s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment x y) (hyz : f y ≤ f z) :
  f z ≤ f x :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.le_left_of_right_le' hx hy ha hb.le hab hyz,
end

lemma concave_on.left_le_of_le_right (hf : concave_on s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment x y) (hyz : f z ≤ f y) :
  f x ≤ f z :=
@convex_on.le_left_of_right_le _ _ _ _ (order_dual γ) _ _ _ f hf x y z hx hy hz hyz

lemma convex_on.le_right_of_left_le (hf : convex_on s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment x y) (hxz : f x ≤ f z) :
  f z ≤ f y :=
begin
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz,
  exact hf.le_right_of_left_le' hx hy ha.le hb hab hxz,
end

lemma concave_on.le_right_of_left_le (hf : concave_on s f) {x y z : E} (hx : x ∈ s)
  (hy : y ∈ s) (hz : z ∈ open_segment x y) (hxz : f z ≤ f x) :
  f y ≤ f z :=
@convex_on.le_right_of_left_le _ _ _ _ (order_dual γ) _ _ _ f hf x y z hx hy hz hxz

end linear_order

lemma convex_on.convex_le [ordered_module ℝ β] {f : E → β} (hf : convex_on s f) (r : β) :
  convex {x ∈ s | f x ≤ r} :=
λ x y hx hy a b ha hb hab,
begin
  refine ⟨hf.1 hx.1 hy.1 ha hb hab, _⟩,
  calc
    f (a • x + b • y) ≤ a • (f x) + b • (f y) : hf.2 hx.1 hy.1 ha hb hab
                  ... ≤ a • r + b • r         : add_le_add (smul_le_smul_of_nonneg hx.2 ha)
                                                  (smul_le_smul_of_nonneg hy.2 hb)
                  ... ≤ r                     : by simp [←add_smul, hab]
end

lemma concave_on.concave_le [ordered_module ℝ β] {f : E → β} (hf : concave_on s f) (r : β) :
  convex {x ∈ s | r ≤ f x} :=
@convex_on.convex_le _ _ _ _ (order_dual β) _ _ _ f hf r

lemma convex_on.convex_lt {γ : Type*} [ordered_cancel_add_comm_monoid γ]
  [module ℝ γ] [ordered_module ℝ γ]
  {f : E → γ} (hf : convex_on s f) (r : γ) : convex {x ∈ s | f x < r} :=
begin
  intros a b as bs xa xb hxa hxb hxaxb,
  refine ⟨hf.1 as.1 bs.1 hxa hxb hxaxb, _⟩,
  by_cases H : xa = 0,
  { have H' : xb = 1 := by rwa [H, zero_add] at hxaxb,
    rw [H, H', zero_smul, one_smul, zero_add],
    exact bs.2 },
  { calc
      f (xa • a + xb • b) ≤ xa • (f a) + xb • (f b) : hf.2 as.1 bs.1 hxa hxb hxaxb
                      ... < xa • r + xb • (f b)     : (add_lt_add_iff_right (xb • (f b))).mpr
                                                        (smul_lt_smul_of_pos as.2
                                                          (lt_of_le_of_ne hxa (ne.symm H)))
                      ... ≤ xa • r + xb • r         : (add_le_add_iff_left (xa • r)).mpr
                                                        (smul_le_smul_of_nonneg bs.2.le hxb)
                      ... = r                       : by simp only [←add_smul, hxaxb, one_smul] }
end

lemma concave_on.convex_lt {γ : Type*} [ordered_cancel_add_comm_monoid γ]
  [module ℝ γ] [ordered_module ℝ γ]
  {f : E → γ} (hf : concave_on s f) (r : γ) : convex {x ∈ s | r < f x} :=
@convex_on.convex_lt _ _ _ _ (order_dual γ) _ _ _ f hf r

lemma convex_on.convex_epigraph {γ : Type*} [ordered_add_comm_group γ]
  [module ℝ γ] [ordered_module ℝ γ]
  {f : E → γ} (hf : convex_on s f) :
  convex {p : E × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  rintros ⟨x, r⟩ ⟨y, t⟩ ⟨hx, hr⟩ ⟨hy, ht⟩ a b ha hb hab,
  refine ⟨hf.1 hx hy ha hb hab, _⟩,
  calc f (a • x + b • y) ≤ a • f x + b • f y : hf.2 hx hy ha hb hab
  ... ≤ a • r + b • t : add_le_add (smul_le_smul_of_nonneg hr ha)
                            (smul_le_smul_of_nonneg ht hb)
end

lemma concave_on.convex_hypograph {γ : Type*} [ordered_add_comm_group γ]
  [module ℝ γ] [ordered_module ℝ γ]
  {f : E → γ} (hf : concave_on s f) :
  convex {p : E × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on.convex_epigraph _ _ _ _ (order_dual γ) _ _ _ f hf

lemma convex_on_iff_convex_epigraph {γ : Type*} [ordered_add_comm_group γ]
  [module ℝ γ] [ordered_module ℝ γ]
  {f : E → γ} :
  convex_on s f ↔ convex {p : E × γ | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  refine ⟨convex_on.convex_epigraph, λ h, ⟨_, _⟩⟩,
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).1 },
  { assume x y hx hy a b ha hb hab,
    exact (@h (x, f x) (y, f y) ⟨hx, le_refl _⟩ ⟨hy, le_refl _⟩ a b ha hb hab).2 }
end

lemma concave_on_iff_convex_hypograph {γ : Type*} [ordered_add_comm_group γ]
  [module ℝ γ] [ordered_module ℝ γ]
  {f : E → γ} :
  concave_on s f ↔ convex {p : E × γ | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on_iff_convex_epigraph _ _ _ _ (order_dual γ) _ _ _ f

/- A linear map is convex. -/
lemma linear_map.convex_on (f : E →ₗ[ℝ] β) {s : set E} (hs : convex s) : convex_on s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/- A linear map is concave. -/
lemma linear_map.concave_on (f : E →ₗ[ℝ] β) {s : set E} (hs : convex s) : concave_on s f :=
⟨hs, λ _ _ _ _ _ _ _ _ _, by rw [f.map_add, f.map_smul, f.map_smul]⟩

/-- If a function is convex on `s`, it remains convex when precomposed by an affine map. -/
lemma convex_on.comp_affine_map {f : F → β} (g : E →ᵃ[ℝ] F) {s : set F}
  (hf : convex_on s f) : convex_on (g ⁻¹' s) (f ∘ g) :=
begin
  refine ⟨hf.1.affine_preimage  _,_⟩,
  intros x y xs ys a b ha hb hab,
  calc
    (f ∘ g) (a • x + b • y) = f (g (a • x + b • y))         : rfl
                       ...  = f (a • (g x) + b • (g y))     : by rw [convex.combo_affine_apply hab]
                       ...  ≤ a • f (g x) + b • f (g y)     : hf.2 xs ys ha hb hab
                       ...  = a • (f ∘ g) x + b • (f ∘ g) y : rfl
end

/-- If a function is concave on `s`, it remains concave when precomposed by an affine map. -/
lemma concave_on.comp_affine_map {f : F → β} (g : E →ᵃ[ℝ] F) {s : set F}
  (hf : concave_on s f) : concave_on (g ⁻¹' s) (f ∘ g) :=
@convex_on.comp_affine_map _ _ _ _ _ _ (order_dual β) _ _ f g s hf

/-- If `g` is convex on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
lemma convex_on.comp_linear_map {g : F → β} {s : set F} (hg : convex_on s g) (f : E →ₗ[ℝ] F) :
  convex_on (f ⁻¹' s) (g ∘ f) :=
hg.comp_affine_map f.to_affine_map

/-- If `g` is concave on `s`, so is `(g ∘ f)` on `f ⁻¹' s` for a linear `f`. -/
lemma concave_on.comp_linear_map {g : F → β} {s : set F} (hg : concave_on s g) (f : E →ₗ[ℝ] F) :
  concave_on (f ⁻¹' s) (g ∘ f) :=
hg.comp_affine_map f.to_affine_map

/-- If a function is convex on `s`, it remains convex after a translation. -/
lemma convex_on.translate_right {f : E → β} {s : set E} {a : E} (hf : convex_on s f) :
  convex_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const ℝ E a +ᵥ affine_map.id ℝ E

/-- If a function is concave on `s`, it remains concave after a translation. -/
lemma concave_on.translate_right {f : E → β} {s : set E} {a : E} (hf : concave_on s f) :
  concave_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const ℝ E a +ᵥ affine_map.id ℝ E

/-- If a function is convex on `s`, it remains convex after a translation. -/
lemma convex_on.translate_left {f : E → β} {s : set E} {a : E} (hf : convex_on s f) :
  convex_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using  hf.translate_right

/-- If a function is concave on `s`, it remains concave after a translation. -/
lemma concave_on.translate_left {f : E → β} {s : set E} {a : E} (hf : concave_on s f) :
  concave_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using  hf.translate_right

end functions

/-! ### Center of mass -/

section center_mass

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
noncomputable def finset.center_mass (t : finset ι) (w : ι → ℝ) (z : ι → E) : E :=
(∑ i in t, w i)⁻¹ • (∑ i in t, w i • z i)

variables (i j : ι) (c : ℝ) (t : finset ι) (w : ι → ℝ) (z : ι → E)

open finset

lemma finset.center_mass_empty : (∅ : finset ι).center_mass w z = 0 :=
by simp only [center_mass, sum_empty, smul_zero]

lemma finset.center_mass_pair (hne : i ≠ j) :
  ({i, j} : finset ι).center_mass w z = (w i / (w i + w j)) • z i + (w j / (w i + w j)) • z j :=
by simp only [center_mass, sum_pair hne, smul_add, (mul_smul _ _ _).symm, div_eq_inv_mul]

variable {w}

lemma finset.center_mass_insert (ha : i ∉ t) (hw : ∑ j in t, w j ≠ 0) :
  (insert i t).center_mass w z = (w i / (w i + ∑ j in t, w j)) • z i +
    ((∑ j in t, w j) / (w i + ∑ j in t, w j)) • t.center_mass w z :=
begin
  simp only [center_mass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ← div_eq_inv_mul],
  congr' 2,
  rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div]
end

lemma finset.center_mass_singleton (hw : w i ≠ 0) : ({i} : finset ι).center_mass w z = z i :=
by rw [center_mass, sum_singleton, sum_singleton, ← mul_smul, inv_mul_cancel hw, one_smul]

lemma finset.center_mass_eq_of_sum_1 (hw : ∑ i in t, w i = 1) :
  t.center_mass w z = ∑ i in t, w i • z i :=
by simp only [finset.center_mass, hw, inv_one, one_smul]

lemma finset.center_mass_smul : t.center_mass w (λ i, c • z i) = c • t.center_mass w z :=
by simp only [finset.center_mass, finset.smul_sum, (mul_smul _ _ _).symm, mul_comm c, mul_assoc]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
lemma finset.center_mass_segment'
  (s : finset ι) (t : finset ι') (ws : ι → ℝ) (zs : ι → E) (wt : ι' → ℝ) (zt : ι' → E)
  (hws : ∑ i in s, ws i = 1) (hwt : ∑ i in t, wt i = 1) (a b : ℝ) (hab : a + b = 1) :
  a • s.center_mass ws zs + b • t.center_mass wt zt =
    (s.map function.embedding.inl ∪ t.map function.embedding.inr).center_mass
      (sum.elim (λ i, a * ws i) (λ j, b * wt j))
      (sum.elim zs zt) :=
begin
  rw [s.center_mass_eq_of_sum_1 _ hws, t.center_mass_eq_of_sum_1 _ hwt,
    smul_sum, smul_sum, ← finset.sum_sum_elim, finset.center_mass_eq_of_sum_1],
  { congr' with ⟨⟩; simp only [sum.elim_inl, sum.elim_inr, mul_smul] },
  { rw [sum_sum_elim, ← mul_sum, ← mul_sum, hws, hwt, mul_one, mul_one, hab] }
end

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
lemma finset.center_mass_segment
  (s : finset ι) (w₁ w₂ : ι → ℝ) (z : ι → E)
  (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (a b : ℝ) (hab : a + b = 1) :
  a • s.center_mass w₁ z + b • s.center_mass w₂ z =
    s.center_mass (λ i, a * w₁ i + b * w₂ i) z :=
have hw : ∑ i in s, (a * w₁ i + b * w₂ i) = 1,
  by simp only [mul_sum.symm, sum_add_distrib, mul_one, *],
by simp only [finset.center_mass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul, *]

lemma finset.center_mass_ite_eq (hi : i ∈ t) :
  t.center_mass (λ j, if (i = j) then 1 else 0) z = z i :=
begin
  rw [finset.center_mass_eq_of_sum_1],
  transitivity ∑ j in t, if (i = j) then z i else 0,
  { congr' with i, split_ifs, exacts [h ▸ one_smul _ _, zero_smul _ _] },
  { rw [sum_ite_eq, if_pos hi] },
  { rw [sum_ite_eq, if_pos hi] }
end

variables {t w}

lemma finset.center_mass_subset {t' : finset ι} (ht : t ⊆ t')
  (h : ∀ i ∈ t', i ∉ t → w i = 0) :
  t.center_mass w z = t'.center_mass w z :=
begin
  rw [center_mass, sum_subset ht h, smul_sum, center_mass, smul_sum],
  apply sum_subset ht,
  assume i hit' hit,
  rw [h i hit' hit, zero_smul, smul_zero]
end

lemma finset.center_mass_filter_ne_zero :
  (t.filter (λ i, w i ≠ 0)).center_mass w z = t.center_mass w z :=
finset.center_mass_subset z (filter_subset _ _) $ λ i hit hit',
  by simpa only [hit, mem_filter, true_and, ne.def, not_not] using hit'

variable {z}

/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
lemma convex.center_mass_mem (hs : convex s) :
  (∀ i ∈ t, 0 ≤ w i) → (0 < ∑ i in t, w i) → (∀ i ∈ t, z i ∈ s) → t.center_mass w z ∈ s :=
begin
  induction t using finset.induction with i t hi ht, { simp [lt_irrefl] },
  intros h₀ hpos hmem,
  have zi : z i ∈ s, from hmem _ (mem_insert_self _ _),
  have hs₀ : ∀ j ∈ t, 0 ≤ w j, from λ j hj, h₀ j $ mem_insert_of_mem hj,
  rw [sum_insert hi] at hpos,
  by_cases hsum_t : ∑ j in t, w j = 0,
  { have ws : ∀ j ∈ t, w j = 0, from (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t,
    have wz : ∑ j in t, w j • z j = 0, from sum_eq_zero (λ i hi, by simp [ws i hi]),
    simp only [center_mass, sum_insert hi, wz, hsum_t, add_zero],
    simp only [hsum_t, add_zero] at hpos,
    rw [← mul_smul, inv_mul_cancel (ne_of_gt hpos), one_smul],
    exact zi },
  { rw [finset.center_mass_insert _ _ _ hi hsum_t],
    refine convex_iff_div.1 hs zi (ht hs₀ _ _) _ (sum_nonneg hs₀) hpos,
    { exact lt_of_le_of_ne (sum_nonneg hs₀) (ne.symm hsum_t) },
    { intros j hj, exact hmem j (mem_insert_of_mem hj) },
    { exact h₀ _ (mem_insert_self _ _) } }
end

lemma convex.sum_mem (hs : convex s) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hz : ∀ i ∈ t, z i ∈ s) :
  ∑ i in t, w i • z i ∈ s :=
by simpa only [h₁, center_mass, inv_one, one_smul] using
  hs.center_mass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

lemma convex_iff_sum_mem :
  convex s ↔
    (∀ (t : finset E) (w : E → ℝ),
      (∀ i ∈ t, 0 ≤ w i) → ∑ i in t, w i = 1 → (∀ x ∈ t, x ∈ s) → ∑ x in t, w x • x ∈ s ) :=
begin
  refine ⟨λ hs t w hw₀ hw₁ hts, hs.sum_mem hw₀ hw₁ hts, _⟩,
  intros h x y hx hy a b ha hb hab,
  by_cases h_cases: x = y,
  { rw [h_cases, ←add_smul, hab, one_smul], exact hy },
  { convert h {x, y} (λ z, if z = y then b else a) _ _ _,
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl] },
    { simp_intros i hi,
      cases hi; subst i; simp [ha, hb, if_neg h_cases] },
    { simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl, hab] },
    { simp_intros i hi,
      cases hi; subst i; simp [hx, hy, if_neg h_cases] } }
end

/-- Jensen's inequality, `finset.center_mass` version. -/
lemma convex_on.map_center_mass_le {f : E → ℝ} (hf : convex_on s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (hpos : 0 < ∑ i in t, w i)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (t.center_mass w z) ≤ t.center_mass w (f ∘ z) :=
begin
  have hmem' : ∀ i ∈ t, (z i, (f ∘ z) i) ∈ {p : E × ℝ | p.1 ∈ s ∧ f p.1 ≤ p.2},
    from λ i hi, ⟨hmem i hi, le_refl _⟩,
  convert (hf.convex_epigraph.center_mass_mem h₀ hpos hmem').2;
    simp only [center_mass, function.comp, prod.smul_fst, prod.fst_sum, prod.smul_snd, prod.snd_sum]
end

/-- Jensen's inequality, `finset.sum` version. -/
lemma convex_on.map_sum_le {f : E → ℝ} (hf : convex_on s f)
  (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i in t, w i = 1)
  (hmem : ∀ i ∈ t, z i ∈ s) : f (∑ i in t, w i • z i) ≤ ∑ i in t, w i * (f (z i)) :=
by simpa only [center_mass, h₁, inv_one, one_smul]
  using hf.map_center_mass_le h₀ (h₁.symm ▸ zero_lt_one) hmem

/-- If a function `f` is convex on `s` takes value `y` at the center of mass of some points
`z i ∈ s`, then for some `i` we have `y ≤ f (z i)`. -/
lemma convex_on.exists_ge_of_center_mass {f : E → ℝ} (h : convex_on s f)
  (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hws : 0 < ∑ i in t, w i) (hz : ∀ i ∈ t, z i ∈ s) :
  ∃ i ∈ t, f (t.center_mass w z) ≤ f (z i) :=
begin
  set y := t.center_mass w z,
  have : f y ≤ t.center_mass w (f ∘ z) := h.map_center_mass_le hw₀ hws hz,
  rw ← sum_filter_ne_zero at hws,
  rw [← finset.center_mass_filter_ne_zero (f ∘ z), center_mass, smul_eq_mul,
    ← div_eq_inv_mul, le_div_iff hws, mul_sum] at this,
  replace : ∃ i ∈ t.filter (λ i, w i ≠ 0), f y * w i ≤ w i • (f ∘ z) i :=
    exists_le_of_sum_le (nonempty_of_sum_ne_zero (ne_of_gt hws)) this,
  rcases this with ⟨i, hi, H⟩,
  rw [mem_filter] at hi,
  use [i, hi.1],
  simp only [smul_eq_mul, mul_comm (w i)] at H,
  refine (mul_le_mul_right _).1 H,
  exact lt_of_le_of_ne (hw₀ i hi.1) hi.2.symm
end

end center_mass

/-! ### Convex hull -/

section convex_hull

variable {t : set E}

/-- The convex hull of a set `s` is the minimal convex set that includes `s`. -/
def convex_hull : closure_operator (set E) :=
closure_operator.mk₃
  (λ s, ⋂ (t : set E) (hst : s ⊆ t) (ht : convex t), t)
  convex
  (λ s, set.subset_Inter (λ t, set.subset_Inter $ λ hst, set.subset_Inter $ λ ht, hst))
  (λ s, convex_Inter $ λ t, convex_Inter $ λ ht, convex_Inter id)
  (λ s t hst ht, set.Inter_subset_of_subset t $ set.Inter_subset_of_subset hst $
  set.Inter_subset _ ht)

variable (s)

lemma subset_convex_hull : s ⊆ convex_hull s :=
convex_hull.le_closure s

lemma convex_convex_hull : convex (convex_hull s) :=
closure_operator.closure_mem_mk₃ s

variable {s}

lemma convex_hull_min (hst : s ⊆ t) (ht : convex t) : convex_hull s ⊆ t :=
closure_operator.closure_le_mk₃_iff (show s ≤ t, from hst) ht

lemma convex_hull_mono (hst : s ⊆ t) : convex_hull s ⊆ convex_hull t :=
convex_hull.monotone hst

lemma convex.convex_hull_eq {s : set E} (hs : convex s) : convex_hull s = s :=
closure_operator.mem_mk₃_closed hs

@[simp]
lemma convex_hull_empty :
  convex_hull (∅ : set E) = ∅ :=
convex_empty.convex_hull_eq

@[simp]
lemma convex_hull_empty_iff :
  convex_hull s = ∅ ↔ s = ∅ :=
begin
  split,
  { intro h,
    rw [←set.subset_empty_iff, ←h],
    exact subset_convex_hull _ },
  { rintro rfl,
    exact convex_hull_empty }
end

@[simp] lemma convex_hull_nonempty_iff :
  (convex_hull s).nonempty ↔ s.nonempty :=
begin
  rw [←ne_empty_iff_nonempty, ←ne_empty_iff_nonempty, ne.def, ne.def],
  exact not_congr convex_hull_empty_iff,
end

@[simp]
lemma convex_hull_singleton {x : E} : convex_hull ({x} : set E) = {x} :=
(convex_singleton x).convex_hull_eq

lemma convex.convex_remove_iff_not_mem_convex_hull_remove {s : set E} (hs : convex s) (x : E) :
  convex (s \ {x}) ↔ x ∉ convex_hull (s \ {x}) :=
begin
  split,
  { rintro hsx hx,
    rw hsx.convex_hull_eq at hx,
    exact hx.2 (mem_singleton _) },
  rintro hx,
  suffices h : s \ {x} = convex_hull (s \ {x}), { convert convex_convex_hull _ },
  exact subset.antisymm (subset_convex_hull _) (λ y hy, ⟨convex_hull_min (diff_subset _ _) hs hy,
    by { rintro (rfl : y = x), exact hx hy }⟩),
end

lemma is_linear_map.image_convex_hull {f : E → F} (hf : is_linear_map ℝ f) :
  f '' (convex_hull s) = convex_hull (f '' s) :=
begin
  refine set.subset.antisymm _ _,
  { rw [set.image_subset_iff],
    exact convex_hull_min (set.image_subset_iff.1 $ subset_convex_hull $ f '' s)
      ((convex_convex_hull (f '' s)).is_linear_preimage hf) },
  { exact convex_hull_min (set.image_subset _ $ subset_convex_hull s)
     ((convex_convex_hull s).is_linear_image hf) }
end

lemma linear_map.image_convex_hull (f : E →ₗ[ℝ] F) :
  f '' (convex_hull s) = convex_hull (f '' s) :=
f.is_linear.image_convex_hull

lemma finset.center_mass_mem_convex_hull (t : finset ι) {w : ι → ℝ} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
  (hws : 0 < ∑ i in t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
  t.center_mass w z ∈ convex_hull s :=
(convex_convex_hull s).center_mass_mem hw₀ hws (λ i hi, subset_convex_hull s $ hz i hi)

-- TODO : Do we need other versions of the next lemma?

/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `z '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
lemma convex_hull_eq (s : set E) :
  convex_hull s = {x : E | ∃ (ι : Type u') (t : finset ι) (w : ι → ℝ) (z : ι → E)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i in t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s),
    t.center_mass w z = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    use [punit, {punit.star}, λ _, 1, λ _, x, λ _ _, zero_le_one,
      finset.sum_singleton, λ _ _, hx],
    simp only [finset.center_mass, finset.sum_singleton, inv_one, one_smul] },
  { rintros x y ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩
      a b ha hb hab,
    rw [finset.center_mass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, _, _, _, _, rfl⟩,
    { rintros i hi,
      rw [finset.mem_union, finset.mem_map, finset.mem_map] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr];
        apply_rules [mul_nonneg, hwx₀, hwy₀] },
    { simp [finset.sum_sum_elim, finset.mul_sum.symm, *] },
    { intros i hi,
      rw [finset.mem_union, finset.mem_map, finset.mem_map] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩; apply_rules [hzx, hzy] } },
  { rintros _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    exact t.center_mass_mem_convex_hull hw₀ (hw₁.symm ▸ zero_lt_one) hz }
end

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then `f` can't have a maximum on `convex_hull s` outside of `s`. -/
lemma convex_on.exists_ge_of_mem_convex_hull {f : E → ℝ} (hf : convex_on (convex_hull s) f)
  {x} (hx : x ∈ convex_hull s) : ∃ y ∈ s, f x ≤ f y :=
begin
  rw convex_hull_eq at hx,
  rcases hx with ⟨α, t, w, z, hw₀, hw₁, hz, rfl⟩,
  rcases hf.exists_ge_of_center_mass hw₀ (hw₁.symm ▸ zero_lt_one)
    (λ i hi, subset_convex_hull s (hz i hi)) with ⟨i, hit, Hi⟩,
  exact ⟨z i, hz i hit, Hi⟩
end

lemma finset.convex_hull_eq (s : finset E) :
  convex_hull ↑s = {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y in s, w y = 1),
    s.center_mass w id = x} :=
begin
  refine subset.antisymm (convex_hull_min _ _) _,
  { intros x hx,
    rw [finset.mem_coe] at hx,
    refine ⟨_, _, _, finset.center_mass_ite_eq _ _ _ hx⟩,
    { intros, split_ifs, exacts [zero_le_one, le_refl 0] },
    { rw [finset.sum_ite_eq, if_pos hx] } },
  { rintros x y ⟨wx, hwx₀, hwx₁, rfl⟩ ⟨wy, hwy₀, hwy₁, rfl⟩
      a b ha hb hab,
    rw [finset.center_mass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab],
    refine ⟨_, _, _, rfl⟩,
    { rintros i hi,
      apply_rules [add_nonneg, mul_nonneg, hwx₀, hwy₀], },
    { simp only [finset.sum_add_distrib, finset.mul_sum.symm, mul_one, *] } },
  { rintros _ ⟨w, hw₀, hw₁, rfl⟩,
    exact s.center_mass_mem_convex_hull (λ x hx, hw₀ _  hx)
      (hw₁.symm ▸ zero_lt_one) (λ x hx, hx) }
end

lemma set.finite.convex_hull_eq {s : set E} (hs : finite s) :
  convex_hull s = {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ s, 0 ≤ w y)
    (hw₁ : ∑ y in hs.to_finset, w y = 1), hs.to_finset.center_mass w id = x} :=
by simpa only [set.finite.coe_to_finset, set.finite.mem_to_finset, exists_prop]
  using hs.to_finset.convex_hull_eq

lemma convex_hull_eq_union_convex_hull_finite_subsets (s : set E) :
  convex_hull s = ⋃ (t : finset E) (w : ↑t ⊆ s), convex_hull ↑t :=
begin
  refine subset.antisymm _ _,
  { rw [convex_hull_eq.{u}],
    rintros x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩,
    simp only [mem_Union],
    refine ⟨t.image z, _, _⟩,
    { rw [finset.coe_image, image_subset_iff],
      exact hz },
    { apply t.center_mass_mem_convex_hull hw₀,
      { simp only [hw₁, zero_lt_one] },
      { exact λ i hi, finset.mem_coe.2 (finset.mem_image_of_mem _ hi) } } },
   { exact Union_subset (λ i, Union_subset convex_hull_mono), },
end

lemma is_linear_map.convex_hull_image {f : E → F} (hf : is_linear_map ℝ f) (s : set E) :
  convex_hull (f '' s) = f '' convex_hull s :=
set.subset.antisymm (convex_hull_min (image_subset _ (subset_convex_hull s)) $
  (convex_convex_hull s).is_linear_image hf)
  (image_subset_iff.2 $ convex_hull_min
    (image_subset_iff.1 $ subset_convex_hull _)
    ((convex_convex_hull _).is_linear_preimage hf))

lemma linear_map.convex_hull_image (f : E →ₗ[ℝ] F) (s : set E) :
  convex_hull (f '' s) = f '' convex_hull s :=
f.is_linear.convex_hull_image s

end convex_hull

/-! ### Simplex -/

section simplex

variables (ι) [fintype ι] {f : ι → ℝ}

/-- The standard simplex in the space of functions `ι → ℝ` is the set
of vectors with non-negative coordinates with total sum `1`. -/
def std_simplex (ι : Type*) [fintype ι] : set (ι → ℝ) :=
{f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1}

lemma std_simplex_eq_inter :
  std_simplex ι = (⋂ x, {f | 0 ≤ f x}) ∩ {f | ∑ x, f x = 1} :=
by { ext f, simp only [std_simplex, set.mem_inter_eq, set.mem_Inter, set.mem_set_of_eq] }

lemma convex_std_simplex : convex (std_simplex ι) :=
begin
  refine λ f g hf hg a b ha hb hab, ⟨λ x, _, _⟩,
  { apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1] },
  { erw [finset.sum_add_distrib, ← finset.smul_sum, ← finset.smul_sum, hf.2, hg.2,
      smul_eq_mul, smul_eq_mul, mul_one, mul_one],
    exact hab }
end

variable {ι}

lemma ite_eq_mem_std_simplex (i : ι) : (λ j, ite (i = j) (1:ℝ) 0) ∈ std_simplex ι :=
⟨λ j, by simp only; split_ifs; norm_num, by rw [finset.sum_ite_eq, if_pos (finset.mem_univ _)]⟩

/-- `std_simplex ι` is the convex hull of the canonical basis in `ι → ℝ`. -/
lemma convex_hull_basis_eq_std_simplex :
  convex_hull (range $ λ(i j:ι), if i = j then (1:ℝ) else 0) = std_simplex ι :=
begin
  refine subset.antisymm (convex_hull_min _ (convex_std_simplex ι)) _,
  { rintros _ ⟨i, rfl⟩,
    exact ite_eq_mem_std_simplex i },
  { rintros w ⟨hw₀, hw₁⟩,
    rw [pi_eq_sum_univ w, ← finset.univ.center_mass_eq_of_sum_1 _ hw₁],
    exact finset.univ.center_mass_mem_convex_hull (λ i hi, hw₀ i)
      (hw₁.symm ▸ zero_lt_one) (λ i hi, mem_range_self i) }
end

variable {ι}

/-- The convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `∑ x in s, w x • x`.

Since we have no sums over finite sets, we use sum over `@finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
lemma set.finite.convex_hull_eq_image {s : set E} (hs : finite s) :
  convex_hull s = by haveI := hs.fintype; exact
    (⇑(∑ x : s, (@linear_map.proj ℝ s _ (λ i, ℝ) _ _ x).smul_right x.1)) '' (std_simplex s) :=
begin
  rw [← convex_hull_basis_eq_std_simplex, ← linear_map.convex_hull_image, ← set.range_comp, (∘)],
  apply congr_arg,
  convert subtype.range_coe.symm,
  ext x,
  simp [linear_map.sum_apply, ite_smul, finset.filter_eq]
end

/-- All values of a function `f ∈ std_simplex ι` belong to `[0, 1]`. -/
lemma mem_Icc_of_mem_std_simplex (hf : f ∈ std_simplex ι) (x) :
  f x ∈ I :=
⟨hf.1 x, hf.2 ▸ finset.single_le_sum (λ y hy, hf.1 y) (finset.mem_univ x)⟩

end simplex
