/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import data.complex.module
import linear_algebra.affine_space.slope
import linear_algebra.affine_space.combination

/-!
# Convex sets and functions on real vector spaces

In a real vector space, we define the following objects and properties.

* `segment x y` is the closed segment joining `x` and `y`.
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
defined using the instance `ordered_semimodule ℝ β`.

## Notations

We use the following local notations:

* `I = Icc (0:ℝ) 1`;
* `[x, y] = segment x y`.

They are defined using `local notation`, so they are not available outside of this file.
-/

variables {E F PE PF ι ι' α : Type*}
  [add_comm_group E] [vector_space ℝ E] [add_torsor E PE]
  [add_comm_group F] [vector_space ℝ F] [add_torsor F PF]
  [linear_ordered_field α]
  {s : set PE}

include E

open set linear_map
open_locale classical big_operators

local notation `I` := (Icc 0 1 : set ℝ)

section sets

/-! ### Segment -/

open affine_map

/-- Segments in an affine space -/
def segment (x y : PE) : set PE := line_map x y '' I
local notation `[`x `, ` y `]` := segment x y

omit E

lemma segment_eq_interval (a b : ℝ) : segment a b = interval a b :=
by rw [segment, ← interval_of_le (@zero_le_one ℝ _), image_interval, line_map_apply_zero,
  line_map_apply_one]

lemma segment_eq_Icc {a b : ℝ} (h : a ≤ b) : [a, b] = Icc a b :=
by rw [segment_eq_interval, interval_of_le h]

include E

lemma segment_symm (x y : PE) : [x, y] = [y, x] :=
by rw [segment, segment, line_map_symm, coe_comp, image_comp, ← segment, segment_eq_interval,
  interval_of_ge (@zero_le_one ℝ _)]

lemma left_mem_segment (x y : PE) : x ∈ [x, y] :=
⟨0, ⟨le_refl 0, zero_le_one⟩, line_map_apply_zero _ _⟩

lemma right_mem_segment (x y : PE) : y ∈ [x, y] :=
segment_symm y x ▸ left_mem_segment y x

lemma segment_same (x : PE) : [x, x] = {x} :=
by { rw [segment, line_map_same, coe_const], exact (nonempty_Icc.2 zero_le_one).image_const _ }

lemma segment_eq_image (x y : PE) : segment x y = (λ θ, θ • (y -ᵥ x) +ᵥ x) '' I := rfl

include F

lemma affine_map.image_segment (f : PE →ᵃ[ℝ] PF) (x y : PE) :
  f '' [x, y] = [f x, f y] :=
by rw [segment, segment, ← image_comp, ← coe_comp, comp_line_map]

omit F

lemma segment_translate_image (a : E) (b c : PE) : (λx, a +ᵥ x) '' [b, c] = [a +ᵥ b, a +ᵥ c] :=
(const ℝ PE a +ᵥ affine_map.id ℝ PE).image_segment b c

lemma segment_translate_preimage (a : E) (b c : PE) :
  (λ x, a +ᵥ x) ⁻¹' [a +ᵥ b, a +ᵥ c] = [b, c] :=
segment_translate_image a b c ▸ preimage_image_eq _ (equiv.const_vadd PE a).injective

lemma mem_segment_translate (a : E) {x b c : PE} : a +ᵥ x ∈ [a +ᵥ b, a +ᵥ c] ↔ x ∈ [b, c] :=
by rw [← segment_translate_preimage a b c, mem_preimage]

/-! ### Convexity of sets -/
/-- Convexity of sets -/
def convex (s : set PE) := ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), maps_to (line_map x y) I s

lemma convex.segment_subset {s : set PE} (hs : convex s) {x y} (hx : x ∈ s) (hy : y ∈ s) :
  [x, y] ⊆ s :=
(hs hx hy).image_subset

lemma convex_iff_open_segment_subset :
  convex s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), maps_to (line_map x y) (Ioo (0:ℝ) 1) s :=
begin
  refine ⟨λ h x hx y hy, (h hx hy).mono Ioo_subset_Icc_self (subset.refl _), _⟩,
  intros h x hx y hy θ hθ,
  rcases mem_Ioo_or_eq_endpoints_of_mem_Icc hθ with rfl|rfl|hθ;
    [simpa only [line_map_apply_zero], simpa [line_map], exact h hx hy hθ]
end

lemma convex_iff_segment_subset : convex s ↔ ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), [x, y] ⊆ s :=
by simp only [convex, maps_to', segment]

/-
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

/-- Alternative definition of set convexity, using division -/
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
-/

/-! ### Examples of convex sets -/

lemma convex_empty : convex (∅ : set PE) :=  by finish

lemma convex_singleton (c : PE) : convex ({c} : set PE) :=
begin
  rintros x (rfl|_) y (rfl|_) a ha,
  simp
end

lemma convex_univ : convex (set.univ : set PE) := λ _ _ _ _, maps_to_univ _ _

lemma convex.inter {t : set PE} (hs: convex s) (ht: convex t) : convex (s ∩ t) :=
λ x hx y hy, (hs hx.left hy.left).inter (ht hx.right hy.right)

lemma convex_sInter {S : set (set PE)} (h : ∀ s ∈ S, convex s) : convex (⋂₀ S) :=
assume x hx y hy, maps_to_sInter $ λ s hs, h s hs (hx s hs) (hy s hs)

lemma convex_Inter {ι : Sort*} {s: ι → set PE} (h: ∀ i : ι, convex (s i)) : convex (⋂ i, s i) :=
(sInter_range s) ▸ convex_sInter $ forall_range_iff.2 h

include F

lemma convex.prod {s : set PE} {t : set PF} (hs : convex s) (ht : convex t) :
  convex (s.prod t) :=
λ x hx y hy a ha, ⟨hs hx.1 hy.1 ha, ht hx.2 hy.2 ha⟩

/-- The preimage of a convex set under an affine map is convex. -/
lemma convex.affine_preimage (f : PE →ᵃ[ℝ] PF) {s : set PF} (hs : convex s) :
  convex (f ⁻¹' s) :=
begin
  intros x hx y hy a ha,
  rw [mem_preimage, f.apply_line_map],
  exact hs hx hy ha
end

/-- The image of a convex set under an affine map is convex. -/
lemma convex.affine_image (f : PE →ᵃ[ℝ] PF) (hs : convex s) :
  convex (f '' s) :=
begin
  rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩,
  rw [← comp_line_map, coe_comp],
  exact (maps_to_image f s).comp (hs hx hy)
end

lemma convex.linear_image {s : set E} (hs : convex s) (f : E →ₗ[ℝ] F) : convex (image f s) :=
hs.affine_image f.to_affine_map

lemma convex.is_linear_image {s : set E} (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) :
  convex (f '' s) :=
hs.linear_image $ hf.mk' f

lemma convex.linear_preimage {s : set F} (hs : convex s) (f : E →ₗ[ℝ] F) :
  convex (preimage f s) :=
hs.affine_preimage f.to_affine_map

lemma convex.is_linear_preimage {s : set F} (hs : convex s) {f : E → F} (hf : is_linear_map ℝ f) :
  convex (preimage f s) :=
hs.linear_preimage $ hf.mk' f

omit F

lemma convex.image_neg {s : set E} (hs : convex s) : convex ((λ z, -z) '' s) :=
hs.linear_image (-linear_map.id)

lemma convex.neg {s : set E} (hs : convex s) : convex (-s) :=
hs.linear_preimage (-linear_map.id)

lemma convex.smul {s : set E} (c : ℝ) (hs : convex s) : convex (c • s) :=
hs.linear_image (linear_map.lsmul _ _ c)

lemma convex.smul_preimage {s : set E} (c : ℝ) (hs : convex s) : convex ((λ z, c • z) ⁻¹' s) :=
hs.linear_preimage (linear_map.lsmul _ _ c)

lemma convex.image_const_vadd (hs : convex s) (z : E) : convex ((λ x, z +ᵥ x) '' s) :=
hs.affine_image $ const ℝ PE z +ᵥ affine_map.id ℝ PE

lemma convex.image_const_add {s : set E} (hs : convex s) (z : E) : convex ((λ x, z + x) '' s) :=
hs.image_const_vadd z

lemma convex.image_vadd_const {s : set E} (hs : convex s) (z : PE) : convex ((λ x, x +ᵥ z) '' s) :=
hs.affine_image $ affine_map.id ℝ E +ᵥ const ℝ E z

lemma convex.image_add_const {s : set E} (hs : convex s) (z : E) : convex ((λ x, x + z) '' s) :=
hs.image_vadd_const z

lemma convex.image_const_vsub (hs : convex s) (z : PE) : convex ((λ x, z -ᵥ x) '' s) :=
hs.affine_image $ const ℝ PE z -ᵥ affine_map.id ℝ PE

lemma convex.image_const_sub {s : set E} (hs : convex s) (z : E) : convex ((λ x, z - x) '' s) :=
hs.image_const_vsub z

lemma convex.image_vsub_const (hs : convex s) (z : PE) : convex ((λ x, x -ᵥ z) '' s) :=
hs.affine_image $ affine_map.id ℝ PE -ᵥ const ℝ PE z

lemma convex.image_sub_const {s : set E} (hs : convex s) (z : E) : convex ((λ x, x - z) '' s) :=
hs.image_vsub_const z

lemma convex.vadd {s : set E} {t : set PE} (hs : convex s) (ht : convex t) :
  convex (image2 (+ᵥ) s t) :=
begin
  rw ← image_prod,
  -- This instance fails defeq for `affine_space ? (E × PE)`. Why?
  letI : affine_space (E × E) (E × PE) := prod.add_torsor,
  exact (hs.prod ht).affine_image ((affine_map.fst : (E × PE) →ᵃ[ℝ] E) +ᵥ snd)
end

lemma convex.add {s t : set E} (hs : convex s) (ht : convex t) : convex (s + t) :=
hs.vadd ht

lemma convex.vsub {s t : set PE} (hs : convex s) (ht : convex t) : convex (image2 (-ᵥ) s t) :=
begin
  rw ← image_prod,
  -- This instance fails defeq for `affine_space ? (PE × PE)`. Why?
  letI : affine_space (E × E) (PE × PE) := prod.add_torsor,
  exact (hs.prod ht).affine_image ((affine_map.fst : (PE × PE) →ᵃ[ℝ] PE) -ᵥ snd)
end

lemma convex.sub {s t : set E} (hs : convex s) (ht : convex t) :
  convex (image2 (has_sub.sub) s t) :=
hs.vsub ht

omit E

lemma real.convex_iff_ord_connected {s : set ℝ} : convex s ↔ ord_connected s :=
by simp only [convex_iff_segment_subset, segment_eq_interval, ord_connected_iff_interval_subset]

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

include E

lemma convex_segment (a b : PE) : convex [a, b] := (convex_Icc 0 1).affine_image _

lemma affine_map.convex_lt (f : PE →ᵃ[ℝ] ℝ) (r : ℝ) :
  convex {w | f w < r} :=
(convex_Iio r).affine_preimage f

lemma affine_map.convex_le (f : PE →ᵃ[ℝ] ℝ) (r : ℝ) :
  convex {w | f w ≤ r} :=
(convex_Iic r).affine_preimage f

lemma affine_map.convex_gt (f : PE →ᵃ[ℝ] ℝ) (r : ℝ) :
  convex {w | r < f w} :=
(convex_Ioi r).affine_preimage f

lemma affine_map.convex_ge (f : E →ᵃ[ℝ] ℝ) (r : ℝ) :
  convex {w | r ≤ f w} :=
(convex_Ici r).affine_preimage f

lemma affine_map.convex_eq (f : E →ᵃ[ℝ] ℝ) (r : ℝ) :
  convex {w | f w = r} :=
(convex_singleton r).affine_preimage f

lemma linear_map.convex_lt (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | f w < r} :=
f.to_affine_map.convex_lt r

lemma linear_map.convex_le (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | f w ≤ r} :=
f.to_affine_map.convex_le r

lemma linear_map.convex_gt (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | r < f w} :=
f.to_affine_map.convex_gt r

lemma linear_map.convex_ge (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | r ≤ f w} :=
f.to_affine_map.convex_ge r

lemma linear_map.convex_eq (f : E →ₗ[ℝ] ℝ) (r : ℝ) :
  convex {w | f w = r} :=
f.to_affine_map.convex_eq r

omit E

lemma convex_halfspace_re_lt (r : ℝ) : convex {c : ℂ | c.re < r} :=
complex.linear_map.re.convex_lt r

lemma convex_halfspace_re_le (r : ℝ) : convex {c : ℂ | c.re ≤ r} :=
complex.linear_map.re.convex_le r

lemma convex_halfspace_re_gt (r : ℝ) : convex {c : ℂ | r < c.re } :=
complex.linear_map.re.convex_gt r

lemma convex_halfspace_re_ge (r : ℝ) : convex {c : ℂ | r ≤ c.re} :=
complex.linear_map.re.convex_ge r

lemma convex_halfspace_im_lt (r : ℝ) : convex {c : ℂ | c.im < r} :=
complex.linear_map.im.convex_lt r

lemma convex_halfspace_im_le (r : ℝ) : convex {c : ℂ | c.im ≤ r} :=
complex.linear_map.im.convex_le r

lemma convex_halfspace_im_gt (r : ℝ) : convex {c : ℂ | r < c.im } :=
complex.linear_map.im.convex_gt r

lemma convex_halfspace_im_ge (r : ℝ) : convex {c : ℂ | r ≤ c.im} :=
complex.linear_map.im.convex_ge r

include E

lemma affine_subspace.convex (K : affine_subspace ℝ PE) : convex (↑K : set PE) :=
λ x hx y hy a ha, K.smul_vsub_vadd_mem a hy hx hx

lemma submodule.convex (K : submodule ℝ E) : convex (↑K : set E) :=
K.to_affine_subspace.convex

end sets

section convex_hull

variable {t : set PE}

/-- Convex hull of a set `s` is the minimal convex set that includes `s` -/
def convex_hull (s : set PE) : set PE :=
⋂ (t : set PE) (hst : s ⊆ t) (ht : convex t), t

variable (s)

lemma subset_convex_hull : s ⊆ convex_hull s :=
set.subset_Inter $ λ t, set.subset_Inter $ λ hst, set.subset_Inter $ λ ht, hst

lemma convex_convex_hull : convex (convex_hull s) :=
convex_Inter $ λ t, convex_Inter $ λ ht, convex_Inter id

variable {s}

lemma convex_hull_min (hst : s ⊆ t) (ht : convex t) : convex_hull s ⊆ t :=
set.Inter_subset_of_subset t $ set.Inter_subset_of_subset hst $ set.Inter_subset _ ht

lemma convex_hull_mono (hst : s ⊆ t) : convex_hull s ⊆ convex_hull t :=
convex_hull_min (set.subset.trans hst $ subset_convex_hull t) (convex_convex_hull t)

lemma convex.convex_hull_eq (hs : convex s) : convex_hull s = s :=
set.subset.antisymm (convex_hull_min (set.subset.refl _) hs) (subset_convex_hull s)

@[simp]
lemma convex_hull_singleton {x : PE} : convex_hull ({x} : set PE) = {x} :=
(convex_singleton x).convex_hull_eq

include F

lemma affine_map.image_convex_hull (f : PE →ᵃ[ℝ] PF) (s : set PE) :
  f '' (convex_hull s) = convex_hull (f '' s) :=
begin
  refine set.subset.antisymm _ _,
  { rw [set.image_subset_iff],
    exact convex_hull_min (set.image_subset_iff.1 $ subset_convex_hull $ f '' s)
      ((convex_convex_hull (f '' s)).affine_preimage f) },
  { exact convex_hull_min (set.image_subset _ $ subset_convex_hull s)
     ((convex_convex_hull s).affine_image f) }
end

lemma linear_map.image_convex_hull (f : E →ₗ[ℝ] F) (s : set E) :
  f '' (convex_hull s) = convex_hull (f '' s) :=
f.to_affine_map.image_convex_hull s

lemma finset.center_mass_mem_convex_hull (t : finset ι) {w : ι → ℝ} (hw₀ : ∀ i ∈ t, 0 ≤ w i)
  (hws : 0 < ∑ i in t, w i) {z : ι → E} (hz : ∀ i ∈ t, z i ∈ s) :
  t.center_mass w z ∈ convex_hull s :=
(convex_convex_hull s).center_mass_mem hw₀ hws (λ i hi, subset_convex_hull s $ hz i hi)

-- TODO : Do we need other versions of the next lemma?

/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `z '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
lemma convex_hull_eq (s : set E) :
  convex_hull s = {x : E | ∃ (ι : Type u') (t : finset ι) (w : ι → ℝ) (z : ι → E)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i in t, w i = 1) (hz : ∀ i ∈ t, z i ∈ s) , t.center_mass w z = x} :=
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
      rw [finset.mem_union, finset.mem_image, finset.mem_image] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr];
        apply_rules [mul_nonneg, hwx₀, hwy₀] },
    { simp [finset.sum_sum_elim, finset.mul_sum.symm, *] },
    { intros i hi,
      rw [finset.mem_union, finset.mem_image, finset.mem_image] at hi,
      rcases hi with ⟨j, hj, rfl⟩|⟨j, hj, rfl⟩;
        simp only [sum.elim_inl, sum.elim_inr]; apply_rules [hzx, hzy] } },
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
  convex_hull s = {x : E | ∃ (w : E → ℝ) (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y in hs.to_finset, w y = 1),
    hs.to_finset.center_mass w id = x} :=
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

/-- Standard simplex in the space of functions `ι → ℝ` is the set
of vectors with non-negative coordinates with total sum `1`. -/
def std_simplex (ι : Type*) [fintype ι] : set (ι → ℝ) :=
{ f | (∀ x, 0 ≤ f x) ∧ ∑ x, f x = 1 }

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
⟨λ j, by simp only; split_ifs; norm_num, by rw [finset.sum_ite_eq, if_pos (finset.mem_univ _)] ⟩

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

/-- Convex hull of a finite set is the image of the standard simplex in `s → ℝ`
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

section center_mass

/-- Center mass of a finite collection of points with prescribed weights.
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
  simp only [center_mass, sum_insert ha, smul_add, (mul_smul _ _ _).symm],
  congr' 2,
  { apply mul_comm },
  { rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div] }
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
  (hws : ∑ i in s, ws i = 1) (hwt : ∑ i in t, wt i = 1) (a b : ℝ) (hab : a + b = 1):
  a • s.center_mass ws zs + b • t.center_mass wt zt =
    (s.image sum.inl ∪ t.image sum.inr).center_mass
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
  (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (a b : ℝ) (hab : a + b = 1):
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
finset.center_mass_subset z (filter_subset _) $ λ i hit hit',
by simpa only [hit, mem_filter, true_and, ne.def, not_not] using hit'

variable {z}

/-- Center mass of a finite subset of a convex set belongs to the set
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

/-- If a function `f` is convex on `s` takes value `y` at the center mass of some points
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

