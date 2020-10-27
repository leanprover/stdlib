section functions

variables {V V' : Type*} [ordered_add_comm_group V] [ordered_semimodule ℝ V]
  [ordered_add_comm_group V'] [ordered_semimodule ℝ V']

local notation `[`x `, ` y `]` := segment x y
open affine_map (line_map line_map_apply)

/-! ### Convex functions -/

/-- Convexity of functions -/
def convex_on (s : set PE) (f : PE → V) : Prop :=
  convex s ∧
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) ⦃a : ℝ⦄ (ha : a ∈ I),
    f (line_map x y a) ≤ line_map (f x) (f y) a

/-- Concavity of functions -/
def concave_on (s : set PE) (f : PE → V) : Prop :=
  convex s ∧
  ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) ⦃a : ℝ⦄ (ha : a ∈ I),
    line_map (f x) (f y) a ≤ f (line_map x y a)

variables {f : PE → V}

lemma convex_on.mono {t : set PE} (ht : convex_on t f) (h : s ⊆ t) (hs : convex s) :
  convex_on s f :=
⟨hs, λ x hx y hy, ht.2 (h hx) (h hy)⟩

lemma concave_on.mono {t : set PE} (ht : concave_on t f) (h : s ⊆ t) (hs : convex s) :
  concave_on s f :=
⟨hs, λ x hx y hy, ht.2 (h hx) (h hy)⟩

lemma convex_on.congr (hf : convex_on s f) {g} (hg : eq_on f g s) : convex_on s g :=
⟨hf.1, λ x hx y hy a ha, hg hx ▸ hg hy ▸ hg (hf.1 hx hy ha) ▸ hf.2 hx hy ha⟩

lemma set.eq_on.convex_on_iff {g} (h : eq_on f g s) : convex_on s f ↔ convex_on s g :=
⟨λ hf, hf.congr h, λ hg, hg.congr h.symm⟩

lemma set.eq_on.concave_on_iff {g} (h : eq_on f g s) : concave_on s f ↔ concave_on s g :=
@set.eq_on.convex_on_iff _ _ _ _ _ _ (order_dual V) _ _ _ _ h

lemma concave_on.congr (hf : concave_on s f) {g} (hs : eq_on f g s) : concave_on s g :=
hs.concave_on_iff.1 hf

lemma convex_on_order_dual_iff : @convex_on E PE _ _ _ (order_dual V) _ _ s f ↔ concave_on s f :=
iff.rfl

lemma concave_on_order_dual_iff : @concave_on E PE _ _ _ (order_dual V) _ _ s f ↔ convex_on s f :=
iff.rfl

alias convex_on_order_dual_iff ↔ concave_on_of_order_dual concave_on.order_dual
alias concave_on_order_dual_iff ↔ convex_on_of_order_dual convex_on.order_dual

lemma affine_map.convex_on (f : affine_map ℝ PE V) (hs : convex s) :
  convex_on s f :=
⟨hs, λ x hx y hy a ha, (f.apply_line_map _ _ _).le⟩

lemma affine_map.concave_on (f : affine_map ℝ PE V) (hs : convex s) :
  concave_on s f :=
⟨hs, λ x hx y hy a ha, (f.apply_line_map _ _ _).ge⟩

lemma linear_map.convex_on (f : E →ₗ[ℝ] V) {s : set E} (hs : convex s) : convex_on s f :=
f.to_affine_map.convex_on hs

lemma linear_map.concave_on (f : E →ₗ[ℝ] V) {s : set E} (hs : convex s) : concave_on s f :=
f.to_affine_map.concave_on hs

section comp

variables {t : set V} {g : V → V'}

lemma convex_on.comp (hg : convex_on t g) (h_mono : monotone g) (hf : convex_on s f)
  (hst : maps_to f s t) : convex_on s (g ∘ f) :=
⟨hf.1, λ x hx y hy a ha,
  calc g (f (line_map x y a)) ≤ g (line_map (f x) (f y) a) : h_mono (hf.2 hx hy ha)
  ... ≤ line_map (g (f x)) (g (f y)) a : hg.2 (hst hx) (hst hy) ha⟩

lemma convex_on.comp_concave_on (hg : convex_on t g) (h_mono : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x)
  (hf : concave_on s f) (hst : maps_to f s t) :
  convex_on s (g ∘ f) :=
⟨hf.1, λ x hx y hy a ha,
  calc g (f (line_map x y a)) ≤ g (line_map (f x) (f y) a) : h_mono (hf.2 hx hy ha)
  ... ≤ line_map (g (f x)) (g (f y)) a : hg.2 (hst hx) (hst hy) ha⟩

lemma concave_on.comp (hg : concave_on t g) (h_mono : monotone g)
  (hf : concave_on s f) (hst : maps_to f s t) :
  concave_on s (g ∘ f) :=
hg.order_dual.comp_concave_on h_mono hf hst

lemma concave_on.comp_convex_on (hg : concave_on t g) (h_mono : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x)
  (hf : convex_on s f) (hst : maps_to f s t) :
  concave_on s (g ∘ f) :=
hg.order_dual.comp h_mono hf hst

lemma convex_on.comp' (hg : convex_on univ g) (h_mono : monotone g) (hf : convex_on s f) :
  convex_on s (g ∘ f) :=
hg.comp h_mono hf (maps_to_univ _ _)

lemma convex_on.comp_concave_on' (hg : convex_on univ g) (h_mono : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x)
  (hf : concave_on s f) :
  convex_on s (g ∘ f) :=
hg.comp_concave_on h_mono hf (maps_to_univ _ _)

lemma concave_on.comp' (hg : concave_on univ g) (h_mono : monotone g) (hf : concave_on s f) :
  concave_on s (g ∘ f) :=
hg.comp h_mono hf (maps_to_univ _ _)

lemma concave_on.comp_convex_on' (hg : concave_on univ g) (h_mono : ∀ ⦃x y⦄, x ≤ y → g y ≤ g x)
  (hf : convex_on s f) :
  concave_on s (g ∘ f) :=
hg.comp_convex_on h_mono hf (maps_to_univ _ _)

end comp

section comp_affine

include F

/-- If a function is convex on s, it remains convex when precomposed by an affine map -/
lemma convex_on.comp_affine_map (hf : convex_on s f) (g : affine_map ℝ PF PE) :
  convex_on (g ⁻¹' s) (f ∘ g) :=
⟨hf.1.affine_preimage _ , λ x hx y hy a ha, by simp only [(∘), g.apply_line_map, hf.2 hx hy ha]⟩

/-- If a function is concave on s, it remains concave when precomposed by an affine map -/
lemma concave_on.comp_affine_map (hf : concave_on s f) (g : affine_map ℝ PF PE) :
  concave_on (g ⁻¹' s) (f ∘ g) :=
hf.order_dual.comp_affine_map g

/-- If a function is convex on s, it remains convex when precomposed by a linear map -/
lemma convex_on.comp_linear_map {s : set E} {f : E → V} (hf : convex_on s f) (g : F →ₗ[ℝ] E) :
  convex_on (g ⁻¹' s) (f ∘ g) :=
hf.comp_affine_map g.to_affine_map

/-- If a function is concave on s, it remains concave when precomposed by a linear map -/
lemma concave_on.comp_linear_map {s : set E} {f : E → V} (hf : concave_on s f) (g : F →ₗ[ℝ] E) :
  concave_on (g ⁻¹' s) (f ∘ g) :=
hf.comp_affine_map g.to_affine_map

omit F

/-- If a function is convex on s, it remains convex after a translation. -/
lemma convex_on.translate_right {a : E} (hf : convex_on s f) :
  convex_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const ℝ E a +ᵥ affine_map.id ℝ E

/-- If a function is concave on s, it remains concave after a translation. -/
lemma concave_on.translate_right {f : E → β} {s : set E} {a : E} (hf : concave_on s f) :
  concave_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, a + z)) :=
hf.comp_affine_map $ affine_map.const ℝ E a +ᵥ affine_map.id ℝ E

/-- If a function is convex on s, it remains convex after a translation. -/
lemma convex_on.translate_left {f : E → β} {s : set E} {a : E} (hf : convex_on s f) :
  convex_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using  hf.translate_right

/-- If a function is concave on s, it remains concave after a translation. -/
lemma concave_on.translate_left {f : E → β} {s : set E} {a : E} (hf : concave_on s f) :
  concave_on ((λ z, a + z) ⁻¹' s) (f ∘ (λ z, z + a)) :=
by simpa only [add_comm] using  hf.translate_right


end comp_affine

lemma convex_on.neg (hf : convex_on s f) : concave_on s (-f) :=
((-linear_map.id).concave_on convex_univ).comp_convex_on' (λ x y, neg_le_neg) hf

lemma concave_on.neg (hf : concave_on s f) : convex_on s (-f) :=
hf.order_dual.neg

@[simp] lemma convex_on_neg_iff : convex_on s (-f) ↔ concave_on s f :=
⟨λ h, neg_neg f ▸ h.neg, λ h, h.neg⟩

@[simp] lemma convex_on_neg_iff' : convex_on s (λ x, -f x) ↔ concave_on s f :=
convex_on_neg_iff

@[simp] lemma concave_on_neg_iff : concave_on s (-f) ↔ convex_on s f :=
⟨λ h, neg_neg f ▸ h.neg, λ h, h.neg⟩

@[simp] lemma concave_on_neg_iff' : concave_on s (λ x, -f x) ↔ convex_on s f :=
concave_on_neg_iff

omit E

lemma convex_on_id {s : set V} (hs : convex s) : convex_on s id :=
linear_map.id.convex_on hs

lemma concave_on_id {s : set V} (hs : convex s) : concave_on s id :=
linear_map.id.concave_on hs

include E

lemma convex_on_const (c : V) (hs : convex s) : convex_on s (λ x:PE, c) :=
(affine_map.const ℝ PE c).convex_on hs

lemma concave_on_const (c : V) (hs : convex s) : concave_on s (λ x:PE, c) :=
(affine_map.const ℝ PE c).concave_on hs

lemma convex_on.prod_mk (hf : convex_on s f) {g : PE → V'} (hg : convex_on s g) :
  convex_on s (λ x, (f x, g x)) :=
⟨hf.1, λ x hx y hy a ha, ⟨hf.2 hx hy ha, hg.2 hx hy ha⟩⟩

lemma convex_on.add (hf : convex_on s f) {g : PE → V} (hg : convex_on s g) :
  convex_on s (f + g) :=
((linear_map.fst ℝ V V + linear_map.snd ℝ V V).convex_on convex_univ).comp'
  (λ x y h, add_le_add h.1 h.2) (hf.prod_mk hg)

lemma concave_on.add (hf : concave_on s f) {g : PE → V} (hg : concave_on s g) :
  concave_on s (f + g) :=
concave_on_of_order_dual $ hf.order_dual.add hg.order_dual

lemma convex_on.sub_concave_on (hf : convex_on s f) {g : PE → V} (hg : concave_on s g) :
  convex_on s (f - g) :=
hf.add hg.neg

lemma concave_on.sub_convex_on (hf : concave_on s f) {g : PE → V} (hg : convex_on s g) :
  concave_on s (f - g) :=
hf.add hg.neg

/-! #### Scalar multiplication -/

variable {c : ℝ}

lemma convex_on.smul_nonneg (hf : convex_on s f) (hc : 0 ≤ c) : convex_on s (c • f) :=
((c • linear_map.id).convex_on convex_univ).comp' (λ x y h, smul_le_smul_of_nonneg h hc) hf

lemma convex_on.smul_nonneg' (hf : convex_on s f) (hc : 0 ≤ c) :
  convex_on s (λ x, c • f x) :=
hf.smul_nonneg hc

lemma convex_on.smul_nonpos (hf : convex_on s f) (hc : c ≤ 0) : concave_on s (c • f) :=
(hf.smul_nonneg (neg_nonneg.2 hc)).neg.congr $ λ x hx, by simp

lemma convex_on.smul_nonpos' (hf : convex_on s f) (hc : c ≤ 0) :
  concave_on s (λ x, c • f x) :=
hf.smul_nonpos hc

lemma concave_on.smul_nonneg (hf : concave_on s f) (hc : 0 ≤ c) : concave_on s (c • f) :=
concave_on_of_order_dual $ hf.order_dual.smul_nonneg hc

lemma concave_on.smul_nonneg' (hf : concave_on s f) (hc : 0 ≤ c) :
  concave_on s (λ x, c • f x) :=
hf.smul_nonneg hc

lemma concave_on.smul_nonpos (hf : concave_on s f) (hc : c ≤ 0) : convex_on s (c • f) :=
convex_on_of_order_dual $ hf.order_dual.smul_nonpos hc

lemma concave_on.smul_nonpos' (hf : concave_on s f) (hc : c ≤ 0) : convex_on s (λ x, c • f x) :=
hf.smul_nonpos hc

lemma convex_on.of_smul_pos' (hc : 0 < c) (hf : convex_on s (λ x, c • f x)) : convex_on s f :=
(hf.smul_nonneg' (inv_nonneg.2 hc.le)).congr $ λ x hx, inv_smul_smul' hc.ne' _

lemma convex_on.of_smul_pos (hc : 0 < c) (hf : convex_on s (c • f)) : convex_on s f :=
hf.of_smul_pos' hc

lemma convex_on_smul_iff_of_pos (hc : 0 < c) : convex_on s (c • f) ↔ convex_on s f :=
⟨λ h, h.of_smul_pos hc, λ h, h.smul_nonneg hc.le⟩

lemma convex_on_smul_iff_of_pos' (hc : 0 < c) : convex_on s (λ x, c • f x) ↔ convex_on s f :=
convex_on_smul_iff_of_pos hc

lemma concave_on_smul_iff_of_pos (hc : 0 < c) : concave_on s (c • f) ↔ concave_on s f :=
@convex_on_smul_iff_of_pos _ _ _ _ _ _ (order_dual V) _ _ _ _ hc

lemma concave_on_smul_iff_of_pos' (hc : 0 < c) : concave_on s (λ x, c • f x) ↔ concave_on s f :=
concave_on_smul_iff_of_pos hc

lemma concave_on.of_smul_pos (hc : 0 < c) (hf : concave_on s (c • f)) : concave_on s f :=
(concave_on_smul_iff_of_pos hc).1 hf

lemma concave_on.of_smul_pos' (hc : 0 < c) (hf : concave_on s (λ x, c • f x)) : concave_on s f :=
hf.of_smul_pos hc

lemma concave_on_of_smul_neg (hc : c < 0) (hf : convex_on s (c • f)) : concave_on s f :=
concave_on.of_smul_pos (neg_pos.2 hc) $ hf.neg.congr $ λ x hx, by simp

lemma concave_on_of_smul_neg' (hc : c < 0) (hf : convex_on s (λ x, c • f x)) : concave_on s f :=
concave_on_of_smul_neg hc hf

lemma convex_on_of_smul_neg (hc : c < 0) (hf : concave_on s (c • f)) : convex_on s f :=
convex_on_of_order_dual $ concave_on_of_smul_neg hc hf.order_dual

lemma convex_on_of_smul_neg' (hc : c < 0) (hf : concave_on s (λ x, c • f x)) : convex_on s f :=
convex_on_of_smul_neg hc hf

lemma convex_on_smul_iff_of_neg (hc : c < 0) : convex_on s (c • f) ↔ concave_on s f :=
⟨concave_on_of_smul_neg hc, λ h, h.smul_nonpos hc.le⟩

lemma convex_on_smul_iff_of_neg' (hc : c < 0) : convex_on s (λ x, c • f x) ↔ concave_on s f :=
convex_on_smul_iff_of_neg hc

lemma concave_on_smul_iff_of_neg (hc : c < 0) : concave_on s (c • f) ↔ convex_on s f :=
⟨convex_on_of_smul_neg hc, λ h, h.smul_nonpos hc.le⟩

lemma concave_on_smul_iff_of_neg' (hc : c < 0) : concave_on s (λ x, c • f x) ↔ convex_on s f :=
concave_on_smul_iff_of_neg hc

open affine_map

/-- For a function on a convex set in a linear ordered space, in order to prove that it is convex
it suffices to verify the inequality `f (line_map x y a) ≤ line_map (f x) (f y) a` only for `x < y`
and positive `a ∈ (0, 1)`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.convex_on_of_lt [linear_order PE] (hs : convex s)
  (hf : ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) (hlt : x < y) ⦃a : ℝ⦄ (ha : a ∈ Ioo (0:ℝ) 1),
    f (line_map x y a) ≤ line_map (f x) (f y) a) : convex_on s f :=
begin
  use hs,
  rintros x hx y hy a ⟨h₀, h₁⟩,
  rcases h₀.eq_or_lt with rfl|h₀, { simp only [line_map_apply_zero] },
  rcases h₁.eq_or_lt with rfl|h₁, { simp only [line_map_apply_one] },
  rcases lt_trichotomy x y with (hxy|rfl|hxy),
  { exact hf hx hy hxy ⟨h₀, h₁⟩ },
  { simp only [line_map_same, coe_const] },
  { rw [← line_map_apply_one_sub y, ← line_map_apply_one_sub (f y)],
    exact hf hy hx hxy ⟨sub_pos.2 h₁, sub_lt_self _ h₀⟩ }
end

/-- For a function on a convex set in a linear ordered space, in order to prove that it is concave
it suffices to verify the inequality `line_map (f x) (f y) a ≤ f (line_map x y a)` only for `x < y`
and positive `a ∈ (0, 1)`. The main use case is `E = ℝ` however one can apply it, e.g., to `ℝ^n` with
lexicographic order. -/
lemma linear_order.concave_on_of_lt [linear_order PE] (hs : convex s)
  (hf : ∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s) (hlt : x < y) ⦃a : ℝ⦄ (ha : a ∈ Ioo (0:ℝ) 1),
    line_map (f x) (f y) a ≤ f (line_map x y a)) : concave_on s f :=
@linear_order.convex_on_of_lt _ _ _ _ _ _ (order_dual V) _ _ _ _ hs hf

/--
If `f x ≤ c`, `f y ≤ c`, and `f : PE → β` is convex on a set `s ⊇ {x, y}`, then `f` is bounded
above by `c` on `[x, y]`. For a function `f : PE → ℝ` we can use `a = max (f x) (f y)`.
This version takes an argument `a ∈ [0, 1]` and proves `f (a • (y -ᵥ x) +ᵥ x) ≤ c`.
-/
lemma convex_on.le_on_segment_of_le' {c : V} {x y : PE} {a : ℝ} (hf : convex_on s f)
  (hx : x ∈ s) (hy : y ∈ s) (hfx : f x ≤ c) (hfy : f y ≤ c) (ha : a ∈ I) :
  f (line_map x y a) ≤ c :=
calc f (line_map x y a) ≤ line_map (f x) (f y) a : hf.2 hx hy ha
... ≤ line_map c c a : line_map_mono_endpoints hfx hfy ha.1 ha.2
... = c : line_map_same_apply c a

/--
If `f x ≤ c`, `f y ≤ c`, and `f : PE → β` is convex on a set `s ⊇ {x, y}`, then `f` is bounded
above by `c` on `[x, y]`. For a function `f : PE → ℝ` we can use `a = max (f x) (f y)`.
-/
lemma convex_on.le_on_segment_of_le {c : V} {x y z : PE} (hf : convex_on s f)
  (hx : x ∈ s) (hy : y ∈ s) (hfx : f x ≤ c) (hfy : f y ≤ c) (hz : z ∈ [x, y]) :
  f z ≤ c :=
let ⟨a, ha, hz⟩ := hz in hz ▸ hf.le_on_segment_of_le' hx hy hfx hfy ha

/--
If `f x < c`, `f y < c`, and `f : PE → β` is convex on a set `s ⊇ {x, y}`, then `f z < c`
on `[x, y]`. This version takes an argument `a ∈ [0, 1]` and proves `f (a • (y -ᵥ x) +ᵥ x) < c`.
-/
lemma convex_on.lt_on_segment_of_lt' {c : V} {x y : PE} {a : ℝ} (hf : convex_on s f)
  (hx : x ∈ s) (hy : y ∈ s) (hfx : f x < c) (hfy : f y < c) (ha : a ∈ I) :
  f (line_map x y a) < c :=
calc f (line_map x y a) ≤ line_map (f x) (f y) a : hf.2 hx hy ha
... < line_map c c a : line_map_strict_mono_endpoints hfx hfy ha.1 ha.2
... = c : line_map_same_apply c a

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment' {V : Type*} [decidable_linear_ordered_add_comm_group V]
  [ordered_semimodule ℝ V] {f : PE → V} {x y : PE} {a : ℝ}
  (hf : convex_on s f) (hx : x ∈ s) (hy : y ∈ s) (ha : a ∈ I) :
  f (line_map x y a)  ≤ max (f x) (f y) :=
hf.le_on_segment_of_le' hx hy (le_max_left _ _) (le_max_right _ _) ha

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment' {V : Type*} [decidable_linear_ordered_add_comm_group V]
  [ordered_semimodule ℝ V] {f : PE → V} {x y : PE} {a : ℝ}
  (hf : concave_on s f) (hx : x ∈ s) (hy : y ∈ s) (ha : a ∈ I) :
  min (f x) (f y) ≤ f (line_map x y a) :=
hf.order_dual.le_on_segment' hx hy ha

/-- A convex function on a segment is upper-bounded by the max of its endpoints. -/
lemma convex_on.le_on_segment {V : Type*} [decidable_linear_ordered_add_comm_group V]
  [ordered_semimodule ℝ V] {f : PE → V} (hf : convex_on s f) {x y z : PE}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x, y]) :
  f z ≤ max (f x) (f y) :=
let ⟨a, ha, hz⟩ := hz in hz ▸ hf.le_on_segment' hx hy ha

/-- A concave function on a segment is lower-bounded by the min of its endpoints. -/
lemma concave_on.le_on_segment {V : Type*} [decidable_linear_ordered_add_comm_group V]
  [ordered_semimodule ℝ V] {f : PE → V} (hf : concave_on s f) {x y z : PE}
  (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ [x, y]) :
    min (f x) (f y) ≤ f z :=
hf.order_dual.le_on_segment hx hy hz

lemma convex_on.convex_le (hf : convex_on s f) (r : V) : convex {x ∈ s | f x ≤ r} :=
λ x hx y hy a ha, ⟨hf.1 hx.1 hy.1 ha, hf.le_on_segment_of_le' hx.1 hy.1 hx.2 hy.2 ha⟩

lemma concave_on.concave_le (hf : concave_on s f) (r : V) : convex {x ∈ s | r ≤ f x} :=
hf.order_dual.convex_le r

lemma convex_on.convex_lt (hf : convex_on s f) (r : V) : convex {x ∈ s | f x < r} :=
λ x hx y hy a ha, ⟨hf.1 hx.1 hy.1 ha, hf.lt_on_segment_of_lt' hx.1 hy.1 hx.2 hy.2 ha⟩

lemma concave_on.convex_lt (hf : concave_on s f) (r : V) : convex {x ∈ s | r < f x} :=
hf.order_dual.convex_lt r

lemma convex_on.convex_epigraph (hf : convex_on s f) :
  convex {p : PE × V | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  rintros ⟨x, r⟩ ⟨hx : x ∈ s, hr : f x ≤ r⟩ ⟨y, t⟩ ⟨hy : y ∈ s, ht : f y ≤ t⟩ a ha,
  simp [hf.1 hx hy ha, (hf.2 hx hy ha).trans (line_map_mono_endpoints hr ht ha.1 ha.2)]
end

lemma concave_on.convex_hypograph (hf : concave_on s f) :
  convex {p : PE × V | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
hf.order_dual.convex_epigraph

lemma convex_on_iff_convex_epigraph :
  convex_on s f ↔ convex {p : PE × V | p.1 ∈ s ∧ f p.1 ≤ p.2} :=
begin
  refine ⟨convex_on.convex_epigraph, λ h, ⟨_, _⟩⟩,
  { assume x hx y hy a ha,
    exact (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a ha).1 },
  { assume x hx y hy a ha,
    exact (@h (x, f x) ⟨hx, le_rfl⟩ (y, f y) ⟨hy, le_rfl⟩ a ha).2 }
end

lemma concave_on_iff_convex_hypograph :
  concave_on s f ↔ convex {p : PE × V | p.1 ∈ s ∧ p.2 ≤ f p.1} :=
@convex_on_iff_convex_epigraph _ _ _ _ _ _ (order_dual V) _ _ f

include F

end functions

