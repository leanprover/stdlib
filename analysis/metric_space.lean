/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Metric spaces.

Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel

Many definitions and theorems expected on metric spaces are already introduced on uniform spaces and
topological spaces. For example:
  open and closed sets, compactness, completeness, continuity and uniform continuity
-/
import data.real.nnreal analysis.topology.topological_structures analysis.emetric_space tactic.linarith
open lattice set filter classical topological_space
noncomputable theory

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

/-- Construct a uniform structure from a distance function and metric space axioms -/
def metric_space.uniform_space_of_dist
  (dist : α → α → ℝ)
  (dist_self : ∀ x : α, dist x x = 0)
  (dist_comm : ∀ x y : α, dist x y = dist y x)
  (dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z) : uniform_space α :=
uniform_space.of_core {
  uniformity := (⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε}),
  refl       := le_infi $ assume ε, le_infi $
    by simp [set.subset_def, id_rel, dist_self, (>)] {contextual := tt},
  comp       := le_infi $ assume ε, le_infi $ assume h, lift'_le
    (mem_infi_sets (ε / 2) $ mem_infi_sets (div_pos_of_pos_of_pos h two_pos) (subset.refl _)) $
    have ∀ (a b c : α), dist a c < ε / 2 → dist c b < ε / 2 → dist a b < ε,
      from assume a b c hac hcb,
      calc dist a b ≤ dist a c + dist c b : dist_triangle _ _ _
        ... < ε / 2 + ε / 2 : add_lt_add hac hcb
        ... = ε : by rw [div_add_div_same, add_self_div_two],
    by simpa [comp_rel],
  symm       := tendsto_infi.2 $ assume ε, tendsto_infi.2 $ assume h,
    tendsto_infi' ε $ tendsto_infi' h $ tendsto_principal_principal.2 $ by simp [dist_comm] }

/-- The distance function (given an ambient metric space on `α`), which returns
  a nonnegative real number `dist x y` given `x y : α`. -/
class has_dist (α : Type*) := (dist : α → α → ℝ)

export has_dist (dist)

/-- Metric space

Each metric space induces a canonical `uniform_space` and hence a canonical `topological_space`.
This is enforced in the type class definition, by extending the `uniform_space` structure. When
instantiating a `metric_space` structure, the uniformity fields are not necessary, they will be
filled in by default. In the same way, each metric space induces an emetric space structure.
It is included in the structure, but filled in by default.

When one instantiates a metric space structure, for instance a product structure,
this makes it possible to use a uniform structure and an edistance that are exactly
the ones for the uniform spaces product and the emetric spaces products, thereby
ensuring that everything in defeq in diamonds.-/
class metric_space (α : Type u) extends has_dist α : Type u :=
(dist_self : ∀ x : α, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)
(edist : α → α → ennreal := λx y, nnreal.of_real (dist x y))
(edist_dist : ∀ x y : α, edist x y = ↑(nnreal.of_real (dist x y)) . control_laws_tac)
(to_uniform_space : uniform_space α := metric_space.uniform_space_of_dist dist dist_self dist_comm dist_triangle)
(uniformity_dist : uniformity = ⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε} . control_laws_tac)

open metric_space (edist)

variables [metric_space α]

instance metric_space.to_uniform_space' : uniform_space α :=
metric_space.to_uniform_space α

@[simp] theorem dist_self (x : α) : dist x x = 0 := metric_space.dist_self x

theorem eq_of_dist_eq_zero {x y : α} : dist x y = 0 → x = y :=
metric_space.eq_of_dist_eq_zero

theorem dist_comm (x y : α) : dist x y = dist y x := metric_space.dist_comm x y

theorem edist_dist (x y : α) : edist x y = ↑(nnreal.of_real (dist x y)) :=
metric_space.edist_dist _ x y

@[simp] theorem dist_eq_zero {x y : α} : dist x y = 0 ↔ x = y :=
iff.intro eq_of_dist_eq_zero (assume : x = y, this ▸ dist_self _)

@[simp] theorem zero_eq_dist {x y : α} : 0 = dist x y ↔ x = y :=
by rw [eq_comm, dist_eq_zero]

theorem dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z :=
metric_space.dist_triangle x y z

theorem dist_triangle_left (x y z : α) : dist x y ≤ dist z x + dist z y :=
by rw dist_comm z; apply dist_triangle

theorem dist_triangle_right (x y z : α) : dist x y ≤ dist x z + dist y z :=
by rw dist_comm y; apply dist_triangle

lemma dist_triangle4 (x y z t : α) :
  dist x t ≤ dist x y + dist y z + dist z t :=
calc
  dist x t ≤ dist x z + dist z t : dist_triangle x z t
       ... ≤ (dist x y + dist y z) + dist z t : add_le_add_right (metric_space.dist_triangle x y z) _

theorem swap_dist : function.swap (@dist α _) = dist :=
by funext x y; exact dist_comm _ _

theorem abs_dist_sub_le (x y z : α) : abs (dist x z - dist y z) ≤ dist x y :=
abs_sub_le_iff.2
 ⟨sub_le_iff_le_add.2 (dist_triangle _ _ _),
  sub_le_iff_le_add.2 (dist_triangle_left _ _ _)⟩

theorem dist_nonneg {x y : α} : 0 ≤ dist x y :=
have 2 * dist x y ≥ 0,
  from calc 2 * dist x y = dist x y + dist y x : by rw [dist_comm x y, two_mul]
    ... ≥ 0 : by rw ← dist_self x; apply dist_triangle,
nonneg_of_mul_nonneg_left this two_pos

@[simp] theorem dist_le_zero {x y : α} : dist x y ≤ 0 ↔ x = y :=
by simpa [le_antisymm_iff, dist_nonneg] using @dist_eq_zero _ _ x y

@[simp] theorem dist_pos {x y : α} : 0 < dist x y ↔ x ≠ y :=
by simpa [-dist_le_zero] using not_congr (@dist_le_zero _ _ x y)


section
variables [metric_space α]

def nndist (a b : α) : nnreal := ⟨dist a b, dist_nonneg⟩

/--Express `nndist` in terms of `edist`-/
@[simp] lemma edist_eq_nndist (x y : α) : (edist x y).to_nnreal = nndist x y :=
by simp [nndist, metric_space.edist_dist, nnreal.of_real, max_eq_left dist_nonneg]

/--Express `edist` in terms of `nndist`-/
@[simp] lemma nndist_eq_edist (x y : α) : ↑(nndist x y) = edist x y :=
by simp [nndist, metric_space.edist_dist, nnreal.of_real, max_eq_left dist_nonneg]

/--In a metric space, the extended distance is always finite-/
lemma edist_ne_top (x y : α) : edist x y ≠ ⊤ :=
by rw [edist_dist x y]; apply ennreal.coe_ne_top

/--`nndist x x` vanishes-/
@[simp] lemma nndist_self (a : α) : nndist a a = 0 := (nnreal.coe_eq_zero _).1 (dist_self a)

/--Express `dist` in terms of `nndist`-/
@[simp] lemma nndist_eq_dist (x y : α) : ↑(nndist x y) = dist x y := rfl

/--Express `nndist` in terms of `dist`-/
@[simp] lemma dist_eq_nndist (x y : α) : nnreal.of_real (dist x y) = nndist x y :=
by rw [← nndist_eq_dist, nnreal.of_real_coe]

/--Deduce the equality of points with the vanishing of the nonnegative distance-/
theorem eq_of_nndist_eq_zero {x y : α} : nndist x y = 0 → x = y :=
by simp [nnreal.eq_iff.symm]

theorem nndist_comm (x y : α) : nndist x y = nndist y x :=
by simpa [nnreal.eq_iff.symm] using dist_comm x y

/--Characterize the equality of points with the vanishing of the nonnegative distance-/
@[simp] theorem nndist_eq_zero {x y : α} : nndist x y = 0 ↔ x = y :=
by simp [nnreal.eq_iff.symm]

@[simp] theorem zero_eq_nndist {x y : α} : 0 = nndist x y ↔ x = y :=
by simp [nnreal.eq_iff.symm]

/--Triangle inequality for the nonnegative distance-/
theorem nndist_triangle (x y z : α) : nndist x z ≤ nndist x y + nndist y z :=
by simpa [nnreal.coe_le] using dist_triangle x y z

theorem nndist_triangle_left (x y z : α) : nndist x y ≤ nndist z x + nndist z y :=
by simpa [nnreal.coe_le] using dist_triangle_left x y z

theorem nndist_triangle_right (x y z : α) : nndist x y ≤ nndist x z + nndist y z :=
by simpa [nnreal.coe_le] using dist_triangle_right x y z

/--Express `edist` in terms of `dist`-/
@[simp] lemma dist_eq_edist (x y : α) : ↑(nnreal.of_real (dist x y)) = edist x y :=
(edist_dist x y).symm

/--Express `dist` in terms `edist`-/
@[simp] lemma edist_eq_dist (x y : α) : ↑((edist x y).to_nnreal) = dist x y :=
by rw [← dist_eq_edist]; simp; rw [nnreal.coe_of_real _ (metric_space.dist_nonneg x y)]

end

/- instantiate metric space as a topology -/
variables {x y z : α} {ε ε₁ ε₂ : ℝ} {s : set α}

/-- `ball x ε` is the set of all points `y` with `dist y x < ε` -/
def ball (x : α) (ε : ℝ) : set α := {y | dist y x < ε}

@[simp] theorem mem_ball : y ∈ ball x ε ↔ dist y x < ε := iff.rfl

theorem mem_ball' : y ∈ ball x ε ↔ dist x y < ε := by rw dist_comm; refl

/-- `closed_ball x ε` is the set of all points `y` with `dist y x ≤ ε` -/
def closed_ball (x : α) (ε : ℝ) := {y | dist y x ≤ ε}

@[simp] theorem mem_closed_ball : y ∈ closed_ball x ε ↔ dist y x ≤ ε := iff.rfl

theorem ball_subset_closed_ball : ball x ε ⊆ closed_ball x ε :=
assume y, by simp; intros h; apply le_of_lt h

theorem pos_of_mem_ball (hy : y ∈ ball x ε) : ε > 0 :=
lt_of_le_of_lt dist_nonneg hy

theorem mem_ball_self (h : ε > 0) : x ∈ ball x ε :=
show dist x x < ε, by rw dist_self; assumption

theorem mem_ball_comm : x ∈ ball y ε ↔ y ∈ ball x ε :=
by simp [dist_comm]

theorem ball_subset_ball (h : ε₁ ≤ ε₂) : ball x ε₁ ⊆ ball x ε₂ :=
λ y (yx : _ < ε₁), lt_of_lt_of_le yx h

theorem ball_disjoint (h : ε₁ + ε₂ ≤ dist x y) : ball x ε₁ ∩ ball y ε₂ = ∅ :=
eq_empty_iff_forall_not_mem.2 $ λ z ⟨h₁, h₂⟩,
not_lt_of_le (dist_triangle_left x y z)
  (lt_of_lt_of_le (add_lt_add h₁ h₂) h)

theorem ball_disjoint_same (h : ε ≤ dist x y / 2) : ball x ε ∩ ball y ε = ∅ :=
ball_disjoint $ by rwa [← two_mul, ← le_div_iff' two_pos]

theorem ball_subset (h : dist x y ≤ ε₂ - ε₁) : ball x ε₁ ⊆ ball y ε₂ :=
λ z zx, by rw ← add_sub_cancel'_right ε₁ ε₂; exact
lt_of_le_of_lt (dist_triangle z x y) (add_lt_add_of_lt_of_le zx h)

theorem ball_half_subset (y) (h : y ∈ ball x (ε / 2)) : ball y (ε / 2) ⊆ ball x ε :=
ball_subset $ by rw sub_self_div_two; exact le_of_lt h

theorem exists_ball_subset_ball (h : y ∈ ball x ε) : ∃ ε' > 0, ball y ε' ⊆ ball x ε :=
⟨_, sub_pos.2 h, ball_subset $ by rw sub_sub_self⟩

theorem ball_eq_empty_iff_nonpos : ε ≤ 0 ↔ ball x ε = ∅ :=
(eq_empty_iff_forall_not_mem.trans
⟨λ h, le_of_not_gt $ λ ε0, h _ $ mem_ball_self ε0,
 λ ε0 y h, not_lt_of_le ε0 $ pos_of_mem_ball h⟩).symm

theorem uniformity_dist : uniformity = (⨅ ε>0, principal {p:α×α | dist p.1 p.2 < ε}) :=
metric_space.uniformity_dist _

theorem uniformity_dist' : uniformity = (⨅ε:{ε:ℝ // ε>0}, principal {p:α×α | dist p.1 p.2 < ε.val}) :=
by simp [infi_subtype]; exact uniformity_dist

theorem mem_uniformity_dist {s : set (α×α)} :
  s ∈ (@uniformity α _).sets ↔ (∃ε>0, ∀{a b:α}, dist a b < ε → (a, b) ∈ s) :=
begin
  rw [uniformity_dist', infi_sets_eq],
  simp [subset_def],
  exact assume ⟨r, hr⟩ ⟨p, hp⟩, ⟨⟨min r p, lt_min hr hp⟩, by simp [lt_min_iff, (≥)] {contextual := tt}⟩,
  exact ⟨⟨1, zero_lt_one⟩⟩
end

theorem dist_mem_uniformity {ε:ℝ} (ε0 : 0 < ε) :
  {p:α×α | dist p.1 p.2 < ε} ∈ (@uniformity α _).sets :=
mem_uniformity_dist.2 ⟨ε, ε0, λ a b, id⟩

theorem uniform_continuous_of_metric [metric_space β] {f : α → β} :
  uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0,
    ∀{a b:α}, dist a b < δ → dist (f a) (f b) < ε :=
uniform_continuous_def.trans
⟨λ H ε ε0, mem_uniformity_dist.1 $ H _ $ dist_mem_uniformity ε0,
 λ H r ru,
  let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  mem_uniformity_dist.2 ⟨δ, δ0, λ a b h, hε (hδ h)⟩⟩

theorem uniform_embedding_of_metric [metric_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ uniform_continuous f ∧
    ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, dist (f a) (f b) < ε → dist a b < δ :=
uniform_embedding_def'.trans $ and_congr iff.rfl $ and_congr iff.rfl
⟨λ H δ δ0, let ⟨t, tu, ht⟩ := H _ (dist_mem_uniformity δ0),
               ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 tu in
  ⟨ε, ε0, λ a b h, ht _ _ (hε h)⟩,
 λ H s su, let ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 su, ⟨ε, ε0, hε⟩ := H _ δ0 in
  ⟨_, dist_mem_uniformity ε0, λ a b h, hδ (hε h)⟩⟩

theorem totally_bounded_of_metric {s : set α} :
  totally_bounded s ↔ ∀ ε > 0, ∃t : set α, finite t ∧ s ⊆ ⋃y∈t, ball y ε :=
⟨λ H ε ε0, H _ (dist_mem_uniformity ε0),
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru,
               ⟨t, ft, h⟩ := H ε ε0 in
  ⟨t, ft, subset.trans h $ Union_subset_Union $ λ y, Union_subset_Union $ λ yt z, hε⟩⟩

/--A metric space space is totally bounded if one can reconstruct up to any ε>0 any element of the
space from finitely many data.-/
lemma totally_bounded_of_finite_discretization {α : Type u} [metric_space α] (s : set α)
  (H : ∀ε > (0 : real), ∃(β : Type*) (t : set β) (F : α → β),
     finite t ∧ (∀x ∈ s, F x ∈ t) ∧ (∀x y ∈ s, F x = F y → dist x y < ε)) :
  totally_bounded s :=
have A : s = ∅ → totally_bounded s :=
begin
  assume hs,
  rw totally_bounded_of_metric,
  intros ε εpos,
  exact ⟨∅, ⟨finite_empty, begin rw hs, by simp end⟩⟩
end,
have B : s ≠ ∅ → totally_bounded s :=
begin
  assume hs,
  rcases exists_mem_of_ne_empty hs with ⟨x0, hx0⟩,
  haveI : inhabited α := ⟨x0⟩,
  rw totally_bounded_of_metric,
  intros ε εpos,
  rcases H ε εpos with ⟨β, t, F, ⟨finite_t, hFt, hF⟩⟩,
  let Finv := function.inv_fun_on F s,
  let t' := Finv '' t,
  have : finite t' := finite_image _ finite_t,
  have : s ⊆ ⋃ (y : α) (H : y ∈ t'), ball y ε :=
  begin
    assume x x_in_s,
    let x' := Finv (F x),
    have : x' ∈ s := function.inv_fun_on_mem ⟨x, x_in_s, rfl⟩,
    have : F x' = F x := function.inv_fun_on_eq ⟨x, x_in_s, rfl⟩,
    have : dist x x' < ε := hF _ _ ‹x ∈ s› ‹x' ∈ s› (this.symm),
    simp,
    exact ⟨x', ⟨⟨F x, ⟨hFt _ x_in_s, by refl⟩⟩, by assumption⟩⟩
  end,
  exact ⟨t', ⟨‹finite t'›, this⟩⟩
end,
classical.by_cases A B

lemma cauchy_of_metric {f : filter α} :
  cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f.sets, ∀ x y ∈ t, dist x y < ε :=
cauchy_iff.trans $ and_congr iff.rfl
⟨λ H ε ε0, let ⟨t, tf, ts⟩ := H _ (dist_mem_uniformity ε0) in
   ⟨t, tf, λ x y xt yt, @ts (x, y) ⟨xt, yt⟩⟩,
 λ H r ru, let ⟨ε, ε0, hε⟩ := mem_uniformity_dist.1 ru,
               ⟨t, tf, h⟩ := H ε ε0 in
   ⟨t, tf, λ ⟨x, y⟩ ⟨hx, hy⟩, hε (h x y hx hy)⟩⟩

theorem nhds_eq_metric : nhds x = (⨅ε:{ε:ℝ // ε>0}, principal (ball x ε.val)) :=
begin
  rw [nhds_eq_uniformity, uniformity_dist', lift'_infi],
  { apply congr_arg, funext ε,
    rw [lift'_principal],
    { simp [ball, dist_comm] },
    { exact monotone_preimage } },
  { exact ⟨⟨1, zero_lt_one⟩⟩ },
  { intros, refl }
end

theorem mem_nhds_iff_metric : s ∈ (nhds x).sets ↔ ∃ε>0, ball x ε ⊆ s :=
begin
  rw [nhds_eq_metric, infi_sets_eq],
  { simp },
  { intros y z, cases y with y hy, cases z with z hz,
    refine ⟨⟨min y z, lt_min hy hz⟩, _⟩,
    simp [ball_subset_ball, min_le_left, min_le_right, (≥)] },
  { exact ⟨⟨1, zero_lt_one⟩⟩ }
end

theorem is_open_metric : is_open s ↔ ∀x∈s, ∃ε>0, ball x ε ⊆ s :=
by simp [is_open_iff_nhds, mem_nhds_iff_metric]

theorem is_open_ball : is_open (ball x ε) :=
is_open_metric.2 $ λ y, exists_ball_subset_ball

theorem ball_mem_nhds (x : α) {ε : ℝ} (ε0 : 0 < ε) : ball x ε ∈ (nhds x).sets :=
mem_nhds_sets is_open_ball (mem_ball_self ε0)

theorem tendsto_nhds_of_metric [metric_space β] {f : α → β} {a b} :
  tendsto f (nhds a) (nhds b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀{x:α}, dist x a < δ → dist (f x) b < ε :=
⟨λ H ε ε0, mem_nhds_iff_metric.1 (H (ball_mem_nhds _ ε0)),
 λ H s hs,
  let ⟨ε, ε0, hε⟩ := mem_nhds_iff_metric.1 hs, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  mem_nhds_iff_metric.2 ⟨δ, δ0, λ x h, hε (hδ h)⟩⟩

theorem continuous_of_metric [metric_space β] {f : α → β} :
  continuous f ↔
    ∀b (ε > 0), ∃ δ > 0, ∀a, dist a b < δ → dist (f a) (f b) < ε :=
continuous_iff_tendsto.trans $ forall_congr $ λ b, tendsto_nhds_of_metric

theorem exists_delta_of_continuous [metric_space β] {f : α → β} {ε : ℝ}
  (hf : continuous f) (hε : ε > 0) (b : α) :
  ∃ δ > 0, ∀a, dist a b ≤ δ → dist (f a) (f b) < ε :=
let ⟨δ, δ_pos, hδ⟩ := continuous_of_metric.1 hf b ε hε in
⟨δ / 2, half_pos δ_pos, assume a ha, hδ a $ lt_of_le_of_lt ha $ div_two_lt_of_pos δ_pos⟩

theorem tendsto_nhds_topo_metric {f : filter β} {u : β → α} {a : α} :
  tendsto u f (nhds a) ↔ ∀ ε > 0, ∃ n ∈ f.sets, ∀x ∈ n,  dist (u x) a < ε :=
⟨λ H ε ε0, ⟨u⁻¹' (ball a ε), H (ball_mem_nhds _ ε0), by simp⟩,
 λ H s hs,
  let ⟨ε, ε0, hε⟩ := mem_nhds_iff_metric.1 hs, ⟨δ, δ0, hδ⟩ := H _ ε0 in
  f.sets_of_superset δ0 (λx xδ, hε (hδ x xδ))⟩

theorem continuous_topo_metric [topological_space β] {f : β → α} :
  continuous f ↔ ∀a (ε > 0), ∃ n ∈ (nhds a).sets, ∀b ∈ n, dist (f b) (f a) < ε :=
continuous_iff_tendsto.trans $ forall_congr $ λ b, tendsto_nhds_topo_metric

theorem tendsto_at_top_metric [inhabited β] [semilattice_sup β] (u : β → α) {a : α} :
  tendsto u at_top (nhds a) ↔ ∀ε>0, ∃N, ∀n≥N, dist (u n) a < ε :=
begin
  rw tendsto_nhds_topo_metric,
  apply forall_congr,
  intro ε,
  apply forall_congr,
  intro hε,
  simp,
  exact ⟨λ ⟨s, ⟨N, hN⟩, hs⟩, ⟨N, λn hn, hs _ (hN _ hn)⟩, λ ⟨N, hN⟩, ⟨{n | n ≥ N}, ⟨⟨N, by simp⟩, hN⟩⟩⟩,
end

theorem eq_of_forall_dist_le {x y : α} (h : ∀ε, ε > 0 → dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

instance metric_space.to_separated : separated α :=
separated_def.2 $ λ x y h, eq_of_forall_dist_le $
  λ ε ε0, le_of_lt (h _ (dist_mem_uniformity ε0))

/-- Instantiate the reals as a metric space. -/
instance : metric_space ℝ :=
{ dist               := λx y, abs (x - y),
  dist_self          := by simp [abs_zero],
  eq_of_dist_eq_zero := by simp [add_neg_eq_zero],
  dist_comm          := assume x y, abs_sub _ _,
  dist_triangle      := assume x y z, abs_sub_le _ _ _ }

theorem real.dist_eq (x y : ℝ) : dist x y = abs (x - y) := rfl

theorem real.dist_0_eq_abs (x : ℝ) : dist x 0 = abs x :=
by simp [real.dist_eq]

@[simp] theorem abs_dist {a b : α} : abs (dist a b) = dist a b :=
abs_of_nonneg dist_nonneg

instance : orderable_topology ℝ :=
orderable_topology_of_nhds_abs $ λ x, begin
  simp only [show ∀ r, {b : ℝ | abs (x - b) < r} = ball x r,
    by simp [-sub_eq_add_neg, abs_sub, ball, real.dist_eq]],
  apply le_antisymm,
  { simp [le_infi_iff],
    exact λ ε ε0, mem_nhds_sets (is_open_ball) (mem_ball_self ε0) },
  { intros s h,
    rcases mem_nhds_iff_metric.1 h with ⟨ε, ε0, ss⟩,
    exact mem_infi_sets _ (mem_infi_sets ε0 (mem_principal_sets.2 ss)) },
end


section cauchy_seq
variables [inhabited β] [semilattice_sup β]

/--In a metric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small-/
theorem cauchy_seq_metric {u : β → α} :
  cauchy_seq u ↔ ∀ε>0, ∃N, ∀m n≥N, dist (u n) (u m) < ε :=
begin
  unfold cauchy_seq,
  rw cauchy_of_metric,
  simp,
  split,
  { intros H ε εpos,
    rcases H ε εpos with ⟨t, ⟨N, hN⟩, ht⟩,
    exact ⟨N, λm n hm hn, ht _ _ (hN _ hn) (hN _ hm)⟩ },
  { intros H ε εpos,
    rcases H (ε/2) (half_pos εpos) with ⟨N, hN⟩,
    existsi ball (u N) (ε/2),
    split,
    { exact ⟨N, λx hx, hN _ _ (le_refl N) hx⟩ },
    { exact λx y hx hy, calc
        dist x y ≤ dist x (u N) + dist y (u N) : dist_triangle_right _ _ _
        ... < ε/2 + ε/2 : add_lt_add hx hy
        ... = ε : add_halves _ } }
end

/--A variation around the metric characterization of Cauchy sequences-/
theorem cauchy_seq_metric' {u : β → α} :
  cauchy_seq u ↔ ∀ε>0, ∃N, ∀n≥N, dist (u n) (u N) < ε :=
begin
  rw cauchy_seq_metric,
  split,
  { intros H ε εpos,
    rcases H ε εpos with ⟨N, hN⟩,
    exact ⟨N, λn hn, hN _ _ (le_refl N) hn⟩ },
  { intros H ε εpos,
    rcases H (ε/2) (half_pos εpos) with ⟨N, hN⟩,
    exact ⟨N, λ m n hm hn, calc
       dist (u n) (u m) ≤ dist (u n) (u N) + dist (u m) (u N) : dist_triangle_right _ _ _
                    ... < ε/2 + ε/2 : add_lt_add (hN _ hn) (hN _ hm)
                    ... = ε : add_halves _⟩ }
end

/--Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient.-/
lemma cauchy_seq_iff_le_tendsto_0 {s : ℕ → α} :
  cauchy_seq s ↔ (∃ (b: ℕ → ℝ), (∀ n m N : ℕ, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N)
                    ∧ (tendsto b at_top (nhds 0))) :=
⟨begin
  assume hs,
  rw cauchy_seq_metric at hs,
  /- `s` is Cauchy sequence. The sequence `b` will be constructed by taking
  the supremum of the distances between `s n` and `s m` for `n m ≥ N`.
  First, we prove that all these distances are bounded, as otherwise the Sup
  would not make sense.-/
  rcases hs 1 (zero_lt_one) with ⟨N, hN⟩,
  have A : bdd_above ((λn, dist (s n) (s N)) '' {n | n ≤ N}) :=
    bdd_above_finite (finite_image _ (finite_le_nat N)),
  rcases A with ⟨CA, hA⟩,
  let M := max 1 CA,
  have B : ∀n, dist (s n) (s N) ≤ M :=
  begin
    intros n,
    cases le_total n N with h,
    { simp at hA,
      calc dist (s n) (s N) ≤ CA : hA (dist (s n) (s N)) _ h rfl
                        ... ≤ M : le_max_right _ _ },
    { calc dist (s n) (s N) ≤ 1 : le_of_lt (hN _ _ (le_refl _) h)
                        ... ≤ M : le_max_left _ _ }
  end,
  have bdd : bdd_above (range (λ(p : ℕ × ℕ), dist (s p.1) (s p.2))) :=
    ⟨M + M, begin simp, intros y n m hy, calc
      y = dist (s n) (s m) : hy.symm
      ... ≤ dist (s n) (s N) + dist (s m) (s N) : dist_triangle_right _ _ _
      ... ≤ M + M : add_le_add (B n) (B m)
    end⟩,
  --We define `b`
  let b := λN, Sup ((λ(p : ℕ × ℕ), dist (s p.1) (s p.2))''{p | p.1 ≥ N ∧ p.2 ≥ N}),
  --Prove that it bounds the distances of points in the Cauchy sequence
  have C : ∀ n m N, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N :=
  begin
    intros m n N hm hn,
    apply le_cSup,
    { apply bdd_above_subset _ bdd,
      intros d hd,
      simp at hd,
      rcases hd with ⟨m, n, ⟨h1, h2⟩⟩,
      rw ← h2,
      simp,
      exact ⟨m, n, rfl⟩ },
    { existsi (prod.mk m n),
      simp,
      exact ⟨hm, hn⟩}
  end,
  --Prove that it tends to `0`, by using the Cauchy property of `s`
  have D : tendsto b at_top (nhds 0) :=
  begin
    rw tendsto_at_top_metric,
    intros ε εpos,
    rcases hs (ε/2) (half_pos εpos) with ⟨N, hN⟩,
    existsi N,
    intros n hn,
    have : b n ≤ ε/2 :=
    begin
      apply cSup_le,
      { have : {p : ℕ × ℕ | p.fst ≥ n ∧ p.snd ≥ n} ≠ ∅ :=
          @ne_empty_of_mem _ _ (prod.mk n n) (by simp; apply le_refl),
        simpa using this },
      { simp,
        intros d p q hp hq hd,
        rw ← hd,
        apply le_of_lt (hN q p (le_trans hn hq) (le_trans hn hp)) }
    end,
    have : b n < ε := lt_of_le_of_lt this (half_lt_self εpos),
    have : 0 ≤ b n := calc
      0 = dist (s n) (s n) : by simp
        ... ≤ b n : C n n n (le_refl n) (le_refl n),
    rw real.dist_0_eq_abs,
    exact abs_lt_of_lt_of_neg_lt ‹b n < ε› (by linarith)
  end,
  -- Conclude
  exact ⟨b, ⟨C, D⟩⟩
end,
begin
  rintros ⟨b, ⟨b_bound, b_lim⟩⟩,
  /-b : ℕ → ℝ, b_bound : ∀ (n m N : ℕ), N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N,
    b_lim : tendsto b at_top (nhds 0)-/
  rw cauchy_seq_metric,
  intros ε εpos, /-ε : ℝ, εpos : ε > 0-/
  rw tendsto_at_top_metric at b_lim,
  rcases b_lim ε εpos with ⟨N, hN⟩,
  existsi N,
  intros m n hm hn,
  calc dist (s n) (s m) ≤ b N : b_bound n m N hn hm
                    ... ≤ abs(b N) : le_abs_self _
                    ... = dist (b N) 0 : by rw real.dist_0_eq_abs; refl
                    ... < ε : (hN _ (le_refl N))
end⟩

end cauchy_seq

theorem eq_of_forall_dist_le {x y : α} (h : ∀ε, ε > 0 → dist x y ≤ ε) : x = y :=
eq_of_dist_eq_zero (eq_of_le_of_forall_le_of_dense dist_nonneg h)

instance metric_space.to_separated : separated α :=
separated_def.2 $ λ x y h, eq_of_forall_dist_le $
  λ ε ε0, le_of_lt (h _ (dist_mem_uniformity ε0))

/-Instantiate a metric space as an emetric space. Before we can state the instance,
we need to show that the uniform structure coming from the edistance and the
distance coincide. -/

/--Expressing the uniformity in terms of `edist`-/
lemma mem_uniformity_dist_edist {s : set (α×α)} :
  s ∈ (@uniformity α _).sets ↔ (∃ε>0, ∀{a b:α}, edist a b < ε → (a, b) ∈ s) :=
suffices (∃ε>0, ∀a b, edist a b < ε → (a, b) ∈ s) ↔ (∃ε>0, ∀a b, dist a b < ε → (a, b) ∈ s), from
  iff.trans (mem_uniformity_dist) this.symm,
⟨show (∃ε>0, ∀a b, edist a b < ε → (a, b) ∈ s) → (∃ε>0, ∀a b, dist a b < ε → (a, b) ∈ s),
begin
  rintro ⟨ε, εpos, Hε⟩,
  rcases ε with h,
  { /- ε = ⊤, i.e., all points belong to `s` as the distance is finite.-/
    have A : ∀ a b : α, edist a b < ⊤ := assume a b, lt_top_iff_ne_top.2 (edist_ne_top a b),
    have B : ∀ a b : α, (a, b) ∈ s := assume a b, Hε _ _ (A a b),
    exact ⟨1, zero_lt_one, assume a b _, B a b⟩ },
  { /- ε < ⊤, and we can use the same value of ε as a real parameter-/
    have A : ε > 0 := ennreal.coe_lt_coe.1 εpos,
    have B : ∀ (a b : α), dist a b < ↑ε → (a, b) ∈ s := begin
      assume a b Dab,
      have I : nndist a b < ε := by rwa [← nndist_eq_dist, ← nnreal.coe_lt] at Dab,
      have J : edist a b < ε := by rw [← nndist_eq_edist]; apply ennreal.coe_lt_coe.2 I,
      exact Hε a b J
    end,
    exact ⟨ε, by simpa using A, B⟩ }
end,
show (∃ε>0, ∀a b, dist a b < ε → (a, b) ∈ s) → (∃ε>0, ∀a b, edist a b < ε → (a, b) ∈ s),
begin
  rintro ⟨ε, εpos, Hε⟩,
  have A : ((nnreal.of_real ε) : ennreal) > (0:nnreal) :=
  by apply ennreal.coe_lt_coe.2; simpa using εpos,
  have B : ∀ (a b : α), edist a b < nnreal.of_real ε → (a, b) ∈ s :=
  begin
    assume a b Dab,
    have I : nndist a b < nnreal.of_real ε :=
    by rwa [← nndist_eq_edist, ennreal.coe_lt_coe] at Dab,
    have J : dist a b < ε := begin
      rw [← nndist_eq_dist],
      have K := nnreal.coe_lt.1 I,
      rwa [nnreal.coe_of_real _ (le_of_lt εpos)] at K
    end,
    exact Hε a b J
  end,
  exact ⟨nnreal.of_real ε, A, B⟩
end⟩

theorem uniformity_edist' : uniformity = (⨅ε:{ε:ennreal // ε>0}, principal {p:α×α | edist p.1 p.2 < ε.val}) :=
suffices ∀s, s ∈ (⨅ε:{ε:ennreal // ε>0}, principal {p:α×α | edist p.1 p.2 < ε.val}).sets ↔
    (∃ε>0, ∀{a b:α}, edist a b < ε → (a, b) ∈ s), from
  filter.ext $ assume s, iff.trans (mem_uniformity_dist_edist) ((this s).symm),
begin
  assume s,
  rw [infi_sets_eq],
  simp [subset_def],
  exact assume ⟨r, hr⟩ ⟨p, hp⟩, ⟨⟨min r p, lt_min hr hp⟩, by simp [lt_min_iff, (≥)] {contextual := tt}⟩,
  exact ⟨⟨1, ennreal.zero_lt_one⟩⟩
end

theorem uniformity_edist : uniformity = (⨅ ε>0, principal {p:α×α | edist p.1 p.2 < ε}) :=
by simpa [infi_subtype] using @uniformity_edist' α _

/--A metric space induces an emetric space-/
instance emetric_space_of_metric_space [a : metric_space α] : emetric_space α :=
{ edist_self          := by simp [edist_dist],
  eq_of_edist_eq_zero := assume x y h,
    by rw [edist_dist] at h; simpa [-dist_eq_edist, -dist_eq_nndist] using h,
  edist_comm          := by simp only [edist_dist, dist_comm]; simp,
  edist_triangle      := assume x y z,
  begin
    rw [edist_dist, edist_dist, edist_dist, ← ennreal.coe_add, ennreal.coe_le_coe,
        nnreal.of_real_add_of_real (@dist_nonneg _ _ x y) (@dist_nonneg _ _ y z),
        nnreal.of_real_le_of_real_iff $
          add_nonneg (@dist_nonneg _ _ x y) (@dist_nonneg _ _ y z)],
    apply dist_triangle x y z
  end,
  uniformity_edist    := uniformity_edist,
  ..a }

section real

/-- Instantiate the reals as a metric space. -/
instance : metric_space ℝ :=
{ dist               := λx y, abs (x - y),
  dist_self          := by simp [abs_zero],
  eq_of_dist_eq_zero := by simp [add_neg_eq_zero],
  dist_comm          := assume x y, abs_sub _ _,
  dist_triangle      := assume x y z, abs_sub_le _ _ _ }

theorem real.dist_eq (x y : ℝ) : dist x y = abs (x - y) := rfl

theorem real.dist_0_eq_abs (x : ℝ) : dist x 0 = abs x :=
by simp [real.dist_eq]

@[simp] theorem abs_dist {a b : α} : abs (dist a b) = dist a b :=
abs_of_nonneg dist_nonneg


lemma closed_ball_Icc {x r : ℝ} : closed_ball x r = Icc (x-r) (x+r) :=
by ext y; rw [mem_closed_ball, dist_comm, real.dist_eq,
  abs_sub_le_iff, mem_Icc, ← sub_le_iff_le_add', sub_le]

end real

def metric_space.replace_uniformity {α} [U : uniform_space α] (m : metric_space α)
  (H : @uniformity _ U = @uniformity _ (metric_space.to_uniform_space α)) :
  metric_space α :=
{ dist               := @dist _ m.to_has_dist,
  dist_self          := dist_self,
  eq_of_dist_eq_zero := @eq_of_dist_eq_zero _ _,
  dist_comm          := dist_comm,
  dist_triangle      := dist_triangle,
  edist              := @edist _ m,
  edist_dist         := edist_dist,
  to_uniform_space   := U,
  uniformity_dist    := H.trans (@uniformity_dist α _) }

def metric_space.induced {α β} (f : α → β) (hf : function.injective f)
  (m : metric_space β) : metric_space α :=
{ dist               := λ x y, dist (f x) (f y),
  dist_self          := λ x, dist_self _,
  eq_of_dist_eq_zero := λ x y h, hf (dist_eq_zero.1 h),
  dist_comm          := λ x y, dist_comm _ _,
  dist_triangle      := λ x y z, dist_triangle _ _ _,
  edist              := λ x y, edist (f x) (f y),
  edist_dist         := λ x y, edist_dist _ _,
  to_uniform_space   := uniform_space.comap f m.to_uniform_space,
  uniformity_dist    := begin
    apply @uniformity_dist_of_mem_uniformity _ _ _ _ _ (λ x y, dist (f x) (f y)),
    refine λ s, mem_comap_sets.trans _,
    split; intro H,
    { rcases H with ⟨r, ru, rs⟩,
      rcases mem_uniformity_dist.1 ru with ⟨ε, ε0, hε⟩,
      refine ⟨ε, ε0, λ a b h, rs (hε _)⟩, exact h },
    { rcases H with ⟨ε, ε0, hε⟩,
      exact ⟨_, dist_mem_uniformity ε0, λ ⟨a, b⟩, hε⟩ }
  end }

instance {p : α → Prop} [t : metric_space α] : metric_space (subtype p) :=
metric_space.induced subtype.val (λ x y, subtype.eq) t

theorem subtype.dist_eq {p : α → Prop} [t : metric_space α] (x y : subtype p) :
  dist x y = dist x.1 y.1 := rfl

section prod

instance prod.metric_space_max [metric_space β] : metric_space (α × β) :=
{ dist := λ x y, max (dist x.1 y.1) (dist x.2 y.2),
  dist_self := λ x, by simp,
  eq_of_dist_eq_zero := λ x y h, begin
    cases max_le_iff.1 (le_of_eq h) with h₁ h₂,
    exact prod.ext_iff.2 ⟨dist_le_zero.1 h₁, dist_le_zero.1 h₂⟩
  end,
  dist_comm := λ x y, by simp [dist_comm],
  dist_triangle := λ x y z, max_le
    (le_trans (dist_triangle _ _ _) (add_le_add (le_max_left _ _) (le_max_left _ _)))
    (le_trans (dist_triangle _ _ _) (add_le_add (le_max_right _ _) (le_max_right _ _))),
  edist := λ x y, max (edist x.1 y.1) (edist x.2 y.2),
  edist_dist := assume x y, begin
    have I : monotone (nnreal.of_real) := assume x y h, nnreal.of_real_le_of_real h,
    have J : monotone (λ (t:nnreal), (t:ennreal)) := assume x y h, ennreal.coe_le_coe.2 h,
    have A : monotone (λ (a:ℝ), ((nnreal.of_real a) : ennreal)) := monotone_comp I J,
    have B := (max_distrib_of_monotone A).symm,
    rw [← dist_eq_edist, ← dist_eq_edist, B]
  end,
  uniformity_dist := begin
    refine uniformity_prod.trans _,
    simp [uniformity_dist, comap_infi],
    rw ← infi_inf_eq, congr, funext,
    rw ← infi_inf_eq, congr, funext,
    simp [inf_principal, ext_iff, max_lt_iff]
  end,
  to_uniform_space := prod.uniform_space }

lemma prod.dist_eq [metric_space β] {x y : α × β} :
  dist x y = max (dist x.1 y.1) (dist x.2 y.2) := rfl

end prod

section sum
variables [metric_space β] [inhabited α] [inhabited β]
open sum (inl inr)

/--Distance on a disjoint union. There are many (noncanonical) ways to put a distance compatible with each factor.
If the two spaces are bounded, one can say for instance that each point in the first is at distance
`diam α + diam β + 1` of each point in the second.
Instead, we choose a construction that works for unbounded spaces, but requires basepoints.
We embed isometrically each factor, set the basepoints at distance 1,
arbitrarily, and say that the distance from `a` to `b` is the sum of the distances of `a` and `b` to
their respective basepoints, plus the distance 1 between the basepoints.
Since there is an arbitrary choice in this construction, it is not an instance by default-/
private def sum.dist : α ⊕ β → α ⊕ β → ℝ
| (inl a) (inl a') := dist a a'
| (inr b) (inr b') := dist b b'
| (inl a) (inr b)  := dist a (default α) + 1 + dist (default β) b
| (inr b) (inl a)  := dist b (default β) + 1 + dist (default α) a

private lemma sum.dist_comm (x y : α ⊕ β) : sum.dist x y = sum.dist y x :=
by cases x; cases y; simp only [sum.dist, dist_comm, add_comm, add_left_comm]

lemma sum.one_dist_le {x : α} {y : β} : 1 ≤ sum.dist (inl x) (inr y) :=
le_trans (le_add_of_nonneg_right dist_nonneg) $
add_le_add_right (le_add_of_nonneg_left dist_nonneg) _

lemma sum.one_dist_le' {x : α} {y : β} : 1 ≤ sum.dist (inr y) (inl x) :=
by rw sum.dist_comm; exact sum.one_dist_le

private lemma sum.dist_triangle : ∀ x y z : α ⊕ β, sum.dist x z ≤ sum.dist x y + sum.dist y z
| (inl x) (inl y) (inl z) := dist_triangle _ _ _
| (inl x) (inl y) (inr z) := by unfold sum.dist; rw [← add_assoc, ← add_assoc];
  exact add_le_add_right (add_le_add_right (dist_triangle _ _ _) _) _
| (inl x) (inr y) (inl z) := by unfold sum.dist; rw [add_assoc _ (1:ℝ), add_assoc];
  refine le_trans (dist_triangle _ _ _) (add_le_add_left _ _);
  refine le_trans (le_add_of_nonneg_left (add_nonneg zero_le_one dist_nonneg)) (add_le_add_left _ _);
  exact le_add_of_nonneg_left (add_nonneg dist_nonneg zero_le_one)
| (inr x) (inl y) (inl z) := by unfold sum.dist; rw [add_assoc _ _ (dist y z)];
  exact add_le_add_left (dist_triangle _ _ _) _
| (inr x) (inr y) (inl z) := by unfold sum.dist; rw [← add_assoc, ← add_assoc];
  exact add_le_add_right (add_le_add_right (dist_triangle _ _ _) _) _
| (inr x) (inl y) (inr z) := by unfold sum.dist; rw [add_assoc _ (1:ℝ), add_assoc];
  refine le_trans (dist_triangle _ _ _) (add_le_add_left _ _);
  refine le_trans (le_add_of_nonneg_left (add_nonneg zero_le_one dist_nonneg)) (add_le_add_left _ _);
  exact le_add_of_nonneg_left (add_nonneg dist_nonneg zero_le_one)
| (inl x) (inr y) (inr z) := by unfold sum.dist; rw [add_assoc _ _ (dist y z)];
  exact add_le_add_left (dist_triangle _ _ _) _
| (inr x) (inr y) (inr z) := dist_triangle _ _ _

private lemma sum.eq_of_dist_eq_zero : ∀ x y : α ⊕ β, sum.dist x y = 0 → x = y
| (inl x) (inl y) h := by simp only [sum.dist] at h ⊢; exact eq_of_dist_eq_zero h
| (inl x) (inr y) h :=
  (ne_of_gt (lt_of_lt_of_le zero_lt_one sum.one_dist_le) h).elim
| (inr x) (inl y) h :=
  (ne_of_gt (lt_of_lt_of_le zero_lt_one sum.one_dist_le') h).elim
| (inr x) (inr y) h := by simp only [sum.dist] at h ⊢; exact eq_of_dist_eq_zero h

private lemma sum.mem_uniformity (s : set ((α ⊕ β) × (α ⊕ β))) :
  s ∈ (@uniformity (α ⊕ β) _).sets ↔ ∃ ε > 0, ∀ a b, sum.dist a b < ε → (a, b) ∈ s :=
begin
  split,
  { rintro ⟨hsα, hsβ⟩,
    rcases mem_uniformity_dist.1 hsα with ⟨εα, εα0, hα⟩,
    rcases mem_uniformity_dist.1 hsβ with ⟨εβ, εβ0, hβ⟩,
    refine ⟨min (min εα εβ) 1, lt_min (lt_min εα0 εβ0) zero_lt_one, _⟩,
    rintro (a|a) (b|b) h,
    { exact hα (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_left _ _))) },
    { cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) sum.one_dist_le },
    { cases not_le_of_lt (lt_of_lt_of_le h (min_le_right _ _)) sum.one_dist_le' },
    { exact hβ (lt_of_lt_of_le h (le_trans (min_le_left _ _) (min_le_right _ _))) } },
  { rintro ⟨ε, ε0, H⟩,
    split; rw [filter.mem_map, mem_uniformity_dist];
      exact ⟨ε, ε0, λ x y h, H _ _ (by exact h)⟩ }
end

/-- The distance on the disjoint union indeed defines a metric space. All the distance properties follow from our
choice of the distance. The harder work is to show that the uniform structure defined by the distance coincides
with the disjoint union uniform structure. -/
def metric_space_sum : metric_space (α ⊕ β) :=
{ dist := sum.dist,
  dist_self := λx, by cases x; simp only [sum.dist, dist_self],
  dist_comm := sum.dist_comm,
  dist_triangle := sum.dist_triangle,
  eq_of_dist_eq_zero := sum.eq_of_dist_eq_zero,
  to_uniform_space := sum.uniform_space,
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ sum.mem_uniformity }

end sum

theorem uniform_continuous_dist' : uniform_continuous (λp:α×α, dist p.1 p.2) :=
uniform_continuous_of_metric.2 (λ ε ε0, ⟨ε/2, half_pos ε0,
begin
  suffices,
  { intros p q h, cases p with p₁ p₂, cases q with q₁ q₂,
    cases max_lt_iff.1 h with h₁ h₂, clear h,
    dsimp at h₁ h₂ ⊢,
    rw real.dist_eq,
    refine abs_sub_lt_iff.2 ⟨_, _⟩,
    { revert p₁ p₂ q₁ q₂ h₁ h₂, exact this },
    { apply this; rwa dist_comm } },
  intros p₁ p₂ q₁ q₂ h₁ h₂,
  have := add_lt_add
    (abs_sub_lt_iff.1 (lt_of_le_of_lt (abs_dist_sub_le p₁ q₁ p₂) h₁)).1
    (abs_sub_lt_iff.1 (lt_of_le_of_lt (abs_dist_sub_le p₂ q₂ q₁) h₂)).1,
  rwa [add_halves, dist_comm p₂, sub_add_sub_cancel, dist_comm q₂] at this
end⟩)

theorem uniform_continuous_dist [uniform_space β] {f g : β → α}
  (hf : uniform_continuous f) (hg : uniform_continuous g) :
  uniform_continuous (λb, dist (f b) (g b)) :=
(hf.prod_mk hg).comp uniform_continuous_dist'

theorem continuous_dist' : continuous (λp:α×α, dist p.1 p.2) :=
uniform_continuous_dist'.continuous

theorem continuous_dist [topological_space β] {f g : β → α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, dist (f b) (g b)) :=
(hf.prod_mk hg).comp continuous_dist'

theorem tendsto_dist {f g : β → α} {x : filter β} {a b : α}
  (hf : tendsto f x (nhds a)) (hg : tendsto g x (nhds b)) :
  tendsto (λx, dist (f x) (g x)) x (nhds (dist a b)) :=
have tendsto (λp:α×α, dist p.1 p.2) (nhds (a, b)) (nhds (dist a b)),
  from continuous_iff_tendsto.mp continuous_dist' (a, b),
(hf.prod_mk hg).comp (by rw [nhds_prod_eq] at this; exact this)

lemma nhds_comap_dist (a : α) : (nhds (0 : ℝ)).comap (λa', dist a' a) = nhds a :=
have h₁ : ∀ε, (λa', dist a' a) ⁻¹' ball 0 ε ⊆ ball a ε,
  by simp [subset_def, real.dist_0_eq_abs],
have h₂ : tendsto (λa', dist a' a) (nhds a) (nhds (dist a a)),
  from tendsto_dist tendsto_id tendsto_const_nhds,
le_antisymm
  (by simp [h₁, nhds_eq_metric, infi_le_infi, principal_mono,
      -le_principal_iff, -le_infi_iff])
  (by simpa [map_le_iff_le_comap.symm, tendsto] using h₂)

lemma tendsto_iff_dist_tendsto_zero {f : β → α} {x : filter β} {a : α} :
  (tendsto f x (nhds a)) ↔ (tendsto (λb, dist (f b) a) x (nhds 0)) :=
by rw [← nhds_comap_dist a, tendsto_comap_iff]

theorem is_closed_ball : is_closed (closed_ball x ε) :=
is_closed_le (continuous_dist continuous_id continuous_const) continuous_const

/-- ε-characterization of the closure in metric spaces-/
theorem mem_closure_iff' {α : Type u} [metric_space α] {s : set α} {a : α} :
  a ∈ closure s ↔ ∀ε>0, ∃b ∈ s, dist a b < ε :=
⟨begin
  intros ha ε hε,
  have A : ball a ε ∩ s ≠ ∅ := mem_closure_iff.1 ha _ is_open_ball (mem_ball_self hε),
  cases ne_empty_iff_exists_mem.1 A with b hb,
  simp,
  exact ⟨b, ⟨hb.2, by have B := hb.1; simpa [mem_ball'] using B⟩⟩
end,
begin
  intros H,
  apply mem_closure_iff.2,
  intros o ho ao,
  rcases is_open_metric.1 ho a ao with ⟨ε, ⟨εpos, hε⟩⟩,
  rcases H ε εpos with ⟨b, ⟨bs, bdist⟩⟩,
  have B : b ∈ o ∩ s := ⟨hε (by simpa [dist_comm]), bs⟩,
  apply ne_empty_of_mem B
end⟩

section pi
open finset lattice
variables {π : β → Type*} [fintype β] [∀b, metric_space (π b)]

instance has_dist_pi : has_dist (Πb, π b) :=
⟨λf g, ((finset.sup univ (λb, nndist (f b) (g b)) : nnreal) : ℝ)⟩

lemma dist_pi_def (f g : Πb, π b) :
  dist f g = (finset.sup univ (λb, nndist (f b) (g b)) : nnreal) := rfl

instance metric_space_pi : metric_space (Πb, π b) :=
{ dist := dist,
  dist_self := assume f, (nnreal.coe_eq_zero _).2 $ bot_unique $ finset.sup_le $ by simp,
  dist_comm := assume f g, nnreal.eq_iff.2 $ by congr; ext a; exact nndist_comm _ _,
  dist_triangle := assume f g h, show dist f h ≤ (dist f g) + (dist g h), from
    begin
      simp only [dist_pi_def, (nnreal.coe_add _ _).symm, nnreal.coe_le.symm,
        finset.sup_le_iff],
      assume b hb,
      exact le_trans (nndist_triangle _ (g b) _) (add_le_add (le_sup hb) (le_sup hb))
    end,
  eq_of_dist_eq_zero := assume f g eq0,
    begin
      simp only [dist_pi_def, nnreal.coe_eq_zero, nnreal.bot_eq_zero.symm, eq_bot_iff,
        finset.sup_le_iff] at eq0,
      exact (funext $ assume b, eq_of_nndist_eq_zero $ bot_unique $ eq0 b $ mem_univ b),
    end,
  edist := λ f g, finset.sup univ (λb, edist (f b) (g b)),
  edist_dist := assume x y,
  have A : sup univ (λ (b : β), ((nndist (x b) (y b)) : ennreal)) = ↑(sup univ (λ (b : β), nndist (x b) (y b))) :=
  begin
    refine eq.symm (comp_sup_eq_sup_comp _ _ _),
    exact (assume x y h, ennreal.coe_le_coe.2 h), refl
  end,
  by unfold dist; simp; simp only [(nndist_eq_edist _ _).symm, A] }

end pi

section first_countable

instance metric_space.first_countable_topology (α : Type u) [metric_space α] :
  first_countable_topology α :=
⟨assume a, ⟨⋃ i:ℕ, {ball a (i + 1 : ℝ)⁻¹},
  countable_Union $ assume n, countable_singleton _,
  suffices (⨅ i:{ i : ℝ // i > 0}, principal (ball a i)) = ⨅ (n : ℕ), principal (ball a (↑n + 1)⁻¹),
    by simpa [nhds_eq_metric, @infi_comm _ _ ℕ],
  begin
    apply le_antisymm,
    { refine le_infi (assume n, infi_le_of_le _ _),
      exact ⟨(n + 1)⁻¹, inv_pos $ add_pos_of_nonneg_of_pos (nat.cast_nonneg n) zero_lt_one⟩,
      exact le_refl _ },
    refine le_infi (assume ε, _),
    rcases exists_nat_gt (ε:ℝ)⁻¹ with ⟨_ | n, εn⟩,
    { exact (lt_irrefl (0:ℝ) $ lt_trans (inv_pos ε.2) εn).elim },
    refine infi_le_of_le n (principal_mono.2 $ ball_subset_ball $ _),
    exact (inv_le ε.2 $ add_pos_of_nonneg_of_pos (nat.cast_nonneg n) zero_lt_one).1 (le_of_lt εn)
  end⟩⟩

end first_countable

section second_countable

/-- A separable metric space is second countable: one obtains a countable basis by taking
the balls centered at points in a dense subset, and with rational radii. We do not register
this as an instance, as there is already an instance going in the other direction
from second countable spaces to separable spaces, and we want to avoid loops.-/
lemma second_countable_of_separable_metric_space (α : Type u) [metric_space α] [separable_space α] :
  second_countable_topology α :=
let ⟨S, ⟨S_countable, S_dense⟩⟩ := separable_space.exists_countable_closure_eq_univ α in
⟨⟨⋃x ∈ S, ⋃ (n : nat), {ball x (n⁻¹)},
⟨show countable ⋃x ∈ S, ⋃ (n : nat), {ball x (n⁻¹)},
begin
  apply countable_bUnion S_countable,
  intros a aS,
  apply countable_Union,
  simp
end,
show uniform_space.to_topological_space α = generate_from (⋃x ∈ S, ⋃ (n : nat), {ball x (n⁻¹)}),
begin
  have A : ∀ (u : set α), (u ∈ ⋃x ∈ S, ⋃ (n : nat), ({ball x ((n : ℝ)⁻¹)} : set (set α))) → is_open u :=
  begin
    simp,
    intros u x hx i u_ball,
    rw [u_ball],
    apply is_open_ball
  end,
  have B : is_topological_basis (⋃x ∈ S, ⋃ (n : nat), ({ball x (n⁻¹)} : set (set α))) :=
  begin
    apply is_topological_basis_of_open_of_nhds A,
    intros a u au open_u,
    rcases is_open_metric.1 open_u a au with ⟨ε, εpos, εball⟩,
    have : ε / 2 > 0 := half_pos εpos,
    /- The ball `ball a ε` is included in `u`. We need to find one of our balls `ball x (n⁻¹)`
    containing `a` and contained in `ball a ε`. For this, we take `n` larger than `2/ε`, and
    then `x` in `S` at distance at most `n⁻¹` of `a`-/
    rcases exists_nat_gt (ε/2)⁻¹ with ⟨n, εn⟩,
    have : (n : ℝ) > 0 := lt_trans (inv_pos ‹ε/2 > 0›) εn,
    have : 0 < (n : ℝ)⁻¹ := inv_pos this,
    have : (n : ℝ)⁻¹ < ε/2 := (inv_lt ‹ε/2 > 0› ‹(n : ℝ) > 0›).1 εn,
    have : (a : α) ∈ closure (S : set α) := by rw [S_dense]; simp,
    rcases mem_closure_iff'.1 this _ ‹0 < (n : ℝ)⁻¹› with ⟨x, xS, xdist⟩,
    have : a ∈ ball x (n⁻¹) := by simpa,
    have : ball x (n⁻¹) ⊆ ball a ε :=
    begin
      intros y,
      simp,
      intros ydist,
      calc dist y a = dist a y : dist_comm _ _
          ... ≤ dist a x + dist y x : dist_triangle_right _ _ _
          ... < n⁻¹ + n⁻¹ : add_lt_add xdist ydist
          ... < ε/2 + ε/2 : add_lt_add ‹(n : ℝ)⁻¹ < ε/2› ‹(n : ℝ)⁻¹ < ε/2›
          ... = ε : add_halves _,
    end,
    have : ball x (n⁻¹) ⊆ u := subset.trans this εball,
    existsi ball x (↑n)⁻¹,
    simp,
    exact ⟨⟨x, ⟨xS, ⟨n, rfl⟩⟩⟩, ⟨by assumption, by assumption⟩⟩,
  end,
  exact B.2.2,
end⟩⟩⟩

end second_countable

section compact

/-- Any compact set in a metric space can be covered by finitely many balls of a given positive
radius -/
lemma finite_cover_balls_of_compact {α : Type u} [metric_space α] {s : set α}
  (hs : compact s) {e : ℝ} (he : e > 0) :
  ∃t ⊆ s, (finite t ∧ s ⊆ (⋃x∈t, ball x e)) :=
begin
  apply compact_elim_finite_subcover_image hs,
  { simp [is_open_ball] },
  { intros x xs,
    simp,
    exact ⟨x, ⟨xs, by simpa⟩⟩ }
end

/-- A compact set in a metric space is separable, i.e., it is the closure of a countable set -/
lemma countable_closure_of_compact {α : Type u} [metric_space α] {s : set α} (hs : compact s) :
  ∃ t ⊆ s, (countable t ∧ s = closure t) :=
begin
  have A : ∀ (e:ℝ), e > 0 → ∃ t ⊆ s, (finite t ∧ s ⊆ (⋃x∈t, ball x e)) :=
    assume e, finite_cover_balls_of_compact hs,
  have B : ∀ (e:ℝ), ∃ t ⊆ s, finite t ∧ (e > 0 → s ⊆ (⋃x∈t, ball x e)) :=
  begin
    intro e,
    cases le_or_gt e 0 with h,
    { exact ⟨∅, by finish⟩ },
    { rcases A e h with ⟨s, ⟨finite_s, closure_s⟩⟩, existsi s, finish }
  end,
  /- The desired countable set is obtained by taking for each `n` the centers of a finite cover
  by balls of radius `1/n`, and then the union over `n`. -/
  choose T T_in_s finite_T using B,
  let t := ⋃n, T (n : ℕ)⁻¹,
  have T₁ : t ⊆ s := begin apply Union_subset, assume n, apply T_in_s end,
  have T₂ : countable t := by finish [countable_Union, countable_finite],
  have T₃ : s ⊆ closure t :=
  begin
    intros x x_in_s,
    apply mem_closure_iff'.2,
    intros ε εpos,
    rcases exists_nat_gt ε⁻¹ with ⟨n, εn⟩,
    have : (n : ℝ) > 0 := lt_trans (inv_pos εpos) εn,
    have inv_n_pos : 0 < (n : ℝ)⁻¹ := inv_pos this,
    have C : x ∈ (⋃y∈ T (↑n)⁻¹, ball y (↑n)⁻¹) := mem_of_mem_of_subset x_in_s ((finite_T (↑n)⁻¹).2 inv_n_pos),
    rcases mem_Union.1 C with ⟨y, _, ⟨y_in_T, rfl⟩, x_w⟩,
    simp at x_w,
    have : y ∈ t := mem_of_mem_of_subset y_in_T (by apply subset_Union (λ (n:ℕ), T (n : ℝ)⁻¹)),
    have : dist x y < ε := lt_trans x_w ((inv_lt εpos ‹(n : ℝ) > 0›).1 εn),
    exact ⟨y, ‹y ∈ t›, ‹dist x y < ε›⟩
  end,
  have T₄ : closure t ⊆ s :=
  calc closure t ⊆ closure s : closure_mono T₁
             ... = s : closure_eq_of_is_closed (closed_of_compact _ hs),
  exact ⟨t, ⟨T₁, T₂, subset.antisymm T₃ T₄⟩⟩
end

end compact

section proper_space

/-- A metric space is proper if all closed balls are compact. -/
class proper_space (α : Type u) [metric_space α] : Prop :=
(compact_ball : ∀x:α, ∀r, compact (closed_ball x r))

/- A compact metric space is proper -/
instance proper_of_compact [metric_space α] [compact_space α] : proper_space α :=
⟨assume x r, compact_of_is_closed_subset compact_univ is_closed_ball (subset_univ _)⟩

/-- A proper space is locally compact -/
instance locally_compact_of_proper [metric_space α] [proper_space α] :
  locally_compact_space α :=
begin
  apply locally_compact_of_compact_nhds,
  intros x,
  existsi closed_ball x 1,
  split,
  { apply mem_nhds_iff_metric.2,
    existsi (1 : ℝ),
    simp,
    exact ⟨zero_lt_one, ball_subset_closed_ball⟩ },
  { apply proper_space.compact_ball }
end

/-- A proper space is complete -/
instance complete_of_proper {α : Type u} [metric_space α] [proper_space α] : complete_space α :=
⟨begin
  intros f hf,
  /- We want to show that the Cauchy filter `f` is converging. It suffices to find a closed
  ball (therefore compact by properness) where it is nontrivial. -/
  have A : ∃ t ∈ f.sets, ∀ x y ∈ t, dist x y < 1 := (cauchy_of_metric.1 hf).2 1 zero_lt_one,
  rcases A with ⟨t, ⟨t_fset, ht⟩⟩,
  rcases inhabited_of_mem_sets hf.1 t_fset with ⟨x, xt⟩,
  have : t ⊆ closed_ball x 1 := by intros y yt; simp [dist_comm]; apply le_of_lt (ht x y xt yt),
  have : closed_ball x 1 ∈ f.sets := f.sets_of_superset t_fset this,
  rcases (compact_iff_totally_bounded_complete.1 (proper_space.compact_ball x 1)).2 f hf (le_principal_iff.2 this)
    with ⟨y, _, hy⟩,
  exact ⟨y, hy⟩
end⟩

/-- A proper metric space is separable, and therefore second countable. Indeed, any ball is
compact, and therefore admits a countable dense subset. Taking a countable union over the balls
centered at a fixed point and with integer radius, one obtains a countable set which is
dense in the whole space. -/
instance second_countable_of_proper [metric_space α] [proper_space α] :
  second_countable_topology α :=
begin
  /- We show that the space admits a countable dense subset. The case where the space is empty
  is special, and trivial. -/
  have A : (univ : set α) = ∅ → ∃(s : set α), countable s ∧ closure s = (univ : set α) :=
    assume H, ⟨∅, ⟨by simp, by simp; exact H.symm⟩⟩,
  have B : (univ : set α) ≠ ∅ → ∃(s : set α), countable s ∧ closure s = (univ : set α) :=
  begin
    /- When the space is not empty, we take a point `x` in the space, and then a countable set
    `T r` which is dense in the closed ball `closed_ball x r` for each `r`. Then the set
    `t = ⋃ T n` (where the union is over all integers `n`) is countable, as a countable union
    of countable sets, and dense in the space by construction. -/
    assume non_empty,
    rcases ne_empty_iff_exists_mem.1 non_empty with ⟨x, x_univ⟩,
    choose T a using show ∀ (r:ℝ), ∃ t ⊆ closed_ball x r, (countable (t : set α) ∧ closed_ball x r = closure t),
      from assume r, countable_closure_of_compact (proper_space.compact_ball _ _),
    let t := (⋃n:ℕ, T (n : ℝ)),
    have T₁ : countable t := by finish [countable_Union],
    have T₂ : closure t ⊆ univ := by simp,
    have T₃ : univ ⊆ closure t :=
    begin
      intros y y_univ,
      rcases exists_nat_gt (dist y x) with ⟨n, n_large⟩,
      have h : y ∈ closed_ball x (n : ℝ) := by simp; apply le_of_lt n_large,
      have h' : closed_ball x (n : ℝ) = closure (T (n : ℝ)) := by finish,
      have : y ∈ closure (T (n : ℝ)) := by rwa h' at h,
      show y ∈ closure t, from mem_of_mem_of_subset this (by apply closure_mono; apply subset_Union (λ(n:ℕ), T (n:ℝ))),
    end,
    exact ⟨t, ⟨T₁, subset.antisymm T₂ T₃⟩⟩
  end,
  haveI : separable_space α := ⟨by_cases A B⟩,
  apply second_countable_of_separable_metric_space,
end

end proper_space

lemma lebesgue_number_lemma_of_metric
  {s : set α} {ι} {c : ι → set α} (hs : compact s)
  (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
  ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i :=
let ⟨n, en, hn⟩ := lebesgue_number_lemma hs hc₁ hc₂,
    ⟨δ, δ0, hδ⟩ := mem_uniformity_dist.1 en in
⟨δ, δ0, assume x hx, let ⟨i, hi⟩ := hn x hx in
 ⟨i, assume y hy, hi (hδ (mem_ball'.mp hy))⟩⟩

lemma lebesgue_number_lemma_of_metric_sUnion
  {s : set α} {c : set (set α)} (hs : compact s)
  (hc₁ : ∀ t ∈ c, is_open t) (hc₂ : s ⊆ ⋃₀ c) :
  ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, ball x δ ⊆ t :=
by rw sUnion_eq_Union at hc₂;
   simpa using lebesgue_number_lemma_of_metric hs (by simpa) hc₂
