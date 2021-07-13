/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.mean_value
import tactic.monotonicity

/-!
# Extending differentiability to the boundary

We investigate how differentiable functions inside a set extend to differentiable functions
on the boundary. For this, it suffices that the function and its derivative admit limits there.
A general version of this statement is given in `has_fderiv_at_boundary_of_tendsto_fderiv`.

One-dimensional versions, in which one wants to obtain differentiability at the left endpoint or
the right endpoint of an interval, are given in
`has_deriv_at_interval_left_endpoint_of_tendsto_deriv` and
`has_deriv_at_interval_right_endpoint_of_tendsto_deriv`. These versions are formulated in terms
of the one-dimensional derivative `deriv ℝ f`.
-/


variables {E : Type*} [normed_group E] [normed_space ℝ E]
          {F : Type*} [normed_group F] [normed_space ℝ F]

open filter set metric continuous_linear_map
open_locale topological_space
local attribute [mono] prod_mono

/-- If a function `f` is differentiable in a convex open set and continuous on its closure, and its
derivative converges to a limit `f'` at a point on the boundary, then `f` is differentiable there
with derivative `f'`. -/
theorem has_fderiv_at_boundary_of_tendsto_fderiv {f : E → F} {s : set E} {x : E} {f' : E →L[ℝ] F}
  (f_diff : differentiable_on ℝ f s) (s_conv : convex s) (s_open : is_open s)
  (f_cont : ∀y ∈ closure s, continuous_within_at f s y)
  (h : tendsto (λy, fderiv ℝ f y) (𝓝[s] x) (𝓝 f')) :
  has_fderiv_within_at f f' (closure s) x :=
begin
  classical,
  -- one can assume without loss of generality that `x` belongs to the closure of `s`, as the
  -- statement is empty otherwise
  by_cases hx : x ∉ closure s,
  { rw ← closure_closure at hx, exact has_fderiv_within_at_of_not_mem_closure hx },
  push_neg at hx,
  rw [has_fderiv_within_at, has_fderiv_at_filter, asymptotics.is_o_iff],
  /- One needs to show that `∥f y - f x - f' (y - x)∥ ≤ ε ∥y - x∥` for `y` close to `x` in `closure
  s`, where `ε` is an arbitrary positive constant. By continuity of the functions, it suffices to
  prove this for nearby points inside `s`. In a neighborhood of `x`, the derivative of `f` is
  arbitrarily close to `f'` by assumption. The mean value inequality completes the proof. -/
  assume ε ε_pos,
  obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ y ∈ s, dist y x < δ → ∥fderiv ℝ f y - f'∥ < ε,
    by simpa [dist_zero_right] using tendsto_nhds_within_nhds.1 h ε ε_pos,
  set B := ball x δ,
  suffices : ∀ y ∈ B ∩ (closure s), ∥f y - f x - (f' y - f' x)∥ ≤ ε * ∥y - x∥,
    from mem_nhds_within_iff.2 ⟨δ, δ_pos, λy hy, by simpa using this y hy⟩,
  suffices : ∀ p : E × E, p ∈ closure ((B ∩ s).prod (B ∩ s)) → ∥f p.2 - f p.1 - (f' p.2 - f' p.1)∥
    ≤ ε * ∥p.2 - p.1∥,
  { rw closure_prod_eq at this,
    intros y y_in,
    apply this ⟨x, y⟩,
    have : B ∩ closure s ⊆ closure (B ∩ s), from closure_inter_open is_open_ball,
    exact ⟨this ⟨mem_ball_self δ_pos, hx⟩, this y_in⟩ },
  have key : ∀ p : E × E, p ∈ (B ∩ s).prod (B ∩ s) → ∥f p.2 - f p.1 - (f' p.2 - f' p.1)∥
    ≤ ε * ∥p.2 - p.1∥,
  { rintros ⟨u, v⟩ ⟨u_in, v_in⟩,
    have conv : convex (B ∩ s) := (convex_ball _ _).inter s_conv,
    have diff : differentiable_on ℝ f (B ∩ s) := f_diff.mono (inter_subset_right _ _),
    have bound : ∀ z ∈ (B ∩ s), ∥fderiv_within ℝ f (B ∩ s) z - f'∥ ≤ ε,
    { intros z z_in,
      convert le_of_lt (hδ _ z_in.2 z_in.1),
      have op : is_open (B ∩ s) := is_open_ball.inter s_open,
      rw differentiable_at.fderiv_within _ (op.unique_diff_on z z_in),
      exact (diff z z_in).differentiable_at (is_open.mem_nhds op z_in) },
    simpa using conv.norm_image_sub_le_of_norm_fderiv_within_le' diff bound u_in v_in },
  rintros ⟨u, v⟩ uv_in,
  refine continuous_within_at.closure_le uv_in _ _ key,
  have f_cont' : ∀y ∈ closure s, continuous_within_at (f - f') s y,
  { intros y y_in,
    exact tendsto.sub (f_cont y y_in) (f'.cont.continuous_within_at) },
  all_goals { -- common start for both continuity proofs
    have : (B ∩ s).prod (B ∩ s) ⊆ s.prod s, by mono ; exact inter_subset_right _ _,
    obtain ⟨u_in, v_in⟩ : u ∈ closure s ∧ v ∈ closure s,
      by simpa [closure_prod_eq] using closure_mono this uv_in,
    apply continuous_within_at.mono _ this,
    simp only [continuous_within_at] },
  rw nhds_within_prod_eq,
  { have : ∀ u v, f v - f u - (f' v - f' u) = f v - f' v - (f u - f' u) := by { intros, abel },
    simp only [this],
    exact tendsto.comp continuous_norm.continuous_at
      ((tendsto.comp (f_cont' v v_in) tendsto_snd).sub $
        tendsto.comp (f_cont' u u_in) tendsto_fst) },
  { apply tendsto_nhds_within_of_tendsto_nhds,
    rw nhds_prod_eq,
    exact tendsto_const_nhds.mul
      (tendsto.comp continuous_norm.continuous_at $ tendsto_snd.sub tendsto_fst) },
end

/-- If a function is differentiable on the right of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the right at `a`. -/
lemma has_deriv_at_interval_left_endpoint_of_tendsto_deriv {s : set ℝ} {e : E} {a : ℝ} {f : ℝ → E}
  (f_diff : differentiable_on ℝ f s) (f_lim : continuous_within_at f s a)
  (hs : s ∈ 𝓝[Ioi a] a)
  (f_lim' : tendsto (λx, deriv f x) (𝓝[Ioi a] a) (𝓝 e)) :
  has_deriv_within_at f e (Ici a) a :=
begin
  /- This is a specialization of `has_fderiv_at_boundary_of_tendsto_fderiv`. To be in the setting of
  this theorem, we need to work on an open interval with closure contained in `s ∪ {a}`, that we
  call `t = (a, b)`. Then, we check all the assumptions of this theorem and we apply it. -/
  obtain ⟨b, ab, sab⟩ : ∃ b ∈ Ioi a, Ioc a b ⊆ s :=
    mem_nhds_within_Ioi_iff_exists_Ioc_subset.1 hs,
  let t := Ioo a b,
  have ts : t ⊆ s := subset.trans Ioo_subset_Ioc_self sab,
  have t_diff : differentiable_on ℝ f t := f_diff.mono ts,
  have t_conv : convex t := convex_Ioo a b,
  have t_open : is_open t := is_open_Ioo,
  have t_closure : closure t = Icc a b := closure_Ioo ab,
  have t_cont : ∀y ∈ closure t, continuous_within_at f t y,
  { rw t_closure,
    assume y hy,
    by_cases h : y = a,
    { rw h, exact f_lim.mono ts },
    { have : y ∈ s := sab ⟨lt_of_le_of_ne hy.1 (ne.symm h), hy.2⟩,
      exact (f_diff.continuous_on y this).mono ts } },
  have t_diff' : tendsto (λx, fderiv ℝ f x) (𝓝[t] a) (𝓝 (smul_right 1 e)),
  { simp [deriv_fderiv.symm],
    refine tendsto.comp is_bounded_bilinear_map_smul_right.continuous_right.continuous_at _,
    exact tendsto_nhds_within_mono_left Ioo_subset_Ioi_self f_lim' },
  -- now we can apply `has_fderiv_at_boundary_of_differentiable`
  have : has_deriv_within_at f e (Icc a b) a,
  { rw [has_deriv_within_at_iff_has_fderiv_within_at, ← t_closure],
    exact has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff' },
  exact this.nhds_within (mem_nhds_within_Ici_iff_exists_Icc_subset.2 ⟨b, ab, subset.refl _⟩)
end

/-- If a function is differentiable on the left of a point `a : ℝ`, continuous at `a`, and
its derivative also converges at `a`, then `f` is differentiable on the left at `a`. -/
lemma has_deriv_at_interval_right_endpoint_of_tendsto_deriv {s : set ℝ} {e : E} {a : ℝ} {f : ℝ → E}
  (f_diff : differentiable_on ℝ f s) (f_lim : continuous_within_at f s a)
  (hs : s ∈ 𝓝[Iio a] a)
  (f_lim' : tendsto (λx, deriv f x) (𝓝[Iio a] a) (𝓝 e)) :
  has_deriv_within_at f e (Iic a) a :=
begin
  /- This is a specialization of `has_fderiv_at_boundary_of_differentiable`. To be in the setting of
  this theorem, we need to work on an open interval with closure contained in `s ∪ {a}`, that we
  call `t = (b, a)`. Then, we check all the assumptions of this theorem and we apply it. -/
  obtain ⟨b, ba, sab⟩ : ∃ b ∈ Iio a, Ico b a ⊆ s :=
    mem_nhds_within_Iio_iff_exists_Ico_subset.1 hs,
  let t := Ioo b a,
  have ts : t ⊆ s := subset.trans Ioo_subset_Ico_self sab,
  have t_diff : differentiable_on ℝ f t := f_diff.mono ts,
  have t_conv : convex t := convex_Ioo b a,
  have t_open : is_open t := is_open_Ioo,
  have t_closure : closure t = Icc b a := closure_Ioo ba,
  have t_cont : ∀y ∈ closure t, continuous_within_at f t y,
  { rw t_closure,
    assume y hy,
    by_cases h : y = a,
    { rw h, exact f_lim.mono ts },
    { have : y ∈ s := sab ⟨hy.1, lt_of_le_of_ne hy.2 h⟩,
      exact (f_diff.continuous_on y this).mono ts } },
  have t_diff' : tendsto (λx, fderiv ℝ f x) (𝓝[t] a) (𝓝 (smul_right 1 e)),
  { simp [deriv_fderiv.symm],
    refine tendsto.comp is_bounded_bilinear_map_smul_right.continuous_right.continuous_at _,
    exact tendsto_nhds_within_mono_left Ioo_subset_Iio_self f_lim' },
  -- now we can apply `has_fderiv_at_boundary_of_differentiable`
  have : has_deriv_within_at f e (Icc b a) a,
  { rw [has_deriv_within_at_iff_has_fderiv_within_at, ← t_closure],
    exact has_fderiv_at_boundary_of_tendsto_fderiv t_diff t_conv t_open t_cont t_diff' },
  exact this.nhds_within (mem_nhds_within_Iic_iff_exists_Icc_subset.2 ⟨b, ba, subset.refl _⟩)
end

/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is also the derivative of `f` at this point. -/
lemma has_deriv_at_of_has_deriv_at_of_ne {f g : ℝ → E} {x : ℝ}
  (f_diff : ∀ y ≠ x, has_deriv_at f (g y) y)
  (hf : continuous_at f x) (hg : continuous_at g x) :
  has_deriv_at f (g x) x :=
begin
  have A : has_deriv_within_at f (g x) (Ici x) x,
  { have diff : differentiable_on ℝ f (Ioi x) :=
      λy hy, (f_diff y (ne_of_gt hy)).differentiable_at.differentiable_within_at,
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply has_deriv_at_interval_left_endpoint_of_tendsto_deriv diff hf.continuous_within_at
      self_mem_nhds_within,
    have : tendsto g (𝓝[Ioi x] x) (𝓝 (g x)) := tendsto_inf_left hg,
    apply this.congr' _,
    apply mem_sets_of_superset self_mem_nhds_within (λy hy, _),
    exact (f_diff y (ne_of_gt hy)).deriv.symm },
  have B : has_deriv_within_at f (g x) (Iic x) x,
  { have diff : differentiable_on ℝ f (Iio x) :=
      λy hy, (f_diff y (ne_of_lt hy)).differentiable_at.differentiable_within_at,
    -- next line is the nontrivial bit of this proof, appealing to differentiability
    -- extension results.
    apply has_deriv_at_interval_right_endpoint_of_tendsto_deriv diff hf.continuous_within_at
      self_mem_nhds_within,
    have : tendsto g (𝓝[Iio x] x) (𝓝 (g x)) := tendsto_inf_left hg,
    apply this.congr' _,
    apply mem_sets_of_superset self_mem_nhds_within (λy hy, _),
    exact (f_diff y (ne_of_lt hy)).deriv.symm },
  simpa using B.union A
end

/-- If a real function `f` has a derivative `g` everywhere but at a point, and `f` and `g` are
continuous at this point, then `g` is the derivative of `f` everywhere. -/
lemma has_deriv_at_of_has_deriv_at_of_ne' {f g : ℝ → E} {x : ℝ}
  (f_diff : ∀ y ≠ x, has_deriv_at f (g y) y)
  (hf : continuous_at f x) (hg : continuous_at g x) (y : ℝ) :
  has_deriv_at f (g y) y :=
begin
  rcases em (y = x) with rfl|hne,
  { exact has_deriv_at_of_has_deriv_at_of_ne f_diff hf hg },
  { exact f_diff y hne }
end
