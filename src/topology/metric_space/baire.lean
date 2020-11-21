/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.specific_limits
import order.filter.countable_Inter
import topology.G_delta

/-!
# Baire theorem

In a complete metric space, a countable intersection of dense open subsets is dense.

The good concept underlying the theorem is that of a Gδ set, i.e., a countable intersection
of open sets. Then Baire theorem can also be formulated as the fact that a countable
intersection of dense Gδ sets is a dense Gδ set. We prove Baire theorem, giving several different
formulations that can be handy. We also prove the important consequence that, if the space is
covered by a countable union of closed sets, then the union of their interiors is dense.

The names of the theorems do not contain the string "Baire", but are instead built from the form of
the statement. "Baire" is however in the docstring of all the theorems, to facilitate grep searches.

We also define the filter `residual α` generated by dense `Gδ` sets and prove that this filter
has the countable intersection property.
-/

noncomputable theory
open_locale classical topological_space filter

open filter encodable set

variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

section Baire_theorem
open emetric ennreal
variables [emetric_space α] [complete_space α]

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here when
the source space is ℕ (and subsumed below by `dense_Inter_of_open` working with any
encodable source space). -/
theorem dense_Inter_of_open_nat {f : ℕ → set α} (ho : ∀n, is_open (f n))
  (hd : ∀n, dense (f n)) : dense (⋂n, f n) :=
begin
  let B : ℕ → ennreal := λn, 1/2^n,
  have Bpos : ∀n, 0 < B n,
  { intro n,
    simp only [B, div_def, one_mul, ennreal.inv_pos],
    exact pow_ne_top two_ne_top },
  /- Translate the density assumption into two functions `center` and `radius` associating
  to any n, x, δ, δpos a center and a positive radius such that
  `closed_ball center radius` is included both in `f n` and in `closed_ball x δ`.
  We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have : ∀n x δ, δ > 0 → ∃y r, r > 0 ∧ r ≤ B (n+1) ∧ closed_ball y r ⊆ (closed_ball x δ) ∩ f n,
  { assume n x δ δpos,
    have : x ∈ closure (f n) := hd n x,
    rcases emetric.mem_closure_iff.1 this (δ/2) (ennreal.half_pos δpos) with ⟨y, ys, xy⟩,
    rw edist_comm at xy,
    obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closed_ball y r ⊆ f n :=
      nhds_basis_closed_eball.mem_iff.1 (is_open_iff_mem_nhds.1 (ho n) y ys),
    refine ⟨y, min (min (δ/2) r) (B (n+1)), _, _, λz hz, ⟨_, _⟩⟩,
    show 0 < min (min (δ / 2) r) (B (n+1)),
      from lt_min (lt_min (ennreal.half_pos δpos) rpos) (Bpos (n+1)),
    show min (min (δ / 2) r) (B (n+1)) ≤ B (n+1), from min_le_right _ _,
    show z ∈ closed_ball x δ, from calc
      edist z x ≤ edist z y + edist y x : edist_triangle _ _ _
      ... ≤ (min (min (δ / 2) r) (B (n+1))) + (δ/2) : add_le_add hz (le_of_lt xy)
      ... ≤ δ/2 + δ/2 : add_le_add (le_trans (min_le_left _ _) (min_le_left _ _)) (le_refl _)
      ... = δ : ennreal.add_halves δ,
    show z ∈ f n, from hr (calc
      edist z y ≤ min (min (δ / 2) r) (B (n+1)) : hz
      ... ≤ r : le_trans (min_le_left _ _) (min_le_right _ _)) },
  choose! center radius H using this,
  refine λ x, (mem_closure_iff_nhds_basis nhds_basis_closed_eball).2 (λ ε εpos, _),
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x` belonging to all
  `f n`. For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed ball
  `closed_ball (c n) (r n)` is included in the previous ball and in `f n`, and such that
  `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
  limit which belongs to all the `f n`. -/
  let F : ℕ → (α × ennreal) := λn, nat.rec_on n (prod.mk x (min ε (B 0)))
                              (λn p, prod.mk (center n p.1 p.2) (radius n p.1 p.2)),
  let c : ℕ → α := λn, (F n).1,
  let r : ℕ → ennreal := λn, (F n).2,
  have rpos : ∀n, r n > 0,
  { assume n,
    induction n with n hn,
    exact lt_min εpos (Bpos 0),
    exact (H n (c n) (r n) hn).1 },
  have rB : ∀n, r n ≤ B n,
  { assume n,
    induction n with n hn,
    exact min_le_right _ _,
    exact (H n (c n) (r n) (rpos n)).2.1 },
  have incl : ∀n, closed_ball (c (n+1)) (r (n+1)) ⊆ (closed_ball (c n) (r n)) ∩ (f n) :=
    λn, (H n (c n) (r n) (rpos n)).2.2,
  have cdist : ∀n, edist (c n) (c (n+1)) ≤ B n,
  { assume n,
    rw edist_comm,
    have A : c (n+1) ∈ closed_ball (c (n+1)) (r (n+1)) := mem_closed_ball_self,
    have I := calc
      closed_ball (c (n+1)) (r (n+1)) ⊆ closed_ball (c n) (r n) :
        subset.trans (incl n) (inter_subset_left _ _)
      ... ⊆ closed_ball (c n) (B n) : closed_ball_subset_closed_ball (rB n),
    exact I A },
  have : cauchy_seq c :=
    cauchy_seq_of_edist_le_geometric_two _ one_ne_top cdist,
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchy_seq_tendsto_of_complete this with ⟨y, ylim⟩,
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y,
  simp only [exists_prop, set.mem_Inter],
  have I : ∀n, ∀m ≥ n, closed_ball (c m) (r m) ⊆ closed_ball (c n) (r n),
  { assume n,
    refine nat.le_induction _ (λm hnm h, _),
    { exact subset.refl _ },
    { exact subset.trans (incl m) (subset.trans (inter_subset_left _ _) h) }},
  have yball : ∀n, y ∈ closed_ball (c n) (r n),
  { assume n,
    refine is_closed_ball.mem_of_tendsto ylim _,
    refine (filter.eventually_ge_at_top n).mono (λ m hm, _),
    exact I n m hm mem_closed_ball_self },
  split,
  show ∀n, y ∈ f n,
  { assume n,
    have : closed_ball (c (n+1)) (r (n+1)) ⊆ f n := subset.trans (incl n) (inter_subset_right _ _),
    exact this (yball (n+1)) },
  show edist y x ≤ ε, from le_trans (yball 0) (min_le_left _ _),
end

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_open {S : set (set α)} (ho : ∀s∈S, is_open s) (hS : countable S)
  (hd : ∀s∈S, dense s) : dense (⋂₀S) :=
begin
  cases S.eq_empty_or_nonempty with h h,
  { simp [h] },
  { rcases hS.exists_surjective h with ⟨f, hf⟩,
    have F : ∀n, f n ∈ S := λn, by rw hf; exact mem_range_self _,
    rw [hf, sInter_range],
    exact dense_Inter_of_open_nat (λn, ho _ (F n)) (λn, hd _ (F n)) }
end

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_bInter_of_open {S : set β} {f : β → set α} (ho : ∀s∈S, is_open (f s))
  (hS : countable S) (hd : ∀s∈S, dense (f s)) : dense (⋂s∈S, f s) :=
begin
  rw ← sInter_image,
  apply dense_sInter_of_open,
  { rwa ball_image_iff },
  { exact hS.image _ },
  { rwa ball_image_iff }
end

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is an encodable type. -/
theorem dense_Inter_of_open [encodable β] {f : β → set α} (ho : ∀s, is_open (f s))
  (hd : ∀s, dense (f s)) : dense (⋂s, f s) :=
begin
  rw ← sInter_range,
  apply dense_sInter_of_open,
  { rwa forall_range_iff },
  { exact countable_range _ },
  { rwa forall_range_iff }
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_Gδ {S : set (set α)} (ho : ∀s∈S, is_Gδ s) (hS : countable S)
  (hd : ∀s∈S, dense s) : dense (⋂₀S) :=
begin
  -- the result follows from the result for a countable intersection of dense open sets,
  -- by rewriting each set as a countable intersection of open sets, which are of course dense.
  choose T hT using ho,
  have : ⋂₀ S = ⋂₀ (⋃s∈S, T s ‹_›) := (sInter_bUnion (λs hs, (hT s hs).2.2)).symm,
  rw this,
  refine dense_sInter_of_open _ (hS.bUnion (λs hs, (hT s hs).2.1)) _;
    simp only [set.mem_Union, exists_prop]; rintro t ⟨s, hs, tTs⟩,
  show is_open t,
  { exact (hT s hs).1 t tTs },
  show dense t,
  { intro x,
    have := hd s hs x,
    rw (hT s hs).2.2 at this,
    exact closure_mono (sInter_subset_of_mem tTs) this }
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is an encodable type. -/
theorem dense_Inter_of_Gδ [encodable β] {f : β → set α} (ho : ∀s, is_Gδ (f s))
  (hd : ∀s, dense (f s)) : dense (⋂s, f s) :=
begin
  rw ← sInter_range,
  exact dense_sInter_of_Gδ (forall_range_iff.2 ‹_›) (countable_range _) (forall_range_iff.2 ‹_›)
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_bInter_of_Gδ {S : set β} {f : Π x ∈ S, set α} (ho : ∀s∈S, is_Gδ (f s ‹_›))
  (hS : countable S) (hd : ∀s∈S, dense (f s ‹_›)) : dense (⋂s∈S, f s ‹_›) :=
begin
  rw bInter_eq_Inter,
  haveI := hS.to_encodable,
  exact dense_Inter_of_Gδ (λ s, ho s s.2) (λ s, hd s s.2)
end

/-- Baire theorem: the intersection of two dense Gδ sets is dense. -/
theorem dense.inter_of_Gδ {s t : set α} (hs : is_Gδ s) (ht : is_Gδ t) (hsc : dense s)
  (htc : dense t) :
  dense (s ∩ t) :=
begin
  rw [inter_eq_Inter],
  apply dense_Inter_of_Gδ; simp [bool.forall_bool, *]
end

/-- A property holds on a residual (comeagre) set if and only if it holds on some dense `Gδ` set. -/
lemma eventually_residual {p : α → Prop} :
  (∀ᶠ x in residual α, p x) ↔ ∃ (t : set α), is_Gδ t ∧ dense t ∧ ∀ x ∈ t, p x :=
calc (∀ᶠ x in residual α, p x) ↔
  ∀ᶠ x in ⨅ (t : set α) (ht : is_Gδ t ∧ dense t), 𝓟 t, p x :
    by simp only [residual, infi_and]
... ↔ ∃ (t : set α) (ht : is_Gδ t ∧ dense t), ∀ᶠ x in 𝓟 t, p x :
  mem_binfi (λ t₁ h₁ t₂ h₂, ⟨t₁ ∩ t₂, ⟨h₁.1.inter h₂.1, dense.inter_of_Gδ h₁.1 h₂.1 h₁.2 h₂.2⟩,
    by simp⟩) ⟨univ, is_Gδ_univ, dense_univ⟩
... ↔ _ : by simp [and_assoc]

/-- A set is residual (comeagre) if and only if it includes a dense `Gδ` set. -/
lemma mem_residual {s : set α} : s ∈ residual α ↔ ∃ t ⊆ s, is_Gδ t ∧ dense t :=
(@eventually_residual α _ _ (λ x, x ∈ s)).trans $ exists_congr $
λ t, by rw [exists_prop, and_comm (t ⊆ s), subset_def, and_assoc]

instance : countable_Inter_filter (residual α) :=
⟨begin
  intros S hSc hS,
  simp only [mem_residual] at *,
  choose T hTs hT using hS,
  refine ⟨⋂ s ∈ S, T s ‹_›, _, _, _⟩,
  { rw [sInter_eq_bInter],
    exact Inter_subset_Inter (λ s, Inter_subset_Inter $ hTs s) },
  { exact is_Gδ_bInter hSc (λ s hs, (hT s hs).1) },
  { exact dense_bInter_of_Gδ (λ s hs, (hT s hs).1) hSc (λ s hs, (hT s hs).2) }
end⟩

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable set in any type. -/
theorem dense_bUnion_interior_of_closed {S : set β} {f : β → set α} (hc : ∀s∈S, is_closed (f s))
  (hS : countable S) (hU : (⋃s∈S, f s) = univ) : dense (⋃s∈S, interior (f s)) :=
begin
  let g := λs, (frontier (f s))ᶜ,
  have : dense (⋂s∈S, g s),
  { refine dense_bInter_of_open (λs hs, _) hS (λs hs, _),
    show is_open (g s), from is_open_compl_iff.2 is_closed_frontier,
    show dense (g s),
    { intro x,
      simp [interior_frontier (hc s hs)] }},
  refine this.mono _,
  show (⋂s∈S, g s) ⊆ (⋃s∈S, interior (f s)),
  assume x hx,
  have : x ∈ ⋃s∈S, f s, { have := mem_univ x, rwa ← hU at this },
  rcases mem_bUnion_iff.1 this with ⟨s, hs, xs⟩,
  have : x ∈ g s := mem_bInter_iff.1 hx s hs,
  have : x ∈ interior (f s),
  { have : x ∈ f s \ (frontier (f s)) := mem_inter xs this,
    simpa [frontier, xs, (hc s hs).closure_eq] using this },
  exact mem_bUnion_iff.2 ⟨s, ⟨hs, this⟩⟩
end

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with `⋃₀`. -/
theorem dense_sUnion_interior_of_closed {S : set (set α)} (hc : ∀s∈S, is_closed s)
  (hS : countable S) (hU : (⋃₀ S) = univ) : dense (⋃s∈S, interior s) :=
by rw sUnion_eq_bUnion at hU; exact dense_bUnion_interior_of_closed hc hS hU

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is an encodable type. -/
theorem dense_Union_interior_of_closed [encodable β] {f : β → set α} (hc : ∀s, is_closed (f s))
  (hU : (⋃s, f s) = univ) : dense (⋃s, interior (f s)) :=
begin
  rw ← bUnion_univ,
  apply dense_bUnion_interior_of_closed,
  { simp [hc] },
  { apply countable_encodable },
  { rwa ← bUnion_univ at hU }
end

/-- One of the most useful consequences of Baire theorem: if a countable union of closed sets
covers the space, then one of the sets has nonempty interior. -/
theorem nonempty_interior_of_Union_of_closed [nonempty α] [encodable β] {f : β → set α}
  (hc : ∀s, is_closed (f s)) (hU : (⋃s, f s) = univ) :
  ∃s, (interior $ f s).nonempty :=
begin
  by_contradiction h,
  simp only [not_exists, not_nonempty_iff_eq_empty] at h,
  have := calc ∅ = closure (⋃s, interior (f s)) : by simp [h]
             ... = univ : (dense_Union_interior_of_closed hc hU).closure_eq,
  exact univ_nonempty.ne_empty this.symm
end

end Baire_theorem
