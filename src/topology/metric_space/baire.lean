/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.specific_limits
import order.filter.countable_Inter

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

section is_Gδ
variable [topological_space α]

/-- A Gδ set is a countable intersection of open sets. -/
def is_Gδ (s : set α) : Prop :=
  ∃T : set (set α), (∀t ∈ T, is_open t) ∧ countable T ∧ s = (⋂₀ T)

/-- An open set is a Gδ set. -/
lemma is_open.is_Gδ {s : set α} (h : is_open s) : is_Gδ s :=
⟨{s}, by simp [h], countable_singleton _, (set.sInter_singleton _).symm⟩

lemma is_Gδ_univ : is_Gδ (univ : set α) := is_open_univ.is_Gδ

lemma is_Gδ_bInter_of_open {I : set ι} (hI : countable I) {f : ι → set α}
  (hf : ∀i ∈ I, is_open (f i)) : is_Gδ (⋂i∈I, f i) :=
⟨f '' I, by rwa ball_image_iff, hI.image _, by rw sInter_image⟩

lemma is_Gδ_Inter_of_open [encodable ι] {f : ι → set α}
  (hf : ∀i, is_open (f i)) : is_Gδ (⋂i, f i) :=
⟨range f, by rwa forall_range_iff, countable_range _, by rw sInter_range⟩

/-- A countable intersection of Gδ sets is a Gδ set. -/
lemma is_Gδ_sInter {S : set (set α)} (h : ∀s∈S, is_Gδ s) (hS : countable S) : is_Gδ (⋂₀ S) :=
begin
  choose T hT using h,
  refine ⟨_, _, _, (sInter_bUnion (λ s hs, (hT s hs).2.2)).symm⟩,
  { simp only [mem_Union],
    rintros t ⟨s, hs, tTs⟩,
    exact (hT s hs).1 t tTs },
  { exact hS.bUnion (λs hs, (hT s hs).2.1) },
end

lemma is_Gδ_Inter [encodable ι]  {s : ι → set α} (hs : ∀ i, is_Gδ (s i)) : is_Gδ (⋂ i, s i) :=
is_Gδ_sInter (forall_range_iff.2 hs) $ countable_range s

lemma is_Gδ_bInter {s : set ι} (hs : countable s) {t : Π i ∈ s, set α} (ht : ∀ i ∈ s, is_Gδ (t i ‹_›)) :
  is_Gδ (⋂ i ∈ s, t i ‹_›) :=
begin
  rw [bInter_eq_Inter],
  haveI := hs.to_encodable,
  exact is_Gδ_Inter (λ x, ht x x.2)
end

lemma is_Gδ.inter {s t : set α} (hs : is_Gδ s) (ht : is_Gδ t) : is_Gδ (s ∩ t) :=
by { rw inter_eq_Inter, exact is_Gδ_Inter (bool.forall_bool.2 ⟨ht, hs⟩) }

/-- The union of two Gδ sets is a Gδ set. -/
lemma is_Gδ.union {s t : set α} (hs : is_Gδ s) (ht : is_Gδ t) : is_Gδ (s ∪ t) :=
begin
  rcases hs with ⟨S, Sopen, Scount, rfl⟩,
  rcases ht with ⟨T, Topen, Tcount, rfl⟩,
  rw [sInter_union_sInter],
  apply is_Gδ_bInter_of_open (countable_prod Scount Tcount),
  rintros ⟨a, b⟩ hab,
  exact is_open_union (Sopen a hab.1) (Topen b hab.2)
end

end is_Gδ

/-- A set `s` is called *residual* if it includes a dense `Gδ` set. If `α` is a Baire space
(e.g., a complete metric space), then residual sets form a filter, see `mem_residual`.

 For technical reasons we define the filter `residual` in any topological space
 but in a non-Baire space it is not useful because it may contain some non-residual
 sets. -/
def residual (α : Type*) [topological_space α] : filter α :=
⨅ t (ht : is_Gδ t) (ht' : closure t = univ), 𝓟 t

section Baire_theorem
open emetric ennreal
variables [emetric_space α] [complete_space α]

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here when
the source space is ℕ (and subsumed below by `dense_Inter_of_open` working with any
encodable source space). -/
theorem dense_Inter_of_open_nat {f : ℕ → set α} (ho : ∀n, is_open (f n))
  (hd : ∀n, closure (f n) = univ) : closure (⋂n, f n) = univ :=
begin
  let B : ℕ → ennreal := λn, 1/2^n,
  have Bpos : ∀n, 0 < B n,
  { intro n,
    simp only [B, div_def, one_mul, ennreal.inv_pos],
    exact pow_ne_top two_ne_top },
  /- Translate the density assumption into two functions `center` and `radius` associating
  to any n, x, δ, δpos a center and a positive radius such that
  `closed_ball center radius` is included both in `f n` and in `closed_ball x δ`.
  We can also require `radius ≤ (1/2)^(n+1), to ensure we get a Cauchy sequence later. -/
  have : ∀n x δ, ∃y r, δ > 0 → (r > 0 ∧ r ≤ B (n+1) ∧ closed_ball y r ⊆ (closed_ball x δ) ∩ f n),
  { assume n x δ,
    by_cases δpos : δ > 0,
    { have : x ∈ closure (f n) := by simpa only [(hd n).symm] using mem_univ x,
      rcases emetric.mem_closure_iff.1 this (δ/2) (ennreal.half_pos δpos) with ⟨y, ys, xy⟩,
      rw edist_comm at xy,
      obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closed_ball y r ⊆ f n :=
        nhds_basis_closed_eball.mem_iff.1 (is_open_iff_mem_nhds.1 (ho n) y ys),
      refine ⟨y, min (min (δ/2) r) (B (n+1)), λ_, ⟨_, _, λz hz, ⟨_, _⟩⟩⟩,
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
    { use [x, 0] }},
  choose center radius H using this,

  refine subset.antisymm (subset_univ _) (λx hx, _),
  refine (mem_closure_iff_nhds_basis nhds_basis_closed_eball).2 (λ ε εpos, _),
  /- ε is positive. We have to find a point in the ball of radius ε around x belonging to all `f n`.
  For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed ball
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
    refine mem_of_closed_of_tendsto (by simp) ylim is_closed_ball _,
    simp only [filter.mem_at_top_sets, nonempty_of_inhabited, set.mem_preimage],
    exact ⟨n, λm hm, I n m hm mem_closed_ball_self⟩ },
  split,
  show ∀n, y ∈ f n,
  { assume n,
    have : closed_ball (c (n+1)) (r (n+1)) ⊆ f n := subset.trans (incl n) (inter_subset_right _ _),
    exact this (yball (n+1)) },
  show edist y x ≤ ε, from le_trans (yball 0) (min_le_left _ _),
end

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_open {S : set (set α)} (ho : ∀s∈S, is_open s) (hS : countable S)
  (hd : ∀s∈S, closure s = univ) : closure (⋂₀S) = univ :=
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
  (hS : countable S) (hd : ∀s∈S, closure (f s) = univ) : closure (⋂s∈S, f s) = univ :=
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
  (hd : ∀s, closure (f s) = univ) : closure (⋂s, f s) = univ :=
begin
  rw ← sInter_range,
  apply dense_sInter_of_open,
  { rwa forall_range_iff },
  { exact countable_range _ },
  { rwa forall_range_iff }
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_Gδ {S : set (set α)} (ho : ∀s∈S, is_Gδ s) (hS : countable S)
  (hd : ∀s∈S, closure s = univ) : closure (⋂₀S) = univ :=
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
  show closure t = univ,
  { apply eq_univ_of_univ_subset,
    rw [← hd s hs, (hT s hs).2.2],
    exact closure_mono (sInter_subset_of_mem tTs) }
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is an encodable type. -/
theorem dense_Inter_of_Gδ [encodable β] {f : β → set α} (ho : ∀s, is_Gδ (f s))
  (hd : ∀s, closure (f s) = univ) : closure (⋂s, f s) = univ :=
begin
  rw ← sInter_range,
  exact dense_sInter_of_Gδ (forall_range_iff.2 ‹_›) (countable_range _) (forall_range_iff.2 ‹_›)
end

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_bInter_of_Gδ {S : set β} {f : Π x ∈ S, set α} (ho : ∀s∈S, is_Gδ (f s ‹_›))
  (hS : countable S) (hd : ∀s∈S, closure (f s ‹_›) = univ) : closure (⋂s∈S, f s ‹_›) = univ :=
begin
  rw bInter_eq_Inter,
  haveI := hS.to_encodable,
  exact dense_Inter_of_Gδ (λ s, ho s s.2) (λ s, hd s s.2)
end

/-- Baire theorem: the intersection of two dense Gδ sets is dense. -/
theorem dense_inter_of_Gδ {s t : set α} (hs : is_Gδ s) (ht : is_Gδ t) (hsc : closure s = univ)
  (htc : closure t = univ) :
  closure (s ∩ t) = univ :=
begin
  rw [inter_eq_Inter],
  apply dense_Inter_of_Gδ; simp [bool.forall_bool, *]
end

/-- A property holds on a residual (comeagre) set if and only if it holds on some dense `Gδ` set. -/
lemma eventually_residual {p : α → Prop} :
  (∀ᶠ x in residual α, p x) ↔ ∃ (t : set α), is_Gδ t ∧ closure t = univ ∧ ∀ x ∈ t, p x :=
calc (∀ᶠ x in residual α, p x) ↔
  ∀ᶠ x in ⨅ (t : set α) (ht : is_Gδ t ∧ closure t = univ), 𝓟 t, p x :
    by simp only [residual, infi_and]
... ↔ ∃ (t : set α) (ht : is_Gδ t ∧ closure t = univ), ∀ᶠ x in 𝓟 t, p x :
  mem_binfi (λ t₁ h₁ t₂ h₂, ⟨t₁ ∩ t₂, ⟨h₁.1.inter h₂.1, dense_inter_of_Gδ h₁.1 h₂.1 h₁.2 h₂.2⟩,
    by simp⟩) ⟨univ, is_Gδ_univ, closure_univ⟩
... ↔ _ : by simp [and_assoc]

/-- A set is residual (comeagre) if and only if it includes a dense `Gδ` set. -/
lemma mem_residual {s : set α} :
  s ∈ residual α ↔ ∃ t ⊆ s, is_Gδ t ∧ closure t = univ :=
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
  (hS : countable S) (hU : (⋃s∈S, f s) = univ) : closure (⋃s∈S, interior (f s)) = univ :=
begin
  let g := λs, ∁ (frontier (f s)),
  have clos_g : closure (⋂s∈S, g s) = univ,
  { refine dense_bInter_of_open (λs hs, _) hS (λs hs, _),
    show is_open (g s), from is_open_compl_iff.2 is_closed_frontier,
    show closure (g s) = univ,
    { apply subset.antisymm (subset_univ _),
      simp [interior_frontier (hc s hs)] }},
  have : (⋂s∈S, g s) ⊆ (⋃s∈S, interior (f s)),
  { assume x hx,
    have : x ∈ ⋃s∈S, f s, { have := mem_univ x, rwa ← hU at this },
    rcases mem_bUnion_iff.1 this with ⟨s, hs, xs⟩,
    have : x ∈ g s := mem_bInter_iff.1 hx s hs,
    have : x ∈ interior (f s),
    { have : x ∈ f s \ (frontier (f s)) := mem_inter xs this,
      simpa [frontier, xs, closure_eq_of_is_closed (hc s hs)] using this },
    exact mem_bUnion_iff.2 ⟨s, ⟨hs, this⟩⟩ },
  have := closure_mono this,
  rw clos_g at this,
  exact subset.antisymm (subset_univ _) this
end

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with ⋃₀. -/
theorem dense_sUnion_interior_of_closed {S : set (set α)} (hc : ∀s∈S, is_closed s)
  (hS : countable S) (hU : (⋃₀ S) = univ) : closure (⋃s∈S, interior s) = univ :=
by rw sUnion_eq_bUnion at hU; exact dense_bUnion_interior_of_closed hc hS hU

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is an encodable type. -/
theorem dense_Union_interior_of_closed [encodable β] {f : β → set α} (hc : ∀s, is_closed (f s))
  (hU : (⋃s, f s) = univ) : closure (⋃s, interior (f s)) = univ :=
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
             ... = univ : dense_Union_interior_of_closed hc hU,
  exact univ_nonempty.ne_empty this.symm
end

end Baire_theorem
