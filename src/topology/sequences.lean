/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot
-/
import topology.metric_space.basic

/-!
# Sequences in topological spaces

In this file we define sequences in topological spaces and show how they are related to
filters and the topology. In particular, we
* define the sequential closure of a set and prove that it's contained in the closure,
* define a type class "sequential_space" in which closure and sequential closure agree,
* define sequential continuity and show that it coincides with continuity in sequential spaces,
* provide an instance that shows that every first-countable (and in particular metric) space is
  a sequential space.
* define sequential compactness, prove that compactness implies sequential compactness in first
  countable spaces, and prove they are equivalent for uniform spaces having a countable uniformity
  basis (in particular metric spaces).
-/

open set filter
open_locale topological_space

variables {α : Type*} {β : Type*}

local notation f ` ⟶ ` limit := tendsto f at_top (𝓝 limit)

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/
section topological_space
variables [topological_space α] [topological_space β]

/-- A sequence converges in the sence of topological spaces iff the associated statement for filter
holds. -/
lemma topological_space.seq_tendsto_iff {x : ℕ → α} {limit : α} :
  tendsto x at_top (𝓝 limit) ↔
    ∀ U : set α, limit ∈ U → is_open U → ∃ N, ∀ n ≥ N, (x n) ∈ U :=
(at_top_basis.tendsto_iff (nhds_basis_opens limit)).trans $
  by simp only [and_imp, exists_prop, true_and, set.mem_Ici, ge_iff_le, id]

/-- The sequential closure of a subset M ⊆ α of a topological space α is
the set of all p ∈ α which arise as limit of sequences in M. -/
def sequential_closure (M : set α) : set α :=
{p | ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ M) ∧ (x ⟶ p)}

lemma subset_sequential_closure (M : set α) : M ⊆ sequential_closure M :=
assume p (_ : p ∈ M), show p ∈ sequential_closure M, from
  ⟨λ n, p, assume n, ‹p ∈ M›, tendsto_const_nhds⟩

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def is_seq_closed (s : set α) : Prop := s = sequential_closure s

/-- A convenience lemma for showing that a set is sequentially closed. -/
lemma is_seq_closed_of_def {A : set α}
  (h : ∀(x : ℕ → α) (p : α), (∀ n : ℕ, x n ∈ A) → (x ⟶ p) → p ∈ A) : is_seq_closed A :=
show A = sequential_closure A, from subset.antisymm
  (subset_sequential_closure A)
  (show ∀ p, p ∈ sequential_closure A → p ∈ A, from
    (assume p ⟨x, _, _⟩, show p ∈ A, from h x p ‹∀ n : ℕ, ((x n) ∈ A)› ‹(x ⟶ p)›))

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
lemma sequential_closure_subset_closure (M : set α) : sequential_closure M ⊆ closure M :=
assume p ⟨x, xM, xp⟩,
mem_closure_of_tendsto xp (univ_mem_sets' xM)

/-- A set is sequentially closed if it is closed. -/
lemma is_seq_closed_of_is_closed (M : set α) (_ : is_closed M) : is_seq_closed M :=
suffices sequential_closure M ⊆ M, from
  set.eq_of_subset_of_subset (subset_sequential_closure M) this,
calc sequential_closure M ⊆ closure M : sequential_closure_subset_closure M
  ... = M : is_closed.closure_eq ‹is_closed M›

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
lemma mem_of_is_seq_closed {A : set α} (_ : is_seq_closed A) {x : ℕ → α}
  (_ : ∀ n, x n ∈ A) {limit : α} (_ : (x ⟶ limit)) : limit ∈ A :=
have limit ∈ sequential_closure A, from
  show ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ A) ∧ (x ⟶ limit), from ⟨x, ‹∀ n, x n ∈ A›, ‹(x ⟶ limit)›⟩,
eq.subst (eq.symm ‹is_seq_closed A›) ‹limit ∈ sequential_closure A›

/-- The limit of a convergent sequence in a closed set is in that set.-/
lemma mem_of_is_closed_sequential {A : set α} (_ : is_closed A) {x : ℕ → α}
  (_ : ∀ n, x n ∈ A) {limit : α} (_ : x ⟶ limit) : limit ∈ A :=
mem_of_is_seq_closed (is_seq_closed_of_is_closed A ‹is_closed A›) ‹∀ n, x n ∈ A› ‹(x ⟶ limit)›

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class sequential_space (α : Type*) [topological_space α] : Prop :=
(sequential_closure_eq_closure : ∀ M : set α, sequential_closure M = closure M)

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
lemma is_seq_closed_iff_is_closed [sequential_space α] {M : set α} :
  is_seq_closed M ↔ is_closed M :=
iff.intro
  (assume _, closure_eq_iff_is_closed.mp (eq.symm
    (calc M = sequential_closure M : by assumption
        ... = closure M            : sequential_space.sequential_closure_eq_closure M)))
  (is_seq_closed_of_is_closed M)

/-- In a sequential space, a point belongs to the closure of a set iff it is a limit of a sequence
taking values in this set. -/
lemma mem_closure_iff_seq_limit [sequential_space α] {s : set α} {a : α} :
  a ∈ closure s ↔ ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ s) ∧ (x ⟶ a) :=
by { rw ← sequential_space.sequential_closure_eq_closure, exact iff.rfl }

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def sequentially_continuous (f : α → β) : Prop :=
∀ (x : ℕ → α), ∀ {limit : α}, (x ⟶ limit) → (f∘x ⟶ f limit)

/- A continuous function is sequentially continuous. -/
lemma continuous.to_sequentially_continuous {f : α → β} (_ : continuous f) :
  sequentially_continuous f :=
assume x limit (_ : x ⟶ limit),
have tendsto f (𝓝 limit) (𝓝 (f limit)), from continuous.tendsto ‹continuous f› limit,
show (f ∘ x) ⟶ (f limit), from tendsto.comp this ‹(x ⟶ limit)›

/-- In a sequential space, continuity and sequential continuity coincide. -/
lemma continuous_iff_sequentially_continuous {f : α → β} [sequential_space α] :
  continuous f ↔ sequentially_continuous f :=
iff.intro
  (assume _, ‹continuous f›.to_sequentially_continuous)
  (assume : sequentially_continuous f, show continuous f, from
    suffices h : ∀ {A : set β}, is_closed A → is_seq_closed (f ⁻¹' A), from
      continuous_iff_is_closed.mpr (assume A _, is_seq_closed_iff_is_closed.mp $ h ‹is_closed A›),
    assume A (_ : is_closed A),
      is_seq_closed_of_def $
        assume (x : ℕ → α) p (_ : ∀ n, f (x n) ∈ A) (_ : x ⟶ p),
        have (f ∘ x) ⟶ (f p), from ‹sequentially_continuous f› x ‹(x ⟶ p)›,
        show f p ∈ A, from
          mem_of_is_closed_sequential ‹is_closed A› ‹∀ n, f (x n) ∈ A› ‹(f∘x ⟶ f p)›)

end topological_space

namespace topological_space

namespace first_countable_topology

variables [topological_space α] [first_countable_topology α]

/-- Every first-countable space is sequential. -/
@[priority 100] -- see Note [lower instance priority]
instance : sequential_space α :=
⟨show ∀ M, sequential_closure M = closure M, from assume M,
  suffices closure M ⊆ sequential_closure M,
    from set.subset.antisymm (sequential_closure_subset_closure M) this,
  -- For every p ∈ closure M, we need to construct a sequence x in M that converges to p:
  assume (p : α) (hp : p ∈ closure M),
  -- Since we are in a first-countable space, the neighborhood filter around `p` has a decreasing
  -- basis `U` indexed by `ℕ`.
  let ⟨U, hU⟩ := (nhds_generated_countable p).exists_antimono_basis in
  -- Since `p ∈ closure M`, there is an element in each `M ∩ U i`
  have hp : ∀ (i : ℕ), ∃ (y : α), y ∈ M ∧ y ∈ U i,
    by simpa using (mem_closure_iff_nhds_basis hU.1).mp hp,
  begin
    -- The axiom of (countable) choice builds our sequence from the later fact
    choose u hu using hp,
    rw forall_and_distrib at hu,
    -- It clearly takes values in `M`
    use [u, hu.1],
    -- and converges to `p` because the basis is decreasing.
    apply hU.tendsto hu.2,
  end⟩


end first_countable_topology

end topological_space

section seq_compact
open topological_space topological_space.first_countable_topology
variables [topological_space α]

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def is_seq_compact (s : set α) :=
  ∀ ⦃u : ℕ → α⦄, (∀ n, u n ∈ s) →
    ∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x)

/-- A space `α` is sequentially compact if every sequence in `α` has a
converging subsequence. -/
class seq_compact_space (α : Type*) [topological_space α] : Prop :=
(seq_compact_univ : is_seq_compact (univ : set α))

lemma is_seq_compact.subseq_of_frequently_in {s : set α} (hs : is_seq_compact s) {u : ℕ → α}
  (hu : ∃ᶠ n in at_top, u n ∈ s) :
  ∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_at_top hu, ⟨x, x_in, φ, hφ, h⟩ := hs huψ in
⟨x, x_in, ψ ∘ φ, hψ.comp hφ, h⟩

lemma seq_compact_space.tendsto_subseq [seq_compact_space α] (u : ℕ → α) :
  ∃ x (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
let ⟨x, _, φ, mono, h⟩ := seq_compact_space.seq_compact_univ (by simp : ∀ n, u n ∈ univ) in
⟨x, φ, mono, h⟩

section first_countable_topology
variables [first_countable_topology α]
open topological_space.first_countable_topology

lemma is_compact.is_seq_compact {s : set α} (hs : is_compact s) : is_seq_compact s :=
λ u u_in,
let ⟨x, x_in, hx⟩ := @hs (map u at_top) _
  (le_principal_iff.mpr (univ_mem_sets' u_in : _)) in ⟨x, x_in, tendsto_subseq hx⟩

lemma is_compact.tendsto_subseq' {s : set α} {u : ℕ → α} (hs : is_compact s)
  (hu : ∃ᶠ n in at_top, u n ∈ s) :
∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
hs.is_seq_compact.subseq_of_frequently_in hu

lemma is_compact.tendsto_subseq {s : set α} {u : ℕ → α} (hs : is_compact s) (hu : ∀ n, u n ∈ s) :
∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
hs.is_seq_compact hu

@[priority 100] -- see Note [lower instance priority]
instance first_countable_topology.seq_compact_of_compact [compact_space α] : seq_compact_space α :=
⟨compact_univ.is_seq_compact⟩

lemma compact_space.tendsto_subseq [compact_space α] (u : ℕ → α) :
  ∃ x (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
seq_compact_space.tendsto_subseq u

end first_countable_topology
end seq_compact

section uniform_space_seq_compact

open_locale uniformity
open uniform_space prod

variables [uniform_space β] {s : set β}

lemma lebesgue_number_lemma_seq {ι : Type*} {c : ι → set β}
  (hs : is_seq_compact s) (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i)
  (hU : is_countably_generated (𝓤 β)) :
  ∃ V ∈ 𝓤 β, symmetric_rel V ∧ ∀ x ∈ s, ∃ i, ball x V ⊆ c i :=
begin
  classical,
  obtain ⟨V, hV, Vsymm⟩ :
    ∃ V : ℕ → set (β × β), (𝓤 β).has_antimono_basis (λ _, true) V ∧  ∀ n, swap ⁻¹' V n = V n,
      from uniform_space.has_seq_basis hU, clear hU,
  suffices : ∃ n, ∀ x ∈ s, ∃ i, ball x (V n) ⊆ c i,
  { cases this with n hn,
    exact ⟨V n, hV.to_has_basis.mem_of_mem trivial, Vsymm n, hn⟩ },
  by_contradiction H,
  obtain ⟨x, x_in, hx⟩ : ∃ x : ℕ → β, (∀ n, x n ∈ s) ∧ ∀ n i, ¬ ball (x n) (V n) ⊆ c i,
  { push_neg at H,
    choose x hx using H,
    exact ⟨x, forall_and_distrib.mp hx⟩ }, clear H,
  obtain ⟨x₀, x₀_in, φ, φ_mono, hlim⟩ : ∃ (x₀ ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ (x ∘ φ ⟶ x₀),
    from hs x_in, clear hs,
  obtain ⟨i₀, x₀_in⟩ : ∃ i₀, x₀ ∈ c i₀,
  { rcases hc₂ x₀_in with ⟨_, ⟨i₀, rfl⟩, x₀_in_c⟩,
    exact ⟨i₀, x₀_in_c⟩ }, clear hc₂,
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ball x₀ (V n₀) ⊆ c i₀,
  { rcases (nhds_basis_uniformity hV.to_has_basis).mem_iff.mp
      (is_open_iff_mem_nhds.mp (hc₁ i₀) _ x₀_in) with ⟨n₀, _, h⟩,
    use n₀,
    rwa ← ball_eq_of_symmetry (Vsymm n₀) at h }, clear hc₁,
  obtain ⟨W, W_in, hWW⟩ : ∃ W ∈ 𝓤 β, W ○ W ⊆ V n₀,
    from comp_mem_uniformity_sets (hV.to_has_basis.mem_of_mem trivial),
  obtain ⟨N, x_φ_N_in, hVNW⟩ : ∃ N, x (φ N) ∈ ball x₀ W ∧ V (φ N) ⊆ W,
  { obtain ⟨N₁, h₁⟩ : ∃ N₁, ∀ n ≥ N₁, x (φ n) ∈ ball x₀ W,
      from tendsto_at_top'.mp hlim _ (mem_nhds_left x₀ W_in),
    obtain ⟨N₂, h₂⟩ : ∃ N₂, V (φ N₂) ⊆ W,
    { rcases hV.to_has_basis.mem_iff.mp W_in with ⟨N, _, hN⟩,
      use N,
      exact subset.trans (hV.decreasing trivial trivial $  φ_mono.id_le _) hN },
    have : φ N₂ ≤ φ (max N₁ N₂),
      from φ_mono.le_iff_le.mpr (le_max_right _ _),
    exact ⟨max N₁ N₂, h₁ _ (le_max_left _ _), trans (hV.decreasing trivial trivial this) h₂⟩ },
  suffices : ball (x (φ N)) (V (φ N)) ⊆ c i₀,
    from hx (φ N) i₀ this,
  calc
    ball (x $ φ N) (V $ φ N) ⊆ ball (x $ φ N) W : preimage_mono hVNW
                         ... ⊆ ball x₀ (V n₀)   : ball_subset_of_comp_subset x_φ_N_in hWW
                         ... ⊆ c i₀             : hn₀,
end

lemma is_seq_compact.totally_bounded (h : is_seq_compact s) : totally_bounded s :=
begin
  classical,
  apply totally_bounded_of_forall_symm,
  unfold is_seq_compact at h,
  contrapose! h,
  rcases h with ⟨V, V_in, V_symm, h⟩,
  simp_rw [not_subset] at h,
  have : ∀ (t : set β), finite t → ∃ a, a ∈ s ∧ a ∉ ⋃ y ∈ t, ball y V,
  { intros t ht,
    obtain ⟨a, a_in, H⟩ : ∃ a ∈ s, ∀ (x : β), x ∈ t → (x, a) ∉ V,
      by simpa [ht] using h t,
    use [a, a_in],
    intro H',
    obtain ⟨x, x_in, hx⟩ := mem_bUnion_iff.mp H',
    exact H x x_in hx },
  cases seq_of_forall_finite_exists this with u hu, clear h this,
  simp [forall_and_distrib] at hu,
  cases hu with u_in hu,
  use [u, u_in], clear u_in,
  intros x x_in φ,
  intros hφ huφ,
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V,
    from huφ.cauchy_seq.mem_entourage V_in,
  specialize hN N (N+1) (le_refl N) (nat.le_succ N),
  specialize hu (φ $ N+1) (φ N) (hφ $ lt_add_one N),
  exact hu hN,
end

protected lemma is_seq_compact.is_compact (h : is_countably_generated $ 𝓤 β)
  (hs : is_seq_compact s) :
  is_compact s :=
begin
  classical,
  rw compact_iff_finite_subcover,
  intros ι U Uop s_sub,
  rcases lebesgue_number_lemma_seq hs Uop s_sub h with ⟨V, V_in, Vsymm, H⟩,
  rcases totally_bounded_iff_subset.mp hs.totally_bounded V V_in with ⟨t,t_sub, tfin,  ht⟩,
  have : ∀ x : t, ∃ (i : ι), ball x.val V ⊆ U i,
  { rintros ⟨x, x_in⟩,
    exact H x (t_sub x_in) },
  choose i hi using this,
  haveI : fintype t := tfin.fintype,
  use finset.image i finset.univ,
  transitivity ⋃ y ∈ t, ball y V,
  { intros x x_in,
    specialize ht x_in,
    rw mem_bUnion_iff at *,
    simp_rw ball_eq_of_symmetry Vsymm,
    exact ht },
  { apply bUnion_subset_bUnion,
    intros x x_in,
    exact ⟨i ⟨x, x_in⟩, finset.mem_image_of_mem _ (finset.mem_univ _), hi ⟨x, x_in⟩⟩ },
end

protected lemma uniform_space.compact_iff_seq_compact (h : is_countably_generated $ 𝓤 β) :
 is_compact s ↔ is_seq_compact s :=
begin
  haveI := uniform_space.first_countable_topology h,
  exact ⟨λ H, H.is_seq_compact, λ H, H.is_compact h⟩
end

lemma uniform_space.compact_space_iff_seq_compact_space (H : is_countably_generated $ 𝓤 β) :
  compact_space β ↔ seq_compact_space β :=
have key : is_compact univ ↔ is_seq_compact univ := uniform_space.compact_iff_seq_compact H,
⟨λ ⟨h⟩, ⟨key.mp h⟩, λ ⟨h⟩, ⟨key.mpr h⟩⟩

end uniform_space_seq_compact

section metric_seq_compact

variables [metric_space β] {s : set β}
open metric

/-- A version of Bolzano-Weistrass: in a metric space, is_compact s ↔ is_seq_compact s -/
lemma metric.compact_iff_seq_compact : is_compact s ↔ is_seq_compact s :=
uniform_space.compact_iff_seq_compact emetric.uniformity_has_countable_basis

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
lemma tendsto_subseq_of_frequently_bounded [proper_space β] (hs : bounded s)
  {u : ℕ → β} (hu : ∃ᶠ n in at_top, u n ∈ s) :
∃ b ∈ closure s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 b) :=
begin
  have hcs : is_compact (closure s) :=
    compact_iff_closed_bounded.mpr ⟨is_closed_closure, bounded_closure_of_bounded hs⟩,
  replace hcs : is_seq_compact (closure s),
    by rwa metric.compact_iff_seq_compact at hcs,
  have hu' : ∃ᶠ n in at_top, u n ∈ closure s,
  { apply frequently.mono hu,
    intro n,
    apply subset_closure },
  exact hcs.subseq_of_frequently_in hu',
end

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
lemma tendsto_subseq_of_bounded [proper_space β] (hs : bounded s)
  {u : ℕ → β} (hu : ∀ n, u n ∈ s) :
∃ b ∈ closure s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 b) :=
tendsto_subseq_of_frequently_bounded hs $ frequently_of_forall hu

lemma metric.compact_space_iff_seq_compact_space : compact_space β ↔ seq_compact_space β :=
uniform_space.compact_space_iff_seq_compact_space emetric.uniformity_has_countable_basis

lemma seq_compact.lebesgue_number_lemma_of_metric
  {ι : Type*} {c : ι → set β} (hs : is_seq_compact s)
  (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
  ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i :=
begin
  rcases lebesgue_number_lemma_seq hs hc₁ hc₂ emetric.uniformity_has_countable_basis
    with ⟨V, V_in, _, hV⟩,
  rcases uniformity_basis_dist.mem_iff.mp V_in with ⟨δ, δ_pos, h⟩,
  use [δ, δ_pos],
  intros x x_in,
  rcases hV x x_in with ⟨i, hi⟩,
  use i,
  have := ball_mono h x,
  rw ball_eq_ball' at this,
  exact subset.trans this hi,
end

end metric_seq_compact
