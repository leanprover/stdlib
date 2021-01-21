/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.continuous_on

/-!
# Theory of topological monoids

In this file we define mixin classes `has_continuous_mul` and `has_continuous_add`. While in many
applications the underlying type is a monoid (multiplicative or additive), we do not require this in
the definitions.
-/

open classical set filter topological_space
open_locale classical topological_space big_operators

variables {α β M N : Type*}

/-- Basic hypothesis to talk about a topological additive monoid or a topological additive
semigroup. A topological additive monoid over `α`, for example, is obtained by requiring both the
instances `add_monoid α` and `has_continuous_add α`. -/
class has_continuous_add (M : Type*) [topological_space M] [has_add M] : Prop :=
(continuous_add : continuous (λ p : M × M, p.1 + p.2))

/-- Basic hypothesis to talk about a topological monoid or a topological semigroup.
A topological monoid over `α`, for example, is obtained by requiring both the instances `monoid α`
and `has_continuous_mul α`. -/
@[to_additive]
class has_continuous_mul (M : Type*) [topological_space M] [has_mul M] : Prop :=
(continuous_mul : continuous (λ p : M × M, p.1 * p.2))

section has_continuous_mul

variables [topological_space M] [has_mul M] [has_continuous_mul M]

@[to_additive]
lemma continuous_mul : continuous (λp:M×M, p.1 * p.2) :=
has_continuous_mul.continuous_mul

@[continuity, to_additive]
lemma continuous.mul [topological_space α] {f : α → M} {g : α → M}
  (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x * g x) :=
continuous_mul.comp (hf.prod_mk hg : _)

-- should `to_additive` be doing this?
attribute [continuity] continuous.add

@[to_additive]
lemma continuous_mul_left (a : M) : continuous (λ b:M, a * b) :=
continuous_const.mul continuous_id

@[to_additive]
lemma continuous_mul_right (a : M) : continuous (λ b:M, b * a) :=
continuous_id.mul continuous_const

@[to_additive]
lemma continuous_on.mul [topological_space α] {f : α → M} {g : α → M} {s : set α}
  (hf : continuous_on f s) (hg : continuous_on g s) :
  continuous_on (λx, f x * g x) s :=
(continuous_mul.comp_continuous_on (hf.prod hg) : _)

@[to_additive]
lemma tendsto_mul {a b : M} : tendsto (λp:M×M, p.fst * p.snd) (𝓝 (a, b)) (𝓝 (a * b)) :=
continuous_iff_continuous_at.mp has_continuous_mul.continuous_mul (a, b)

@[to_additive]
lemma filter.tendsto.mul {f : α → M} {g : α → M} {x : filter α} {a b : M}
  (hf : tendsto f x (𝓝 a)) (hg : tendsto g x (𝓝 b)) :
  tendsto (λx, f x * g x) x (𝓝 (a * b)) :=
tendsto_mul.comp (hf.prod_mk_nhds hg)

@[to_additive]
lemma tendsto.const_mul (b : M) {c : M} {f : α → M} {l : filter α}
  (h : tendsto (λ (k:α), f k) l (𝓝 c)) : tendsto (λ (k:α), b * f k) l (𝓝 (b * c)) :=
tendsto_const_nhds.mul h

@[to_additive]
lemma tendsto.mul_const (b : M) {c : M} {f : α → M} {l : filter α}
  (h : tendsto (λ (k:α), f k) l (𝓝 c)) : tendsto (λ (k:α), f k * b) l (𝓝 (c * b)) :=
h.mul tendsto_const_nhds

@[to_additive]
lemma continuous_at.mul [topological_space α] {f : α → M} {g : α → M} {x : α}
  (hf : continuous_at f x) (hg : continuous_at g x) :
  continuous_at (λx, f x * g x) x :=
hf.mul hg

@[to_additive]
lemma continuous_within_at.mul [topological_space α] {f : α → M} {g : α → M} {s : set α} {x : α}
  (hf : continuous_within_at f s x) (hg : continuous_within_at g s x) :
  continuous_within_at (λx, f x * g x) s x :=
hf.mul hg

@[to_additive]
instance [topological_space N] [has_mul N] [has_continuous_mul N] : has_continuous_mul (M × N) :=
⟨((continuous_fst.comp continuous_fst).mul (continuous_fst.comp continuous_snd)).prod_mk
 ((continuous_snd.comp continuous_fst).mul (continuous_snd.comp continuous_snd))⟩

@[priority 100, to_additive]
instance has_continuous_mul_of_discrete_topology [topological_space N]
  [has_mul N] [discrete_topology N] : has_continuous_mul N :=
⟨continuous_of_discrete_topology⟩

open_locale filter

open function

@[to_additive]
lemma has_continuous_mul.of_nhds_one {M : Type*} [monoid M] [topological_space M]
  (hmul : tendsto (uncurry ((*) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) $ 𝓝 1)
  (hleft : ∀ x₀ : M, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1))
  (hright : ∀ x₀ : M, 𝓝 x₀ = map (λ x, x*x₀) (𝓝 1)) : has_continuous_mul M :=
⟨begin
    rw continuous_iff_continuous_at,
    rintros ⟨x₀, y₀⟩,
    have key : (λ p : M × M, x₀ * p.1 * (p.2 * y₀)) = ((λ x, x₀*x) ∘ (λ x, x*y₀)) ∘ (uncurry (*)),
    { ext p, simp [uncurry, mul_assoc] },
    have key₂ : (λ x, x₀*x) ∘ (λ x, y₀*x) = λ x, (x₀ *y₀)*x,
    { ext x, simp },
    calc map (uncurry (*)) (𝓝 (x₀, y₀))
        = map (uncurry (*)) (𝓝 x₀ ×ᶠ 𝓝 y₀) : by rw nhds_prod_eq
    ... = map (λ (p : M × M), x₀ * p.1 * (p.2 * y₀)) ((𝓝 1) ×ᶠ (𝓝 1))
            : by rw [uncurry, hleft x₀, hright y₀, prod_map_map_eq, filter.map_map]
    ... = map ((λ x, x₀ * x) ∘ λ x, x * y₀) (map (uncurry (*)) (𝓝 1 ×ᶠ 𝓝 1))
            : by { rw [key, ← filter.map_map], }
    ... ≤ map ((λ (x : M), x₀ * x) ∘ λ x, x * y₀) (𝓝 1) : map_mono hmul
    ... = 𝓝 (x₀*y₀) : by rw [← filter.map_map, ← hright, hleft y₀, filter.map_map, key₂, ← hleft]
  end⟩

@[to_additive]
lemma has_continuous_mul_of_comm_of_nhds_one (M : Type*) [comm_monoid M] [topological_space M]
  (hmul : tendsto (uncurry ((*) : M → M → M)) (𝓝 1 ×ᶠ 𝓝 1) (𝓝 1))
  (hleft : ∀ x₀ : M, 𝓝 x₀ = map (λ x, x₀*x) (𝓝 1)) : has_continuous_mul M :=
begin
  apply has_continuous_mul.of_nhds_one hmul hleft,
  intros x₀,
  simp_rw [mul_comm, hleft x₀]
end

end has_continuous_mul

section has_continuous_mul

variables [topological_space M] [monoid M] [has_continuous_mul M]

@[to_additive exists_open_nhds_zero_half]
lemma exists_open_nhds_one_split {s : set M} (hs : s ∈ 𝓝 (1 : M)) :
  ∃ V : set M, is_open V ∧ (1 : M) ∈ V ∧ ∀ (v ∈ V) (w ∈ V), v * w ∈ s :=
have ((λa:M×M, a.1 * a.2) ⁻¹' s) ∈ 𝓝 ((1, 1) : M × M),
  from tendsto_mul (by simpa only [one_mul] using hs),
by simpa only [prod_subset_iff] using exists_nhds_square this

@[to_additive exists_nhds_zero_half]
lemma exists_nhds_one_split {s : set M} (hs : s ∈ 𝓝 (1 : M)) :
  ∃ V ∈ 𝓝 (1 : M), ∀ (v ∈ V) (w ∈ V), v * w ∈ s :=
let ⟨V, Vo, V1, hV⟩ := exists_open_nhds_one_split hs
in ⟨V, mem_nhds_sets Vo V1, hV⟩

@[to_additive exists_nhds_zero_quarter]
lemma exists_nhds_one_split4 {u : set M} (hu : u ∈ 𝓝 (1 : M)) :
  ∃ V ∈ 𝓝 (1 : M),
    ∀ {v w s t}, v ∈ V → w ∈ V → s ∈ V → t ∈ V → v * w * s * t ∈ u :=
begin
  rcases exists_nhds_one_split hu with ⟨W, W1, h⟩,
  rcases exists_nhds_one_split W1 with ⟨V, V1, h'⟩,
  use [V, V1],
  intros v w s t v_in w_in s_in t_in,
  simpa only [mul_assoc] using h _ (h' v v_in w w_in) _ (h' s s_in t t_in)
end

/-- Given a neighborhood `U` of `1` there is an open neighborhood `V` of `1`
such that `VV ⊆ U`. -/
@[to_additive "Given a open neighborhood `U` of `0` there is a open neighborhood `V` of `0`
  such that `V + V ⊆ U`."]
lemma exists_open_nhds_one_mul_subset {U : set M} (hU : U ∈ 𝓝 (1 : M)) :
  ∃ V : set M, is_open V ∧ (1 : M) ∈ V ∧ V * V ⊆ U :=
begin
  rcases exists_open_nhds_one_split hU with ⟨V, Vo, V1, hV⟩,
  use [V, Vo, V1],
  rintros _ ⟨x, y, hx, hy, rfl⟩,
  exact hV _ hx _ hy
end

@[to_additive]
lemma tendsto_list_prod {f : β → α → M} {x : filter α} {a : β → M} :
  ∀l:list β, (∀c∈l, tendsto (f c) x (𝓝 (a c))) →
    tendsto (λb, (l.map (λc, f c b)).prod) x (𝓝 ((l.map a).prod))
| []       _ := by simp [tendsto_const_nhds]
| (f :: l) h :=
  begin
    simp only [list.map_cons, list.prod_cons],
    exact (h f (list.mem_cons_self _ _)).mul
      (tendsto_list_prod l (assume c hc, h c (list.mem_cons_of_mem _ hc)))
  end

@[to_additive]
lemma continuous_list_prod [topological_space α] {f : β → α → M} (l : list β)
  (h : ∀c∈l, continuous (f c)) :
  continuous (λa, (l.map (λc, f c a)).prod) :=
continuous_iff_continuous_at.2 $ assume x, tendsto_list_prod l $ assume c hc,
  continuous_iff_continuous_at.1 (h c hc) x

-- @[to_additive continuous_smul]
@[continuity]
lemma continuous_pow : ∀ n : ℕ, continuous (λ a : M, a ^ n)
| 0 := by simpa using continuous_const
| (k+1) := show continuous (λ (a : M), a * a ^ k), from continuous_id.mul (continuous_pow _)

@[continuity]
lemma continuous.pow {f : α → M} [topological_space α] (h : continuous f) (n : ℕ) :
  continuous (λ b, (f b) ^ n) :=
continuous.comp (continuous_pow n) h

end has_continuous_mul

section

variables [topological_space M] [comm_monoid M]

@[to_additive]
lemma submonoid.mem_nhds_one (S : submonoid M) (oS : is_open (S : set M)) :
  (S : set M) ∈ 𝓝 (1 : M) :=
mem_nhds_sets oS S.one_mem

variable [has_continuous_mul M]

@[to_additive]
lemma tendsto_multiset_prod {f : β → α → M} {x : filter α} {a : β → M} (s : multiset β) :
  (∀c∈s, tendsto (f c) x (𝓝 (a c))) →
    tendsto (λb, (s.map (λc, f c b)).prod) x (𝓝 ((s.map a).prod)) :=
by { rcases s with ⟨l⟩, simp, exact tendsto_list_prod l }

@[to_additive]
lemma tendsto_finset_prod {f : β → α → M} {x : filter α} {a : β → M} (s : finset β) :
  (∀c∈s, tendsto (f c) x (𝓝 (a c))) → tendsto (λb, ∏ c in s, f c b) x (𝓝 (∏ c in s, a c)) :=
tendsto_multiset_prod _

@[to_additive, continuity]
lemma continuous_multiset_prod [topological_space α] {f : β → α → M} (s : multiset β) :
  (∀c∈s, continuous (f c)) → continuous (λa, (s.map (λc, f c a)).prod) :=
by { rcases s with ⟨l⟩, simp, exact continuous_list_prod l }

attribute [continuity] continuous_multiset_sum

@[continuity, to_additive]
lemma continuous_finset_prod [topological_space α] {f : β → α → M} (s : finset β) :
  (∀c∈s, continuous (f c)) → continuous (λa, ∏ c in s, f c a) :=
continuous_multiset_prod _

-- should `to_additive` be doing this?
attribute [continuity] continuous_finset_sum

end

instance additive.has_continuous_add {M} [h : topological_space M] [has_mul M]
  [has_continuous_mul M] : @has_continuous_add (additive M) h _ :=
{ continuous_add := @continuous_mul M _ _ _  }

instance multiplicative.has_continuous_mul {M} [h : topological_space M] [has_add M]
  [has_continuous_add M] : @has_continuous_mul (multiplicative M) h _ :=
{ continuous_mul := @continuous_add M _ _ _  }
