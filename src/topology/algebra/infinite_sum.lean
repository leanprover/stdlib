/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import algebra.big_operators.intervals
import topology.instances.real
import topology.algebra.module
import algebra.indicator_function
import data.equiv.encodable.lattice
import data.nat.parity
import order.filter.at_top_bot

/-!
# Infinite sum over a topological monoid

This sum is known as unconditionally convergent, as it sums to the same value under all possible
permutations. For Euclidean spaces (finite dimensional Banach spaces) this is equivalent to absolute
convergence.

Note: There are summable sequences which are not unconditionally convergent! The other way holds
generally, see `has_sum.tendsto_sum_nat`.

## References

* Bourbaki: General Topology (1995), Chapter 3 §5 (Infinite sums in commutative groups)

-/

noncomputable theory
open finset filter function classical
open_locale topological_space classical big_operators nnreal

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section has_sum
variables [add_comm_monoid α] [topological_space α]

/-- Infinite sum on a topological monoid

The `at_top` filter on `finset β` is the limit of all finite sets towards the entire type. So we sum
up bigger and bigger sets. This sum operation is invariant under reordering. In particular,
the function `ℕ → ℝ` sending `n` to `(-1)^n / (n+1)` does not have a
sum for this definition, but a series which is absolutely convergent will have the correct sum.

This is based on Mario Carneiro's
[infinite sum `df-tsms` in Metamath](http://us.metamath.org/mpeuni/df-tsms.html).

For the definition or many statements, `α` does not need to be a topological monoid. We only add
this assumption later, for the lemmas where it is relevant.
-/
def has_sum (f : β → α) (a : α) : Prop := tendsto (λs:finset β, ∑ b in s, f b) at_top (𝓝 a)

/-- `summable f` means that `f` has some (infinite) sum. Use `tsum` to get the value. -/
def summable (f : β → α) : Prop := ∃a, has_sum f a

/-- `∑' i, f i` is the sum of `f` it exists, or 0 otherwise -/
@[irreducible] def tsum {β} (f : β → α) := if h : summable f then classical.some h else 0

-- see Note [operator precedence of big operators]
notation `∑'` binders `, ` r:(scoped:67 f, tsum f) := r

variables {f g : β → α} {a b : α} {s : finset β}

lemma summable.has_sum (ha : summable f) : has_sum f (∑'b, f b) :=
by simp [ha, tsum]; exact some_spec ha

lemma has_sum.summable (h : has_sum f a) : summable f := ⟨a, h⟩

/-- Constant zero function has sum `0` -/
lemma has_sum_zero : has_sum (λb, 0 : β → α) 0 :=
by simp [has_sum, tendsto_const_nhds]

lemma has_sum_empty [is_empty β] : has_sum f 0 :=
by convert has_sum_zero

lemma summable_zero : summable (λb, 0 : β → α) := has_sum_zero.summable

lemma summable_empty [is_empty β] : summable f := has_sum_empty.summable

lemma tsum_eq_zero_of_not_summable (h : ¬ summable f) : ∑'b, f b = 0 :=
by simp [tsum, h]

lemma has_sum.has_sum_of_sum_eq {g : γ → α}
  (h_eq : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
  (hf : has_sum g a) :
  has_sum f a :=
le_trans (map_at_top_finset_sum_le_of_sum_eq h_eq) hf

lemma has_sum_iff_has_sum {g : γ → α}
  (h₁ : ∀u:finset γ, ∃v:finset β, ∀v', v ⊆ v' → ∃u', u ⊆ u' ∧ ∑ x in u', g x = ∑ b in v', f b)
  (h₂ : ∀v:finset β, ∃u:finset γ, ∀u', u ⊆ u' → ∃v', v ⊆ v' ∧ ∑ b in v', f b = ∑ x in u', g x) :
  has_sum f a ↔ has_sum g a :=
⟨has_sum.has_sum_of_sum_eq h₂, has_sum.has_sum_of_sum_eq h₁⟩

lemma function.injective.has_sum_iff {g : γ → β} (hg : injective g)
  (hf : ∀ x ∉ set.range g, f x = 0) :
  has_sum (f ∘ g) a ↔ has_sum f a :=
by simp only [has_sum, tendsto, hg.map_at_top_finset_sum_eq hf]

lemma function.injective.summable_iff {g : γ → β} (hg : injective g)
  (hf : ∀ x ∉ set.range g, f x = 0) :
  summable (f ∘ g) ↔ summable f :=
exists_congr $ λ _, hg.has_sum_iff hf

lemma has_sum_subtype_iff_of_support_subset {s : set β} (hf : support f ⊆ s) :
  has_sum (f ∘ coe : s → α) a ↔ has_sum f a :=
subtype.coe_injective.has_sum_iff $ by simpa using support_subset_iff'.1 hf

lemma has_sum_subtype_iff_indicator {s : set β} :
  has_sum (f ∘ coe : s → α) a ↔ has_sum (s.indicator f) a :=
by rw [← set.indicator_range_comp, subtype.range_coe,
  has_sum_subtype_iff_of_support_subset set.support_indicator_subset]

@[simp] lemma has_sum_subtype_support : has_sum (f ∘ coe : support f → α) a ↔ has_sum f a :=
has_sum_subtype_iff_of_support_subset $ set.subset.refl _

lemma has_sum_fintype [fintype β] (f : β → α) : has_sum f (∑ b, f b) :=
order_top.tendsto_at_top_nhds _

protected lemma finset.has_sum (s : finset β) (f : β → α) :
  has_sum (f ∘ coe : (↑s : set β) → α) (∑ b in s, f b) :=
by { rw ← sum_attach, exact has_sum_fintype _ }

protected lemma finset.summable (s : finset β) (f : β → α) :
  summable (f ∘ coe : (↑s : set β) → α) :=
(s.has_sum f).summable

protected lemma set.finite.summable {s : set β} (hs : s.finite) (f : β → α) :
  summable (f ∘ coe : s → α) :=
by convert hs.to_finset.summable f; simp only [hs.coe_to_finset]

/-- If a function `f` vanishes outside of a finite set `s`, then it `has_sum` `∑ b in s, f b`. -/
lemma has_sum_sum_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : has_sum f (∑ b in s, f b) :=
(has_sum_subtype_iff_of_support_subset $ support_subset_iff'.2 hf).1 $ s.has_sum f

lemma summable_of_ne_finset_zero (hf : ∀b∉s, f b = 0) : summable f :=
(has_sum_sum_of_ne_finset_zero hf).summable

lemma has_sum_single {f : β → α} (b : β) (hf : ∀b' ≠ b, f b' = 0) :
  has_sum f (f b) :=
suffices has_sum f (∑ b' in {b}, f b'),
  by simpa using this,
has_sum_sum_of_ne_finset_zero $ by simpa [hf]

lemma has_sum_ite_eq (b : β) [decidable_pred (= b)] (a : α) :
  has_sum (λb', if b' = b then a else 0) a :=
begin
  convert has_sum_single b _,
  { exact (if_pos rfl).symm },
  assume b' hb',
  exact if_neg hb'
end

lemma equiv.has_sum_iff (e : γ ≃ β) :
  has_sum (f ∘ e) a ↔ has_sum f a :=
e.injective.has_sum_iff $ by simp

lemma function.injective.has_sum_range_iff {g : γ → β} (hg : injective g) :
  has_sum (λ x : set.range g, f x) a ↔ has_sum (f ∘ g) a :=
(equiv.of_injective g hg).has_sum_iff.symm

lemma equiv.summable_iff (e : γ ≃ β) :
  summable (f ∘ e) ↔ summable f :=
exists_congr $ λ a, e.has_sum_iff

lemma summable.prod_symm {f : β × γ → α} (hf : summable f) : summable (λ p : γ × β, f p.swap) :=
(equiv.prod_comm γ β).summable_iff.2 hf

lemma equiv.has_sum_iff_of_support {g : γ → α} (e : support f ≃ support g)
  (he : ∀ x : support f, g (e x) = f x) :
  has_sum f a ↔ has_sum g a :=
have (g ∘ coe) ∘ e = f ∘ coe, from funext he,
by rw [← has_sum_subtype_support, ← this, e.has_sum_iff, has_sum_subtype_support]

lemma has_sum_iff_has_sum_of_ne_zero_bij {g : γ → α} (i : support g → β)
  (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
  (hf : support f ⊆ set.range i) (hfg : ∀ x, f (i x) = g x) :
  has_sum f a ↔ has_sum g a :=
iff.symm $ equiv.has_sum_iff_of_support
  (equiv.of_bijective (λ x, ⟨i x, λ hx, x.coe_prop $ hfg x ▸ hx⟩)
    ⟨λ x y h, subtype.ext $ hi $ subtype.ext_iff.1 h,
      λ y, (hf y.coe_prop).imp $ λ x hx, subtype.ext hx⟩)
  hfg

lemma equiv.summable_iff_of_support {g : γ → α} (e : support f ≃ support g)
  (he : ∀ x : support f, g (e x) = f x) :
  summable f ↔ summable g :=
exists_congr $ λ _, e.has_sum_iff_of_support he

protected lemma has_sum.map [add_comm_monoid γ] [topological_space γ] (hf : has_sum f a)
  (g : α →+ γ) (hg : continuous g) :
  has_sum (g ∘ f) (g a) :=
have g ∘ (λs:finset β, ∑ b in s, f b) = (λs:finset β, ∑ b in s, g (f b)),
  from funext $ g.map_sum _,
show tendsto (λs:finset β, ∑ b in s, g (f b)) at_top (𝓝 (g a)),
  from this ▸ (hg.tendsto a).comp hf

protected lemma summable.map [add_comm_monoid γ] [topological_space γ] (hf : summable f)
  (g : α →+ γ) (hg : continuous g) :
  summable (g ∘ f) :=
(hf.has_sum.map g hg).summable

/-- If `f : ℕ → α` has sum `a`, then the partial sums `∑_{i=0}^{n-1} f i` converge to `a`. -/
lemma has_sum.tendsto_sum_nat {f : ℕ → α} (h : has_sum f a) :
  tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
h.comp tendsto_finset_range

lemma has_sum.unique {a₁ a₂ : α} [t2_space α] : has_sum f a₁ → has_sum f a₂ → a₁ = a₂ :=
tendsto_nhds_unique

lemma summable.has_sum_iff_tendsto_nat [t2_space α] {f : ℕ → α} {a : α} (hf : summable f) :
  has_sum f a ↔ tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
begin
  refine ⟨λ h, h.tendsto_sum_nat, λ h, _⟩,
  rw tendsto_nhds_unique h hf.has_sum.tendsto_sum_nat,
  exact hf.has_sum
end

lemma equiv.summable_iff_of_has_sum_iff {α' : Type*} [add_comm_monoid α']
  [topological_space α'] (e : α' ≃ α) {f : β → α} {g : γ → α'}
  (he : ∀ {a}, has_sum f (e a) ↔ has_sum g a) :
  summable f ↔ summable g :=
⟨λ ⟨a, ha⟩, ⟨e.symm a, he.1 $ by rwa [e.apply_symm_apply]⟩, λ ⟨a, ha⟩, ⟨e a, he.2 ha⟩⟩

variable [has_continuous_add α]

lemma has_sum.add (hf : has_sum f a) (hg : has_sum g b) : has_sum (λb, f b + g b) (a + b) :=
by simp only [has_sum, sum_add_distrib]; exact hf.add hg

lemma summable.add (hf : summable f) (hg : summable g) : summable (λb, f b + g b) :=
(hf.has_sum.add hg.has_sum).summable

lemma has_sum_sum {f : γ → β → α} {a : γ → α} {s : finset γ} :
  (∀i∈s, has_sum (f i) (a i)) → has_sum (λb, ∑ i in s, f i b) (∑ i in s, a i) :=
finset.induction_on s (by simp only [has_sum_zero, sum_empty, forall_true_iff])
  (by simp only [has_sum.add, sum_insert, mem_insert, forall_eq_or_imp,
        forall_2_true_iff, not_false_iff, forall_true_iff] {contextual := tt})

lemma summable_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, summable (f i)) :
  summable (λb, ∑ i in s, f i b) :=
(has_sum_sum $ assume i hi, (hf i hi).has_sum).summable

lemma has_sum.add_disjoint {s t : set β} (hs : disjoint s t)
  (ha : has_sum (f ∘ coe : s → α) a) (hb : has_sum (f ∘ coe : t → α) b) :
  has_sum (f ∘ coe : s ∪ t → α) (a + b) :=
begin
  rw has_sum_subtype_iff_indicator at *,
  rw set.indicator_union_of_disjoint hs,
  exact ha.add hb
end

lemma has_sum.add_is_compl {s t : set β} (hs : is_compl s t)
  (ha : has_sum (f ∘ coe : s → α) a) (hb : has_sum (f ∘ coe : t → α) b) :
  has_sum f (a + b) :=
by simpa [← hs.compl_eq]
  using (has_sum_subtype_iff_indicator.1 ha).add (has_sum_subtype_iff_indicator.1 hb)

lemma has_sum.add_compl {s : set β} (ha : has_sum (f ∘ coe : s → α) a)
  (hb : has_sum (f ∘ coe : sᶜ → α) b) :
  has_sum f (a + b) :=
ha.add_is_compl is_compl_compl hb

lemma summable.add_compl {s : set β} (hs : summable (f ∘ coe : s → α))
  (hsc : summable (f ∘ coe : sᶜ → α)) :
  summable f :=
(hs.has_sum.add_compl hsc.has_sum).summable

lemma has_sum.compl_add {s : set β} (ha : has_sum (f ∘ coe : sᶜ → α) a)
  (hb : has_sum (f ∘ coe : s → α) b) :
  has_sum f (a + b) :=
ha.add_is_compl is_compl_compl.symm hb

lemma has_sum.even_add_odd {f : ℕ → α} (he : has_sum (λ k, f (2 * k)) a)
  (ho : has_sum (λ k, f (2 * k + 1)) b) :
  has_sum f (a + b) :=
begin
  have := mul_right_injective' (@two_ne_zero ℕ _ _),
  replace he := this.has_sum_range_iff.2 he,
  replace ho := ((add_left_injective 1).comp this).has_sum_range_iff.2 ho,
  refine he.add_is_compl _ ho,
  simpa [(∘)] using nat.is_compl_even_odd
end

lemma summable.compl_add {s : set β} (hs : summable (f ∘ coe : sᶜ → α))
  (hsc : summable (f ∘ coe : s → α)) :
  summable f :=
(hs.has_sum.compl_add hsc.has_sum).summable

lemma summable.even_add_odd {f : ℕ → α} (he : summable (λ k, f (2 * k)))
  (ho : summable (λ k, f (2 * k + 1))) :
  summable f :=
(he.has_sum.even_add_odd ho.has_sum).summable

lemma has_sum.sigma [regular_space α] {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α} {a : α}
  (ha : has_sum f a) (hf : ∀b, has_sum (λc, f ⟨b, c⟩) (g b)) : has_sum g a :=
begin
  refine (at_top_basis.tendsto_iff (closed_nhds_basis a)).mpr _,
  rintros s ⟨hs, hsc⟩,
  rcases mem_at_top_sets.mp (ha hs) with ⟨u, hu⟩,
  use [u.image sigma.fst, trivial],
  intros bs hbs,
  simp only [set.mem_preimage, ge_iff_le, finset.le_iff_subset] at hu,
  have : tendsto (λ t : finset (Σ b, γ b), ∑ p in t.filter (λ p, p.1 ∈ bs), f p)
    at_top (𝓝 $ ∑ b in bs, g b),
  { simp only [← sigma_preimage_mk, sum_sigma],
    refine tendsto_finset_sum _ (λ b hb, _),
    change tendsto (λ t, (λ t, ∑ s in t, f ⟨b, s⟩) (preimage t (sigma.mk b) _)) at_top (𝓝 (g b)),
    exact tendsto.comp (hf b) (tendsto_finset_preimage_at_top_at_top _) },
  refine hsc.mem_of_tendsto this (eventually_at_top.2 ⟨u, λ t ht, hu _ (λ x hx, _)⟩),
  exact mem_filter.2 ⟨ht hx, hbs $ mem_image_of_mem _ hx⟩
end

/-- If a series `f` on `β × γ` has sum `a` and for each `b` the restriction of `f` to `{b} × γ`
has sum `g b`, then the series `g` has sum `a`. -/
lemma has_sum.prod_fiberwise [regular_space α] {f : β × γ → α} {g : β → α} {a : α}
  (ha : has_sum f a) (hf : ∀b, has_sum (λc, f (b, c)) (g b)) :
  has_sum g a :=
has_sum.sigma ((equiv.sigma_equiv_prod β γ).has_sum_iff.2 ha) hf

lemma summable.sigma' [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) (hf : ∀b, summable (λc, f ⟨b, c⟩)) :
  summable (λb, ∑'c, f ⟨b, c⟩) :=
(ha.has_sum.sigma (assume b, (hf b).has_sum)).summable

lemma has_sum.sigma_of_has_sum [regular_space α] {γ : β → Type*} {f : (Σ b:β, γ b) → α} {g : β → α}
  {a : α} (ha : has_sum g a) (hf : ∀b, has_sum (λc, f ⟨b, c⟩) (g b)) (hf' : summable f) :
  has_sum f a :=
by simpa [(hf'.has_sum.sigma hf).unique ha] using hf'.has_sum

end has_sum

section tsum
variables [add_comm_monoid α] [topological_space α] [t2_space α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma has_sum.tsum_eq (ha : has_sum f a) : ∑'b, f b = a :=
(summable.has_sum ⟨a, ha⟩).unique ha

lemma summable.has_sum_iff (h : summable f) : has_sum f a ↔ ∑'b, f b = a :=
iff.intro has_sum.tsum_eq (assume eq, eq ▸ h.has_sum)

@[simp] lemma tsum_zero : ∑'b:β, (0:α) = 0 := has_sum_zero.tsum_eq

@[simp] lemma tsum_empty [is_empty β] : ∑'b, f b = 0 := has_sum_empty.tsum_eq

lemma tsum_eq_sum {f : β → α} {s : finset β} (hf : ∀b∉s, f b = 0)  :
  ∑' b, f b = ∑ b in s, f b :=
(has_sum_sum_of_ne_finset_zero hf).tsum_eq

lemma tsum_congr {α β : Type*} [add_comm_monoid α] [topological_space α]
  {f g : β → α} (hfg : ∀ b, f b = g b) : ∑' b, f b = ∑' b, g b :=
congr_arg tsum (funext hfg)

lemma tsum_fintype [fintype β] (f : β → α) : ∑'b, f b = ∑ b, f b :=
(has_sum_fintype f).tsum_eq

@[simp] lemma finset.tsum_subtype (s : finset β) (f : β → α) :
  ∑' x : {x // x ∈ s}, f x = ∑ x in s, f x :=
(s.has_sum f).tsum_eq

@[simp] lemma finset.tsum_subtype' (s : finset β) (f : β → α) :
  ∑' x : (s : set β), f x = ∑ x in s, f x :=
s.tsum_subtype f

lemma tsum_eq_single {f : β → α} (b : β) (hf : ∀b' ≠ b, f b' = 0)  :
  ∑'b, f b = f b :=
(has_sum_single b hf).tsum_eq

@[simp] lemma tsum_ite_eq (b : β) [decidable_pred (= b)] (a : α) :
  ∑' b', (if b' = b then a else 0) = a :=
(has_sum_ite_eq b a).tsum_eq

lemma tsum_dite_right (P : Prop) [decidable P] (x : β → ¬ P → α) :
  ∑' (b : β), (if h : P then (0 : α) else x b h) = if h : P then (0 : α) else ∑' (b : β), x b h :=
by by_cases hP : P; simp [hP]

lemma tsum_dite_left (P : Prop) [decidable P] (x : β → P → α) :
  ∑' (b : β), (if h : P then x b h else 0) = if h : P then (∑' (b : β), x b h) else 0 :=
by by_cases hP : P; simp [hP]

lemma equiv.tsum_eq_tsum_of_has_sum_iff_has_sum {α' : Type*} [add_comm_monoid α']
  [topological_space α'] (e : α' ≃ α) (h0 : e 0 = 0) {f : β → α} {g : γ → α'}
  (h : ∀ {a}, has_sum f (e a) ↔ has_sum g a) :
  ∑' b, f b = e (∑' c, g c) :=
by_cases
  (assume : summable g, (h.mpr this.has_sum).tsum_eq)
  (assume hg : ¬ summable g,
    have hf : ¬ summable f, from mt (e.summable_iff_of_has_sum_iff @h).1 hg,
    by simp [tsum, hf, hg, h0])

lemma tsum_eq_tsum_of_has_sum_iff_has_sum {f : β → α} {g : γ → α}
  (h : ∀{a}, has_sum f a ↔ has_sum g a) :
  ∑'b, f b = ∑'c, g c :=
(equiv.refl α).tsum_eq_tsum_of_has_sum_iff_has_sum rfl @h

lemma equiv.tsum_eq (j : γ ≃ β) (f : β → α) : ∑'c, f (j c) = ∑'b, f b :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ λ a, j.has_sum_iff

lemma equiv.tsum_eq_tsum_of_support {f : β → α} {g : γ → α} (e : support f ≃ support g)
  (he : ∀ x, g (e x) = f x) :
  (∑' x, f x) = ∑' y, g y :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ λ _, e.has_sum_iff_of_support he

lemma tsum_eq_tsum_of_ne_zero_bij {g : γ → α} (i : support g → β)
  (hi : ∀ ⦃x y⦄, i x = i y → (x : γ) = y)
  (hf : support f ⊆ set.range i) (hfg : ∀ x, f (i x) = g x) :
  ∑' x, f x  = ∑' y, g y :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ λ _, has_sum_iff_has_sum_of_ne_zero_bij i hi hf hfg

lemma tsum_subtype (s : set β) (f : β → α) :
  ∑' x:s, f x = ∑' x, s.indicator f x :=
tsum_eq_tsum_of_has_sum_iff_has_sum $ λ _, has_sum_subtype_iff_indicator

section has_continuous_add
variable [has_continuous_add α]

lemma tsum_add (hf : summable f) (hg : summable g) : ∑'b, (f b + g b) = (∑'b, f b) + (∑'b, g b) :=
(hf.has_sum.add hg.has_sum).tsum_eq

lemma tsum_sum {f : γ → β → α} {s : finset γ} (hf : ∀i∈s, summable (f i)) :
  ∑'b, ∑ i in s, f i b = ∑ i in s, ∑'b, f i b :=
(has_sum_sum $ assume i hi, (hf i hi).has_sum).tsum_eq

lemma tsum_sigma' [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (h₁ : ∀b, summable (λc, f ⟨b, c⟩)) (h₂ : summable f) : ∑'p, f p = ∑'b c, f ⟨b, c⟩ :=
(h₂.has_sum.sigma (assume b, (h₁ b).has_sum)).tsum_eq.symm

lemma tsum_prod' [regular_space α] {f : β × γ → α} (h : summable f)
  (h₁ : ∀b, summable (λc, f (b, c))) :
  ∑'p, f p = ∑'b c, f (b, c) :=
(h.has_sum.prod_fiberwise (assume b, (h₁ b).has_sum)).tsum_eq.symm

lemma tsum_comm' [regular_space α] {f : β → γ → α} (h : summable (function.uncurry f))
  (h₁ : ∀b, summable (f b)) (h₂ : ∀ c, summable (λ b, f b c)) :
  ∑' c b, f b c = ∑' b c, f b c :=
begin
  erw [← tsum_prod' h h₁, ← tsum_prod' h.prod_symm h₂, ← (equiv.prod_comm β γ).tsum_eq],
  refl,
  assumption
end

end has_continuous_add

section encodable
open encodable
variable [encodable γ]

/-- You can compute a sum over an encodably type by summing over the natural numbers and
  taking a supremum. This is useful for outer measures. -/
theorem tsum_supr_decode₂ [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0)
  (s : γ → β) : ∑' i : ℕ, m (⨆ b ∈ decode₂ γ i, s b) = ∑' b : γ, m (s b) :=
begin
  have H : ∀ n, m (⨆ b ∈ decode₂ γ n, s b) ≠ 0 → (decode₂ γ n).is_some,
  { intros n h,
    cases decode₂ γ n with b,
    { refine (h $ by simp [m0]).elim },
    { exact rfl } },
  symmetry, refine tsum_eq_tsum_of_ne_zero_bij (λ a, option.get (H a.1 a.2)) _ _ _,
  { rintros ⟨m, hm⟩ ⟨n, hn⟩ e,
    have := mem_decode₂.1 (option.get_mem (H n hn)),
    rwa [← e, mem_decode₂.1 (option.get_mem (H m hm))] at this },
  { intros b h,
    refine ⟨⟨encode b, _⟩, _⟩,
    { simp only [mem_support, encodek₂] at h ⊢, convert h, simp [set.ext_iff, encodek₂] },
    { exact option.get_of_mem _ (encodek₂ _) } },
  { rintros ⟨n, h⟩, dsimp only [subtype.coe_mk],
    transitivity, swap,
    rw [show decode₂ γ n = _, from option.get_mem (H n h)],
    congr, simp [ext_iff, -option.some_get] }
end

/-- `tsum_supr_decode₂` specialized to the complete lattice of sets. -/
theorem tsum_Union_decode₂ (m : set β → α) (m0 : m ∅ = 0)
  (s : γ → set β) : ∑' i, m (⋃ b ∈ decode₂ γ i, s b) = ∑' b, m (s b) :=
tsum_supr_decode₂ m m0 s

/-! Some properties about measure-like functions.
  These could also be functions defined on complete sublattices of sets, with the property
  that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/

/-- If a function is countably sub-additive then it is sub-additive on encodable types -/
theorem rel_supr_tsum [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0)
  (R : α → α → Prop) (m_supr : ∀(s : ℕ → β), R (m (⨆ i, s i)) ∑' i, m (s i))
  (s : γ → β) : R (m (⨆ b : γ, s b)) ∑' b : γ, m (s b) :=
by { rw [← supr_decode₂, ← tsum_supr_decode₂ _ m0 s], exact m_supr _ }

/-- If a function is countably sub-additive then it is sub-additive on finite sets -/
theorem rel_supr_sum [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0)
  (R : α → α → Prop) (m_supr : ∀(s : ℕ → β), R (m (⨆ i, s i)) (∑' i, m (s i)))
  (s : δ → β) (t : finset δ) :
  R (m (⨆ d ∈ t, s d)) (∑ d in t, m (s d)) :=
by { cases t.nonempty_encodable, rw [supr_subtype'], convert rel_supr_tsum m m0 R m_supr _,
     rw [← finset.tsum_subtype], assumption }

/-- If a function is countably sub-additive then it is binary sub-additive -/
theorem rel_sup_add [complete_lattice β] (m : β → α) (m0 : m ⊥ = 0)
  (R : α → α → Prop) (m_supr : ∀(s : ℕ → β), R (m (⨆ i, s i)) (∑' i, m (s i)))
  (s₁ s₂ : β) : R (m (s₁ ⊔ s₂)) (m s₁ + m s₂) :=
begin
  convert rel_supr_tsum m m0 R m_supr (λ b, cond b s₁ s₂),
  { simp only [supr_bool_eq, cond] },
  { rw [tsum_fintype, fintype.sum_bool, cond, cond] }
end

end encodable

variables [has_continuous_add α]

lemma tsum_add_tsum_compl {s : set β} (hs : summable (f ∘ coe : s → α))
  (hsc : summable (f ∘ coe : sᶜ → α)) :
  (∑' x : s, f x) + (∑' x : sᶜ, f x) = ∑' x, f x :=
(hs.has_sum.add_compl hsc.has_sum).tsum_eq.symm

lemma tsum_union_disjoint {s t : set β} (hd : disjoint s t)
  (hs : summable (f ∘ coe : s → α)) (ht : summable (f ∘ coe : t → α)) :
  (∑' x : s ∪ t, f x) = (∑' x : s, f x) + (∑' x : t, f x) :=
(hs.has_sum.add_disjoint hd ht.has_sum).tsum_eq

lemma tsum_even_add_odd {f : ℕ → α} (he : summable (λ k, f (2 * k)))
  (ho : summable (λ k, f (2 * k + 1))) :
  (∑' k, f (2 * k)) + (∑' k, f (2 * k + 1)) = ∑' k, f k :=
(he.has_sum.even_add_odd ho.has_sum).tsum_eq.symm

end tsum

section pi
variables {ι : Type*} {π : α → Type*} [∀ x, add_comm_monoid (π x)] [∀ x, topological_space (π x)]

lemma pi.has_sum {f : ι → ∀ x, π x} {g : ∀ x, π x} :
  has_sum f g ↔ ∀ x, has_sum (λ i, f i x) (g x) :=
by simp only [has_sum, tendsto_pi, sum_apply]

lemma pi.summable {f : ι → ∀ x, π x} : summable f ↔ ∀ x, summable (λ i, f i x) :=
by simp only [summable, pi.has_sum, skolem]

lemma tsum_apply [∀ x, t2_space (π x)] {f : ι → ∀ x, π x}{x : α} (hf : summable f) :
  (∑' i, f i) x = ∑' i, f i x :=
(pi.has_sum.mp hf.has_sum x).tsum_eq.symm

end pi

section topological_group
variables [add_comm_group α] [topological_space α] [topological_add_group α]
variables {f g : β → α} {a a₁ a₂ : α}

-- `by simpa using` speeds up elaboration. Why?
lemma has_sum.neg (h : has_sum f a) : has_sum (λb, - f b) (- a) :=
by simpa only using h.map (-add_monoid_hom.id α) continuous_neg

lemma summable.neg (hf : summable f) : summable (λb, - f b) :=
hf.has_sum.neg.summable

lemma summable.of_neg (hf : summable (λb, - f b)) : summable f :=
by simpa only [neg_neg] using hf.neg

lemma summable_neg_iff : summable (λ b, - f b) ↔ summable f :=
⟨summable.of_neg, summable.neg⟩

lemma has_sum.sub (hf : has_sum f a₁) (hg : has_sum g a₂) : has_sum (λb, f b - g b) (a₁ - a₂) :=
by { simp only [sub_eq_add_neg], exact hf.add hg.neg }

lemma summable.sub (hf : summable f) (hg : summable g) : summable (λb, f b - g b) :=
(hf.has_sum.sub hg.has_sum).summable

lemma has_sum.update (hf : has_sum f a₁) (b : β) [decidable_eq β] (a : α) :
  has_sum (update f b a) (a - f b + a₁) :=
begin
  convert ((has_sum_ite_eq b _).add hf),
  ext b',
  by_cases h : b' = b,
  { rw [h, update_same],
    simp only [eq_self_iff_true, if_true, sub_add_cancel] },
  simp only [h, update_noteq, if_false, ne.def, zero_add, not_false_iff],
end

lemma summable.update (hf : summable f) (b : β) [decidable_eq β] (a : α) :
  summable (update f b a) :=
(hf.has_sum.update b a).summable

lemma has_sum.has_sum_compl_iff {s : set β} (hf : has_sum (f ∘ coe : s → α) a₁) :
  has_sum (f ∘ coe : sᶜ → α) a₂ ↔ has_sum f (a₁ + a₂) :=
begin
  refine ⟨λ h, hf.add_compl h, λ h, _⟩,
  rw [has_sum_subtype_iff_indicator] at hf ⊢,
  rw [set.indicator_compl],
  simpa only [add_sub_cancel'] using h.sub hf
end

lemma has_sum.has_sum_iff_compl {s : set β} (hf : has_sum (f ∘ coe : s → α) a₁) :
  has_sum f a₂ ↔ has_sum (f ∘ coe : sᶜ → α) (a₂ - a₁) :=
iff.symm $ hf.has_sum_compl_iff.trans $ by rw [add_sub_cancel'_right]

lemma summable.summable_compl_iff {s : set β} (hf : summable (f ∘ coe : s → α)) :
  summable (f ∘ coe : sᶜ → α) ↔ summable f :=
⟨λ ⟨a, ha⟩, (hf.has_sum.has_sum_compl_iff.1 ha).summable,
  λ ⟨a, ha⟩, (hf.has_sum.has_sum_iff_compl.1 ha).summable⟩

protected lemma finset.has_sum_compl_iff (s : finset β) :
  has_sum (λ x : {x // x ∉ s}, f x) a ↔ has_sum f (a + ∑ i in s, f i) :=
(s.has_sum f).has_sum_compl_iff.trans $ by rw [add_comm]

protected lemma finset.has_sum_iff_compl (s : finset β) :
  has_sum f a ↔ has_sum (λ x : {x // x ∉ s}, f x) (a - ∑ i in s, f i) :=
(s.has_sum f).has_sum_iff_compl

protected lemma finset.summable_compl_iff (s : finset β) :
  summable (λ x : {x // x ∉ s}, f x) ↔ summable f :=
(s.summable f).summable_compl_iff

lemma set.finite.summable_compl_iff {s : set β} (hs : s.finite) :
  summable (f ∘ coe : sᶜ → α) ↔ summable f :=
(hs.summable f).summable_compl_iff

lemma has_sum_ite_eq_extract [decidable_eq β] (hf : has_sum f a) (b : β) :
  has_sum (λ n, ite (n = b) 0 (f n)) (a - f b) :=
begin
  convert hf.update b 0 using 1,
  { ext n, rw function.update_apply, },
  { rw [sub_add_eq_add_sub, zero_add], },
end

section tsum
variables [t2_space α]

lemma tsum_neg (hf : summable f) : ∑'b, - f b = - ∑'b, f b :=
hf.has_sum.neg.tsum_eq

lemma tsum_sub (hf : summable f) (hg : summable g) : ∑'b, (f b - g b) = ∑'b, f b - ∑'b, g b :=
(hf.has_sum.sub hg.has_sum).tsum_eq

lemma sum_add_tsum_compl {s : finset β} (hf : summable f) :
  (∑ x in s, f x) + (∑' x : (↑s : set β)ᶜ, f x) = ∑' x, f x :=
((s.has_sum f).add_compl (s.summable_compl_iff.2 hf).has_sum).tsum_eq.symm

/-- Let `f : β → α` be a sequence with summable series and let `b ∈ β` be an index.
Lemma `tsum_ite_eq_extract` writes `Σ f n` as the sum of `f b` plus the series of the
remaining terms. -/
lemma tsum_ite_eq_extract [decidable_eq β] (hf : summable f) (b : β) :
  ∑' n, f n = f b + ∑' n, ite (n = b) 0 (f n) :=
begin
  rw (has_sum_ite_eq_extract hf.has_sum b).tsum_eq,
  exact (add_sub_cancel'_right _ _).symm,
end

end tsum

/-!
### Sums on subtypes

If `s` is a finset of `α`, we show that the summability of `f` in the whole space and on the subtype
`univ - s` are equivalent, and relate their sums. For a function defined on `ℕ`, we deduce the
formula `(∑ i in range k, f i) + (∑' i, f (i + k)) = (∑' i, f i)`, in `sum_add_tsum_nat_add`.
-/
section subtype

lemma has_sum_nat_add_iff {f : ℕ → α} (k : ℕ) {a : α} :
  has_sum (λ n, f (n + k)) a ↔ has_sum f (a + ∑ i in range k, f i) :=
begin
  refine iff.trans _ ((range k).has_sum_compl_iff),
  rw [← (not_mem_range_equiv k).symm.has_sum_iff],
  refl
end

lemma summable_nat_add_iff {f : ℕ → α} (k : ℕ) : summable (λ n, f (n + k)) ↔ summable f :=
iff.symm $ (equiv.add_right (∑ i in range k, f i)).summable_iff_of_has_sum_iff $
  λ a, (has_sum_nat_add_iff k).symm

lemma has_sum_nat_add_iff' {f : ℕ → α} (k : ℕ) {a : α} :
  has_sum (λ n, f (n + k)) (a - ∑ i in range k, f i) ↔ has_sum f a :=
by simp [has_sum_nat_add_iff]

lemma sum_add_tsum_nat_add [t2_space α] {f : ℕ → α} (k : ℕ) (h : summable f) :
  (∑ i in range k, f i) + (∑' i, f (i + k)) = ∑' i, f i :=
by simpa only [add_comm] using
  ((has_sum_nat_add_iff k).1 ((summable_nat_add_iff k).2 h).has_sum).unique h.has_sum

lemma tsum_eq_zero_add [t2_space α] {f : ℕ → α} (hf : summable f) :
  ∑'b, f b = f 0 + ∑'b, f (b + 1) :=
by simpa only [sum_range_one] using (sum_add_tsum_nat_add 1 hf).symm

/-- For `f : ℕ → α`, then `∑' k, f (k + i)` tends to zero. This does not require a summability
assumption on `f`, as otherwise all sums are zero. -/
lemma tendsto_sum_nat_add [t2_space α] (f : ℕ → α) : tendsto (λ i, ∑' k, f (k + i)) at_top (𝓝 0) :=
begin
  by_cases hf : summable f,
  { have h₀ : (λ i, (∑' i, f i) - ∑ j in range i, f j) = λ i, ∑' (k : ℕ), f (k + i),
    { ext1 i,
      rw [sub_eq_iff_eq_add, add_comm, sum_add_tsum_nat_add i hf] },
    have h₁ : tendsto (λ i : ℕ, ∑' i, f i) at_top (𝓝 (∑' i, f i)) := tendsto_const_nhds,
    simpa only [h₀, sub_self] using tendsto.sub h₁ hf.has_sum.tendsto_sum_nat },
  { convert tendsto_const_nhds,
    ext1 i,
    rw ← summable_nat_add_iff i at hf,
    { exact tsum_eq_zero_of_not_summable hf },
    { apply_instance } }
end

end subtype

end topological_group

section topological_semiring
variables [semiring α] [topological_space α] [topological_semiring α]
variables {f g : β → α} {a a₁ a₂ : α}
lemma has_sum.mul_left (a₂) (h : has_sum f a₁) : has_sum (λb, a₂ * f b) (a₂ * a₁) :=
by simpa only using h.map (add_monoid_hom.mul_left a₂) (continuous_const.mul continuous_id)

lemma has_sum.mul_right (a₂) (hf : has_sum f a₁) : has_sum (λb, f b * a₂) (a₁ * a₂) :=
by simpa only using hf.map (add_monoid_hom.mul_right a₂) (continuous_id.mul continuous_const)

lemma summable.mul_left (a) (hf : summable f) : summable (λb, a * f b) :=
(hf.has_sum.mul_left _).summable

lemma summable.mul_right (a) (hf : summable f) : summable (λb, f b * a) :=
(hf.has_sum.mul_right _).summable

section tsum
variables [t2_space α]

lemma summable.tsum_mul_left (a) (hf : summable f) : ∑'b, a * f b = a * ∑'b, f b :=
(hf.has_sum.mul_left _).tsum_eq

lemma summable.tsum_mul_right (a) (hf : summable f) : (∑'b, f b * a) = (∑'b, f b) * a :=
(hf.has_sum.mul_right _).tsum_eq

end tsum

end topological_semiring

section has_continuous_smul
variables {R : Type*}
[semiring R] [topological_space R]
[topological_space α] [add_comm_monoid α]
[module R α] [has_continuous_smul R α]
{f : β → α}

lemma has_sum.smul {a : α} {r : R} (hf : has_sum f a) : has_sum (λ z, r • f z) (r • a) :=
hf.map (const_smul_hom α r) (continuous_const.smul continuous_id)

lemma summable.smul {r : R} (hf : summable f) : summable (λ z, r • f z) :=
hf.has_sum.smul.summable

lemma tsum_smul [t2_space α] {r : R} (hf : summable f) : ∑' z, r • f z = r • ∑' z, f z :=
hf.has_sum.smul.tsum_eq

end has_continuous_smul

section division_ring

variables [division_ring α] [topological_space α] [topological_semiring α]
{f g : β → α} {a a₁ a₂ : α}

lemma has_sum.div_const (h : has_sum f a) (b : α) : has_sum (λ x, f x / b) (a / b) :=
by simp only [div_eq_mul_inv, h.mul_right b⁻¹]

lemma has_sum_mul_left_iff (h : a₂ ≠ 0) : has_sum f a₁ ↔ has_sum (λb, a₂ * f b) (a₂ * a₁) :=
⟨has_sum.mul_left _, λ H, by simpa only [inv_mul_cancel_left' h] using H.mul_left a₂⁻¹⟩

lemma has_sum_mul_right_iff (h : a₂ ≠ 0) : has_sum f a₁ ↔ has_sum (λb, f b * a₂) (a₁ * a₂) :=
⟨has_sum.mul_right _, λ H, by simpa only [mul_inv_cancel_right' h] using H.mul_right a₂⁻¹⟩

lemma summable_mul_left_iff (h : a ≠ 0) : summable f ↔ summable (λb, a * f b) :=
⟨λ H, H.mul_left _, λ H, by simpa only [inv_mul_cancel_left' h] using H.mul_left a⁻¹⟩

lemma summable_mul_right_iff (h : a ≠ 0) : summable f ↔ summable (λb, f b * a) :=
⟨λ H, H.mul_right _, λ H, by simpa only [mul_inv_cancel_right' h] using H.mul_right a⁻¹⟩

lemma tsum_mul_left [t2_space α] : (∑' x, a * f x) = a * ∑' x, f x :=
if hf : summable f then hf.tsum_mul_left a
else if ha : a = 0 then by simp [ha]
else by rw [tsum_eq_zero_of_not_summable hf,
  tsum_eq_zero_of_not_summable (mt (summable_mul_left_iff ha).2 hf), mul_zero]

lemma tsum_mul_right [t2_space α] : (∑' x, f x * a) = (∑' x, f x) * a :=
if hf : summable f then hf.tsum_mul_right a
else if ha : a = 0 then by simp [ha]
else by rw [tsum_eq_zero_of_not_summable hf,
  tsum_eq_zero_of_not_summable (mt (summable_mul_right_iff ha).2 hf), zero_mul]

end division_ring

section order_topology
variables [ordered_add_comm_monoid α] [topological_space α] [order_closed_topology α]
variables {f g : β → α} {a a₁ a₂ : α}

lemma has_sum_le (h : ∀b, f b ≤ g b) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
le_of_tendsto_of_tendsto' hf hg $ assume s, sum_le_sum $ assume b _, h b

@[mono] lemma has_sum_mono (hf : has_sum f a₁) (hg : has_sum g a₂) (h : f ≤ g) : a₁ ≤ a₂ :=
has_sum_le h hf hg

lemma has_sum_le_of_sum_le (hf : has_sum f a) (h : ∀ s : finset β, ∑ b in s, f b ≤ a₂) :
  a ≤ a₂ :=
le_of_tendsto' hf h

lemma le_has_sum_of_le_sum (hf : has_sum f a) (h : ∀ s : finset β, a₂ ≤ ∑ b in s, f b) :
  a₂ ≤ a :=
ge_of_tendsto' hf h

lemma has_sum_le_inj {g : γ → α} (i : β → γ) (hi : injective i) (hs : ∀c∉set.range i, 0 ≤ g c)
  (h : ∀b, f b ≤ g (i b)) (hf : has_sum f a₁) (hg : has_sum g a₂) : a₁ ≤ a₂ :=
have has_sum (λc, (partial_inv i c).cases_on' 0 f) a₁,
begin
  refine (has_sum_iff_has_sum_of_ne_zero_bij (i ∘ coe) _ _ _).2 hf,
  { exact assume c₁ c₂ eq, hi eq },
  { intros c hc,
    rw [mem_support] at hc,
    cases eq : partial_inv i c with b; rw eq at hc,
    { contradiction },
    { rw [partial_inv_of_injective hi] at eq,
      exact ⟨⟨b, hc⟩, eq⟩ } },
  { assume c, simp [partial_inv_left hi, option.cases_on'] }
end,
begin
  refine has_sum_le (assume c, _) this hg,
  by_cases c ∈ set.range i,
  { rcases h with ⟨b, rfl⟩,
    rw [partial_inv_left hi, option.cases_on'],
    exact h _ },
  { have : partial_inv i c = none := dif_neg h,
    rw [this, option.cases_on'],
    exact hs _ h }
end

lemma tsum_le_tsum_of_inj {g : γ → α} (i : β → γ) (hi : injective i) (hs : ∀c∉set.range i, 0 ≤ g c)
  (h : ∀b, f b ≤ g (i b)) (hf : summable f) (hg : summable g) : tsum f ≤ tsum g :=
has_sum_le_inj i hi hs h hf.has_sum hg.has_sum

lemma sum_le_has_sum (s : finset β) (hs : ∀ b∉s, 0 ≤ f b) (hf : has_sum f a) :
  ∑ b in s, f b ≤ a :=
ge_of_tendsto hf (eventually_at_top.2 ⟨s, λ t hst,
  sum_le_sum_of_subset_of_nonneg hst $ λ b hbt hbs, hs b hbs⟩)

lemma is_lub_has_sum (h : ∀ b, 0 ≤ f b) (hf : has_sum f a) :
  is_lub (set.range (λ s : finset β, ∑ b in s, f b)) a :=
is_lub_of_tendsto (finset.sum_mono_set_of_nonneg h) hf

lemma le_has_sum (hf : has_sum f a) (b : β) (hb : ∀ b' ≠ b, 0 ≤ f b') : f b ≤ a :=
calc f b = ∑ b in {b}, f b : finset.sum_singleton.symm
... ≤ a : sum_le_has_sum _ (by { convert hb, simp }) hf

lemma sum_le_tsum {f : β → α} (s : finset β) (hs : ∀ b∉s, 0 ≤ f b) (hf : summable f) :
  ∑ b in s, f b ≤ ∑' b, f b :=
sum_le_has_sum s hs hf.has_sum

lemma le_tsum (hf : summable f) (b : β) (hb : ∀ b' ≠ b, 0 ≤ f b') : f b ≤ ∑' b, f b :=
le_has_sum (summable.has_sum hf) b hb

lemma tsum_le_tsum (h : ∀b, f b ≤ g b) (hf : summable f) (hg : summable g) : ∑'b, f b ≤ ∑'b, g b :=
has_sum_le h hf.has_sum hg.has_sum

@[mono] lemma tsum_mono (hf : summable f) (hg : summable g) (h : f ≤ g) :
  ∑' n, f n ≤ ∑' n, g n :=
tsum_le_tsum h hf hg

lemma tsum_le_of_sum_le (hf : summable f) (h : ∀ s : finset β, ∑ b in s, f b ≤ a₂) :
  ∑' b, f b ≤ a₂ :=
has_sum_le_of_sum_le hf.has_sum h

lemma tsum_le_of_sum_le' (ha₂ : 0 ≤ a₂) (h : ∀ s : finset β, ∑ b in s, f b ≤ a₂) :
  ∑' b, f b ≤ a₂ :=
begin
  by_cases hf : summable f,
  { exact tsum_le_of_sum_le hf h },
  { rw tsum_eq_zero_of_not_summable hf,
    exact ha₂ }
end

lemma has_sum.nonneg (h : ∀ b, 0 ≤ g b) (ha : has_sum g a) : 0 ≤ a :=
has_sum_le h has_sum_zero ha

lemma has_sum.nonpos (h : ∀ b, g b ≤ 0) (ha : has_sum g a) : a ≤ 0 :=
has_sum_le h ha has_sum_zero

lemma tsum_nonneg (h : ∀ b, 0 ≤ g b) : 0 ≤ ∑'b, g b :=
begin
  by_cases hg : summable g,
  { exact hg.has_sum.nonneg h },
  { simp [tsum_eq_zero_of_not_summable hg] }
end

lemma tsum_nonpos (h : ∀ b, f b ≤ 0) : ∑'b, f b ≤ 0 :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.nonpos h },
  { simp [tsum_eq_zero_of_not_summable hf] }
end

end order_topology

section ordered_topological_group

variables [ordered_add_comm_group α] [topological_space α] [topological_add_group α]
  [order_closed_topology α] {f g : β → α} {a₁ a₂ : α}

lemma has_sum_lt {i : β} (h : ∀ (b : β), f b ≤ g b) (hi : f i < g i)
  (hf : has_sum f a₁) (hg : has_sum g a₂) :
  a₁ < a₂ :=
have update f i 0 ≤ update g i 0 := update_le_update_iff.mpr ⟨rfl.le, λ i _, h i⟩,
have 0 - f i + a₁ ≤ 0 - g i + a₂ := has_sum_le this (hf.update i 0) (hg.update i 0),
by simpa only [zero_sub, add_neg_cancel_left] using add_lt_add_of_lt_of_le hi this

@[mono] lemma has_sum_strict_mono (hf : has_sum f a₁) (hg : has_sum g a₂) (h : f < g) : a₁ < a₂ :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in has_sum_lt hle hi hf hg

lemma tsum_lt_tsum {i : β} (h : ∀ (b : β), f b ≤ g b) (hi : f i < g i)
  (hf : summable f) (hg : summable g) :
  ∑' n, f n < ∑' n, g n :=
has_sum_lt h hi hf.has_sum hg.has_sum

@[mono] lemma tsum_strict_mono (hf : summable f) (hg : summable g) (h : f < g) :
  ∑' n, f n < ∑' n, g n :=
let ⟨hle, i, hi⟩ := pi.lt_def.mp h in tsum_lt_tsum hle hi hf hg

lemma tsum_pos (hsum : summable g) (hg : ∀ b, 0 ≤ g b) (i : β) (hi : 0 < g i) :
  0 < ∑' b, g b :=
by { rw ← tsum_zero, exact tsum_lt_tsum hg hi summable_zero hsum }

end ordered_topological_group

section canonically_ordered
variables [canonically_ordered_add_monoid α] [topological_space α] [order_closed_topology α]
variables {f : β → α} {a : α}

lemma le_has_sum' (hf : has_sum f a) (b : β) : f b ≤ a :=
le_has_sum hf b $ λ _ _, zero_le _

lemma le_tsum' (hf : summable f) (b : β) : f b ≤ ∑' b, f b :=
le_tsum hf b $ λ _ _, zero_le _

lemma has_sum_zero_iff : has_sum f 0 ↔ ∀ x, f x = 0 :=
begin
  refine ⟨_, λ h, _⟩,
  { contrapose!,
    exact λ ⟨x, hx⟩ h, irrefl _ (lt_of_lt_of_le (pos_iff_ne_zero.2 hx) (le_has_sum' h x)) },
  { convert has_sum_zero,
    exact funext h }
end

lemma tsum_eq_zero_iff (hf : summable f) : ∑' i, f i = 0 ↔ ∀ x, f x = 0 :=
by rw [←has_sum_zero_iff, hf.has_sum_iff]

lemma tsum_ne_zero_iff (hf : summable f) : ∑' i, f i ≠ 0 ↔ ∃ x, f x ≠ 0 :=
by rw [ne.def, tsum_eq_zero_iff hf, not_forall]

lemma is_lub_has_sum' (hf : has_sum f a) : is_lub (set.range (λ s : finset β, ∑ b in s, f b)) a :=
is_lub_of_tendsto (finset.sum_mono_set f) hf

end canonically_ordered

section uniform_group

variables [add_comm_group α] [uniform_space α]

lemma summable_iff_cauchy_seq_finset [complete_space α] {f : β → α} :
  summable f ↔ cauchy_seq (λ (s : finset β), ∑ b in s, f b) :=
cauchy_map_iff_exists_tendsto.symm

variables [uniform_add_group α] {f g : β → α} {a a₁ a₂ : α}

lemma cauchy_seq_finset_iff_vanishing :
  cauchy_seq (λ (s : finset β), ∑ b in s, f b)
  ↔ ∀ e ∈ 𝓝 (0:α), (∃s:finset β, ∀t, disjoint t s → ∑ b in t, f b ∈ e) :=
begin
  simp only [cauchy_seq, cauchy_map_iff, and_iff_right at_top_ne_bot,
    prod_at_top_at_top_eq, uniformity_eq_comap_nhds_zero α, tendsto_comap_iff, (∘)],
  rw [tendsto_at_top'],
  split,
  { assume h e he,
    rcases h e he with ⟨⟨s₁, s₂⟩, h⟩,
    use [s₁ ∪ s₂],
    assume t ht,
    specialize h (s₁ ∪ s₂, (s₁ ∪ s₂) ∪ t) ⟨le_sup_left, le_sup_of_le_left le_sup_right⟩,
    simpa only [finset.sum_union ht.symm, add_sub_cancel'] using h },
  { assume h e he,
    rcases exists_nhds_half_neg he with ⟨d, hd, hde⟩,
    rcases h d hd with ⟨s, h⟩,
    use [(s, s)],
    rintros ⟨t₁, t₂⟩ ⟨ht₁, ht₂⟩,
    have : ∑ b in t₂, f b - ∑ b in t₁, f b = ∑ b in t₂ \ s, f b - ∑ b in t₁ \ s, f b,
    { simp only [(finset.sum_sdiff ht₁).symm, (finset.sum_sdiff ht₂).symm,
        add_sub_add_right_eq_sub] },
    simp only [this],
    exact hde _ (h _ finset.sdiff_disjoint) _ (h _ finset.sdiff_disjoint) }
end

variable [complete_space α]

lemma summable_iff_vanishing :
  summable f ↔ ∀ e ∈ 𝓝 (0:α), (∃s:finset β, ∀t, disjoint t s → ∑ b in t, f b ∈ e) :=
by rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing]

/- TODO: generalize to monoid with a uniform continuous subtraction operator: `(a + b) - b = a` -/
lemma summable.summable_of_eq_zero_or_self (hf : summable f) (h : ∀b, g b = 0 ∨ g b = f b) :
  summable g :=
summable_iff_vanishing.2 $
  assume e he,
  let ⟨s, hs⟩ := summable_iff_vanishing.1 hf e he in
  ⟨s, assume t ht,
    have eq : ∑ b in t.filter (λb, g b = f b), f b = ∑ b in t, g b :=
      calc ∑ b in t.filter (λb, g b = f b), f b = ∑ b in t.filter (λb, g b = f b), g b :
          finset.sum_congr rfl (assume b hb, (finset.mem_filter.1 hb).2.symm)
        ... = ∑ b in t, g b :
        begin
          refine finset.sum_subset (finset.filter_subset _ _) _,
          assume b hbt hb,
          simp only [(∉), finset.mem_filter, and_iff_right hbt] at hb,
          exact (h b).resolve_right hb
        end,
    eq ▸ hs _ $ finset.disjoint_of_subset_left (finset.filter_subset _ _) ht⟩

protected lemma summable.indicator (hf : summable f) (s : set β) :
  summable (s.indicator f) :=
hf.summable_of_eq_zero_or_self $ set.indicator_eq_zero_or_self _ _

lemma summable.comp_injective {i : γ → β} (hf : summable f) (hi : injective i) :
  summable (f ∘ i) :=
begin
  simpa only [set.indicator_range_comp]
    using (hi.summable_iff _).2 (hf.indicator (set.range i)),
  exact λ x hx, set.indicator_of_not_mem hx _
end

lemma summable.subtype (hf : summable f) (s : set β) : summable (f ∘ coe : s → α) :=
hf.comp_injective subtype.coe_injective

lemma summable_subtype_and_compl {s : set β} :
  summable (λ x : s, f x) ∧ summable (λ x : sᶜ, f x) ↔ summable f :=
⟨and_imp.2 summable.add_compl, λ h, ⟨h.subtype s, h.subtype sᶜ⟩⟩

lemma summable.sigma_factor {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) (b : β) : summable (λc, f ⟨b, c⟩) :=
ha.comp_injective sigma_mk_injective

lemma summable.sigma [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) : summable (λb, ∑'c, f ⟨b, c⟩) :=
ha.sigma' (λ b, ha.sigma_factor b)

lemma summable.prod_factor {f : β × γ → α} (h : summable f) (b : β) :
  summable (λ c, f (b, c)) :=
h.comp_injective $ λ c₁ c₂ h, (prod.ext_iff.1 h).2

lemma tsum_sigma [regular_space α] {γ : β → Type*} {f : (Σb:β, γ b) → α}
  (ha : summable f) : ∑'p, f p = ∑'b c, f ⟨b, c⟩ :=
tsum_sigma' (λ b, ha.sigma_factor b) ha

lemma tsum_prod [regular_space α] {f : β × γ → α} (h : summable f) :
  ∑'p, f p = ∑'b c, f ⟨b, c⟩ :=
tsum_prod' h h.prod_factor

lemma tsum_comm [regular_space α] {f : β → γ → α} (h : summable (function.uncurry f)) :
  ∑' c b, f b c = ∑' b c, f b c :=
tsum_comm' h h.prod_factor h.prod_symm.prod_factor

end uniform_group

section topological_group

variables {G : Type*} [topological_space G] [add_comm_group G] [topological_add_group G]
  {f : α → G}

lemma summable.vanishing (hf : summable f) ⦃e : set G⦄ (he : e ∈ 𝓝 (0 : G)) :
  ∃ s : finset α, ∀ t, disjoint t s → ∑ k in t, f k ∈ e :=
begin
  letI : uniform_space G := topological_add_group.to_uniform_space G,
  letI : uniform_add_group G := topological_add_group_is_uniform,
  rcases hf with ⟨y, hy⟩,
  exact cauchy_seq_finset_iff_vanishing.1 hy.cauchy_seq e he
end

/-- Series divergence test: if `f` is a convergent series, then `f x` tends to zero along
`cofinite`. -/
lemma summable.tendsto_cofinite_zero (hf : summable f) : tendsto f cofinite (𝓝 0) :=
begin
  intros e he,
  rw [filter.mem_map],
  rcases hf.vanishing he with ⟨s, hs⟩,
  refine s.eventually_cofinite_nmem.mono (λ x hx, _),
  by simpa using hs {x} (singleton_disjoint.2 hx)
end

lemma summable.tendsto_at_top_zero {f : ℕ → G} (hf : summable f) : tendsto f at_top (𝓝 0) :=
by { rw ←nat.cofinite_eq_at_top, exact hf.tendsto_cofinite_zero }

end topological_group

section linear_order

/-! For infinite sums taking values in a linearly ordered monoid, the existence of a least upper
bound for the finite sums is a criterion for summability.

This criterion is useful when applied in a linearly ordered monoid which is also a complete or
conditionally complete linear order, such as `ℝ`, `ℝ≥0`, `ℝ≥0∞`, because it is then easy to check
the existence of a least upper bound.
-/

lemma has_sum_of_is_lub_of_nonneg [linear_ordered_add_comm_monoid β] [topological_space β]
  [order_topology β] {f : α → β} (b : β) (h : ∀ b, 0 ≤ f b)
  (hf : is_lub (set.range (λ s, ∑ a in s, f a)) b) :
  has_sum f b :=
tendsto_at_top_is_lub (finset.sum_mono_set_of_nonneg h) hf

lemma has_sum_of_is_lub [canonically_linear_ordered_add_monoid β] [topological_space β]
   [order_topology β] {f : α → β} (b : β) (hf : is_lub (set.range (λ s, ∑ a in s, f a)) b) :
  has_sum f b :=
tendsto_at_top_is_lub (finset.sum_mono_set f) hf

lemma summable_abs_iff [linear_ordered_add_comm_group β] [uniform_space β]
  [uniform_add_group β] [complete_space β] {f : α → β} :
  summable (λ x, abs (f x)) ↔ summable f :=
have h1 : ∀ x : {x | 0 ≤ f x}, abs (f x) = f x := λ x, abs_of_nonneg x.2,
have h2 : ∀ x : {x | 0 ≤ f x}ᶜ, abs (f x) = -f x := λ x, abs_of_neg (not_le.1 x.2),
calc summable (λ x, abs (f x)) ↔
  summable (λ x : {x | 0 ≤ f x}, abs (f x)) ∧ summable (λ x : {x | 0 ≤ f x}ᶜ, abs (f x)) :
  summable_subtype_and_compl.symm
... ↔ summable (λ x : {x | 0 ≤ f x}, f x) ∧ summable (λ x : {x | 0 ≤ f x}ᶜ, -f x) :
  by simp only [h1, h2]
... ↔ _ : by simp only [summable_neg_iff, summable_subtype_and_compl]

alias summable_abs_iff ↔ summable.of_abs summable.abs

end linear_order

section cauchy_seq
open finset.Ico filter

/-- If the extended distance between consecutive points of a sequence is estimated
by a summable series of `nnreal`s, then the original sequence is a Cauchy sequence. -/
lemma cauchy_seq_of_edist_le_of_summable [pseudo_emetric_space α] {f : ℕ → α} (d : ℕ → ℝ≥0)
  (hf : ∀ n, edist (f n) (f n.succ) ≤ d n) (hd : summable d) : cauchy_seq f :=
begin
  refine emetric.cauchy_seq_iff_nnreal.2 (λ ε εpos, _),
  -- Actually we need partial sums of `d` to be a Cauchy sequence
  replace hd : cauchy_seq (λ (n : ℕ), ∑ x in range n, d x) :=
    let ⟨_, H⟩ := hd in H.tendsto_sum_nat.cauchy_seq,
  -- Now we take the same `N` as in one of the definitions of a Cauchy sequence
  refine (metric.cauchy_seq_iff'.1 hd ε (nnreal.coe_pos.2 εpos)).imp (λ N hN n hn, _),
  have hsum := hN n hn,
  -- We simplify the known inequality
  rw [dist_nndist, nnreal.nndist_eq, ← sum_range_add_sum_Ico _ hn, nnreal.add_sub_cancel'] at hsum,
  norm_cast at hsum,
  replace hsum := lt_of_le_of_lt (le_max_left _ _) hsum,
  rw edist_comm,

  -- Then use `hf` to simplify the goal to the same form
  apply lt_of_le_of_lt (edist_le_Ico_sum_of_edist_le hn (λ k _ _, hf k)),
  assumption_mod_cast
end

/-- If the distance between consecutive points of a sequence is estimated by a summable series,
then the original sequence is a Cauchy sequence. -/
lemma cauchy_seq_of_dist_le_of_summable [pseudo_metric_space α] {f : ℕ → α} (d : ℕ → ℝ)
  (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : summable d) : cauchy_seq f :=
begin
  refine metric.cauchy_seq_iff'.2 (λε εpos, _),
  replace hd : cauchy_seq (λ (n : ℕ), ∑ x in range n, d x) :=
    let ⟨_, H⟩ := hd in H.tendsto_sum_nat.cauchy_seq,
  refine (metric.cauchy_seq_iff'.1 hd ε εpos).imp (λ N hN n hn, _),
  have hsum := hN n hn,
  rw [real.dist_eq, ← sum_Ico_eq_sub _ hn] at hsum,
  calc dist (f n) (f N) = dist (f N) (f n) : dist_comm _ _
  ... ≤ ∑ x in Ico N n, d x : dist_le_Ico_sum_of_dist_le hn (λ k _ _, hf k)
  ... ≤ abs (∑ x in Ico N n, d x) : le_abs_self _
  ... < ε : hsum
end

lemma cauchy_seq_of_summable_dist [pseudo_metric_space α] {f : ℕ → α}
  (h : summable (λn, dist (f n) (f n.succ))) : cauchy_seq f :=
cauchy_seq_of_dist_le_of_summable _ (λ _, le_refl _) h

lemma dist_le_tsum_of_dist_le_of_tendsto [pseudo_metric_space α] {f : ℕ → α} (d : ℕ → ℝ)
  (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : summable d) {a : α} (ha : tendsto f at_top (𝓝 a))
  (n : ℕ) :
  dist (f n) a ≤ ∑' m, d (n + m) :=
begin
  refine le_of_tendsto (tendsto_const_nhds.dist ha)
    (eventually_at_top.2 ⟨n, λ m hnm, _⟩),
  refine le_trans (dist_le_Ico_sum_of_dist_le hnm (λ k _ _, hf k)) _,
  rw [sum_Ico_eq_sum_range],
  refine sum_le_tsum (range _) (λ _ _, le_trans dist_nonneg (hf _)) _,
  exact hd.comp_injective (add_right_injective n)
end

lemma dist_le_tsum_of_dist_le_of_tendsto₀ [pseudo_metric_space α] {f : ℕ → α} (d : ℕ → ℝ)
  (hf : ∀ n, dist (f n) (f n.succ) ≤ d n) (hd : summable d) {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ tsum d :=
by simpa only [zero_add] using dist_le_tsum_of_dist_le_of_tendsto d hf hd ha 0

lemma dist_le_tsum_dist_of_tendsto [pseudo_metric_space α] {f : ℕ → α}
  (h : summable (λn, dist (f n) (f n.succ))) {a : α} (ha : tendsto f at_top (𝓝 a)) (n) :
  dist (f n) a ≤ ∑' m, dist (f (n+m)) (f (n+m).succ) :=
show dist (f n) a ≤ ∑' m, (λx, dist (f x) (f x.succ)) (n + m), from
dist_le_tsum_of_dist_le_of_tendsto (λ n, dist (f n) (f n.succ)) (λ _, le_refl _) h ha n

lemma dist_le_tsum_dist_of_tendsto₀ [pseudo_metric_space α] {f : ℕ → α}
  (h : summable (λn, dist (f n) (f n.succ))) {a : α} (ha : tendsto f at_top (𝓝 a)) :
  dist (f 0) a ≤ ∑' n, dist (f n) (f n.succ) :=
by simpa only [zero_add] using dist_le_tsum_dist_of_tendsto h ha 0

end cauchy_seq
