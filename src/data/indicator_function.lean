/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import group_theory.group_action
import data.support

/-!
# Indicator function

`indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.

## Implementation note

In mathematics, an indicator function or a characteristic function is a function used to indicate
membership of an element in a set `s`, having the value `1` for all elements of `s` and the value `0`
otherwise. But since it is usually used to restrict a function to a certain set `s`, we let the
indicator function take the value `f x` for some function `f`, instead of `1`. If the usual indicator
function is needed, just set `f` to be the constant function `λx, 1`.

## Tags
indicator, characteristic
-/

noncomputable theory
open_locale classical big_operators
open function

variables {α α' β γ : Type*}

namespace set

section has_zero
variables [has_zero β] {s t : set α} {f g : α → β} {a : α}

/-- `indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.  -/
@[reducible]
def indicator (s : set α) (f : α → β) : α → β := λ x, if x ∈ s then f x else 0

@[simp] lemma piecewise_eq_indicator {s : set α} : s.piecewise f 0 = s.indicator f := rfl

lemma indicator_apply (s : set α) (f : α → β) (a : α) :
  indicator s f a = if a ∈ s then f a else 0 := rfl

@[simp] lemma indicator_of_mem (h : a ∈ s) (f : α → β) : indicator s f a = f a := if_pos h

@[simp] lemma indicator_of_not_mem (h : a ∉ s) (f : α → β) : indicator s f a = 0 := if_neg h

lemma indicator_eq_zero_or_self (s : set α) (f : α → β) (a : α) :
  indicator s f a = 0 ∨ indicator s f a = f a :=
if h : a ∈ s then or.inr (indicator_of_mem h f) else or.inl (indicator_of_not_mem h f)

/-- If an indicator function is nonzero at a point, that
point is in the set. -/
lemma mem_of_indicator_ne_zero (h : indicator s f a ≠ 0) : a ∈ s :=
not_imp_comm.1 (λ hn, indicator_of_not_mem hn f) h

lemma eq_on_indicator : eq_on (indicator s f) f s := λ x hx, indicator_of_mem hx f

lemma support_indicator : function.support (s.indicator f) ⊆ s :=
λ x hx, hx.imp_symm (λ h, indicator_of_not_mem h f)

@[simp] lemma indicator_apply_eq_self : s.indicator f a = f a ↔ (a ∉ s → f a = 0) :=
ite_eq_left_iff.trans $ by rw [@eq_comm _ (f a)]

@[simp] lemma indicator_eq_self : s.indicator f = f ↔ support f ⊆ s :=
by simp only [funext_iff, subset_def, mem_support, indicator_apply_eq_self, not_imp_comm]

@[simp] lemma indicator_support : (support f).indicator f = f :=
indicator_eq_self.2 $ subset.refl _

@[simp] lemma indicator_apply_eq_zero : indicator s f a = 0 ↔ (a ∈ s → f a = 0) :=
ite_eq_right_iff

@[simp] lemma indicator_eq_zero : indicator s f = (λ x, 0) ↔ disjoint (support f) s :=
by simp only [funext_iff, indicator_apply_eq_zero, set.disjoint_left, mem_support, not_imp_not]

@[simp] lemma indicator_eq_zero' : indicator s f = 0 ↔ disjoint (support f) s :=
indicator_eq_zero

@[simp] lemma indicator_range_comp {ι : Sort*} (f : ι → α) (g : α → β) :
  indicator (range f) g ∘ f = g ∘ f :=
piecewise_range_comp _ _ _

lemma indicator_congr (h : ∀ a ∈ s, f a = g a) : indicator s f = indicator s g :=
funext $ λx, by { simp only [indicator], split_ifs, { exact h _ h_1 }, refl }

@[simp] lemma indicator_univ (f : α → β) : indicator (univ : set α) f = f :=
indicator_eq_self.2 $ subset_univ _

@[simp] lemma indicator_empty (f : α → β) : indicator (∅ : set α) f = λa, 0 :=
indicator_eq_zero.2 $ disjoint_empty _

variable (β)

@[simp] lemma indicator_zero (s : set α) : indicator s (λx, (0:β)) = λx, (0:β) :=
indicator_eq_zero.2 $ by simp only [support_zero, empty_disjoint]

@[simp] lemma indicator_zero' {s : set α} : s.indicator (0 : α → β) = 0 :=
indicator_zero β s

variable {β}

lemma indicator_indicator (s t : set α) (f : α → β) :
  indicator s (indicator t f) = indicator (s ∩ t) f :=
funext $ λx, by { simp only [indicator], split_ifs, repeat {simp * at * {contextual := tt}} }

lemma comp_indicator (h : β → γ) (f : α → β) {s : set α} {x : α} :
  h (s.indicator f x) = s.piecewise (h ∘ f) (const α (h 0)) x :=
s.comp_piecewise h

lemma indicator_comp_right {s : set α} (f : γ → α) {g : α → β} {x : γ} :
  indicator (f ⁻¹' s) (g ∘ f) x = indicator s g (f x) :=
by { simp only [indicator], split_ifs; refl }

lemma indicator_comp_of_zero [has_zero γ] {g : β → γ} (hg : g 0 = 0) :
  indicator s (g ∘ f) = g ∘ (indicator s f) :=
begin
  funext,
  simp only [indicator],
  split_ifs; simp [*]
end

lemma indicator_preimage (s : set α) (f : α → β) (B : set β) :
  (indicator s f)⁻¹' B = s ∩ f ⁻¹' B ∪ sᶜ ∩ (λa:α, (0:β)) ⁻¹' B :=
piecewise_preimage s f 0 B

lemma indicator_preimage_of_not_mem (s : set α) (f : α → β) {t : set β} (ht : (0:β) ∉ t) :
  (indicator s f)⁻¹' t = s ∩ f ⁻¹' t :=
by simp [indicator_preimage, set.preimage_const_of_not_mem ht]

lemma mem_range_indicator {r : β} {s : set α} {f : α → β} :
  r ∈ range (indicator s f) ↔ (r = 0 ∧ s ≠ univ) ∨ (r ∈ f '' s) :=
by simp [indicator, ite_eq_iff, exists_or_distrib, eq_univ_iff_forall, and_comm, or_comm,
  @eq_comm _ r 0]

lemma indicator_rel_indicator {r : β → β → Prop} (h0 : r 0 0) (ha : a ∈ s → r (f a) (g a)) :
  r (indicator s f a) (indicator s g a) :=
by { simp only [indicator], split_ifs with has has, exacts [ha has, h0] }

/-- Consider a sum of `g i (f i)` over a `finset`.  Suppose `g` is a
function such as multiplication, which maps a second argument of 0 to
0.  (A typical use case would be a weighted sum of `f i * h i` or `f i
• h i`, where `f` gives the weights that are multiplied by some other
function `h`.)  Then if `f` is replaced by the corresponding indicator
function, the `finset` may be replaced by a possibly larger `finset`
without changing the value of the sum. -/
lemma sum_indicator_subset_of_eq_zero {γ : Type*} [add_comm_monoid γ] (f : α → β)
    (g : α → β → γ) {s₁ s₂ : finset α} (h : s₁ ⊆ s₂) (hg : ∀ a, g a 0 = 0) :
  ∑ i in s₁, g i (f i) = ∑ i in s₂, g i (indicator ↑s₁ f i) :=
begin
  rw ←finset.sum_subset h _,
  { apply finset.sum_congr rfl,
    intros i hi,
    congr,
    symmetry,
    exact indicator_of_mem hi _ },
  { refine λ i hi hn, _,
    convert hg i,
    exact indicator_of_not_mem hn _ }
end

/-- Summing an indicator function over a possibly larger `finset` is
the same as summing the original function over the original
`finset`. -/
lemma sum_indicator_subset {γ : Type*} [add_comm_monoid γ] (f : α → γ) {s₁ s₂ : finset α}
    (h : s₁ ⊆ s₂) : ∑ i in s₁, f i = ∑ i in s₂, indicator ↑s₁ f i :=
sum_indicator_subset_of_eq_zero _ (λ a b, b) h (λ _, rfl)

end has_zero

section add_monoid
variables [add_monoid β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_union_of_not_mem_inter (h : a ∉ s ∩ t) (f : α → β) :
  indicator (s ∪ t) f a = indicator s f a + indicator t f a :=
by { simp only [indicator], split_ifs, repeat {simp * at * {contextual := tt}} }

lemma indicator_union_of_disjoint (h : disjoint s t) (f : α → β) :
  indicator (s ∪ t) f = λa, indicator s f a + indicator t f a :=
funext $ λa, indicator_union_of_not_mem_inter
  (by { convert not_mem_empty a, have := disjoint.eq_bot h, assumption })
  _

lemma indicator_add (s : set α) (f g : α → β) :
  indicator s (λa, f a + g a) = λa, indicator s f a + indicator s g a :=
by { funext, simp only [indicator], split_ifs, { refl }, rw add_zero }

@[simp] lemma indicator_compl_add_self_apply (s : set α) (f : α → β) (a : α) :
  indicator sᶜ f a + indicator s f a = f a :=
classical.by_cases (λ ha : a ∈ s, by simp [ha]) (λ ha, by simp [ha])

@[simp] lemma indicator_compl_add_self (s : set α) (f : α → β) :
  indicator sᶜ f + indicator s f = f :=
funext $ indicator_compl_add_self_apply s f

@[simp] lemma indicator_self_add_compl_apply (s : set α) (f : α → β) (a : α) :
  indicator s f a + indicator sᶜ f a = f a :=
classical.by_cases (λ ha : a ∈ s, by simp [ha]) (λ ha, by simp [ha])

@[simp] lemma indicator_self_add_compl (s : set α) (f : α → β) :
  indicator s f + indicator sᶜ f = f :=
funext $ indicator_self_add_compl_apply s f

variables (β)
instance is_add_monoid_hom.indicator (s : set α) : is_add_monoid_hom (λf:α → β, indicator s f) :=
{ map_add := λ _ _, indicator_add _ _ _,
  map_zero := indicator_zero _ _ }

variables {β} {𝕜 : Type*} [monoid 𝕜] [distrib_mul_action 𝕜 β]

lemma indicator_smul (s : set α) (r : 𝕜) (f : α → β) :
  indicator s (λ (x : α), r • f x) = λ (x : α), r • indicator s f x :=
by { simp only [indicator], funext, split_ifs, refl, exact (smul_zero r).symm }

lemma indicator_add_eq_left {f g : α → β} (h : univ ⊆ f ⁻¹' {0} ∪ g ⁻¹' {0}) :
  (f ⁻¹' {0})ᶜ.indicator (f + g) = f :=
begin
  ext x, by_cases hx : x ∈ (f ⁻¹' {0})ᶜ,
  { have : g x = 0, { simp at hx, specialize h (mem_univ x), simpa [hx] using h },
    simp [hx, this] },
  { simp * at * }
end

lemma indicator_add_eq_right {f g : α → β} (h : univ ⊆ f ⁻¹' {0} ∪ g ⁻¹' {0}) :
  (g ⁻¹' {0})ᶜ.indicator (f + g) = g :=
begin
  ext x, by_cases hx : x ∈ (g ⁻¹' {0})ᶜ,
  { have : f x = 0, { simp at hx, specialize h (mem_univ x), simpa [hx] using h },
    simp [hx, this] },
  { simp * at * }
end

end add_monoid

section add_group
variables [add_group β] {s t : set α} {f g : α → β} {a : α}

variables (β)
instance is_add_group_hom.indicator (s : set α) : is_add_group_hom (λf:α → β, indicator s f) :=
{ .. is_add_monoid_hom.indicator β s }
variables {β}

lemma indicator_neg (s : set α) (f : α → β) : indicator s (λa, - f a) = λa, - indicator s f a :=
show indicator s (- f) = - indicator s f, from is_add_group_hom.map_neg _ _

lemma indicator_sub (s : set α) (f g : α → β) :
  indicator s (λa, f a - g a) = λa, indicator s f a - indicator s g a :=
show indicator s (f - g) = indicator s f - indicator s g, from is_add_group_hom.map_sub _ _ _

lemma indicator_compl (s : set α) (f : α → β) : indicator sᶜ f = f - indicator s f :=
eq_sub_of_add_eq $ s.indicator_compl_add_self f

lemma indicator_finset_sum {β} [add_comm_monoid β] {ι : Type*} (I : finset ι) (s : set α) (f : ι → α → β) :
  indicator s (∑ i in I, f i) = ∑ i in I, indicator s (f i) :=
begin
  convert (finset.sum_hom _ _).symm,
  split,
  exact indicator_zero _ _
end

lemma indicator_finset_bUnion {β} [add_comm_monoid β] {ι} (I : finset ι)
  (s : ι → set α) {f : α → β} : (∀ (i ∈ I) (j ∈ I), i ≠ j → s i ∩ s j = ∅) →
  indicator (⋃ i ∈ I, s i) f = λ a, ∑ i in I, indicator (s i) f a :=
begin
  refine finset.induction_on I _ _,
  assume h,
  { funext, simp },
  assume a I haI ih hI,
  funext,
  simp only [haI, finset.sum_insert, not_false_iff],
  rw [finset.bUnion_insert, indicator_union_of_not_mem_inter, ih _],
  { assume i hi j hj hij,
    exact hI i (finset.mem_insert_of_mem hi) j (finset.mem_insert_of_mem hj) hij },
  simp only [not_exists, exists_prop, mem_Union, mem_inter_eq, not_and],
  assume hx a' ha',
  have := hI a (finset.mem_insert_self _ _) a' (finset.mem_insert_of_mem ha') _,
  { assume h, have h := mem_inter hx h, rw this at h, exact not_mem_empty _ h },
  { assume h, rw h at haI, contradiction }
end

end add_group

section mul_zero_class
variables [mul_zero_class β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_mul (s : set α) (f g : α → β) :
  indicator s (λa, f a * g a) = λa, indicator s f a * indicator s g a :=
by { funext, simp only [indicator], split_ifs, { refl }, rw mul_zero }

lemma indicator_mul_left (s : set α) (f g : α → β) :
  indicator s (λa, f a * g a) a = indicator s f a * g a :=
by { simp only [indicator], split_ifs, { refl }, rw [zero_mul] }

lemma indicator_mul_right (s : set α) (f g : α → β) :
  indicator s (λa, f a * g a) a = f a * indicator s g a :=
by { simp only [indicator], split_ifs, { refl }, rw [mul_zero] }

end mul_zero_class

section monoid_with_zero

variables [monoid_with_zero β]

lemma indicator_prod_one {s : set α} {t : set α'}
  {x : α} {y : α'} : (s.prod t).indicator (1 : _ → β) (x, y) = s.indicator 1 x * t.indicator 1 y :=
by simp [indicator, ← ite_and]

end monoid_with_zero

section order
variables [has_zero β] [preorder β] {s t : set α} {f g : α → β} {a : α}

lemma indicator_nonneg' (h : a ∈ s → 0 ≤ f a) : 0 ≤ indicator s f a :=
by { rw indicator_apply, split_ifs with as, { exact h as }, refl }

lemma indicator_nonneg (h : ∀ a ∈ s, 0 ≤ f a) : ∀ a, 0 ≤ indicator s f a :=
λ a, indicator_nonneg' (h a)

lemma indicator_nonpos' (h : a ∈ s → f a ≤ 0) : indicator s f a ≤ 0 :=
by { rw indicator_apply, split_ifs with as, { exact h as }, refl }

lemma indicator_nonpos (h : ∀ a ∈ s, f a ≤ 0) : ∀ a, indicator s f a ≤ 0 :=
λ a, indicator_nonpos' (h a)

lemma indicator_le' (hfg : ∀ a ∈ s, f a ≤ g a) (hg : ∀ a ∉ s, 0 ≤ g a) :
  indicator s f ≤ g :=
λ a, if ha : a ∈ s then by simpa [ha] using hfg a ha else by simpa [ha] using hg a ha

@[mono] lemma indicator_le_indicator (h : f a ≤ g a) : indicator s f a ≤ indicator s g a :=
indicator_rel_indicator (le_refl _) (λ _, h)

lemma indicator_le_indicator_of_subset (h : s ⊆ t) (hf : ∀a, 0 ≤ f a) (a : α) :
  indicator s f a ≤ indicator t f a :=
begin
  simp only [indicator],
  split_ifs with h₁,
  { refl },
  { have := h h₁, contradiction },
  { exact hf a },
  { refl }
end

lemma indicator_le_self' (hf : ∀ x ∉ s, 0 ≤ f x) : indicator s f ≤ f :=
indicator_le' (λ _ _, le_refl _) hf

lemma indicator_le_self {β} [canonically_ordered_add_monoid β] (s : set α) (f : α → β) :
  indicator s f ≤ f :=
indicator_le_self' $ λ _ _, zero_le _

lemma indicator_le {β} [canonically_ordered_add_monoid β] {s : set α}
  {f g : α → β} (hfg : ∀ a ∈ s, f a ≤ g a) :
  indicator s f ≤ g :=
indicator_le' hfg $ λ _ _, zero_le _

lemma indicator_Union_apply {ι β} [complete_lattice β] [has_zero β] (h0 : (⊥:β) = 0)
  (s : ι → set α) (f : α → β) (x : α) :
  indicator (⋃ i, s i) f x = ⨆ i, indicator (s i) f x :=
begin
  by_cases hx : x ∈ ⋃ i, s i,
  { rw [indicator_of_mem hx],
    rw [mem_Union] at hx,
    refine le_antisymm _ (supr_le $ λ i, indicator_le_self' (λ x hx, h0 ▸ bot_le) x),
    rcases hx with ⟨i, hi⟩,
    exact le_supr_of_le i (ge_of_eq $ indicator_of_mem hi _) },
  { rw [indicator_of_not_mem hx],
    simp only [mem_Union, not_exists] at hx,
    simp [hx, ← h0] }
end

end order

end set

lemma add_monoid_hom.map_indicator {M N : Type*} [add_monoid M] [add_monoid N] (f : M →+ N)
  (s : set α) (g : α → M) (x : α) :
  f (s.indicator g x) = s.indicator (f ∘ g) x :=
congr_fun (set.indicator_comp_of_zero f.map_zero).symm x
