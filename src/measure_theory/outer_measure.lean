/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import analysis.specific_limits
import measure_theory.measurable_space

/-!
# Outer Measures

An outer measure is a function `μ : set α → ennreal`, from the powerset of a type to the extended
nonnegative real numbers that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is monotone;
3. `μ` is countably subadditive. This means that the outer measure of a countable union is at most
   the sum of the outer measure on the individual sets.

Note that we do not need `α` to be measurable to define an outer measure.

The outer measures on a type `α` form a complete lattice.

Given an arbitrary function `m : set α → ennreal` that sends `∅` to `0` we can define an outer
measure on `α` that on `s` is defined to be the infimum of `∑ᵢ, m (sᵢ)` for all collections of sets
`sᵢ` that cover `s`. This is the unique maximal outer measure that is at most the given function.
We also define this for functions `m` defined on a subset of `set α`, by treating the function as
having value `∞` outside its domain.

Given an outer measure `m`, the Carathéodory-measurable sets are the sets `s` such that
for all sets `t` we have `m t = m (t ∩ s) + m (t \ s)`. This forms a measurable space.

## Main definitions and statements

* `outer_measure.bounded_by` is the greatest outer measure that is at most the given function.
  If you know that the given functions sends `∅` to `0`, then `outer_measure.of_function` is a
  special case.
* `caratheodory` is the Carathéodory-measurable space of an outer measure.
* `Inf_eq_of_function_Inf_gen` is a characterization of the infimum of outer measures.
* `induced_outer_measure` is the measure induced by a function on a subset of `set α`

## References

* <https://en.wikipedia.org/wiki/Outer_measure>
* <https://en.wikipedia.org/wiki/Carath%C3%A9odory%27s_criterion>

## Tags

outer measure, Carathéodory-measurable, Carathéodory's criterion
-/

noncomputable theory

open set finset function filter encodable
open_locale classical big_operators nnreal topological_space

namespace measure_theory

/-- An outer measure is a countably subadditive monotone function that sends `∅` to `0`. -/
structure outer_measure (α : Type*) :=
(measure_of : set α → ennreal)
(empty : measure_of ∅ = 0)
(mono : ∀{s₁ s₂}, s₁ ⊆ s₂ → measure_of s₁ ≤ measure_of s₂)
(Union_nat : ∀(s:ℕ → set α), measure_of (⋃i, s i) ≤ ∑'i, measure_of (s i))

namespace outer_measure

section basic

variables {α : Type*} {β : Type*} {ms : set (outer_measure α)} {m : outer_measure α}

instance : has_coe_to_fun (outer_measure α) := ⟨_, λ m, m.measure_of⟩

@[simp] lemma measure_of_eq_coe (m : outer_measure α) : m.measure_of = m := rfl

@[simp] theorem empty' (m : outer_measure α) : m ∅ = 0 := m.empty

theorem mono' (m : outer_measure α) {s₁ s₂}
  (h : s₁ ⊆ s₂) : m s₁ ≤ m s₂ := m.mono h

protected theorem Union (m : outer_measure α)
  {β} [encodable β] (s : β → set α) :
  m (⋃i, s i) ≤ ∑'i, m (s i) :=
rel_supr_tsum m m.empty (≤) m.Union_nat s

lemma Union_null (m : outer_measure α)
  {β} [encodable β] {s : β → set α} (h : ∀ i, m (s i) = 0) : m (⋃i, s i) = 0 :=
by simpa [h] using m.Union s

protected lemma Union_finset (m : outer_measure α) (s : β → set α) (t : finset β) :
  m (⋃i ∈ t, s i) ≤ ∑ i in t, m (s i) :=
rel_supr_sum m m.empty (≤) m.Union_nat s t

protected lemma union (m : outer_measure α) (s₁ s₂ : set α) :
  m (s₁ ∪ s₂) ≤ m s₁ + m s₂ :=
rel_sup_add m m.empty (≤) m.Union_nat s₁ s₂

lemma le_inter_add_diff {m : outer_measure α} {t : set α} (s : set α) :
  m t ≤ m (t ∩ s) + m (t \ s) :=
by { convert m.union _ _, rw inter_union_diff t s }

lemma diff_null (m : outer_measure α) (s : set α) {t : set α} (ht : m t = 0) :
  m (s \ t) = m s :=
begin
  refine le_antisymm (m.mono $ diff_subset _ _) _,
  calc m s ≤ m (s ∩ t) + m (s \ t) : le_inter_add_diff _
       ... ≤ m t + m (s \ t)       : add_le_add_right (m.mono $ inter_subset_right _ _) _
       ... = m (s \ t)             : by rw [ht, zero_add]
end

lemma union_null (m : outer_measure α) {s₁ s₂ : set α}
  (h₁ : m s₁ = 0) (h₂ : m s₂ = 0) : m (s₁ ∪ s₂) = 0 :=
by simpa [h₁, h₂] using m.union s₁ s₂

lemma injective_coe_fn : injective (λ (μ : outer_measure α) (s : set α), μ s) :=
λ μ₁ μ₂ h, by { cases μ₁, cases μ₂, congr, exact h }

@[ext] lemma ext {μ₁ μ₂ : outer_measure α} (h : ∀ s, μ₁ s = μ₂ s) : μ₁ = μ₂ :=
injective_coe_fn $ funext h

instance : has_zero (outer_measure α) :=
⟨{ measure_of := λ_, 0,
   empty      := rfl,
   mono       := assume _ _ _, le_refl 0,
   Union_nat  := assume s, zero_le _ }⟩

@[simp] theorem coe_zero : ⇑(0 : outer_measure α) = 0 := rfl

instance : inhabited (outer_measure α) := ⟨0⟩

instance : has_add (outer_measure α) :=
⟨λm₁ m₂,
  { measure_of := λs, m₁ s + m₂ s,
    empty      := show m₁ ∅ + m₂ ∅ = 0, by simp [outer_measure.empty],
    mono       := assume s₁ s₂ h, add_le_add (m₁.mono h) (m₂.mono h),
    Union_nat  := assume s,
      calc m₁ (⋃i, s i) + m₂ (⋃i, s i) ≤
          (∑'i, m₁ (s i)) + (∑'i, m₂ (s i)) :
          add_le_add (m₁.Union_nat s) (m₂.Union_nat s)
        ... = _ : ennreal.tsum_add.symm}⟩

@[simp] theorem coe_add (m₁ m₂ : outer_measure α) : ⇑(m₁ + m₂) = m₁ + m₂ := rfl

theorem add_apply (m₁ m₂ : outer_measure α) (s : set α) : (m₁ + m₂) s = m₁ s + m₂ s := rfl

instance add_comm_monoid : add_comm_monoid (outer_measure α) :=
{ zero      := 0,
  add       := (+),
  .. injective.add_comm_monoid (show outer_measure α → set α → ennreal, from coe_fn)
    injective_coe_fn rfl (λ _ _, rfl) }

instance : has_scalar ennreal (outer_measure α) :=
⟨λ c m,
  { measure_of := λ s, c * m s,
    empty      := by simp,
    mono       := λ s t h, ennreal.mul_left_mono $ m.mono h,
    Union_nat  := λ s, by { rw [ennreal.tsum_mul_left], exact ennreal.mul_left_mono (m.Union _) } }⟩

@[simp] lemma coe_smul (c : ennreal) (m : outer_measure α) : ⇑(c • m) = c • m := rfl

lemma smul_apply (c : ennreal) (m : outer_measure α) (s : set α) : (c • m) s = c * m s := rfl

instance : semimodule ennreal (outer_measure α) :=
{ smul := (•),
  .. injective.semimodule ennreal ⟨show outer_measure α → set α → ennreal, from coe_fn, coe_zero,
    coe_add⟩ injective_coe_fn coe_smul }

instance : has_bot (outer_measure α) := ⟨0⟩

instance outer_measure.order_bot : order_bot (outer_measure α) :=
{ le          := λm₁ m₂, ∀s, m₁ s ≤ m₂ s,
  bot         := 0,
  le_refl     := assume a s, le_refl _,
  le_trans    := assume a b c hab hbc s, le_trans (hab s) (hbc s),
  le_antisymm := assume a b hab hba, ext $ assume s, le_antisymm (hab s) (hba s),
  bot_le      := assume a s, zero_le _ }

section supremum

instance : has_Sup (outer_measure α) :=
⟨λms, {
  measure_of := λs, ⨆ m ∈ ms, (m : outer_measure α) s,
  empty      := nonpos_iff_eq_zero.1 $ bsupr_le $ λ m h, le_of_eq m.empty,
  mono       := assume s₁ s₂ hs, bsupr_le_bsupr $ assume m hm, m.mono hs,
  Union_nat  := assume f, bsupr_le $ assume m hm,
    calc m (⋃i, f i) ≤ ∑' (i : ℕ), m (f i) : m.Union_nat _
      ... ≤ ∑'i, (⨆ m ∈ ms, (m : outer_measure α) (f i)) :
        ennreal.tsum_le_tsum $ assume i, le_bsupr m hm }⟩

instance : complete_lattice (outer_measure α) :=
{ .. outer_measure.order_bot, .. complete_lattice_of_Sup (outer_measure α)
    (λ ms, ⟨λ m hm s, le_bsupr m hm, λ m hm s, bsupr_le (λ m' hm', hm hm' s)⟩) }

@[simp] theorem Sup_apply (ms : set (outer_measure α)) (s : set α) :
  (Sup ms) s = ⨆ m ∈ ms, (m : outer_measure α) s := rfl

@[simp] theorem supr_apply {ι} (f : ι → outer_measure α) (s : set α) :
  (⨆ i : ι, f i) s = ⨆ i, f i s :=
by rw [supr, Sup_apply, supr_range, supr]

@[norm_cast] theorem coe_supr {ι} (f : ι → outer_measure α) :
  ⇑(⨆ i, f i) = ⨆ i, f i :=
funext $ λ s, by rw [supr_apply, _root_.supr_apply]

@[simp] theorem sup_apply (m₁ m₂ : outer_measure α) (s : set α) :
  (m₁ ⊔ m₂) s = m₁ s ⊔ m₂ s :=
by have := supr_apply (λ b, cond b m₁ m₂) s;
  rwa [supr_bool_eq, supr_bool_eq] at this

end supremum

/-- The pushforward of `m` along `f`. The outer measure on `s` is defined to be `m (f ⁻¹' s)`. -/
def map {β} (f : α → β) : outer_measure α →ₗ[ennreal] outer_measure β :=
{ to_fun := λ m,
    { measure_of := λs, m (f ⁻¹' s),
      empty := m.empty,
      mono := λ s t h, m.mono (preimage_mono h),
      Union_nat := λ s, by rw [preimage_Union]; exact
        m.Union_nat (λ i, f ⁻¹' s i) },
  map_add' := λ m₁ m₂, injective_coe_fn rfl,
  map_smul' := λ c m, injective_coe_fn rfl }

@[simp] theorem map_apply {β} (f : α → β)
  (m : outer_measure α) (s : set β) : map f m s = m (f ⁻¹' s) := rfl

@[simp] theorem map_id (m : outer_measure α) : map id m = m :=
ext $ λ s, rfl

@[simp] theorem map_map {β γ} (f : α → β) (g : β → γ)
  (m : outer_measure α) : map g (map f m) = map (g ∘ f) m :=
ext $ λ s, rfl

instance : functor outer_measure := {map := λ α β f, map f}

instance : is_lawful_functor outer_measure :=
{ id_map := λ α, map_id,
  comp_map := λ α β γ f g m, (map_map f g m).symm }

/-- The dirac outer measure. -/
def dirac (a : α) : outer_measure α :=
{ measure_of := λs, indicator s (λ _, 1) a,
  empty := by simp,
  mono := λ s t h, indicator_le_indicator_of_subset h (λ _, zero_le _) a,
  Union_nat := λ s,
    if hs : a ∈ ⋃ n, s n then let ⟨i, hi⟩ := mem_Union.1 hs in
      calc indicator (⋃ n, s n) (λ _, (1 : ennreal)) a = 1 : indicator_of_mem hs _
      ... = indicator (s i) (λ _, 1) a : (indicator_of_mem hi _).symm
      ... ≤ ∑' n, indicator (s n) (λ _, 1) a : ennreal.le_tsum _
    else by simp only [indicator_of_not_mem hs, zero_le]}

@[simp] theorem dirac_apply (a : α) (s : set α) :
  dirac a s = indicator s (λ _, 1) a := rfl

/-- The sum of an (arbitrary) collection of outer measures. -/
def sum {ι} (f : ι → outer_measure α) : outer_measure α :=
{ measure_of := λs, ∑' i, f i s,
  empty := by simp,
  mono := λ s t h, ennreal.tsum_le_tsum (λ i, (f i).mono' h),
  Union_nat := λ s, by rw ennreal.tsum_comm; exact
    ennreal.tsum_le_tsum (λ i, (f i).Union_nat _) }

@[simp] theorem sum_apply {ι} (f : ι → outer_measure α) (s : set α) :
  sum f s = ∑' i, f i s := rfl

theorem smul_dirac_apply (a : ennreal) (b : α) (s : set α) :
  (a • dirac b) s = indicator s (λ _, a) b :=
by simp

/-- Pullback of an `outer_measure`: `comap f μ s = μ (f '' s)`. -/
def comap {β} (f : α → β) : outer_measure β →ₗ[ennreal] outer_measure α :=
{ to_fun := λ m,
    { measure_of := λ s, m (f '' s),
      empty := by simp,
      mono := λ s t h, m.mono $ image_subset f h,
      Union_nat := λ s, by { rw [image_Union], apply m.Union_nat } },
  map_add' := λ m₁ m₂, rfl,
  map_smul' := λ c m, rfl }

@[simp] lemma comap_apply {β} (f : α → β) (m : outer_measure β) (s : set α) :
  comap f m s = m (f '' s) :=
rfl

/-- Restrict an `outer_measure` to a set. -/
def restrict (s : set α) : outer_measure α →ₗ[ennreal] outer_measure α :=
(map coe).comp (comap (coe : s → α))

@[simp] lemma restrict_apply (s t : set α) (m : outer_measure α) :
  restrict s m t = m (t ∩ s) :=
by simp [restrict]

theorem top_apply {s : set α} (h : s.nonempty) : (⊤ : outer_measure α) s = ⊤ :=
let ⟨a, as⟩ := h in
top_unique $ le_trans (by simp [smul_dirac_apply, as]) (le_bsupr ((⊤ : ennreal) • dirac a) trivial)

end basic

section of_function
set_option eqn_compiler.zeta true

variables {α : Type*} (m : set α → ennreal) (m_empty : m ∅ = 0)
include m_empty

/-- Given any function `m` assigning measures to sets satisying `m ∅ = 0`, there is
  a unique maximal outer measure `μ` satisfying `μ s ≤ m s` for all `s : set α`. -/
protected def of_function : outer_measure α :=
let μ := λs, ⨅{f : ℕ → set α} (h : s ⊆ ⋃i, f i), ∑'i, m (f i) in
{ measure_of := μ,
  empty      := le_antisymm
    (infi_le_of_le (λ_, ∅) $ infi_le_of_le (empty_subset _) $ by simp [m_empty])
    (zero_le _),
  mono       := assume s₁ s₂ hs, infi_le_infi $ assume f,
    infi_le_infi2 $ assume hb, ⟨subset.trans hs hb, le_refl _⟩,
  Union_nat := assume s, ennreal.le_of_forall_pos_le_add $ begin
    assume ε hε (hb : ∑'i, μ (s i) < ⊤),
    rcases ennreal.exists_pos_sum_of_encodable (ennreal.coe_lt_coe.2 hε) ℕ with ⟨ε', hε', hl⟩,
    refine le_trans _ (add_le_add_left (le_of_lt hl) _),
    rw ← ennreal.tsum_add,
    choose f hf using show
      ∀i, ∃f:ℕ → set α, s i ⊆ (⋃i, f i) ∧ ∑'i, m (f i) < μ (s i) + ε' i,
    { intro,
      have : μ (s i) < μ (s i) + ε' i :=
        ennreal.lt_add_right
          (lt_of_le_of_lt (by apply ennreal.le_tsum) hb)
          (by simpa using hε' i),
      simpa [μ, infi_lt_iff] },
    refine le_trans _ (ennreal.tsum_le_tsum $ λ i, le_of_lt (hf i).2),
    rw [← ennreal.tsum_prod, ← equiv.nat_prod_nat_equiv_nat.symm.tsum_eq],
    swap, {apply_instance},
    refine infi_le_of_le _ (infi_le _ _),
    exact Union_subset (λ i, subset.trans (hf i).1 $
      Union_subset $ λ j, subset.trans (by simp) $
      subset_Union _ $ equiv.nat_prod_nat_equiv_nat (i, j)),
  end }

lemma of_function_apply (s : set α) :
  outer_measure.of_function m m_empty s =
  (⨅ (t : ℕ → set α) (h : s ⊆ Union t), ∑' n, m (t n)) := rfl

variables {m m_empty}
theorem of_function_le (s : set α) : outer_measure.of_function m m_empty s ≤ m s :=
let f : ℕ → set α := λi, nat.rec_on i s (λn s, ∅) in
infi_le_of_le f $ infi_le_of_le (subset_Union f 0) $ le_of_eq $
calc ∑'i, m (f i) = ∑ i in {0}, m (f i) :
    tsum_eq_sum $ by intro i; cases i; simp [m_empty]
  ... = m s : by simp; refl

theorem of_function_eq (s : set α) (m_mono : ∀ ⦃t : set α⦄, s ⊆ t → m s ≤ m t)
  (m_subadd : ∀ (s : ℕ → set α), m (⋃i, s i) ≤ ∑'i, m (s i)) :
  outer_measure.of_function m m_empty s = m s :=
le_antisymm (of_function_le s) $ le_infi $ λ f, le_infi $ λ hf, le_trans (m_mono hf) (m_subadd f)

theorem le_of_function {μ : outer_measure α} :
  μ ≤ outer_measure.of_function m m_empty ↔ ∀ s, μ s ≤ m s :=
⟨λ H s, le_trans (H s) (of_function_le s),
 λ H s, le_infi $ λ f, le_infi $ λ hs,
  le_trans (μ.mono hs) $ le_trans (μ.Union f) $
  ennreal.tsum_le_tsum $ λ i, H _⟩

end of_function

section bounded_by

variables {α : Type*} (m : set α → ennreal)

/-- Given any function `m` assigning measures to sets, there is a unique maximal outer measure `μ`
  satisfying `μ s ≤ m s` for all `s : set α`. This is the same as `outer_measure.of_function`,
  except that it doesn't require `m ∅ = 0`. -/
def bounded_by : outer_measure α :=
outer_measure.of_function (λ s, ⨆ (h : s.nonempty), m s) (by simp [empty_not_nonempty])

variables {m}
theorem bounded_by_le (s : set α) : bounded_by m s ≤ m s :=
(of_function_le _).trans supr_const_le

theorem bounded_by_eq_of_function (m_empty : m ∅ = 0) (s : set α) :
  bounded_by m s = outer_measure.of_function m m_empty s :=
begin
  have : (λ s : set α, ⨆ (h : s.nonempty), m s) = m,
  { ext1 t, cases t.eq_empty_or_nonempty with h h; simp [h, empty_not_nonempty, m_empty] },
  simp [bounded_by, this]
end
theorem bounded_by_apply (s : set α) :
  bounded_by m s = ⨅ (t : ℕ → set α) (h : s ⊆ Union t), ∑' n, ⨆ (h : (t n).nonempty), m (t n) :=
by simp [bounded_by, of_function_apply]

theorem bounded_by_eq (s : set α) (m_empty : m ∅ = 0) (m_mono : ∀ ⦃t : set α⦄, s ⊆ t → m s ≤ m t)
  (m_subadd : ∀ (s : ℕ → set α), m (⋃i, s i) ≤ ∑'i, m (s i)) : bounded_by m s = m s :=
by rw [bounded_by_eq_of_function m_empty, of_function_eq s m_mono m_subadd]

theorem le_bounded_by {μ : outer_measure α} : μ ≤ bounded_by m ↔ ∀ s, μ s ≤ m s :=
begin
  rw [bounded_by, le_of_function, forall_congr], intro s,
  cases s.eq_empty_or_nonempty with h h; simp [h, empty_not_nonempty]
end

theorem le_bounded_by' {μ : outer_measure α} :
  μ ≤ bounded_by m ↔ ∀ s : set α, s.nonempty → μ s ≤ m s :=
by { rw [le_bounded_by, forall_congr], intro s, cases s.eq_empty_or_nonempty with h h; simp [h] }

end bounded_by

section caratheodory_measurable
universe u
parameters {α : Type u} (m : outer_measure α)
include m

local attribute [simp] set.inter_comm set.inter_left_comm set.inter_assoc

variables {s s₁ s₂ : set α}

/-- A set `s` is Carathéodory-measurable for an outer measure `m` if for all sets `t` we have
  `m t = m (t ∩ s) + m (t \ s)`. -/
def is_caratheodory (s : set α) : Prop := ∀t, m t = m (t ∩ s) + m (t \ s)

lemma is_caratheodory_iff_le' {s : set α} : is_caratheodory s ↔ ∀t, m (t ∩ s) + m (t \ s) ≤ m t :=
forall_congr $ λ t, le_antisymm_iff.trans $ and_iff_right $ le_inter_add_diff _

@[simp] lemma is_caratheodory_empty : is_caratheodory ∅ :=
by simp [is_caratheodory, m.empty, diff_empty]

lemma is_caratheodory_compl : is_caratheodory s₁ → is_caratheodory s₁ᶜ :=
by simp [is_caratheodory, diff_eq, add_comm]

@[simp] lemma is_caratheodory_compl_iff : is_caratheodory sᶜ ↔ is_caratheodory s :=
⟨λ h, by simpa using is_caratheodory_compl m h, is_caratheodory_compl⟩

lemma is_caratheodory_union (h₁ : is_caratheodory s₁) (h₂ : is_caratheodory s₂) :
  is_caratheodory (s₁ ∪ s₂) :=
λ t, begin
  rw [h₁ t, h₂ (t ∩ s₁), h₂ (t \ s₁), h₁ (t ∩ (s₁ ∪ s₂)),
    inter_diff_assoc _ _ s₁, set.inter_assoc _ _ s₁,
    inter_eq_self_of_subset_right (set.subset_union_left _ _),
    union_diff_left, h₂ (t ∩ s₁)],
  simp [diff_eq, add_assoc]
end

lemma measure_inter_union (h : s₁ ∩ s₂ ⊆ ∅) (h₁ : is_caratheodory s₁) {t : set α} :
  m (t ∩ (s₁ ∪ s₂)) = m (t ∩ s₁) + m (t ∩ s₂) :=
by rw [h₁, set.inter_assoc, set.union_inter_cancel_left,
  inter_diff_assoc, union_diff_cancel_left h]

lemma is_caratheodory_Union_lt {s : ℕ → set α} :
  ∀{n:ℕ}, (∀i<n, is_caratheodory (s i)) → is_caratheodory (⋃i<n, s i)
| 0       h := by simp [nat.not_lt_zero]
| (n + 1) h := by rw Union_lt_succ; exact is_caratheodory_union m
  (h n (le_refl (n + 1)))
      (is_caratheodory_Union_lt $ assume i hi, h i $ lt_of_lt_of_le hi $ nat.le_succ _)

lemma is_caratheodory_inter (h₁ : is_caratheodory s₁) (h₂ : is_caratheodory s₂) :
  is_caratheodory (s₁ ∩ s₂) :=
by { rw [← is_caratheodory_compl_iff, compl_inter],
  exact is_caratheodory_union _ (is_caratheodory_compl _ h₁) (is_caratheodory_compl _ h₂) }

lemma is_caratheodory_sum {s : ℕ → set α} (h : ∀i, is_caratheodory (s i))
  (hd : pairwise (disjoint on s)) {t : set α} :
  ∀ {n}, ∑ i in finset.range n, m (t ∩ s i) = m (t ∩ ⋃i<n, s i)
| 0            := by simp [nat.not_lt_zero, m.empty]
| (nat.succ n) := begin
  simp [Union_lt_succ, range_succ],
  rw [measure_inter_union m _ (h n), is_caratheodory_sum],
  intro a, simpa [range_succ] using λ h₁ i hi h₂, hd _ _ (ne_of_gt hi) ⟨h₁, h₂⟩
end

lemma is_caratheodory_Union_nat {s : ℕ → set α} (h : ∀i, is_caratheodory (s i))
  (hd : pairwise (disjoint on s)) : is_caratheodory (⋃i, s i) :=
is_caratheodory_iff_le'.2 $ λ t, begin
  have hp : m (t ∩ ⋃i, s i) ≤ (⨆n, m (t ∩ ⋃i<n, s i)),
  { convert m.Union (λ i, t ∩ s i),
    { rw inter_Union },
    { simp [ennreal.tsum_eq_supr_nat, is_caratheodory_sum m h hd] } },
  refine le_trans (add_le_add_right hp _) _,
  rw ennreal.supr_add,
  refine supr_le (λ n, le_trans (add_le_add_left _ _)
    (ge_of_eq (is_caratheodory_Union_lt m (λ i _, h i) _))),
  refine m.mono (diff_subset_diff_right _),
  exact bUnion_subset (λ i _, subset_Union _ i),
end

lemma f_Union {s : ℕ → set α} (h : ∀i, is_caratheodory (s i))
  (hd : pairwise (disjoint on s)) : m (⋃i, s i) = ∑'i, m (s i) :=
begin
  refine le_antisymm (m.Union_nat s) _,
  rw ennreal.tsum_eq_supr_nat,
  refine supr_le (λ n, _),
  have := @is_caratheodory_sum _ m _ h hd univ n,
  simp at this, simp [this],
  exact m.mono (bUnion_subset (λ i _, subset_Union _ i)),
end

/-- The Carathéodory-measurable sets for an outer measure `m` form a Dynkin system.  -/
def caratheodory_dynkin : measurable_space.dynkin_system α :=
{ has := is_caratheodory,
  has_empty := is_caratheodory_empty,
  has_compl := assume s, is_caratheodory_compl,
  has_Union_nat := assume f hf hn, is_caratheodory_Union_nat hn hf }

/-- Given an outer measure `μ`, the Carathéodory-measurable space is
  defined such that `s` is measurable if `∀t, μ t = μ (t ∩ s) + μ (t \ s)`. -/
protected def caratheodory : measurable_space α :=
caratheodory_dynkin.to_measurable_space $ assume s₁ s₂, is_caratheodory_inter

lemma is_caratheodory_iff {s : set α} :
  caratheodory.is_measurable' s ↔ ∀t, m t = m (t ∩ s) + m (t \ s) :=
iff.rfl

lemma is_caratheodory_iff_le {s : set α} :
  caratheodory.is_measurable' s ↔ ∀t, m (t ∩ s) + m (t \ s) ≤ m t :=
is_caratheodory_iff_le'

protected lemma Union_eq_of_caratheodory {s : ℕ → set α}
  (h : ∀i, caratheodory.is_measurable' (s i)) (hd : pairwise (disjoint on s)) :
  m (⋃i, s i) = ∑'i, m (s i) :=
f_Union h hd

end caratheodory_measurable

variables {α : Type*}

lemma of_function_caratheodory {m : set α → ennreal} {s : set α}
  {h₀ : m ∅ = 0} (hs : ∀t, m (t ∩ s) + m (t \ s) ≤ m t) :
  (outer_measure.of_function m h₀).caratheodory.is_measurable' s :=
begin
  apply (is_caratheodory_iff_le _).mpr,
  refine λ t, le_infi (λ f, le_infi $ λ hf, _),
  refine le_trans (add_le_add
    (infi_le_of_le (λi, f i ∩ s) $ infi_le _ _)
    (infi_le_of_le (λi, f i \ s) $ infi_le _ _)) _,
  { rw ← Union_inter, exact inter_subset_inter_left _ hf },
  { rw ← Union_diff, exact diff_subset_diff_left hf },
  { rw ← ennreal.tsum_add, exact ennreal.tsum_le_tsum (λ i, hs _) }
end

lemma bounded_by_caratheodory {m : set α → ennreal} {s : set α}
  (hs : ∀t, m (t ∩ s) + m (t \ s) ≤ m t) : (bounded_by m).caratheodory.is_measurable' s :=
begin
  apply of_function_caratheodory, intro t,
  cases t.eq_empty_or_nonempty with h h,
  { simp [h, empty_not_nonempty] },
  { convert le_trans _ (hs t), { simp [h] }, exact add_le_add supr_const_le supr_const_le }
end

@[simp] theorem zero_caratheodory : (0 : outer_measure α).caratheodory = ⊤ :=
top_unique $ λ s _ t, (add_zero _).symm

theorem top_caratheodory : (⊤ : outer_measure α).caratheodory = ⊤ :=
top_unique $ assume s hs, (is_caratheodory_iff_le _).2 $ assume t,
  t.eq_empty_or_nonempty.elim (λ ht, by simp [ht])
    (λ ht, by simp only [ht, top_apply, le_top])

theorem le_add_caratheodory (m₁ m₂ : outer_measure α) :
  m₁.caratheodory ⊓ m₂.caratheodory ≤ (m₁ + m₂ : outer_measure α).caratheodory :=
λ s ⟨hs₁, hs₂⟩ t, by simp [hs₁ t, hs₂ t, add_left_comm, add_assoc]

theorem le_sum_caratheodory {ι} (m : ι → outer_measure α) :
  (⨅ i, (m i).caratheodory) ≤ (sum m).caratheodory :=
λ s h t, by simp [λ i,
  measurable_space.is_measurable_infi.1 h i t, ennreal.tsum_add]

theorem le_smul_caratheodory (a : ennreal) (m : outer_measure α) :
  m.caratheodory ≤ (a • m).caratheodory :=
λ s h t, by simp [h t, mul_add]

@[simp] theorem dirac_caratheodory (a : α) : (dirac a).caratheodory = ⊤ :=
top_unique $ λ s _ t, begin
  by_cases ht : a ∈ t, swap, by simp [ht],
  by_cases hs : a ∈ s; simp*
end

section Inf_gen

/-- Given a set of outer measures, we define a new function that on a set `s` is defined to be the
  infimum of `μ(s)` for the outer measures `μ` in the collection. We ensure that this
  function is defined to be `0` on `∅`, even if the collection of outer measures is empty.
  The outer measure generated by this function is the infimum of the given outer measures. -/
def Inf_gen (m : set (outer_measure α)) (s : set α) : ennreal :=
⨅ (μ : outer_measure α) (h : μ ∈ m), μ s

lemma Inf_gen_def (m : set (outer_measure α)) (t : set α) :
  Inf_gen m t = (⨅ (μ : outer_measure α) (h : μ ∈ m), μ t) :=
rfl

lemma Inf_eq_bounded_by_Inf_gen (m : set (outer_measure α)) :
  Inf m = outer_measure.bounded_by (Inf_gen m) :=
begin
  refine le_antisymm _ _,
  { refine (le_bounded_by.2 $ λ s, _), refine le_binfi _,
    intros μ hμ, refine (show Inf m ≤ μ, from Inf_le hμ) s },
  { refine le_Inf _, intros μ hμ t, refine le_trans (bounded_by_le t) (binfi_le μ hμ) }
end

lemma supr_Inf_gen_nonempty {m : set (outer_measure α)} (h : m.nonempty) (t : set α) :
  (⨆ (h : t.nonempty), Inf_gen m t) = (⨅ (μ : outer_measure α) (h : μ ∈ m), μ t) :=
begin
  rcases t.eq_empty_or_nonempty with rfl|ht,
  { rcases h with ⟨μ, hμ⟩,
    rw [eq_false_intro empty_not_nonempty, supr_false, eq_comm],
    simp_rw [empty'],
    apply bot_unique,
    refine infi_le_of_le μ (infi_le _ hμ) },
  { simp [ht, Inf_gen_def] }
end

/-- The value of the Infimum of a nonempty set of outer measures on a set is not simply
the minimum value of a measure on that set: it is the infimum sum of measures of countable set of
sets that covers that set, where a different measure can be used for each set in the cover. -/
lemma Inf_apply {m : set (outer_measure α)} {s : set α} (h : m.nonempty) :
  Inf m s = ⨅ (t : ℕ → set α) (h2 : s ⊆ Union t),
    ∑' n, ⨅ (μ : outer_measure α) (h3 : μ ∈ m), μ (t n) :=
by simp_rw [Inf_eq_bounded_by_Inf_gen, bounded_by_apply, supr_Inf_gen_nonempty h]

/-- This proves that Inf and restrict commute for outer measures, so long as the set of
outer measures is nonempty. -/
lemma restrict_Inf_eq_Inf_restrict
  (m : set (outer_measure α)) {s : set α} (hm : m.nonempty) :
  restrict s (Inf m) = Inf ((restrict s) '' m) :=
begin
  have hm2 : ((measure_theory.outer_measure.restrict s) '' m).nonempty :=
    set.nonempty_image_iff.mpr hm,
  ext1 u, rw [restrict_apply, Inf_apply hm, Inf_apply hm2],
  apply le_antisymm; simp only [set.mem_image, infi_exists, le_infi_iff]; intros t hu,
  { refine infi_le_of_le (λ n, (t n) ∩ s) _,
    refine infi_le_of_le _ _,
    { rw [← Union_inter], exact inter_subset_inter hu subset.rfl },
    apply ennreal.tsum_le_tsum (λ n, _) ,
    simp only [and_imp, set.mem_image, infi_exists, le_infi_iff],
    rintro _ ⟨μ, h_μ_in_s, rfl⟩,
    refine infi_le_of_le μ _,
    refine infi_le_of_le h_μ_in_s _,
    simp_rw [restrict_apply, le_refl] },
  { refine infi_le_of_le (λ n, (t n) ∪ sᶜ) _,
    refine infi_le_of_le _ _,
    { rwa [inter_subset, set.union_comm, Union_union] at hu },
    apply ennreal.tsum_le_tsum (λ n, _),
    refine le_binfi (λ μ hμ, _),
    refine infi_le_of_le (restrict s μ) _,
    refine infi_le_of_le ⟨_, hμ, rfl⟩ _,
    rw [restrict_apply, union_inter_distrib_right, compl_inter_self, set.union_empty],
    exact μ.mono (inter_subset_left _ _) },
end

end Inf_gen

end outer_measure
open outer_measure

/-! ### Induced Outer Measure

  We can extend a function defined on a subset of `set α` to an outer measure.
  The underlying function is called `extend`, and the measure it induces is called
  `induced_outer_measure`.

  Some lemmas below are proven twice, once in the general case, and one where the function `m`
  is only defined on measurable sets (i.e. when `P = is_measurable`). In the latter cases, we can
  remove some hypotheses in the statement. The general version has the same name, but with a prime
  at the end. -/
section extend
variables {α : Type*} {P : α → Prop}
variables (m : Π (s : α), P s → ennreal)

/-- We can trivially extend a function defined on a subclass of objects (with codomain `ennreal`)
  to all objects by defining it to be `∞` on the objects not in the class. -/
def extend (s : α) : ennreal := ⨅ h : P s, m s h

lemma extend_eq {s : α} (h : P s) : extend m s = m s h :=
by simp [extend, h]

lemma le_extend {s : α} (h : P s) : m s h ≤ extend m s :=
by { simp only [extend, le_infi_iff], intro, refl' }

end extend

section extend_set

variables {α : Type*} {P : set α → Prop}
variables {m : Π (s : set α), P s → ennreal}
variables (P0 : P ∅) (m0 : m ∅ P0 = 0)
variables (PU : ∀{{f : ℕ → set α}} (hm : ∀i, P (f i)), P (⋃i, f i))
variables (mU : ∀ {{f : ℕ → set α}} (hm : ∀i, P (f i)), pairwise (disjoint on f) →
  m (⋃i, f i) (PU hm) = ∑'i, m (f i) (hm i))
variables (msU : ∀ {{f : ℕ → set α}} (hm : ∀i, P (f i)),
  m (⋃i, f i) (PU hm) ≤ ∑'i, m (f i) (hm i))
variables (m_mono : ∀⦃s₁ s₂ : set α⦄ (hs₁ : P s₁) (hs₂ : P s₂), s₁ ⊆ s₂ → m s₁ hs₁ ≤ m s₂ hs₂)

lemma extend_empty : extend m ∅ = 0 :=
(extend_eq _ P0).trans m0

lemma extend_Union_nat
  {f : ℕ → set α} (hm : ∀i, P (f i))
  (mU : m (⋃i, f i) (PU hm) = ∑'i, m (f i) (hm i)) :
  extend m (⋃i, f i) = ∑'i, extend m (f i) :=
(extend_eq _ _).trans $ mU.trans $ by { congr' with i, rw extend_eq }

section subadditive
include PU msU
lemma extend_Union_le_tsum_nat'
  (s : ℕ → set α) : extend m (⋃i, s i) ≤ ∑'i, extend m (s i) :=
begin
  by_cases h : ∀i, P (s i),
  { rw [extend_eq _ (PU h), congr_arg tsum _],
    { apply msU h },
    funext i, apply extend_eq _ (h i) },
  { cases not_forall.1 h with i hi,
    exact le_trans (le_infi $ λ h, hi.elim h) (ennreal.le_tsum i) }
end
end subadditive

section mono
include m_mono
lemma extend_mono'
  ⦃s₁ s₂ : set α⦄ (h₁ : P s₁) (hs : s₁ ⊆ s₂) : extend m s₁ ≤ extend m s₂ :=
by { refine le_infi _, intro h₂, rw [extend_eq m h₁], exact m_mono h₁ h₂ hs }
end mono

section unions
include P0 m0 PU mU
lemma extend_Union {β} [encodable β] {f : β → set α}
  (hd : pairwise (disjoint on f)) (hm : ∀i, P (f i)) :
  extend m (⋃i, f i) = ∑'i, extend m (f i) :=
begin
  rw [← encodable.Union_decode2, ← tsum_Union_decode2],
  { exact extend_Union_nat PU
      (λ n, encodable.Union_decode2_cases P0 hm)
      (mU _ (encodable.Union_decode2_disjoint_on hd)) },
  { exact extend_empty P0 m0 }
end

lemma extend_union {s₁ s₂ : set α} (hd : disjoint s₁ s₂) (h₁ : P s₁) (h₂ : P s₂) :
  extend m (s₁ ∪ s₂) = extend m s₁ + extend m s₂ :=
begin
  rw [union_eq_Union, extend_Union P0 m0 PU mU
      (pairwise_disjoint_on_bool.2 hd) (bool.forall_bool.2 ⟨h₂, h₁⟩), tsum_fintype],
  simp
end

end unions

variable (m)
/-- Given an arbitrary function on a subset of sets, we can define the outer measure corresponding
  to it (this is the unique maximal outer measure that is at most `m` on the domain of `m`). -/
def induced_outer_measure : outer_measure α :=
outer_measure.of_function (extend m) (extend_empty P0 m0)
variables {m P0 m0}

include msU m_mono
lemma induced_outer_measure_eq_extend' {s : set α} (hs : P s) :
  induced_outer_measure m P0 m0 s = extend m s :=
of_function_eq s (λ t, extend_mono' m_mono hs) (extend_Union_le_tsum_nat' PU msU)

lemma induced_outer_measure_eq' {s : set α} (hs : P s) :
  induced_outer_measure m P0 m0 s = m s hs :=
(induced_outer_measure_eq_extend' PU msU m_mono hs).trans $ extend_eq _ _

lemma induced_outer_measure_eq_infi (s : set α) :
  induced_outer_measure m P0 m0 s = ⨅ (t : set α) (ht : P t) (h : s ⊆ t), m t ht :=
begin
  apply le_antisymm,
  { simp only [le_infi_iff], intros t ht, simp only [le_infi_iff], intro hs,
    refine le_trans (mono' _ hs) _,
    exact le_of_eq (induced_outer_measure_eq' _ msU m_mono _) },
  { refine le_infi _, intro f, refine le_infi _, intro hf,
    refine le_trans _ (extend_Union_le_tsum_nat' _ msU _),
    refine le_infi _, intro h2f,
    refine infi_le_of_le _ (infi_le_of_le h2f $ infi_le _ hf) }
end

lemma induced_outer_measure_preimage (f : α ≃ α) (Pm : ∀ (s : set α), P (f ⁻¹' s) ↔ P s)
  (mm : ∀ (s : set α) (hs : P s), m (f ⁻¹' s) ((Pm _).mpr hs) = m s hs)
  {A : set α} : induced_outer_measure m P0 m0 (f ⁻¹' A) = induced_outer_measure m P0 m0 A :=
begin
  simp only [induced_outer_measure_eq_infi _ msU m_mono], symmetry,
  refine infi_congr (preimage f) f.injective.preimage_surjective _, intro s,
  refine infi_congr_Prop (Pm s) _, intro hs,
  refine infi_congr_Prop f.surjective.preimage_subset_preimage_iff _,
  intro h2s, exact mm s hs
end

lemma induced_outer_measure_exists_set {s : set α}
  (hs : induced_outer_measure m P0 m0 s < ⊤) {ε : ℝ≥0} (hε : 0 < ε) :
  ∃ (t : set α) (ht : P t), s ⊆ t ∧
    induced_outer_measure m P0 m0 t ≤ induced_outer_measure m P0 m0 s + ε :=
begin
  have := ennreal.lt_add_right hs (ennreal.zero_lt_coe_iff.2 hε),
  conv at this {to_lhs, rw induced_outer_measure_eq_infi _ msU m_mono },
  simp only [infi_lt_iff] at this,
  rcases this with ⟨t, h1t, h2t, h3t⟩,
  exact ⟨t, h1t, h2t,
    le_trans (le_of_eq $ induced_outer_measure_eq' _ msU m_mono h1t) (le_of_lt h3t)⟩
end

/-- To test whether `s` is Carathéodory-measurable we only need to check the sets `t` for which
  `P t` holds. See `of_function_caratheodory` for another way to show the Carathéodory-measurability
  of `s`.
-/
lemma induced_outer_measure_caratheodory (s : set α) :
  (induced_outer_measure m P0 m0).caratheodory.is_measurable' s ↔ ∀ (t : set α), P t →
  induced_outer_measure m P0 m0 (t ∩ s) + induced_outer_measure m P0 m0 (t \ s) ≤
    induced_outer_measure m P0 m0 t :=
begin
  rw is_caratheodory_iff_le,
  split,
  { intros h t ht, exact h t },
  { intros h u, conv_rhs { rw induced_outer_measure_eq_infi _ msU m_mono },
    refine le_infi _, intro t, refine le_infi _, intro ht, refine le_infi _, intro h2t,
    refine le_trans _ (le_trans (h t ht) $ le_of_eq $ induced_outer_measure_eq' _ msU m_mono ht),
    refine add_le_add (mono' _ $ set.inter_subset_inter_left _ h2t)
      (mono' _  $ diff_subset_diff_left h2t) }
end

end extend_set

/-! If `P` is `is_measurable` for some measurable space, then we can remove some hypotheses of the
  above lemmas. -/
section measurable_space

variables {α : Type*} [measurable_space α]
variables {m : Π (s : set α), is_measurable s → ennreal}
variables (m0 : m ∅ is_measurable.empty = 0)
variable (mU : ∀ {{f : ℕ → set α}} (hm : ∀i, is_measurable (f i)), pairwise (disjoint on f) →
  m (⋃i, f i) (is_measurable.Union hm) = ∑'i, m (f i) (hm i))
include m0 mU

lemma extend_mono {s₁ s₂ : set α} (h₁ : is_measurable s₁) (hs : s₁ ⊆ s₂) :
  extend m s₁ ≤ extend m s₂ :=
begin
  refine le_infi _, intro h₂,
  have := extend_union is_measurable.empty m0 is_measurable.Union mU disjoint_diff h₁ (h₂.diff h₁),
  rw union_diff_cancel hs at this,
  rw ← extend_eq m,
  exact le_iff_exists_add.2 ⟨_, this⟩,
end

lemma extend_Union_le_tsum_nat : ∀ (s : ℕ → set α), extend m (⋃i, s i) ≤ ∑'i, extend m (s i) :=
begin
  refine extend_Union_le_tsum_nat' is_measurable.Union _, intros f h,
  simp [Union_disjointed.symm] {single_pass := tt},
  rw [mU (is_measurable.disjointed h) disjoint_disjointed],
  refine ennreal.tsum_le_tsum (λ i, _),
  rw [← extend_eq m, ← extend_eq m],
  exact extend_mono m0 mU (is_measurable.disjointed h _) (inter_subset_left _ _)
end

lemma induced_outer_measure_eq_extend {s : set α} (hs : is_measurable s) :
  induced_outer_measure m is_measurable.empty m0 s = extend m s :=
of_function_eq s (λ t, extend_mono m0 mU hs) (extend_Union_le_tsum_nat m0 mU)

lemma induced_outer_measure_eq {s : set α} (hs : is_measurable s) :
  induced_outer_measure m is_measurable.empty m0 s = m s hs :=
(induced_outer_measure_eq_extend m0 mU hs).trans $ extend_eq _ _

end measurable_space

namespace outer_measure
variables {α : Type*} [measurable_space α] (m : outer_measure α)

/-- Given an outer measure `m` we can forget its value on non-measurable sets, and then consider
  `m.trim`, the unique maximal outer measure less than that function. -/
def trim : outer_measure α :=
induced_outer_measure (λ s _, m s) is_measurable.empty m.empty

theorem le_trim : m ≤ m.trim :=
le_of_function.mpr $ λ s, le_infi $ λ _, le_refl _

theorem trim_eq {s : set α} (hs : is_measurable s) : m.trim s = m s :=
induced_outer_measure_eq' is_measurable.Union (λ f hf, m.Union_nat f) (λ _ _ _ _ h, m.mono h) hs

theorem trim_congr {m₁ m₂ : outer_measure α}
  (H : ∀ {s : set α}, is_measurable s → m₁ s = m₂ s) :
  m₁.trim = m₂.trim :=
by { unfold trim, congr, funext s hs, exact H hs }

theorem trim_le_trim {m₁ m₂ : outer_measure α} (H : m₁ ≤ m₂) : m₁.trim ≤ m₂.trim :=
λ s, binfi_le_binfi $ λ f hs, ennreal.tsum_le_tsum $ λ b, infi_le_infi $ λ hf, H _

theorem le_trim_iff {m₁ m₂ : outer_measure α} : m₁ ≤ m₂.trim ↔ ∀ s, is_measurable s → m₁ s ≤ m₂ s :=
le_of_function.trans $ forall_congr $ λ s, le_infi_iff

theorem trim_eq_infi (s : set α) : m.trim s = ⨅ t (st : s ⊆ t) (ht : is_measurable t), m t :=
by { simp only [infi_comm] {single_pass := tt}, exact induced_outer_measure_eq_infi
    is_measurable.Union (λ f _, m.Union_nat f) (λ _ _ _ _ h, m.mono h) s }

theorem trim_eq_infi' (s : set α) : m.trim s = ⨅ t : {t // s ⊆ t ∧ is_measurable t}, m t :=
by simp [infi_subtype, infi_and, trim_eq_infi]

theorem trim_trim (m : outer_measure α) : m.trim.trim = m.trim :=
le_antisymm (le_trim_iff.2 $ λ s hs, by simp [trim_eq _ hs, le_refl]) (le_trim _)

@[simp] theorem trim_zero : (0 : outer_measure α).trim = 0 :=
ext $ λ s, le_antisymm
  (le_trans ((trim 0).mono (subset_univ s)) $
    le_of_eq $ trim_eq _ is_measurable.univ)
  (zero_le _)

theorem trim_add (m₁ m₂ : outer_measure α) : (m₁ + m₂).trim = m₁.trim + m₂.trim :=
begin
  ext1 s, simp only [trim_eq_infi', add_apply],
  rw ennreal.infi_add_infi,
  rintro ⟨t₁, st₁, ht₁⟩ ⟨t₂, st₂, ht₂⟩,
  exact ⟨⟨_, subset_inter_iff.2 ⟨st₁, st₂⟩, ht₁.inter ht₂⟩,
    add_le_add
      (m₁.mono' (inter_subset_left _ _))
      (m₂.mono' (inter_subset_right _ _))⟩,
end

theorem trim_sum_ge {ι} (m : ι → outer_measure α) : sum (λ i, (m i).trim) ≤ (sum m).trim :=
λ s, by simp [trim_eq_infi]; exact
λ t st ht, ennreal.tsum_le_tsum (λ i,
  infi_le_of_le t $ infi_le_of_le st $ infi_le _ ht)

lemma exists_is_measurable_superset_eq_trim (m : outer_measure α) (s : set α) :
  ∃ t, s ⊆ t ∧ is_measurable t ∧ m t = m.trim s :=
begin
  simp only [trim_eq_infi], set ms := ⨅ (t : set α) (st : s ⊆ t) (ht : is_measurable t), m t,
  by_cases hs : ms = ⊤,
  { simp only [hs],
    simp only [infi_eq_top] at hs,
    exact ⟨univ, subset_univ s, is_measurable.univ, hs _ (subset_univ s) is_measurable.univ⟩ },
  { have : ∀ r > ms, ∃ t, s ⊆ t ∧ is_measurable t ∧ m t < r,
    { intros r hs,
      simpa [infi_lt_iff] using hs },
    have : ∀ n : ℕ, ∃ t, s ⊆ t ∧ is_measurable t ∧ m t < ms + n⁻¹,
    { assume n,
      refine this _ (ennreal.lt_add_right (lt_top_iff_ne_top.2 hs) _),
      exact (ennreal.inv_pos.2 $ ennreal.nat_ne_top _) },
    choose t hsub hm hm',
    refine ⟨⋂ n, t n, subset_Inter hsub, is_measurable.Inter hm, _⟩,
    have : tendsto (λ n : ℕ, ms + n⁻¹) at_top (𝓝 (ms + 0)),
      from tendsto_const_nhds.add ennreal.tendsto_inv_nat_nhds_zero,
    rw add_zero at this,
    refine le_antisymm (ge_of_tendsto' this $ λ n, _) _,
    { exact le_trans (m.mono' $ Inter_subset t n) (hm' n).le },
    { refine infi_le_of_le (⋂ n, t n) _,
      refine infi_le_of_le (subset_Inter hsub) _,
      refine infi_le _ (is_measurable.Inter hm) } }
end

lemma exists_is_measurable_superset_of_trim_eq_zero
  {m : outer_measure α} {s : set α} (h : m.trim s = 0) :
  ∃t, s ⊆ t ∧ is_measurable t ∧ m t = 0 :=
begin
  rcases exists_is_measurable_superset_eq_trim m s with ⟨t, hst, ht, hm⟩,
  exact ⟨t, hst, ht, h ▸ hm⟩
end

theorem trim_smul (c : ennreal) (m : outer_measure α) :
  (c • m).trim = c • m.trim :=
begin
  ext1 s,
  simp only [trim_eq_infi', smul_apply],
  haveI : nonempty {t // s ⊆ t ∧ is_measurable t} := ⟨⟨univ, subset_univ _, is_measurable.univ⟩⟩,
  refine ennreal.infi_mul_left (assume hc hs, _),
  rw ← trim_eq_infi' at hs,
  simpa [and_assoc] using exists_is_measurable_superset_of_trim_eq_zero hs
end

/-- The trimmed property of a measure μ states that `μ.to_outer_measure.trim = μ.to_outer_measure`.
This theorem shows that a restricted trimmed outer measure is a trimmed outer measure. -/
lemma restrict_trim {μ : outer_measure α} {s : set α} (hs : is_measurable s) :
  (restrict s μ).trim = restrict s μ.trim :=
begin
  apply measure_theory.outer_measure.ext, intro t,
  simp_rw [restrict_apply, trim_eq_infi, restrict_apply],
  apply le_antisymm,
  { simp only [le_infi_iff],
    intros v h_subset hv,
    refine infi_le_of_le (v ∪ sᶜ) _,
    refine infi_le_of_le _ _,
    { rwa [set.union_comm, ← inter_subset] },
    refine infi_le_of_le (hv.union hs.compl) _,
    rw [union_inter_distrib_right, compl_inter_self, set.union_empty],
    exact μ.mono (inter_subset_left _ _) },
  { simp only [le_infi_iff], intros u h_subset hu,
    refine infi_le_of_le (u ∩ s) _,
    refine infi_le_of_le (set.inter_subset_inter_left _ h_subset) _,
    refine infi_le_of_le (hu.inter hs) le_rfl },
end

end outer_measure

end measure_theory
