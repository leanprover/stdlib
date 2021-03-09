/-
Copyright (c) 2021 Martin Zinkevich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Martin Zinkevich
-/
import measure_theory.measurable_space

/-!
# Lemmas regarding `is_pi_system`.

`is_pi_system` is similar, but not identical to, the classic π-system encountered in measure
theory. In particular, it is not required to be nonempty, and it isn't closed under disjoint
intersection (thus neither more nor less general than a typical π-system).

## Main statements

* `generate_pi_system g` gives the minimal pi system containing `g`.
  This can be considered a Galois insertion into both measurable spaces and sets.

* `generate_from_generate_pi_system_eq` proves that if you generate a pi_system
  then a measurable space versus generating a measurable space gives the same result. This
  is useful because there are connections between a independent sets that are pi systems
  the generated independent spaces.

* `mem_generate_pi_system_Union_elim` and `mem_generate_pi_system_Union_elim'` are theorems
  that show that any element of the supremum of the union of a set of pi systems can be
  represented as the intersection of a finite number of elements from these sets.

## Implementation details

* is_pi_system is a predicate, not a type. Thus, we don't explicitly define the galois
  insertion, nor do we define a complete lattice. In theory, we could define a complete
  lattice and galois insertion on subtype is_pi_system.

-/

open measurable_space
open_locale classical

lemma is_pi_system.singleton {α} (S : set α) : is_pi_system ({S} : set (set α)) :=
begin
  intros s t h_s h_t h_ne,
  rw [set.mem_singleton_iff.1 h_s, set.mem_singleton_iff.1 h_t, set.inter_self,
      set.mem_singleton_iff],
end

/-- The smallest superset of g that is_pi_system. -/
inductive generate_pi_system {α} (S : set (set α)) : set (set α)
| base {s : set α} (h_s : s ∈ S) : generate_pi_system s
| inter {s t : set α} (h_s : generate_pi_system s)  (h_t : generate_pi_system t)
  (h_nonempty : (s ∩ t).nonempty) : generate_pi_system (s ∩ t)

lemma is_pi_system_generate_pi_system {α} (S : set (set α)) :
  is_pi_system (generate_pi_system S) :=
λ s t h_s h_t h_nonempty, generate_pi_system.inter h_s h_t h_nonempty

lemma subset_generate_pi_system_self {α} (S : set (set α)) : S ⊆ generate_pi_system S :=
λ s, generate_pi_system.base

lemma generate_pi_system_subset_self {α} {S : set (set α)} (h_S : is_pi_system S) :
  generate_pi_system S ⊆ S :=
begin
  intros x h,
  induction h with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  { exact h_s, },
  { exact h_S _ _ h_s h_u h_nonempty, },
end

lemma generate_pi_system_eq {α} {S : set (set α)} (h_pi : is_pi_system S) :
  generate_pi_system S = S :=
set.subset.antisymm (generate_pi_system_subset_self h_pi) (subset_generate_pi_system_self S)

lemma generate_pi_system_mono {α} {S T : set (set α)} (hST : S ⊆ T) :
  generate_pi_system S ⊆ generate_pi_system T :=
begin
  intros t ht,
  induction ht with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  { exact generate_pi_system.base (set.mem_of_subset_of_mem hST h_s),},
  { exact is_pi_system_generate_pi_system T _ _ h_s h_u h_nonempty, },
end

lemma generate_pi_system_measurable_set {α} [M : measurable_space α] {S : set (set α)}
  (h_meas_S : ∀ s ∈ S, measurable_set s) (t : set α)
  (h_in_pi : t ∈ generate_pi_system S) : measurable_set t :=
begin
  induction h_in_pi with s h_s s u h_gen_s h_gen_u h_nonempty h_s h_u,
  { apply h_meas_S _ h_s, },
  { apply measurable_set.inter h_s h_u, },
end

lemma generate_from_measurable_set_of_generate_pi_system {α} {g : set (set α)} (t : set α)
  (ht : t ∈ generate_pi_system g) :
  (generate_from g).measurable_set' t :=
@generate_pi_system_measurable_set α (generate_from g) g
  (λ s h_s_in_g, measurable_set_generate_from h_s_in_g) t ht

lemma generate_from_generate_pi_system_eq {α} {g : set (set α)} :
  generate_from (generate_pi_system g) = generate_from g :=
begin
  apply le_antisymm; apply generate_from_le,
  { exact λ t h_t, generate_from_measurable_set_of_generate_pi_system t h_t, },
  { exact λ t h_t, measurable_set_generate_from (generate_pi_system.base h_t), },
end

/- This theorem shows that every element of the pi system generated by the union of the
   pi systems can be represented by a finite union of elements from the pi systems. -/
lemma mem_generate_pi_system_Union_elim {α β} {g : β → set (set α)}
  (h_pi : ∀ b, is_pi_system (g b)) (t : set α) (h_t : t ∈ generate_pi_system (⋃ b, g b)) :
  (∃ (T : finset β) (f : β → set α), (t = ⋂ b ∈ T, f b) ∧ (∀ b ∈ T, f b ∈ (g b))) :=
begin
  induction h_t with s h_s s t' h_gen_s h_gen_t' h_nonempty h_s h_t',
  { rcases h_s with ⟨t', ⟨⟨b, rfl⟩, h_s_in_t'⟩⟩,
    refine ⟨{b}, (λ _, s), _⟩,
    simpa using h_s_in_t', },
  { rcases h_t' with ⟨T_t', ⟨f_t', ⟨rfl, h_t'⟩⟩⟩,
    rcases h_s with ⟨T_s, ⟨f_s, ⟨rfl, h_s⟩ ⟩ ⟩,
    use [(T_s ∪ T_t'), (λ (b:β),
      if (b ∈ T_s) then (if (b ∈ T_t') then (f_s b ∩ (f_t' b)) else (f_s b))
      else (if (b ∈ T_t') then (f_t' b) else (∅ : set α)))],
    split,
    { ext a,
      simp_rw [set.mem_inter_iff, set.mem_Inter, finset.mem_union, or_imp_distrib],
      rw ← forall_and_distrib,
      split; intros h1 b; by_cases hbs : b ∈ T_s; by_cases hbt : b ∈ T_t'; specialize h1 b;
        simp only [hbs, hbt, if_true, if_false, true_implies_iff, and_self, false_implies_iff,
          and_true, true_and] at h1 ⊢,
      all_goals { exact h1, }, },
    intros b h_b,
    split_ifs with hbs hbt hbt,
    { refine h_pi b (f_s b) (f_t' b) (h_s b hbs) (h_t' b hbt) (set.nonempty.mono _ h_nonempty),
      exact set.inter_subset_inter (set.bInter_subset_of_mem hbs) (set.bInter_subset_of_mem hbt), },
    { exact h_s b hbs, },
    { exact h_t' b hbt, },
    { rw finset.mem_union at h_b,
      apply false.elim (h_b.elim hbs hbt), }, },
end

/- This is similar to mem_generate_pi_system_Union_elim', but
   focuses on a set of elements in b, as opposed to the whole type. -/
lemma mem_generate_pi_system_Union_elim' {α β} {g : β → set (set α)} {s: set β}
  (h_pi : ∀ b ∈ s, is_pi_system (g b)) (t : set α) (h_t : t ∈ generate_pi_system (⋃ b ∈ s, g b)) :
  (∃ (T : finset β) (f : β → set α), (↑T ⊆ s) ∧ (t = ⋂ b ∈ T, f b) ∧ (∀ b ∈ T, f b ∈ (g b))) :=
begin
  have h1 := @mem_generate_pi_system_Union_elim α (subtype s) (g ∘ subtype.val) _ t _,
  rcases h1 with ⟨T, ⟨f,⟨ rfl, h_t'⟩ ⟩⟩,
  use [T.image subtype.val, function.extend subtype.val f (λ (b:β), (∅ : set α))],
  split,
  { simp },
  split,
  { ext a, split;
    { simp only [set.mem_Inter, subtype.forall, finset.set_bInter_finset_image],
      intros h1 b h_b h_b_in_T,
      have h2 := h1 b h_b h_b_in_T,
      revert h2,
      rw function.extend_apply subtype.val_injective,
      apply id } },
  { intros b h_b,
    simp_rw [finset.mem_image, exists_prop, subtype.exists,
             exists_and_distrib_right, exists_eq_right] at h_b,
    cases h_b,
    have h_b_alt : b = (subtype.mk b h_b_w).val := rfl,
    rw [h_b_alt, function.extend_apply subtype.val_injective],
    apply h_t',
    apply h_b_h },
  { intros b, apply h_pi b.val b.property, },
  { suffices h1 : (⋃ (b : subtype s), (g ∘ subtype.val) b) = (⋃ b (H : b ∈ s), g b), by rwa h1,
    ext x,
    simp only [exists_prop, set.mem_Union, function.comp_app, subtype.exists, subtype.coe_mk],
    refl, },
end

