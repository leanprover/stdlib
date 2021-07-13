/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.exposed

/-!
# The Krein-Milman theorem

This file proves the Krein-Milman theorem and the Krein-Milman lemma in locally convex topological
vector spaces (LCTVS for short).

## The lemma

The lemma states that a nonempty compact set `A` has an extreme point. The proof goes:
1. Using Zorn's lemma, find a minimal nonempty closed `B` that is an extreme subset of `A`. We will
  show that `B` is a singleton, thus corresponding to an extreme point.
2. By contradiction, `B` contains two distinct points `x` and `y`.
3. With the (geometric) Hahn-Banach theorem, find an hyperplane that separates `x` and `y`.
4. Look at the extreme (actually exposed) subset of `B` obtained by going the furthest away from
  the separating hyperplane in the direction of `x`. It is nonempty, closed and an extreme subset
  of `A`.
5. It is a strict subset of `B` (`y` isn't in it), so `B` isn't minimal. Absurd.

## The theorem

The theorem states that a compact convex set `A` is the closure of the convex hull of its extreme
points. It is an almost immediate strengthening of the lemma. The proof goes:
1. By contradiction, `A \ closure (convex_hull A.extreme_points)` is nonempty, say with `x`.
2. With the (geometric) Hahn-Banach theorem, find an hyperplane that separates `x` from
  `closure (convex_hull A.extreme_points)`.
3. Look at the extreme (actually exposed) subset of `A \ closure (convex_hull A.extreme_points)`
  obtained by going the furthest away from the separating hyperplane. It is nonempty by assumption
  of nonemptiness and compactness, so by the lemma it has an extreme point.
4. This point is also an extreme point of `A`. Absurd.

## Related theorems

When the space is finite dimensional, the `closure` can be dropped to strengthen the result of the
Krein-Milman theorem. This leads to the Minkowski-Carathéodory theorem (currently not in mathlib).
Birkhoff's theorem is the Minkowski-Carathéodory theorem applied to the set of bistochastic
matrices, permutation matrices being the extreme points.

## References

See chapter 8 of [Barry Simon, *Convexity*][simon2011]

## TODO

*  Both theorems are currently stated for normed `ℝ`-spaces due to the definition of convexity.
  They are more generally true in a LCTVS without changes to the current proofs.
-/

open_locale classical
open set

variables {E : Type*} [normed_group E] [normed_space ℝ E] {A : set E}

theorem geometric_hahn_banach_closed_point {A : set E} {x : E}
  (hA₁ : convex A) (hA₂ : is_closed A)
  (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ s < f x := sorry

theorem geometric_hahn_banach_point_point {x y : E} (hxy : x ≠ y) :
  ∃ (f : E →L[ℝ] ℝ), f x < f y :=
sorry

/-- The Krein-Milman lemma

In a LCTVS (currently only in normed `ℝ`-spaces), any nonempty compact set has an extreme point. -/
lemma is_compact.has_extreme_point (hAcomp : is_compact A) (hAnemp : A.nonempty) :
  A.extreme_points.nonempty :=
begin
  let S : set (set E) := {B | B.nonempty ∧ is_closed B ∧ is_extreme A B},
  suffices h : ∃ B ∈ S, ∀ C ∈ S, C ⊆ B → C = B,
  { obtain ⟨B, ⟨⟨x, hxB⟩, hBclos, hAB⟩, hBmin⟩ := h,
    refine ⟨x, mem_extreme_points_iff_extreme_singleton.2 _⟩,
    convert hAB,
    rw eq_comm,
    refine eq_singleton_iff_unique_mem.2 ⟨hxB, λ y hyB, _⟩,
    by_contra hyx,
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hyx,
    obtain ⟨z, hzB, hz⟩ := (compact_of_is_closed_subset hAcomp hBclos hAB.1).exists_forall_ge
      ⟨x, hxB⟩ l.continuous.continuous_on,
    have h : is_exposed B {z ∈ B | ∀ w ∈ B, l w ≤ l z} := λ h, ⟨l, rfl⟩,
    rw ←hBmin {z ∈ B | ∀ w ∈ B, l w ≤ l z} ⟨⟨z, hzB, hz⟩, h.is_closed hBclos, hAB.trans
      h.is_extreme⟩ (λ z hz, hz.1) at hyB,
    exact hl.not_le (hyB.2 x hxB) },
  apply zorn.zorn_superset,
  rintro F hFS hF,
  obtain rfl | hFnemp := F.eq_empty_or_nonempty,
  { exact ⟨A, ⟨hAnemp, hAcomp.is_closed, is_extreme.refl _⟩, λ B hB, false.elim hB⟩ },
  refine ⟨⋂₀ F, ⟨_, is_closed_sInter (λ B hB, (hFS hB).2.1), is_extreme.sInter hFnemp
    (λ B hB, (hFS hB).2.2)⟩, λ B hB, sInter_subset_of_mem hB⟩,
  haveI : nonempty ↥F := hFnemp.to_subtype,
  rw sInter_eq_Inter,
  refine is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _ (λ B C, _)
    (λ B, (hFS (subtype.mem _)).1)
    (λ B, compact_of_is_closed_subset hAcomp (hFS (subtype.mem _)).2.1 (hFS (subtype.mem _)).2.2.1)
    (λ B, (hFS (subtype.mem _)).2.1),
  obtain hBC | hCB := zorn.chain.total_of_refl hF (subtype.mem B) (subtype.mem C),
  exacts [⟨B, subset.refl _, hBC⟩, ⟨C, hCB, subset.refl _⟩],
end

/-- The Krein-Milman theorem

In a LCTVS (currently only in normed `ℝ`-spaces), any compact convex set is the closure of the
convex hull of its extreme points. -/
lemma eq_closure_convex_hull_extreme_points (hAcomp : is_compact A) (hAconv : convex A) :
  A = closure (convex_hull A.extreme_points) :=
begin
  let B := closure (convex_hull A.extreme_points),
  refine subset.antisymm _ (closure_minimal (convex_hull_min (λ x hx, hx.1) hAconv)
    (is_compact.is_closed hAcomp)),
  by_contra hAB,
  have hABdiff : (A \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
  obtain ⟨l, s, hls, hsx⟩ := geometric_hahn_banach_closed_point
    (convex_convex_hull _).closure is_closed_closure hxB,
  have h : is_exposed A {y ∈ A | ∀ z ∈ A, l z ≤ l y} := λ _, ⟨l, rfl⟩,
  obtain ⟨z, hzA, hz⟩ := hAcomp.exists_forall_ge ⟨x, hxA⟩ l.continuous.continuous_on,
  obtain ⟨y, hy⟩ := (h.is_compact hAcomp).has_extreme_point ⟨z, set.mem_sep hzA hz⟩,
  linarith [hls _ (subset_closure (subset_convex_hull _
    (h.is_extreme.extreme_points_subset_extreme_points hy))), hy.1.2 x hxA],
end
