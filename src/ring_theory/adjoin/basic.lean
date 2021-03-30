/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import ring_theory.polynomial.basic
import algebra.algebra.subalgebra

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of subalgebras of an R-algebra generated
by a set of elements. A basic interface for `adjoin` is set up, and various
results about finitely-generated subalgebras and submodules are proved.

## Definitions

* `fg (S : subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/

universes u v w

open submodule

namespace algebra

variables {R : Type u} {A : Type v} {B : Type w}

section semiring
variables [comm_semiring R] [semiring A] [semiring B]
variables [algebra R A] [algebra R B] {s t : set A}
open subsemiring

theorem subset_adjoin : s ⊆ adjoin R s :=
algebra.gc.le_u_l s

theorem adjoin_le {S : subalgebra R A} (H : s ⊆ S) : adjoin R s ≤ S :=
algebra.gc.l_le H

theorem adjoin_le_iff {S : subalgebra R A} : adjoin R s ≤ S ↔ s ⊆ S:=
algebra.gc _ _

theorem adjoin_mono (H : s ⊆ t) : adjoin R s ≤ adjoin R t :=
algebra.gc.monotone_l H

variables (R A)
@[simp] theorem adjoin_empty : adjoin R (∅ : set A) = ⊥ :=
show adjoin R ⊥ = ⊥, by { apply galois_connection.l_bot, exact algebra.gc }

variables (R) {A} (s)
theorem adjoin_eq_span : (adjoin R s).to_submodule = span R (monoid.closure s) :=
begin
  apply le_antisymm,
  { intros r hr, rcases mem_closure_iff_exists_list.1 hr with ⟨L, HL, rfl⟩, clear hr,
    induction L with hd tl ih, { exact zero_mem _ },
    rw list.forall_mem_cons at HL,
    rw [list.map_cons, list.sum_cons],
    refine submodule.add_mem _ _ (ih HL.2),
    replace HL := HL.1, clear ih tl,
    suffices : ∃ (z : R) r (hr : r ∈ monoid.closure s), z • r = list.prod hd,
    { rcases this with ⟨z, r, hr, hzr⟩, rw ← hzr,
      exact smul_mem _ _ (subset_span hr) },
    induction hd with hd tl ih, { exact ⟨1, 1, is_submonoid.one_mem, one_smul _ _⟩ },
    rw list.forall_mem_cons at HL,
    rcases (ih HL.2) with ⟨z, r, hr, hzr⟩, rw [list.prod_cons, ← hzr],
    rcases HL.1 with ⟨hd, rfl⟩ | hs,
    { refine ⟨hd * z, r, hr, _⟩,
      rw [smul_def, smul_def, (algebra_map _ _).map_mul, _root_.mul_assoc] },
    { exact ⟨z, hd * r, is_submonoid.mul_mem (monoid.subset_closure hs) hr,
        (mul_smul_comm _ _ _).symm⟩ } },
  exact span_le.2 (show monoid.closure s ⊆ adjoin R s, from monoid.closure_subset subset_adjoin)
end

lemma adjoin_image (f : A →ₐ[R] B) (s : set A) :
  adjoin R (f '' s) = (adjoin R s).map f :=
le_antisymm (adjoin_le $ set.image_subset _ subset_adjoin) $
subalgebra.map_le.2 $ adjoin_le $ set.image_subset_iff.1 subset_adjoin

@[simp] lemma adjoin_insert_adjoin (x : A) :
  adjoin R (insert x ↑(adjoin R s)) = adjoin R (insert x s) :=
le_antisymm
  (adjoin_le (set.insert_subset.mpr
    ⟨subset_adjoin (set.mem_insert _ _), adjoin_mono (set.subset_insert _ _)⟩))
  (algebra.adjoin_mono (set.insert_subset_insert algebra.subset_adjoin))

end semiring

section comm_semiring
variables [comm_semiring R] [comm_semiring A]
variables [algebra R A] {s t : set A}
open subsemiring

variables (R s t)
theorem adjoin_union : adjoin R (s ∪ t) = (adjoin R s).under (adjoin (adjoin R s) t) :=
le_antisymm
  (closure_mono $ set.union_subset
    (set.range_subset_iff.2 $ λ r, or.inl ⟨algebra_map R (adjoin R s) r, rfl⟩)
    (set.union_subset_union_left _ $ λ x hxs, ⟨⟨_, subset_adjoin hxs⟩, rfl⟩))
  (closure_le.2 $ set.union_subset
    (set.range_subset_iff.2 $ λ x, adjoin_mono (set.subset_union_left _ _) x.2)
    (set.subset.trans (set.subset_union_right _ _) subset_adjoin))

theorem adjoin_eq_range :
  adjoin R s = (mv_polynomial.aeval (coe : s → A)).range :=
le_antisymm
  (adjoin_le $ λ x hx, ⟨mv_polynomial.X ⟨x, hx⟩, set.mem_univ _, mv_polynomial.eval₂_X _ _ _⟩)
  (λ x ⟨p, _, (hp : mv_polynomial.aeval coe p = x)⟩, hp ▸ mv_polynomial.induction_on p
    (λ r, by { rw [mv_polynomial.aeval_def, mv_polynomial.eval₂_C],
               exact (adjoin R s).algebra_map_mem r })
    (λ p q hp hq, by rw alg_hom.map_add; exact subalgebra.add_mem _ hp hq)
    (λ p ⟨n, hn⟩ hp, by rw [alg_hom.map_mul, mv_polynomial.aeval_def _ (mv_polynomial.X _),
      mv_polynomial.eval₂_X]; exact subalgebra.mul_mem _ hp (subset_adjoin hn)))

theorem adjoin_singleton_eq_range (x : A) : adjoin R {x} = (polynomial.aeval x).range :=
le_antisymm
  (adjoin_le $ set.singleton_subset_iff.2 ⟨polynomial.X, set.mem_univ _, polynomial.eval₂_X _ _⟩)
  (λ y ⟨p, _, (hp : polynomial.aeval x p = y)⟩, hp ▸ polynomial.induction_on p
    (λ r, by { rw [polynomial.aeval_def, polynomial.eval₂_C],
               exact (adjoin R _).algebra_map_mem r })
    (λ p q hp hq, by rw alg_hom.map_add; exact subalgebra.add_mem _ hp hq)
    (λ n r ih, by { rw [pow_succ', ← mul_assoc, alg_hom.map_mul,
      polynomial.aeval_def _ polynomial.X, polynomial.eval₂_X],
      exact subalgebra.mul_mem _ ih (subset_adjoin rfl) }))

lemma adjoin_singleton_one : adjoin R ({1} : set A) = ⊥ :=
eq_bot_iff.2 $ adjoin_le $ set.singleton_subset_iff.2 $ subalgebra.mem_coe.2 $ subalgebra.one_mem ⊥

theorem adjoin_union_coe_submodule : (adjoin R (s ∪ t)).to_submodule =
  (adjoin R s).to_submodule * (adjoin R t).to_submodule :=
begin
  rw [adjoin_eq_span, adjoin_eq_span, adjoin_eq_span, span_mul_span],
  congr' 1 with z, simp [monoid.mem_closure_union_iff, set.mem_mul],
end

end comm_semiring

section ring
variables [comm_ring R] [ring A]
variables [algebra R A] {s t : set A}
variables {R s t}
open ring

theorem adjoin_int (s : set R) : adjoin ℤ s = subalgebra_of_is_subring (closure s) :=
le_antisymm (adjoin_le subset_closure) (closure_subset subset_adjoin : closure s ≤ adjoin ℤ s)

theorem mem_adjoin_iff {s : set A} {x : A} :
  x ∈ adjoin R s ↔ x ∈ closure (set.range (algebra_map R A) ∪ s) :=
⟨λ hx, subsemiring.closure_induction hx subset_closure is_add_submonoid.zero_mem
  is_submonoid.one_mem (λ _ _, is_add_submonoid.add_mem) (λ _ _, is_submonoid.mul_mem),
suffices closure (set.range ⇑(algebra_map R A) ∪ s) ⊆ adjoin R s, from @this x,
closure_subset subsemiring.subset_closure⟩


theorem adjoin_eq_ring_closure (s : set A) :
  (adjoin R s : set A) = closure (set.range (algebra_map R A) ∪ s) :=
set.ext $ λ x, mem_adjoin_iff

end ring

section comm_ring
variables [comm_ring R] [comm_ring A]
variables [algebra R A] {s t : set A}
variables {R s t}
open ring

theorem fg_trans (h1 : (adjoin R s).to_submodule.fg)
  (h2 : (adjoin (adjoin R s) t).to_submodule.fg) :
  (adjoin R (s ∪ t)).to_submodule.fg :=
begin
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩,
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩,
  refine fg_def.2 ⟨p * q, hp.mul hq, le_antisymm _ _⟩,
  { rw [span_le],
    rintros _ ⟨x, y, hx, hy, rfl⟩,
    change x * y ∈ _,
    refine is_submonoid.mul_mem _ _,
    { have : x ∈ (adjoin R s).to_submodule,
      { rw ← hp', exact subset_span hx },
      exact adjoin_mono (set.subset_union_left _ _) this },
    have : y ∈ (adjoin (adjoin R s) t).to_submodule,
    { rw ← hq', exact subset_span hy },
    change y ∈ adjoin R (s ∪ t), rwa adjoin_union },
  { intros r hr,
    change r ∈ adjoin R (s ∪ t) at hr,
    rw adjoin_union at hr,
    change r ∈ (adjoin (adjoin R s) t).to_submodule at hr,
    haveI := classical.dec_eq A,
    haveI := classical.dec_eq R,
    rw [← hq', ← set.image_id q, finsupp.mem_span_iff_total (adjoin R s)] at hr,
    rcases hr with ⟨l, hlq, rfl⟩,
    have := @finsupp.total_apply A A (adjoin R s),
    rw [this, finsupp.sum],
    refine sum_mem _ _,
    intros z hz, change (l z).1 * _ ∈ _,
    have : (l z).1 ∈ (adjoin R s).to_submodule := (l z).2,
    rw [← hp', ← set.image_id p, finsupp.mem_span_iff_total R] at this,
    rcases this with ⟨l2, hlp, hl⟩,
    have := @finsupp.total_apply A A R,
    rw this at hl,
    rw [←hl, finsupp.sum_mul],
    refine sum_mem _ _,
    intros t ht, change _ * _ ∈ _, rw smul_mul_assoc, refine smul_mem _ _ _,
    exact subset_span ⟨t, z, hlp ht, hlq hz, rfl⟩ }
end

end comm_ring

end algebra

namespace subalgebra

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_semiring R] [semiring A] [algebra R A] [semiring B] [algebra R B]

/-- A subalgebra `S` is finitely generated if there exists `t : finset A` such that
`algebra.adjoin R t = S`. -/
def fg (S : subalgebra R A) : Prop :=
∃ t : finset A, algebra.adjoin R ↑t = S

lemma fg_adjoin_finset (s : finset A) : (algebra.adjoin R (↑s : set A)).fg :=
⟨s, rfl⟩

theorem fg_def {S : subalgebra R A} : S.fg ↔ ∃ t : set A, set.finite t ∧ algebra.adjoin R t = S :=
⟨λ ⟨t, ht⟩, ⟨↑t, set.finite_mem_finset t, ht⟩,
λ ⟨t, ht1, ht2⟩, ⟨ht1.to_finset, by rwa set.finite.coe_to_finset⟩⟩

theorem fg_bot : (⊥ : subalgebra R A).fg :=
⟨∅, algebra.adjoin_empty R A⟩

theorem fg_of_fg_to_submodule {S : subalgebra R A} : S.to_submodule.fg → S.fg :=
λ ⟨t, ht⟩, ⟨t, le_antisymm
  (algebra.adjoin_le (λ x hx, show x ∈ S.to_submodule, from ht ▸ subset_span hx)) $
  show S.to_submodule ≤ (algebra.adjoin R ↑t).to_submodule,
  from (λ x hx, span_le.mpr
    (λ x hx, algebra.subset_adjoin hx)
      (show x ∈ span R ↑t, by { rw ht, exact hx }))⟩

theorem fg_of_noetherian [is_noetherian R A] (S : subalgebra R A) : S.fg :=
fg_of_fg_to_submodule (is_noetherian.noetherian S.to_submodule)

lemma fg_of_submodule_fg (h : (⊤ : submodule R A).fg) : (⊤ : subalgebra R A).fg :=
let ⟨s, hs⟩ := h in ⟨s, to_submodule_injective $
by { rw [algebra.coe_top, eq_top_iff, ← hs, span_le], exact algebra.subset_adjoin }⟩

section
open_locale classical
lemma fg_map (S : subalgebra R A) (f : A →ₐ[R] B) (hs : S.fg) : (S.map f).fg :=
let ⟨s, hs⟩ := hs in ⟨s.image f, by rw [finset.coe_image, algebra.adjoin_image, hs]⟩
end

lemma fg_of_fg_map (S : subalgebra R A) (f : A →ₐ[R] B) (hf : function.injective f)
  (hs : (S.map f).fg) : S.fg :=
let ⟨s, hs⟩ := hs in ⟨s.preimage f $ λ _ _ _ _ h, hf h, map_injective f hf $
by { rw [← algebra.adjoin_image, finset.coe_preimage, set.image_preimage_eq_of_subset, hs],
  rw [← alg_hom.coe_range, ← algebra.adjoin_le_iff, hs, ← algebra.map_top], exact map_mono le_top }⟩

lemma fg_top (S : subalgebra R A) : (⊤ : subalgebra R S).fg ↔ S.fg :=
⟨λ h, by { rw [← S.range_val, ← algebra.map_top], exact fg_map _ _ h },
λ h, fg_of_fg_map _ S.val subtype.val_injective $ by { rw [algebra.map_top, range_val], exact h }⟩

lemma induction_on_adjoin [is_noetherian R A] (P : subalgebra R A → Prop)
  (base : P ⊥) (ih : ∀ (S : subalgebra R A) (x : A), P S → P (algebra.adjoin R (insert x S)))
  (S : subalgebra R A) : P S :=
begin
  classical,
  obtain ⟨t, rfl⟩ := S.fg_of_noetherian,
  refine finset.induction_on t _ _,
  { simpa using base },
  intros x t hxt h,
  convert ih _ x h using 1,
  rw [finset.coe_insert, algebra.adjoin_insert_adjoin]
end

end subalgebra

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_ring R] [comm_ring A] [comm_ring B] [algebra R A] [algebra R B]

/-- The image of a Noetherian R-algebra under an R-algebra map is a Noetherian ring. -/
instance alg_hom.is_noetherian_ring_range (f : A →ₐ[R] B) [is_noetherian_ring A] :
  is_noetherian_ring f.range :=
is_noetherian_ring_range f.to_ring_hom

theorem is_noetherian_ring_of_fg {S : subalgebra R A} (HS : S.fg)
  [is_noetherian_ring R] : is_noetherian_ring S :=
let ⟨t, ht⟩ := HS in ht ▸ (algebra.adjoin_eq_range R (↑t : set A)).symm ▸
by haveI : is_noetherian_ring (mv_polynomial (↑t : set A) R) :=
mv_polynomial.is_noetherian_ring;
convert alg_hom.is_noetherian_ring_range _; apply_instance

theorem is_noetherian_ring_closure (s : set R) (hs : s.finite) :
  @@is_noetherian_ring (ring.closure s) subset.ring :=
show is_noetherian_ring (subalgebra_of_is_subring (ring.closure s)), from
algebra.adjoin_int s ▸ is_noetherian_ring_of_fg (subalgebra.fg_def.2 ⟨s, hs, rfl⟩)
