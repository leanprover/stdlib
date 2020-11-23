/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import data.finset
import data.fintype.basic
import combinatorics.basic
import combinatorics.shadows
import combinatorics.colex

/-!
# compressions/UV

UV compressions are immensely useful to prove the Kruskal-Katona theorem.
The idea is that compressing a set family might decrease the size of its
shadow, and so iterated compressions should hopefully minimise the shadow.

The main result proved is:

theorem compression_reduces_shadow {𝒜 : finset (finset α)} {U V : finset α}
    (h₁ : ∀ x ∈ U, ∃ y ∈ V, is_compressed (erase U x) (erase V y) 𝒜)
    (h₂ : U.card = V.card) : (∂ compress_family U V 𝒜).card ≤ (∂𝒜).card

It says that the shadow size decreases under particular conditions -
most importantly, that for every x ∈ U, there is y ∈ V such that the family
is (U-x, V-y) compressed.

## Tags

compression, UV-compression, shadow

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
-/

open fintype
open finset

variable {α : Type*}
variables [decidable_eq α]

variables {n : ℕ}

-- The namespace here is useful to distinguish between other compressions.
namespace UV
  /--
  To UV-compress A, if it doesn't touch U and does contain V, we remove V and
  put U in. We'll only really use this when |U| = |V| and U ∩ V = ∅.
  -/
  def compress (U V : finset α) (A : finset α) :=
  if disjoint U A ∧ (V ⊆ A)
    then (A ∪ U) \ V
    else A

  /-- Compression doesn't change the size of a set. -/
  lemma compress_size (U V : finset α) (A : finset α) (h₁ : U.card = V.card) :
    (compress U V A).card = A.card :=
  begin
    rw compress, split_ifs,
      rw [card_sdiff (subset.trans h.2 (subset_union_left _ _)),
          card_disjoint_union h.1.symm, h₁, nat.add_sub_cancel],
    refl
  end

  /-- Compressing a set is idempotent. -/
  lemma compress_idem (U V : finset α) (A : finset α) :
    compress U V (compress U V A) = compress U V A :=
  begin
    simp only [compress], split_ifs,
      suffices: U = ∅,
        rw [this, union_empty, union_empty, sdiff_idem],
      have: U \ V = U := sdiff_eq_self_of_disjoint
                         (disjoint_of_subset_right h.2 h.1),
      rw ← disjoint_self_iff_empty,
      apply disjoint_of_subset_right (subset_union_right (A\V) _),
      rw [union_sdiff_distrib, ‹U \ V = U›] at h_1,
    all_goals { tauto }
  end

  /--
  Part of the compressed family, where we keep sets whose compression is
  already present.
  -/
  @[reducible]
  def compress_remains (U V : finset α) (𝒜 : finset (finset α)) :=
  𝒜.filter (λ A, compress U V A ∈ 𝒜)
  /--
  Part of the compressed family, where we move the sets whose compression is
  not there.
  -/
  @[reducible]
  def compress_motion (U V : finset α) (𝒜 : finset (finset α)) :=
  (𝒜.filter (λ A, compress U V A ∉ 𝒜)).image (λ A, compress U V A)

  /--
  To UV-compress a set family, we keep all the sets whose compression is
  present, and move all the sets whose compression is not there (and take this
  union).
  -/
  def compress_family (U V : finset α) (𝒜 : finset (finset α)) :=
  compress_motion U V 𝒜 ∪ compress_remains U V 𝒜
  local notation `CC` := compress_family

  lemma mem_compress_remains  {𝒜 : finset (finset α)} (U V A : finset α) :
  A ∈ compress_remains U V 𝒜 ↔ A ∈ 𝒜 ∧ compress U V A ∈ 𝒜 :=
  by rw mem_filter

  lemma mem_compress_motion {𝒜 : finset (finset α)} (U V A : finset α) :
  A ∈ compress_motion U V 𝒜 ↔ A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress U V B = A) :=
  begin
    simp [compress_motion],
    split; rintro ⟨p, q, r⟩,
      exact ⟨r ▸ q.2, p, ⟨q.1, r⟩⟩,
    exact ⟨q, ⟨r.1, r.2.symm ▸ p⟩, r.2⟩,
  end

  /--
  `A` is in the UV-compressed family iff it's in the original and its
  compression is in the original, or it's not in the original but it's the
  compression of something in the original
  -/
  lemma mem_compress {𝒜 : finset (finset α)} (U V : finset α) {A : finset α} :
    A ∈ CC U V 𝒜 ↔
    (A ∉ 𝒜 ∧ (∃ B ∈ 𝒜, compress U V B = A)) ∨ (A ∈ 𝒜 ∧ compress U V A ∈ 𝒜) :=
  by rw [compress_family, mem_union, mem_compress_remains, mem_compress_motion]

  /-- `is_compressed U V 𝒜` expresses that 𝒜 is UV-compressed -/
  @[reducible]
  def is_compressed (U V : finset α) (𝒜 : finset (finset α)) :=
  CC U V 𝒜 = 𝒜

  /-- The empty family is compressed. -/
  lemma is_compressed_empty (𝒜 : finset (finset α)) : is_compressed ∅ ∅ 𝒜 :=
  begin
    have q: ∀ (A : finset α), compress ∅ ∅ A = A, simp [compress],
    simp [is_compressed, compress_family], --ext, q]s
    sorry,
  end

  /--
  Compressing a set doesn't change it's size, so compressing a family keeps
  all sets the same size.
  -/
  lemma compress_family_sized {r : ℕ} {𝒜 : finset (finset α)} {U V : finset α}
    (h₁ : U.card = V.card) (h₂ : all_sized 𝒜 r) :
    all_sized (CC U V 𝒜) r :=
  begin
    intros A HA, rw mem_compress at HA,
    rcases HA with ⟨_, _, z₁, rfl⟩ | ⟨z₁, _⟩,
      rw compress_size _ _ _ h₁,
    all_goals {apply h₂ _ z₁}
  end

  /-- Compressing a family is idempotent. -/
  lemma compress_family_idempotent (U V : finset α) (𝒜 : finset (finset α)) :
    CC U V (CC U V 𝒜) = CC U V 𝒜 :=
  begin
    have: ∀ A ∈ CC U V 𝒜, compress U V A ∈ CC U V 𝒜,
      intros A HA, rw mem_compress at HA ⊢, simp [compress_idem],
      rcases HA with ⟨_, B, _, rfl⟩ | ⟨_, _⟩,
        left, refine ⟨_, B, ‹_›, _⟩; rwa compress_idem,
      right, assumption,
    have: filter (λ A, compress U V A ∉ CC U V 𝒜) (CC U V 𝒜) = ∅,
      rw ← filter_false (CC U V 𝒜), apply filter_congr, simpa,
    rw [compress_family, compress_motion, this, image_empty, union_comm,
        compress_remains, ← this],
    apply filter_union_filter_neg_eq (compress_family U V 𝒜)
  end

  lemma compress_disjoint {𝒜 : finset (finset α)} (U V : finset α) :
    disjoint (compress_motion U V 𝒜) (compress_remains U V 𝒜) :=
  begin
    rw disjoint_left, intros A HA HB,
    rw mem_compress_remains at HB,
    rw mem_compress_motion at HA,
    exact HA.1 HB.1
  end

  /-- Compression is kinda injective. -/
  lemma inj_ish {U V : finset α} {A B : finset α}
    (hA : disjoint U A ∧ V ⊆ A) (hB : disjoint U B ∧ V ⊆ B)
    (Z : (A ∪ U) \ V = (B ∪ U) \ V) : A = B :=
  begin
    ext x, split,
    all_goals {
      intro p, by_cases h₁: (x ∈ V), { exact hB.2 h₁ <|> exact hA.2 h₁ },
      have := mem_sdiff.2 ⟨mem_union_left U ‹_›, h₁⟩,
      rw Z at this <|> rw ← Z at this,
      rw [mem_sdiff, mem_union] at this,
      suffices: x ∉ U, tauto,
      apply disjoint_right.1 ‹disjoint _ _ ∧ _›.1 p }
  end

  /-- Compressing a set family doesn't change its size. -/
  lemma compressed_size {𝒜 : finset (finset α)} (U V : finset α) :
   (CC U V 𝒜).card = 𝒜.card :=
  begin
    rw [compress_family, card_disjoint_union (compress_disjoint _ _),
        card_image_of_inj_on],
      rw [← card_disjoint_union, union_comm, filter_union_filter_neg_eq],
      rw [disjoint_iff_inter_eq_empty, inter_comm],
      apply filter_inter_filter_neg_eq,
    intros A HA B HB Z,
    rw mem_filter at HA HB, rw compress at HA Z, split_ifs at HA Z,
      rw compress at HB Z,
      split_ifs at HB Z,
        exact inj_ish h h_1 Z,
      tauto,
    tauto
  end

  /--
  If A is in the compressed family but V is a subset of A, A must have been
  in the original family.
  -/
  lemma compress_held {𝒜 : finset (finset α)} {U V A : finset α}
    (h₁ : A ∈ CC U V 𝒜) (h₂ : V ⊆ A) (h₃ : U.card = V.card) :
    A ∈ 𝒜 :=
  begin
    rw mem_compress at h₁, rcases h₁ with ⟨_, B, H, HB⟩ | _,
      rw compress at HB, split_ifs at HB,
        have: V = ∅,
          apply eq_empty_of_forall_not_mem,
          intros x xV, replace h₂ := h₂ xV,
          rw [← HB, mem_sdiff] at h₂, exact h₂.2 xV,
        have: U = ∅,
          rwa [← card_eq_zero, h₃, card_eq_zero],
        rw [‹U = ∅›, ‹V = ∅›, union_empty, sdiff_empty] at HB, rwa ← HB,
      rwa ← HB,
    tauto
  end

  /--
  If A is not in the original family but is in the compressed family, then
  A has been compressed, and its original was in the original family.
  -/
  lemma compress_moved {𝒜 : finset (finset α)} {U V A : finset α}
    (h₁ : A ∈ CC U V 𝒜) (h₂ : A ∉ 𝒜) :
    U ⊆ A ∧ disjoint V A ∧ (A ∪ V) \ U ∈ 𝒜 :=
  begin
    rw mem_compress at h₁,
    rcases h₁ with ⟨_, B, H, HB⟩ | _,
    { rw compress at HB,
      split_ifs at HB,
      { rw ← HB at *, refine ⟨_, disjoint_sdiff, _⟩,
          have: disjoint U V := disjoint_of_subset_right h.2 h.1,
          rw union_sdiff_distrib, rw sdiff_eq_self_of_disjoint this,
          apply subset_union_right _ _,
        rwa [sdiff_union_of_subset, union_sdiff_self,
             sdiff_eq_self_of_disjoint h.1.symm],
        apply trans h.2 (subset_union_left _ _) },
      { rw HB at *, tauto } },
    tauto
  end

  /--
  If A is in the compressed family and does move under compression, then the
  compressed version was in the original family.
  -/
  lemma uncompressed_was_already_there {𝒜 : finset (finset α)}
    {U V A : finset α} (h₁ : A ∈ CC U V 𝒜) (h₂ : V ⊆ A) (h₃ : disjoint U A) :
    (A ∪ U) \ V ∈ 𝒜 :=
  begin
    rw mem_compress at h₁, have: disjoint U A ∧ V ⊆ A := ⟨h₃, h₂⟩,
    rcases h₁ with ⟨_, B, B_in_A, cB_eq_A⟩ | ⟨_, cA_in_A⟩,
    { by_cases a: (A ∪ U) \ V = A,
        have: U \ V = U, apply sdiff_eq_self_of_disjoint,
          apply (disjoint_of_subset_right h₂ h₃),
        have: U = ∅,
          rw ← disjoint_self_iff_empty,
          suffices: disjoint U (U \ V), rw ‹U \ V = U› at this, assumption,
          apply disjoint_of_subset_right (subset_union_right (A \ V) _),
          rwa [← union_sdiff_distrib, a],
        have: V = ∅,
          rw ← disjoint_self_iff_empty, apply disjoint_of_subset_right h₂,
          rw ← a, apply disjoint_sdiff,
        simpa [a, cB_eq_A.symm, compress, ‹U = ∅›, ‹V = ∅›],
      have: compress U V A = (A ∪ U) \ V, rw compress, split_ifs, refl,
      exfalso, apply a, rw [← this, ← cB_eq_A, compress_idem] },
    { rw compress at cA_in_A, split_ifs at cA_in_A, assumption }
  end

  lemma sdiff_sdiff {A B C : finset α} (h : C ⊆ A) : A \ (B \ C) = A \ B ∪ C :=
  begin
    ext1 i,
    simp only [mem_union, not_and, mem_sdiff],
    push_neg,
    refine ⟨_, _⟩,
    rintro ⟨iA, iBC⟩,
    by_cases (i ∈ C),
    right, exact h,
    left,
    refine ⟨iA, mt iBC h⟩,
    rintro (⟨iA, niB⟩ | iC),
    refine ⟨iA, λ iB, (niB iB).elim⟩,
    refine ⟨h iC, λ _, iC⟩,
  end

  lemma sdiff_erase {A : finset α} {x : α} (h : x ∈ A) : A \ A.erase x = {x} :=
  begin
    rw [← sdiff_singleton_eq_erase, sdiff_sdiff, sdiff_self, empty_union],
    rwa singleton_subset_iff,
  end

  /--
  Here's the key fact about compression for KK. If, for all `x ∈ U` there is
  `y ∈ V` such that `𝒜` is `(U-x,V-y)`-compressed, then UV-compression will
  reduce the size of `𝒜`'s shadow.
  -/
  theorem compression_reduces_shadow {𝒜 : finset (finset α)} {U V : finset α}
    (h₁ : ∀ x ∈ U, ∃ y ∈ V, is_compressed (erase U x) (erase V y) 𝒜)
    (h₂ : U.card = V.card) : (∂ CC U V 𝒜).card ≤ (∂𝒜).card :=
  begin
    set 𝒜' := compress_family U V 𝒜,
    suffices: (∂𝒜' \ ∂𝒜).card ≤ (∂𝒜 \ ∂𝒜').card,
    { suffices z: card (∂𝒜' \ ∂𝒜 ∪ ∂𝒜' ∩ ∂𝒜) ≤ card (∂𝒜 \ ∂𝒜' ∪ ∂𝒜 ∩ ∂𝒜'),
      { rwa [sdiff_union_inter, sdiff_union_inter] at z },
      rw [card_disjoint_union, card_disjoint_union, inter_comm],
      apply add_le_add_right ‹_›,
      any_goals { apply disjoint_sdiff_inter } },

    -- We'll define an injection ∂𝒜' \ ∂𝒜 → ∂𝒜 \ ∂𝒜'. First, let's prove
    -- a few facts about things in the domain:
    have q₁: ∀ B ∈ ∂𝒜' \ ∂𝒜, U ⊆ B ∧ disjoint V B ∧ (B ∪ V) \ U ∈ ∂𝒜 \ ∂𝒜',
    { intros B HB,
      obtain ⟨k, k'⟩: B ∈ ∂𝒜' ∧ B ∉ ∂𝒜 := mem_sdiff.1 HB,
      -- This is gonna be useful a couple of times so let's name it.
      have m: ∀ y ∉ B, insert y B ∉ 𝒜 := λ y H a, k' (mem_shadow'.2 ⟨y, H, a⟩),
      rcases mem_shadow'.1 k with ⟨x, _, _⟩,
      have q := compress_moved ‹insert x B ∈ 𝒜'› (m _ ‹x ∉ B›),
      have : disjoint V B := (disjoint_insert_right.1 q.2.1).2,
      have dVU : disjoint V U := disjoint_of_subset_right q.1 q.2.1,
      have: V \ U = V := sdiff_eq_self_of_disjoint ‹disjoint V U›,
      -- The first key part is that x ∉ U
      have: x ∉ U,
      { intro a,
        rcases h₁ x ‹x ∈ U› with ⟨y, Hy, xy_comp⟩,
        -- If `x ∈ U`, we can get `y ∈ V` so that `𝒜` is `(U-x,V-y)`-compressed
        apply m y (disjoint_left.1 ‹disjoint V B› Hy),
        -- and we'll use this `y` to contradict `m`.
        rw is_compressed at xy_comp,
        have: (insert x B ∪ V) \ U ∈ compress_family (erase U x) (erase V y) 𝒜,
          rw xy_comp, exact q.2.2,
        -- So we'd like to show insert y B ∈ 𝒜.
        -- We do this by showing the below
        have: ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y ∈ 𝒜,
          apply uncompressed_was_already_there this _,
            apply disjoint_of_subset_left (erase_subset _ _) disjoint_sdiff,
          rw [union_sdiff_distrib, ‹V \ U = V›],
          apply subset.trans (erase_subset _ _) (subset_union_right _ _),
        -- and then arguing that it's the same
        suffices : ((insert x B ∪ V) \ U ∪ erase U x) \ erase V y = insert y B,
          rwa ← this,
        have : x ∉ B ∪ V := not_mem_union.2 ⟨‹x ∉ B›, disjoint_right.1 ‹disjoint V U› a⟩,
        have : erase U x ⊆ insert x B ∪ V := trans (erase_subset x _)
                                             (trans q.1 (subset_union_left _ V)),
        -- which is just a pain.
        rw [← sdiff_sdiff ‹U.erase x ⊆ insert x B ∪ V›, sdiff_erase ‹x ∈ U›,
            sdiff_singleton_eq_erase, insert_union, erase_insert ‹x ∉ B ∪ V›, union_sdiff_distrib,
            sdiff_erase ‹y ∈ V›, sdiff_eq_self_of_disjoint, union_comm, insert_eq],
        rw [disjoint.comm],
        apply disjoint_of_subset_left (erase_subset _ _) ‹disjoint V B› },
      -- Now that that's done, it's immediate that U ⊆ B
      have: U ⊆ B, rw [← erase_eq_of_not_mem ‹x ∉ U›, ← subset_insert_iff], exact q.1,
      -- and we already had that V and B are disjoint
      refine ⟨‹_›, ‹_›, _⟩,
      -- so it only remains to get (B ∪ V) \ U ∈ ∂𝒜 \ ∂𝒜'
      rw mem_sdiff,
      have: x ∉ V := disjoint_right.1 q.2.1 (mem_insert_self _ _),
      split,
        -- (B ∪ V) \ U ∈ ∂𝒜 is pretty direct:
        rw mem_shadow',
        refine ⟨x, _, _⟩,
        { simp [mem_sdiff, mem_union], tauto! },
        convert q.2.2,
        rw [insert_eq, insert_eq, union_assoc, union_sdiff_distrib _ (B ∪ V),
            sdiff_eq_self_of_disjoint (singleton_disjoint.2 ‹x ∉ U›)],
      -- For (B ∪ V) \ U ∉ ∂𝒜', we split up based on w ∈ U
      rw mem_shadow', rintro ⟨w, _, _⟩, by_cases (w ∈ U),
        -- If w ∈ U, we find z ∈ V, and contradict m again
        rcases h₁ w ‹w ∈ U› with ⟨z, Hz, xy_comp⟩,
        apply m z (disjoint_left.1 ‹disjoint V B› Hz),
        have: insert w ((B ∪ V) \ U) ∈ 𝒜,
        { apply compress_held a_h_h _ h₂,
          apply subset.trans _ (subset_insert _ _),
          rw union_sdiff_distrib, rw ‹V \ U = V›, apply subset_union_right },
        have: (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z ∈ 𝒜,
          refine uncompressed_was_already_there _ _ _,
              rw is_compressed at xy_comp, rwa xy_comp,
            apply subset.trans (erase_subset _ _),
            apply subset.trans _ (subset_insert _ _),
            rw [union_sdiff_distrib, ‹V \ U = V›], apply subset_union_right,
          rw disjoint_insert_right, split, apply not_mem_erase,
          apply disjoint_of_subset_left (erase_subset _ _), apply disjoint_sdiff,
        have: (insert w ((B ∪ V) \ U) ∪ erase U w) \ erase V z = insert z B,
          rw [insert_union, ← union_insert, insert_erase h,
              sdiff_union_of_subset (subset.trans ‹U ⊆ B› (subset_union_left _ _)),
              union_sdiff_distrib,
              sdiff_eq_self_of_disjoint (disjoint_of_subset_right (erase_subset _ _) ‹disjoint V B›.symm),
              ← sdiff_singleton_eq_erase, sdiff_sdiff_self_left,
              inter_singleton_of_mem Hz, union_comm], refl,
        rwa ← this,
      -- If w ∉ U, we contradict m again
      rw [mem_sdiff, ← not_imp, not_not] at a_h_w,
      have: w ∉ V := h ∘ a_h_w ∘ mem_union_right _,
      have: w ∉ B := h ∘ a_h_w ∘ mem_union_left _,
      apply m w this,

      have: (insert w ((B ∪ V) \ U) ∪ U) \ V ∈ 𝒜,
        refine uncompressed_was_already_there ‹insert w ((B ∪ V) \ U) ∈ 𝒜'›
               (trans _ (subset_insert _ _)) _,
          rw [union_sdiff_distrib, ‹V \ U = V›], apply subset_union_right,
          rw disjoint_insert_right, exact ⟨‹_›, disjoint_sdiff⟩,
      convert this, rw [insert_union, sdiff_union_of_subset (trans ‹U ⊆ B› (subset_union_left _ _)),
                        ← insert_union, union_sdiff_self], symmetry,
      rw [sdiff_eq_self_iff_disjoint, disjoint_insert_left], split, assumption,
      rwa disjoint.comm },
    apply card_le_card_of_inj_on (λ B, (B ∪ V) \ U) (λ B HB, (q₁ B HB).2.2),
    intros B₁ HB₁ B₂ HB₂ k,
    exact inj_ish ⟨(q₁ B₁ HB₁).2.1, (q₁ B₁ HB₁).1⟩ ⟨(q₁ B₂ HB₂).2.1, (q₁ B₂ HB₂).1⟩ k
  end
end UV
