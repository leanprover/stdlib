/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import topology.algebra.group
/-!
# Topology on lists and vectors

-/
open topological_space set filter
open_locale topological_space filter

variables {α : Type*} {β : Type*} [topological_space α] [topological_space β]

instance : topological_space (list α) :=
topological_space.mk_of_nhds (traverse nhds)

lemma nhds_list (as : list α) : 𝓝 as = traverse 𝓝 as :=
begin
  refine nhds_mk_of_nhds _ _ _ _,
  { assume l, induction l,
    case list.nil { exact le_refl _ },
    case list.cons : a l ih {
      suffices : list.cons <$> pure a <*> pure l ≤ list.cons <$> 𝓝 a <*> traverse 𝓝 l,
      { simpa only [] with functor_norm using this },
      exact filter.seq_mono (filter.map_mono $ pure_le_nhds a) ih } },
  { assume l s hs,
    rcases (mem_traverse_sets_iff _ _).1 hs with ⟨u, hu, hus⟩, clear as hs,
    have : ∃v:list (set α), l.forall₂ (λa s, is_open s ∧ a ∈ s) v ∧ sequence v ⊆ s,
    { induction hu generalizing s,
      case list.forall₂.nil : hs this
        { existsi [], simpa only [list.forall₂_nil_left_iff, exists_eq_left] },
      case list.forall₂.cons : a s as ss ht h ih t hts {
        rcases mem_nhds_sets_iff.1 ht with ⟨u, hut, hu⟩,
        rcases ih (subset.refl _) with ⟨v, hv, hvss⟩,
        exact ⟨u::v, list.forall₂.cons hu hv,
          subset.trans (set.seq_mono (set.image_subset _ hut) hvss) hts⟩ } },
    rcases this with ⟨v, hv, hvs⟩,
    refine ⟨sequence v, mem_traverse_sets _ _ _, hvs, _⟩,
    { exact hv.imp (assume a s ⟨hs, ha⟩, mem_nhds_sets hs ha) },
    { assume u hu,
      have hu := (list.mem_traverse _ _).1 hu,
      have : list.forall₂ (λa s, is_open s ∧ a ∈ s) u v,
      { refine list.forall₂.flip _,
        replace hv := hv.flip,
        simp only [list.forall₂_and_left, flip] at ⊢ hv,
        exact ⟨hv.1, hu.flip⟩ },
      refine mem_sets_of_superset _ hvs,
      exact mem_traverse_sets _ _ (this.imp $ assume a s ⟨hs, ha⟩, mem_nhds_sets hs ha) } }
end

@[simp] lemma nhds_nil : 𝓝 ([] : list α) = pure [] :=
by rw [nhds_list, list.traverse_nil _]; apply_instance

lemma nhds_cons (a : α) (l : list α) :
  𝓝 (a :: l) = list.cons <$> 𝓝 a <*> 𝓝 l  :=
by rw [nhds_list, list.traverse_cons _, ← nhds_list]; apply_instance

lemma list.tendsto_cons {a : α} {l : list α} :
  tendsto (λp:α×list α, list.cons p.1 p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a :: l)) :=
by rw [nhds_cons, tendsto, map_prod]; exact le_refl _

lemma filter.tendsto.cons {α : Type*} {f : α → β} {g : α → list β}
  {a : _root_.filter α} {b : β} {l : list β} (hf : tendsto f a (𝓝 b)) (hg : tendsto g a (𝓝 l)) :
  tendsto (λa, list.cons (f a) (g a)) a (𝓝 (b :: l)) :=
list.tendsto_cons.comp (tendsto.prod_mk hf hg)

namespace list

lemma tendsto_cons_iff {β : Type*} {f : list α → β} {b : _root_.filter β} {a : α} {l : list α} :
  tendsto f (𝓝 (a :: l)) b ↔ tendsto (λp:α×list α, f (p.1 :: p.2)) (𝓝 a ×ᶠ 𝓝 l) b :=
have 𝓝 (a :: l) = (𝓝 a ×ᶠ 𝓝 l).map (λp:α×list α, (p.1 :: p.2)),
begin
  simp only
    [nhds_cons, filter.prod_eq, (filter.map_def _ _).symm, (filter.seq_eq_filter_seq _ _).symm],
  simp [-filter.seq_eq_filter_seq, -filter.map_def, (∘)] with functor_norm,
end,
by rw [this, filter.tendsto_map'_iff]

lemma continuous_cons : continuous (λ x : α × list α, (x.1 :: x.2 : list α)) :=
continuous_iff_continuous_at.mpr $ λ ⟨x, y⟩, continuous_at_fst.cons continuous_at_snd

lemma tendsto_nhds {β : Type*} {f : list α → β} {r : list α → _root_.filter β}
  (h_nil : tendsto f (pure []) (r []))
  (h_cons : ∀l a, tendsto f (𝓝 l) (r l) → tendsto (λp:α×list α, f (p.1 :: p.2)) (𝓝 a ×ᶠ 𝓝 l) (r (a::l))) :
  ∀l, tendsto f (𝓝 l) (r l)
| []     := by rwa [nhds_nil]
| (a::l) := by rw [tendsto_cons_iff]; exact h_cons l a (tendsto_nhds l)

lemma continuous_at_length :
  ∀(l : list α), continuous_at list.length l :=
begin
  simp only [continuous_at, nhds_discrete],
  refine tendsto_nhds _ _,
  { exact tendsto_pure_pure _ _ },
  { assume l a ih,
    dsimp only [list.length],
    refine tendsto.comp (tendsto_pure_pure (λx, x + 1) _) _,
    refine tendsto.comp ih tendsto_snd }
end

lemma tendsto_insert_nth' {a : α} : ∀{n : ℕ} {l : list α},
  tendsto (λp:α×list α, insert_nth n p.1 p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (insert_nth n a l))
| 0     l  := tendsto_cons
| (n+1) [] := by simp
| (n+1) (a'::l) :=
  have 𝓝 a ×ᶠ 𝓝 (a' :: l) =
    (𝓝 a ×ᶠ (𝓝 a' ×ᶠ 𝓝 l)).map (λp:α×α×list α, (p.1, p.2.1 :: p.2.2)),
  begin
    simp only [nhds_cons, filter.prod_eq, ← filter.map_def, ← filter.seq_eq_filter_seq],
    simp [-filter.seq_eq_filter_seq, -filter.map_def, (∘)] with functor_norm
  end,
  begin
    rw [this, tendsto_map'_iff],
    exact (tendsto_fst.comp tendsto_snd).cons
      ((@tendsto_insert_nth' n l).comp $ tendsto_fst.prod_mk $ tendsto_snd.comp tendsto_snd)
  end

lemma tendsto_insert_nth {β} {n : ℕ} {a : α} {l : list α} {f : β → α} {g : β → list α}
  {b : _root_.filter β} (hf : tendsto f b (𝓝 a)) (hg : tendsto g b (𝓝 l)) :
  tendsto (λb:β, insert_nth n (f b) (g b)) b (𝓝 (insert_nth n a l)) :=
tendsto_insert_nth'.comp (tendsto.prod_mk hf hg)

lemma continuous_insert_nth {n : ℕ} : continuous (λp:α×list α, insert_nth n p.1 p.2) :=
continuous_iff_continuous_at.mpr $
  assume ⟨a, l⟩, by rw [continuous_at, nhds_prod_eq]; exact tendsto_insert_nth'

lemma tendsto_remove_nth : ∀{n : ℕ} {l : list α},
  tendsto (λl, remove_nth l n) (𝓝 l) (𝓝 (remove_nth l n))
| _ []      := by rw [nhds_nil]; exact tendsto_pure_nhds _ _
| 0 (a::l) := by rw [tendsto_cons_iff]; exact tendsto_snd
| (n+1) (a::l) :=
  begin
    rw [tendsto_cons_iff],
    dsimp [remove_nth],
    exact tendsto_fst.cons ((@tendsto_remove_nth n l).comp tendsto_snd)
  end

lemma continuous_remove_nth {n : ℕ} : continuous (λl : list α, remove_nth l n) :=
continuous_iff_continuous_at.mpr $ assume a, tendsto_remove_nth

@[to_additive]
lemma tendsto_prod [monoid α] [has_continuous_mul α] {l : list α} :
  tendsto list.prod (𝓝 l) (𝓝 l.prod) :=
begin
  induction l with x l ih, { simp [nhds_nil, mem_of_nhds, tendsto_pure_left] {contextual := tt} },
  simp_rw [tendsto_cons_iff, prod_cons],
  have := continuous_iff_continuous_at.mp continuous_mul (x, l.prod),
  rw [continuous_at, nhds_prod_eq] at this,
  exact this.comp (tendsto_id.prod_map ih)
end

@[to_additive]
lemma continuous_prod [monoid α] [has_continuous_mul α] : continuous (prod : list α → α) :=
continuous_iff_continuous_at.mpr $ λ l, tendsto_prod

end list

namespace vector
open list

instance (n : ℕ) : topological_space (vector α n) :=
by unfold vector; apply_instance

lemma tendsto_cons {n : ℕ} {a : α} {l : vector α n}:
  tendsto (λp:α×vector α n, p.1 ::ᵥ p.2) (𝓝 a ×ᶠ 𝓝 l) (𝓝 (a ::ᵥ l)) :=
by { simp [tendsto_subtype_rng, ←subtype.val_eq_coe, cons_val],
  exact tendsto_fst.cons (tendsto.comp continuous_at_subtype_coe tendsto_snd) }

lemma tendsto_insert_nth
  {n : ℕ} {i : fin (n+1)} {a:α} :
  ∀{l:vector α n}, tendsto (λp:α×vector α n, insert_nth p.1 i p.2)
    (𝓝 a ×ᶠ 𝓝 l) (𝓝 (insert_nth a i l))
| ⟨l, hl⟩ :=
begin
  rw [insert_nth, tendsto_subtype_rng],
  simp [insert_nth_val],
  exact list.tendsto_insert_nth tendsto_fst (tendsto.comp continuous_at_subtype_coe tendsto_snd : _)
end

lemma continuous_insert_nth' {n : ℕ} {i : fin (n+1)} :
  continuous (λp:α×vector α n, insert_nth p.1 i p.2) :=
continuous_iff_continuous_at.mpr $ assume ⟨a, l⟩,
  by rw [continuous_at, nhds_prod_eq]; exact tendsto_insert_nth

lemma continuous_insert_nth {n : ℕ} {i : fin (n+1)}
  {f : β → α} {g : β → vector α n} (hf : continuous f) (hg : continuous g) :
  continuous (λb, insert_nth (f b) i (g b)) :=
continuous_insert_nth'.comp (hf.prod_mk hg : _)

lemma continuous_at_remove_nth {n : ℕ} {i : fin (n+1)} :
  ∀{l:vector α (n+1)}, continuous_at (remove_nth i) l
| ⟨l, hl⟩ :=
--  ∀{l:vector α (n+1)}, tendsto (remove_nth i) (𝓝 l) (𝓝 (remove_nth i l))
--| ⟨l, hl⟩ :=
begin
  rw [continuous_at, remove_nth, tendsto_subtype_rng],
  simp only [← subtype.val_eq_coe, vector.remove_nth_val],
  exact tendsto.comp list.tendsto_remove_nth continuous_at_subtype_coe,
end

lemma continuous_remove_nth {n : ℕ} {i : fin (n+1)} :
  continuous (remove_nth i : vector α (n+1) → vector α n) :=
continuous_iff_continuous_at.mpr $ assume ⟨a, l⟩, continuous_at_remove_nth

end vector
