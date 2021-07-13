/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import topology.compact_open
import topology.stone_cech

/-!

# Extremally disconnected spaces

An extremally disconnected topological space is a space
in which the closure of every open set is open.
Such spaces are also called Stonean spaces.
They are the projective objects in the category of compact Hausdorff spaces;
this fact is proven in `TODO`.

## References

Gleason, Andrew M. (1958), "Projective topological spaces",
Illinois Journal of Mathematics, 2 (4A): 482–489,
doi:10.1215/ijm/1255454110, MR 0121775
-/

universe variables u v w

noncomputable theory
open_locale classical

variables (X : Type u) [topological_space X]

open function

/-- An extremally disconnected topological space is a space
in which the closure of every open set is open.
Such spaces are also called Stonean spaces.
They are the projective objects in the category of compact Hausdorff spaces;
this fact is proven in `TODO`. -/
class extremally_disconnected : Prop :=
(open_closure : ∀ U : set X, is_open U → is_open (closure U))

section

include X
/--  The assertion `compact_t2.projective` states that given continuous maps
`f : X → Z` and `g : Y → Z` with `g` surjective between `t_2`, compact topological spaces,
there exists a continuous lift `h : X → Y`, such that `f = g ∘ h`. -/
def compact_t2.projective : Prop :=
  Π {Y Z : Type u} [topological_space Y] [topological_space Z],
  by exactI Π [compact_space Y] [t2_space Y] [compact_space Z] [t2_space Z],
  by exactI Π {f : X → Z} {g : Y → Z} (hf : continuous f) (hg : continuous g)
    (g_sur : surjective g),
  ∃ h : X → Y, continuous h ∧ g ∘ h = f

end

variable {X}

lemma stone_cech_unit_dense {X : Type u} [topological_space X] :
  closure (set.range (stone_cech_unit : X → stone_cech X)) = set.univ :=
dense.closure_eq dense_range_stone_cech_unit

lemma stone_cech.projective [discrete_topology X] : compact_t2.projective (stone_cech X) :=
begin
  introsI Y Z _tsY _tsZ _csY _t2Y _csZ _csZ f g hf hg g_sur,
  have H : dense_range (stone_cech_unit : X → stone_cech X),
  { rw dense_range_iff_closure_range, exact stone_cech_unit_dense },
  let s : Z → Y := λ z, classical.some $ g_sur z,
  have hs : g ∘ s = id := funext (λ z, classical.some_spec (g_sur z)),
  let t := s ∘ f ∘ stone_cech_unit,
  have ht : continuous t := continuous_of_discrete_topology,
  let h : stone_cech X → Y := stone_cech_extend ht,
  have hh : continuous h := continuous_stone_cech_extend ht,
  use [h, hh],
  apply H.equalizer (hg.comp hh) hf,
  rw [comp.assoc, stone_cech_extend_extends ht, ← comp.assoc, hs, comp.left_id],
end

lemma extremally_disconnected_of_projective [compact_space X] [t2_space X]
  (h : compact_t2.projective X) :
  extremally_disconnected X :=
begin
  refine { open_closure := λ U hU, _ },
  let Z₁ : set (X × bool) := (Uᶜ).prod {tt},
  let Z₂ : set (X × bool) := (closure U).prod {ff},
  let Z : set (X × bool) := Z₁ ∪ Z₂,
  have hZ₁ : is_closed Z₁ := is_closed.prod (is_closed_compl_iff.mpr hU) (t1_space.t1 tt),
  have hZ₂ : is_closed Z₂ := is_closed.prod is_closed_closure (t1_space.t1 ff),
  have hZ : is_closed Z := is_closed.union hZ₁ hZ₂,
  have h_compl : ((subtype.val : Z → (X × bool)) ⁻¹' Z₂)ᶜ = subtype.val ⁻¹' Z₁,
  { ext x, cases x with x hx, change x ∈ (_ ∪ _) at hx,
    simp only [set.mem_preimage, not_and, eq_tt_eq_not_eq_ff, set.mem_singleton_iff,
      set.mem_prod, set.mem_union_eq, set.mem_compl_eq] at hx ⊢,
    rcases hx with hx | ⟨hx1, hx2⟩,
    { simp only [hx, implies_true_iff, eq_self_iff_true, not_false_iff, and_self] },
    { simp only [hx1, hx2, forall_true_left, and_false] } },
  let f : Z → X := prod.fst ∘ subtype.val,
  have f_cont : continuous f := continuous_fst.comp continuous_subtype_val,
  have f_sur : surjective f,
  { intro x, by_cases hx : x ∈ U,
    { refine ⟨⟨(x, ff), _⟩, rfl⟩, right, exact ⟨subset_closure hx, set.mem_singleton _⟩ },
    { refine ⟨⟨(x, tt), _⟩, rfl⟩, left, refine ⟨hx, set.mem_singleton _⟩ } },
  haveI : compact_space Z := is_compact_iff_compact_space.mp hZ.is_compact,
  rcases h continuous_id f_cont f_sur with ⟨g, hg, g_sec⟩,
  let φ := subtype.val ∘ g,
  have hφ : continuous φ := continuous_subtype_val.comp hg,
  have hfstφ : prod.fst ∘ φ = id := by rwa comp.assoc at g_sec,
  suffices : closure U = φ ⁻¹' Z₂,
  { rw [this, set.preimage_comp], apply continuous_def.mp hg,
    rw [← is_closed_compl_iff, h_compl],
    exact continuous_iff_is_closed.mp continuous_subtype_val Z₁ hZ₁ },
  have key : ∀ x ∈ U, φ x = (x, ff),
  { intros x hx,
    replace hfstφ := congr_fun hfstφ x, rw comp_apply at hfstφ,
    ext, { exact hfstφ },
    { have : φ x ∈ (Z₁ ∪ Z₂) := (g x).property,
      simp [hx, hfstφ] at this, exact this.2 } },
  apply set.subset.antisymm,
  { apply closure_minimal _ (continuous_iff_is_closed.mp hφ Z₂ hZ₂),
    intros x hx, simp [key _ hx], exact subset_closure hx },
  { intros x hx, rw [set.mem_preimage, set.mem_prod] at hx,
    replace hfstφ := congr_fun hfstφ x, rw comp_apply at hfstφ,
    rw hfstφ at hx, exact hx.1 }
end
