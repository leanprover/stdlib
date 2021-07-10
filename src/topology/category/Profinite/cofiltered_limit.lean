/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import topology.category.Profinite
import topology.locally_constant.basic
import topology.discrete_quotient

/-!
# Cofiltered limits of profinite sets.

This file contains some theorems about cofiltered limits of profinite sets.

## Main Results

- `exists_clopen_of_cofiltered` shows that any clopen set in a cofiltered limit of profinite
  sets is the pullback of a clopen set from one of the factors in the limit.
- `exists_locally_constant` shows that any locally constant function from a cofiltered limit
  of profinite sets factors through one of the components.
-/


namespace Profinite

open_locale classical
open category_theory
open category_theory.limits

universe u
variables {J : Type u} [small_category J] [is_cofiltered J]
  {F : J ⥤ Profinite.{u}} (C : cone F) (hC : is_limit C)

include hC

/--
If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from
a clopen set in one of the terms in the limit.
-/
theorem exists_clopen_of_cofiltered {U : set C.X} (hU : is_clopen U) :
  ∃ (j : J) (V : set (F.obj j)) (hV : is_clopen V), U = C.π.app j ⁻¹' V :=
begin
  -- First, we have the topological basis of the cofiltered limit obtained by pulling back
  -- clopen sets from the factors in the limit. By continuity, all such sets are again clopen.
  have hB := Top.is_topological_basis_cofiltered_limit
    (F ⋙ Profinite_to_Top)
    (Profinite_to_Top.map_cone C)
    (is_limit_of_preserves _ hC)
    (λ j, {W | is_clopen W})
    _ (λ i, is_clopen_univ) (λ i U1 U2 hU1 hU2, hU1.inter hU2) _,
  rotate,
  { intros i,
    change topological_space.is_topological_basis
      {W : set (F.obj i) | is_clopen W},
    apply is_topological_basis_clopen },
  { rintros i j f V (hV : is_clopen _),
    refine ⟨hV.1.preimage _, hV.2.preimage _⟩;
    continuity },
  -- Using this, since `U` is open, we can write `U` as a union of clopen sets all of which
  -- are preimages of clopens from the factors in the limit.
  obtain ⟨S,hS,h⟩ := hB.open_eq_sUnion hU.1,
  clear hB,
  let j : S → J := λ s, (hS s.2).some,
  let V : Π (s : S), set (F.obj (j s)) := λ s, (hS s.2).some_spec.some,
  have hV : ∀ (s : S), is_clopen (V s) ∧ s.1 = C.π.app (j s) ⁻¹' (V s) :=
    λ s, (hS s.2).some_spec.some_spec,
  -- Since `U` is also closed, hence compact, it is covered by finitely many of the
  -- clopens constructed in the previous step.
  have := hU.2.is_compact.elim_finite_subcover (λ s : S, C.π.app (j s) ⁻¹' (V s)) _ _,
  rotate,
  { intros s,
    refine (hV s).1.1.preimage _,
    continuity },
  { dsimp only,
    rw h,
    rintro x ⟨T,hT,hx⟩,
    refine ⟨_,⟨⟨T,hT⟩,rfl⟩,_⟩,
    dsimp only,
    rwa ← (hV ⟨T,hT⟩).2 },
  -- We thus obtain a finite set `G : finset J` and a clopen set of `F.obj j` for each
  -- `j ∈ G` such that `U` is the union of the preimages of these clopen sets.
  obtain ⟨G,hG⟩ := this,
  -- Since `J` is cofiltered, we can find a single `j0` dominating all the `j ∈ G`.
  -- Pulling back all of the sets from the previous step to `F.obj j0` and taking a union,
  -- we obtain a clopen set in `F.obj j0` which works.
  obtain ⟨j0,hj0⟩ := is_cofiltered.inf_objs_exists (G.image j),
  let f : Π (s : S) (hs : s ∈ G), j0 ⟶ j s :=
    λ s hs, (hj0 (finset.mem_image.mpr ⟨s,hs,rfl⟩)).some,
  let W : S → set (F.obj j0) := λ s,
    if hs : s ∈ G then F.map (f s hs) ⁻¹' (V s) else set.univ,
  -- Conclude, using the `j0` and the clopen set of `F.obj j0` obtained above.
  refine ⟨j0, ⋃ (s : S) (hs : s ∈ G), W s, _, _⟩,
  { apply is_clopen_bUnion,
    intros s hs,
    dsimp only [W],
    rw dif_pos hs,
    refine ⟨(hV s).1.1.preimage _, (hV s).1.2.preimage _⟩;
    continuity },
  { ext x,
    split,
    { intro hx,
      simp_rw [set.preimage_Union, set.mem_Union],
      obtain ⟨_, ⟨s,rfl⟩, _, ⟨hs, rfl⟩, hh⟩ := hG hx,
      refine ⟨s, hs, _⟩,
      dsimp only [W] at hh ⊢,
      rwa [dif_pos hs, ← set.preimage_comp, ← Profinite.coe_comp, C.w] },
    { intro hx,
      simp_rw [set.preimage_Union, set.mem_Union] at hx,
      obtain ⟨s,hs,hx⟩ := hx,
      rw h,
      refine ⟨s.1,s.2,_⟩,
      rw (hV s).2,
      dsimp only [W] at hx,
      rwa [dif_pos hs, ← set.preimage_comp, ← Profinite.coe_comp, C.w] at hx } }
end

lemma exists_locally_constant_fin_two (f : locally_constant C.X (fin 2)) :
  ∃ (j : J) (g : locally_constant (F.obj j) (fin 2)), f = g.comap (C.π.app _) :=
begin
  let U := f ⁻¹' {0},
  have hU : is_clopen U := f.is_locally_constant.is_clopen_fiber _,
  obtain ⟨j,V,hV,h⟩ := exists_clopen_of_cofiltered C hC hU,
  use [j, locally_constant.of_clopen hV],
  apply locally_constant.locally_constant_eq_of_fiber_zero_eq,
  rw locally_constant.coe_comap _ _ (C.π.app j).continuous,
  conv_rhs { rw set.preimage_comp },
  rw [locally_constant.of_clopen_fiber_zero hV, ← h],
end

theorem exists_locally_constant_fintype_aux {α : Type*} [fintype α] (f : locally_constant C.X α) :
  ∃ (j : J) (g : locally_constant (F.obj j) (α → fin 2)),
    f.map (λ a b, if a = b then (0 : fin 2) else 1) = g.comap (C.π.app _) :=
begin
  let ι : α → α → fin 2 := λ x y, if x = y then 0 else 1,
  let ff := (f.map ι).flip,
  have hff := λ (a : α), exists_locally_constant_fin_two _ hC (ff a),
  choose j g h using hff,
  let G : finset J := finset.univ.image j,
  obtain ⟨j0,hj0⟩ := is_cofiltered.inf_objs_exists G,
  have hj : ∀ a, j a ∈ G,
  { intros a,
    simp [G] },
  let fs : Π (a : α), j0 ⟶ j a := λ a, (hj0 (hj a)).some,
  let gg : α → locally_constant (F.obj j0) (fin 2) := λ a, (g a).comap (F.map (fs _)),
  let ggg := locally_constant.unflip gg,
  refine ⟨j0, ggg, _⟩,
  have : f.map ι = locally_constant.unflip (f.map ι).flip, by simp,
  rw this, clear this,
  have : locally_constant.comap (C.π.app j0) ggg =
    locally_constant.unflip (locally_constant.comap (C.π.app j0) ggg).flip, by simp,
  rw this, clear this,
  congr' 1,
  ext1 a,
  change ff a = _,
  rw h,
  dsimp [ggg, gg],
  ext1,
  repeat {
    rw locally_constant.coe_comap,
    dsimp [locally_constant.flip, locally_constant.unflip] },
  { congr' 1,
    change _ = ((C.π.app j0) ≫ (F.map (fs a))) x,
    rw C.w },
  all_goals { continuity },
end

theorem exists_locally_constant_fintype_nonempty {α : Type*} [fintype α] [nonempty α]
  (f : locally_constant C.X α) :
  ∃ (j : J) (g : locally_constant (F.obj j) α), f = g.comap (C.π.app _) :=
begin
  inhabit α,
  obtain ⟨j,gg,h⟩ := exists_locally_constant_fintype_aux _ hC f,
  let ι : α → α → fin 2 := λ a b, if a = b then 0 else 1,
  let σ : (α → fin 2) → α := λ f, if h : ∃ (a : α), ι a = f then h.some else arbitrary _,
  refine ⟨j, gg.map σ, _⟩,
  ext,
  rw locally_constant.coe_comap _ _ (C.π.app j).continuous,
  dsimp [σ],
  have h1 : ι (f x) = gg (C.π.app j x),
  { change f.map (λ a b, if a = b then (0 : fin 2) else 1) x = _,
    rw [h, locally_constant.coe_comap _ _ (C.π.app j).continuous] },
  have h2 : ∃ a : α, ι a = gg (C.π.app j x) := ⟨f x, h1⟩,
  rw dif_pos h2,
  apply_fun ι,
  { rw h2.some_spec,
    exact h1 },
  { intros a b hh,
    apply_fun (λ e, e a) at hh,
    dsimp [ι] at hh,
    rw if_pos rfl at hh,
    split_ifs at hh with hh1 hh1,
    { exact hh1.symm },
    { exact false.elim (bot_ne_top hh) } }
end

/-- Any locally constant function from a cofiltered limit of profinite sets factors through
one of the components. -/
theorem exists_locally_constant {α : Type*} (f : locally_constant C.X α) :
  ∃ (j : J) (g : locally_constant (F.obj j) α), f = g.comap (C.π.app _) :=
begin
  let S := f.discrete_quotient,
  let ff : S → α := f.lift,
  by_cases hα : nonempty S,
  { resetI,
    let f' : locally_constant C.X S := ⟨S.proj, S.proj_is_locally_constant⟩,
    obtain ⟨j,g',h⟩ := exists_locally_constant_fintype_nonempty _ hC f',
    use j,
    refine ⟨⟨ff ∘ g', g'.is_locally_constant.comp _⟩,_⟩,
    ext1 t,
    apply_fun (λ e, e t) at h,
    rw locally_constant.coe_comap _ _ (C.π.app j).continuous at h ⊢,
    dsimp at h ⊢,
    rw ← h,
    refl },
  { suffices : ∃ j : J, ¬ nonempty (F.obj j),
    { obtain ⟨j,hj⟩ := this,
      use j,
      refine ⟨⟨λ x, false.elim (hj ⟨x⟩), λ A, _⟩, _⟩,
      { convert is_open_empty,
        rw set.eq_empty_iff_forall_not_mem,
        intros x,
        exact false.elim (hj ⟨x⟩) },
      { ext x,
        exact false.elim (hj ⟨C.π.app j x⟩) } },
    rw ← not_forall,
    intros h,
    apply hα,
    haveI : ∀ j : J, nonempty ((F ⋙ Profinite_to_Top).obj j) := h,
    haveI : ∀ j : J, t2_space ((F ⋙ Profinite_to_Top).obj j) := λ j,
      (infer_instance : t2_space (F.obj j)),
    haveI : ∀ j : J, compact_space ((F ⋙ Profinite_to_Top).obj j) := λ j,
      (infer_instance : compact_space (F.obj j)),
    have cond := Top.nonempty_limit_cone_of_compact_t2_cofiltered_system
      (F ⋙ Profinite_to_Top),
    suffices : nonempty C.X, by exact nonempty.map S.proj this,
    let D := Profinite_to_Top.map_cone C,
    have hD : is_limit D := is_limit_of_preserves Profinite_to_Top hC,
    have CD := (hD.cone_point_unique_up_to_iso (Top.limit_cone_is_limit _)).inv,
    exact cond.map CD }
end

end Profinite
