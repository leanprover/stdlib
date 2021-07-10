/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz
-/
import topology.separation
import topology.subset_properties
import topology.locally_constant.basic

/-!

# Discrete quotients of a topological space.

This file defines the type of discrete quotients of a topological space,
denoted `discrete_quotient X`. To avoid quantifying over types, we model such
quotients as setoids whose equivalence classes are clopen.

## Definitions
1. `discrete_quotient X` is the type of discrete quotients of `X`.
  It is endowed with a coercion to `Type`, which is defined as the
  quotient associated to the setoid in question, and each such quotient
  is endowed with the discrete topology.
2. Given `S : discrete_quotient X`, the projection `X → S` is denoted
  `S.proj`.
3. When `X` is compact and `S : discrete_quotient X`, the space `S` is
  endowed with a `fintype` instance.

## Order structure
The type `discrete_quotient X` is endowed with an instance of a `semilattice_inf_top`.
The partial ordering `A ≤ B` mathematically means that `B.proj` factors through `A.proj`.
The top element `⊤` is the trivial quotient, meaning that every element of `X` is collapsed
to a point. Given `h : A ≤ B`, the map `A → B` is `discrete_quotient.of_le h`.

Given `f : X → Y` and `h : continuous f`, we define a predicate `le_comap h A B` for
`A : discrete_quotient X` and `B : discrete_quotient Y`, asserting that `f` descends to `A → B`.
If `cond : le_comap h A B`, the function `A → B` is obtained by `discrete_quotient.map cond`.

## Theorems
The two main results proved in this file are:
1. `discrete_quotient.eq_of_proj_eq` which states that when `X` is compact, t2 and totally
  disconnected, any two elements of `X` agree if their projections in `Q` agree for all
  `Q : discrete_quotient X`.
2. `discrete_quotient.exists_of_compat` which states that when `X` is compact, then any
  system of elements of `Q` as `Q : discrete_quotient X` varies, which is compatible with
  respect to `discrete_quotient.of_le`, must arise from some element of `X`.

## Remarks
The constructions in this file will be used to show that any profinite space is a limit
of finite discrete spaces.
-/

variables (X : Type*) [topological_space X]

/-- The type of discrete quotients of a topological space. -/
@[ext]
structure discrete_quotient :=
(rel : X → X → Prop)
(equiv : equivalence rel)
(clopen : ∀ x, is_clopen (set_of (rel x)))

namespace discrete_quotient

variables {X} (S : discrete_quotient X)

/-- Construct a discrete quotient from a clopen set. -/
def of_clopen {A : set X} (h : is_clopen A) : discrete_quotient X :=
{ rel := λ x y, x ∈ A ∧ y ∈ A ∨ x ∉ A ∧ y ∉ A,
  equiv := ⟨by tauto!, by tauto!, by tauto!⟩,
  clopen := begin
    intros x,
    by_cases hx : x ∈ A,
    { apply is_clopen.union,
      { convert h,
        ext,
        exact ⟨λ i, i.2, λ i, ⟨hx,i⟩⟩ },
      { convert is_clopen_empty,
        tidy } },
    { apply is_clopen.union,
      { convert is_clopen_empty,
        tidy },
      { convert is_clopen.compl h,
        ext,
        exact ⟨λ i, i.2, λ i, ⟨hx, i⟩⟩ } },
  end }

lemma refl : ∀ x : X, S.rel x x := S.equiv.1
lemma symm : ∀ x y : X, S.rel x y → S.rel y x := S.equiv.2.1
lemma trans : ∀ x y z : X, S.rel x y → S.rel y z → S.rel x z := S.equiv.2.2

/-- The setoid whose quotient yields the discrete quotient. -/
def setoid : setoid X := ⟨S.rel, S.equiv⟩

instance : has_coe_to_sort (discrete_quotient X) :=
⟨Type*, λ S, quotient S.setoid⟩

instance : topological_space S := ⊥

/-- The projection from `X` to the given discrete quotient. -/
def proj : X → S := quotient.mk'

lemma proj_surjective : function.surjective S.proj := quotient.surjective_quotient_mk'

lemma fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = set_of (S.rel x) :=
begin
  ext1 y,
  simp only [set.mem_preimage, set.mem_singleton_iff, quotient.eq',
    discrete_quotient.proj.equations._eqn_1, set.mem_set_of_eq],
  exact ⟨λ h, S.symm _ _ h, λ h, S.symm _ _ h⟩,
end

lemma proj_is_locally_constant : is_locally_constant S.proj :=
begin
   rw (is_locally_constant.tfae S.proj).out 0 3,
   intros x,
   rcases S.proj_surjective x with ⟨x,rfl⟩,
   simp [fiber_eq, (S.clopen x).1],
end

lemma proj_continuous : continuous S.proj :=
is_locally_constant.continuous $ proj_is_locally_constant _

lemma fiber_closed (A : set S) : is_closed (S.proj ⁻¹' A) :=
is_closed.preimage S.proj_continuous ⟨trivial⟩

lemma fiber_open (A : set S) : is_open (S.proj ⁻¹' A) :=
is_open.preimage S.proj_continuous trivial

lemma fiber_clopen (A : set S) : is_clopen (S.proj ⁻¹' A) := ⟨fiber_open _ _, fiber_closed _ _⟩

instance : semilattice_inf_top (discrete_quotient X) :=
{ top := ⟨λ a b, true, ⟨by tauto, by tauto, by tauto⟩, λ _, is_clopen_univ⟩,
  inf := λ A B,
  { rel := λ x y, A.rel x y ∧ B.rel x y,
    equiv := ⟨λ a, ⟨A.refl _,B.refl _⟩, λ a b h, ⟨A.symm _ _ h.1, B.symm _ _ h.2⟩,
      λ a b c h1 h2, ⟨A.trans _ _ _ h1.1 h2.1, B.trans _ _ _ h1.2 h2.2⟩⟩,
    clopen := λ x, is_clopen.inter (A.clopen _) (B.clopen _) },
  le := λ A B, ∀ x y : X, A.rel x y → B.rel x y,
  le_refl := λ a, by tauto,
  le_trans := λ a b c h1 h2, by tauto,
  le_antisymm := λ a b h1 h2, by { ext, tauto },
  inf_le_left := λ a b, by tauto,
  inf_le_right := λ a b, by tauto,
  le_inf := λ a b c h1 h2, by tauto,
  le_top := λ a, by tauto }

instance : inhabited (discrete_quotient X) := ⟨⊤⟩

section comap

variables {Y : Type*} [topological_space Y] {f : Y → X} (cont : continuous f)

/-- Comap a discrete quotient along a continuous map. -/
def comap : discrete_quotient Y :=
{ rel := λ a b, S.rel (f a) (f b),
  equiv := ⟨λ a, S.refl _, λ a b h, S.symm _ _ h, λ a b c h1 h2, S.trans _ _ _ h1 h2⟩,
  clopen := λ y, ⟨is_open.preimage cont (S.clopen _).1, is_closed.preimage cont (S.clopen _).2⟩ }

@[simp]
lemma comap_id : S.comap (continuous_id : continuous (id : X → X)) = S := by { ext, refl }

@[simp]
lemma comap_comp {Z : Type*} [topological_space Z] {g : Z → Y} (cont' : continuous g) :
  S.comap (continuous.comp cont cont') = (S.comap cont).comap cont' := by { ext, refl }

lemma comap_mono {A B : discrete_quotient X} (h : A ≤ B) : A.comap cont ≤ B.comap cont :=
by tauto

end comap

section of_le

/-- The map induced by a refinement of a discrete quotient. -/
def of_le {A B : discrete_quotient X} (h : A ≤ B) : A → B :=
λ a, quotient.lift_on' a (λ x, B.proj x) (λ a b i, quotient.sound' (h _ _ i))

@[simp]
lemma of_le_refl {A : discrete_quotient X} : of_le (le_refl A) = id := by { ext ⟨⟩, refl }

lemma of_le_refl_apply {A : discrete_quotient X} (a : A) : of_le (le_refl A) a = a := by simp

@[simp]
lemma of_le_comp {A B C : discrete_quotient X} (h1 : A ≤ B) (h2 : B ≤ C) :
  of_le (le_trans h1 h2) = of_le h2 ∘ of_le h1 := by { ext ⟨⟩, refl }

lemma of_le_comp_apply {A B C : discrete_quotient X} (h1 : A ≤ B) (h2 : B ≤ C) (a : A) :
  of_le (le_trans h1 h2) a = of_le h2 (of_le h1 a) := by simp

lemma of_le_continuous {A B : discrete_quotient X} (h : A ≤ B) :
  continuous (of_le h) := continuous_of_discrete_topology

@[simp]
lemma of_le_proj {A B : discrete_quotient X} (h : A ≤ B) :
  of_le h ∘ A.proj = B.proj := by { ext, exact quotient.sound' (B.refl _) }

@[simp]
lemma of_le_proj_apply {A B : discrete_quotient X} (h : A ≤ B) (x : X) :
  of_le h (A.proj x) = B.proj x := by { change (of_le h ∘ A.proj) x = _, simp }

end of_le

section map

variables {Y : Type*} [topological_space Y] {f : Y → X}
  (cont : continuous f) (A : discrete_quotient Y) (B : discrete_quotient X)

/--
Given `cont : continuous f`, `le_comap cont A B` is defined as `A ≤ B.comap f`.
Mathematically this means that `f` descends to a morphism `A → B`.
-/
def le_comap : Prop := A ≤ B.comap cont

variables {cont A B}

lemma le_comap_id (A : discrete_quotient X) : le_comap continuous_id A A := by tauto

lemma le_comap_comp {Z : Type*} [topological_space Z] {g : Z → Y} {cont' : continuous g}
  {C : discrete_quotient Z} : le_comap cont' C A → le_comap cont A B →
  le_comap (continuous.comp cont cont') C B := by tauto

lemma le_comap_trans {C : discrete_quotient X} :
  le_comap cont A B → B ≤ C → le_comap cont A C := λ h1 h2, le_trans h1 $ comap_mono _ h2

/-- Map a discrete quotient along a continuous map. -/
def map (cond : le_comap cont A B) : A → B := quotient.map' f cond

lemma map_continuous (cond : le_comap cont A B) : continuous (map cond) :=
continuous_of_discrete_topology

@[simp]
lemma map_proj (cond : le_comap cont A B) : map cond ∘ A.proj = B.proj ∘ f := rfl

@[simp]
lemma map_proj_apply (cond : le_comap cont A B) (y : Y) : map cond (A.proj y) = B.proj (f y) := rfl

@[simp]
lemma map_id : map (le_comap_id A) = id := by { ext ⟨⟩, refl }

@[simp]
lemma map_comp {Z : Type*} [topological_space Z] {g : Z → Y} {cont' : continuous g}
  {C : discrete_quotient Z} (h1 : le_comap cont' C A) (h2 : le_comap cont A B) :
  map (le_comap_comp h1 h2) = map h2 ∘ map h1 := by { ext ⟨⟩, refl }

@[simp]
lemma of_le_map {C : discrete_quotient X} (cond : le_comap cont A B) (h : B ≤ C) :
   map (le_comap_trans cond h) = of_le h ∘ map cond := by { ext ⟨⟩, refl }

@[simp]
lemma of_le_map_apply {C : discrete_quotient X} (cond : le_comap cont A B) (h : B ≤ C) (a : A) :
  map (le_comap_trans cond h) a = of_le h (map cond a) := by { rcases a, refl }

@[simp]
lemma map_of_le {C : discrete_quotient Y} (cond : le_comap cont A B) (h : C ≤ A) :
   map (le_trans h cond) = map cond ∘ of_le h := by { ext ⟨⟩, refl }

@[simp]
lemma map_of_le_apply {C : discrete_quotient Y} (cond : le_comap cont A B) (h : C ≤ A) (c : C) :
  map (le_trans h cond) c = map cond (of_le h c) := by { rcases c, refl }

end map

lemma eq_of_proj_eq [t2_space X] [compact_space X] [disc : totally_disconnected_space X]
  {x y : X} : (∀ Q : discrete_quotient X, Q.proj x = Q.proj y) → x = y :=
begin
  intro h,
  change x ∈ ({y} : set X),
  rw totally_disconnected_space_iff_connected_component_singleton at disc,
  rw [← disc y, connected_component_eq_Inter_clopen],
  rintros U ⟨⟨U, hU1, hU2⟩, rfl⟩,
  replace h : _ ∨ _ := quotient.exact' (h (of_clopen hU1)),
  tauto,
end

lemma fiber_le_of_le {A B : discrete_quotient X} (h : A ≤ B) (a : A) :
  A.proj ⁻¹' {a} ≤ B.proj ⁻¹' {of_le h a} :=
begin
  induction a,
  erw [fiber_eq, fiber_eq],
  tidy,
end

lemma exists_of_compat [compact_space X] (Qs : Π (Q : discrete_quotient X), Q)
  (compat : ∀ (A B : discrete_quotient X) (h : A ≤ B), of_le h (Qs _) = Qs _) :
  ∃ x : X, ∀ Q : discrete_quotient X, Q.proj x = Qs _ :=
begin
  obtain ⟨x,hx⟩ := is_compact.nonempty_Inter_of_directed_nonempty_compact_closed
    (λ (Q : discrete_quotient X), Q.proj ⁻¹' {Qs _}) (λ A B, _) (λ i, _)
    (λ i,  (fiber_closed _ _).is_compact) (λ i, fiber_closed _ _),
  { refine ⟨x, λ Q, _⟩,
    specialize hx _ ⟨Q,rfl⟩,
    dsimp at hx,
    rcases proj_surjective _ (Qs Q) with ⟨y,hy⟩,
    rw ← hy at *,
    rw fiber_eq at hx,
    exact quotient.sound' (Q.symm y x hx) },
  { refine ⟨A ⊓ B, λ a ha, _, λ a ha, _⟩,
    { dsimp only,
      erw ← compat (A ⊓ B) A inf_le_left,
      exact fiber_le_of_le _ _ ha },
    { dsimp only,
      erw ← compat (A ⊓ B) B inf_le_right,
      exact fiber_le_of_le _ _ ha } },
  { obtain ⟨x,hx⟩ := i.proj_surjective (Qs i),
    refine ⟨x,_⟩,
    dsimp only,
    rw [← hx, fiber_eq],
    apply i.refl },
end

noncomputable instance [compact_space X] : fintype S :=
begin
  have cond : is_compact (⊤ : set X) := compact_univ,
  rw is_compact_iff_finite_subcover at cond,
  have h := @cond S (λ s, S.proj ⁻¹' {s}) (λ s, fiber_open _ _)
    (λ x hx, ⟨S.proj ⁻¹' {S.proj x}, ⟨S.proj x, rfl⟩, rfl⟩),
  let T := classical.some h,
  have hT := classical.some_spec h,
  refine ⟨T,λ s, _⟩,
  rcases S.proj_surjective s with ⟨x,rfl⟩,
  rcases hT (by tauto : x ∈ ⊤) with ⟨j, ⟨j,rfl⟩, h1, ⟨hj, rfl⟩, h2⟩,
  dsimp only at h2,
  suffices : S.proj x = j, by rwa this,
  rcases j with ⟨j⟩,
  apply quotient.sound',
  erw fiber_eq at h2,
  exact S.symm _ _ h2
end

end discrete_quotient

namespace locally_constant

variables {X} {α : Type*} (f : locally_constant X α)

/-- Any locally constant function induces a discrete quotient. -/
def discrete_quotient : discrete_quotient X :=
{ rel := λ a b, f b = f a,
  equiv := ⟨by tauto, by tauto, λ a b c h1 h2, by rw [h2, h1]⟩,
  clopen := λ x, f.is_locally_constant.is_clopen_fiber _ }

/-- The function from the discrete quotient associated to a locally constant function. -/
def lift : f.discrete_quotient → α := λ a, quotient.lift_on' a f (λ a b h, h.symm)

lemma lift_is_locally_constant : _root_.is_locally_constant f.lift := λ A, trivial

/-- A locally constant version of `locally_constant.lift`. -/
def locally_constant_lift : locally_constant f.discrete_quotient α :=
⟨f.lift, f.lift_is_locally_constant⟩

@[simp]
lemma lift_eq_coe : f.lift = f.locally_constant_lift := rfl

@[simp]
lemma factors : f.locally_constant_lift ∘ f.discrete_quotient.proj = f := by { ext, refl }

end locally_constant
