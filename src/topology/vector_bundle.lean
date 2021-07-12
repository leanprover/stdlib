/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel
-/

import topology.topological_fiber_bundle
import topology.continuous_function.algebra


/-!
# Topological vector bundles

In this file we define topological vector bundles.

Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a topological vector bundle structure on `bundle.total_space E`,
one should addtionally have the following data:

* `F` should be a topological space and a module over a semiring `R`;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `R`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* The most important condition: around each point, there should be a bundle trivialization which
is a continuous linear equiv in the fibers.

If all these conditions are satisfied, we register the typeclass
`topological_vector_bundle R F E`. We emphasize that the data is provided by other classes, and
that the `topological_vector_bundle` class is `Prop`-valued.

The point of this formalism is that it is unbundled in the sense that the total space of the bundle
is a type with a topology, with which one can work or put further structure, and still one can
perform operations on topological vector bundles (which are yet to be formalized). For instance,
assume that `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `R`
with fiber models `F₁` and `F₂` which are normed spaces. Then one can construct the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber `E x := (E₁ x →L[R] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[R] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces). Let
`vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂ (x : B)` be a type synonym for `E₁ x →L[R] E₂ x`.
Then one can endow
`bundle.total_space (vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂)`
with a topology and a topological vector bundle structure.

Similar constructions can be done for tensor products of topological vector bundles, exterior
algebras, and so on, where the topology can be defined using a norm on the fiber model if this
helps.

## Sections

In this file we also prove that sections of vector bundles inherit the algebraic structures of the
fibers. The proofs of this are the standard mathematical proofs: continuity is read through
trivializations on the fibers, where checking the continuity of algebraic operations is
straightforward.

## Tags
Vector bundle
-/

noncomputable theory

open bundle set

variables (R : Type*) {B : Type*} (F : Type*) (E : B → Type*)
  [topological_space F] [topological_space (total_space E)] [topological_space B]

section monoid

variables [semiring R] [∀ x, add_comm_monoid (E x)] [∀ x, module R (E x)]
  [add_comm_monoid F] [module R F]

section trivialization

/-- Local trivialization for vector bundles. -/
@[nolint has_inhabited_instance]
structure topological_vector_bundle.trivialization extends bundle_trivialization F (proj E) :=
(linear : ∀ x ∈ base_set, is_linear_map R (λ y : (E x), (to_fun y).2))

instance : has_coe_to_fun (topological_vector_bundle.trivialization R F E) :=
⟨λ _, (total_space E → B × F), λ e, e.to_bundle_trivialization⟩

instance : has_coe (topological_vector_bundle.trivialization R F E)
  (bundle_trivialization F (proj E)) :=
⟨topological_vector_bundle.trivialization.to_bundle_trivialization⟩

namespace topological_vector_bundle

variables {R F E}

lemma trivialization.mem_source (e : trivialization R F E)
  {x : total_space E} : x ∈ e.source ↔ proj E x ∈ e.base_set := bundle_trivialization.mem_source e

@[simp, mfld_simps] lemma trivialization.coe_coe (e : trivialization R F E) :
  ⇑e.to_local_homeomorph = e := rfl

@[simp, mfld_simps] lemma trivialization.coe_fst
  (e : trivialization R F E) {x : total_space E} (ex : x ∈ e.source) :
  (e x).1 = (proj E) x :=
e.proj_to_fun x ex

end topological_vector_bundle

end trivialization

variables [∀ x, topological_space (E x)]

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class topological_vector_bundle : Prop :=
(inducing [] : ∀ (b : B), inducing (λ x : (E b), (id ⟨b, x⟩ : total_space E)))
(locally_trivial [] : ∀ b : B, ∃ e : topological_vector_bundle.trivialization R F E, b ∈ e.base_set)

variable [topological_vector_bundle R F E]

namespace topological_vector_bundle

/-- `trivialization_at R F E b` is some choice of trivialization of a vector bundle whose base set
contains a given point `b`. -/
def trivialization_at : Π b : B, trivialization R F E :=
λ b, classical.some (topological_vector_bundle.locally_trivial R F E b)

@[simp, mfld_simps] lemma mem_base_set_trivialization_at (b : B) :
  b ∈ (trivialization_at R F E b).base_set :=
classical.some_spec (topological_vector_bundle.locally_trivial R F E b)

@[simp, mfld_simps] lemma mem_source_trivialization_at (z : total_space E) :
  z ∈ (trivialization_at R F E z.1).source :=
by { rw bundle_trivialization.mem_source, apply mem_base_set_trivialization_at }

variables {R F E}

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
def trivialization.continuous_linear_equiv_at (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) : E b ≃L[R] F :=
{ to_fun := λ y, (e ⟨b, y⟩).2,
  inv_fun := λ z, begin
    have : ((e.to_local_homeomorph.symm) (b, z)).fst = b :=
      bundle_trivialization.proj_symm_apply' _ hb,
    have C : E ((e.to_local_homeomorph.symm) (b, z)).fst = E b, by rw this,
    exact cast C (e.to_local_homeomorph.symm (b, z)).2
  end,
  left_inv := begin
    assume v,
    rw [← heq_iff_eq],
    apply (cast_heq _ _).trans,
    have A : (b, (e ⟨b, v⟩).snd) = e ⟨b, v⟩,
    { refine prod.ext _ rfl,
      symmetry,
      exact bundle_trivialization.coe_fst' _ hb },
    have B : e.to_local_homeomorph.symm (e ⟨b, v⟩) = ⟨b, v⟩,
    { apply local_homeomorph.left_inv_on,
      rw bundle_trivialization.mem_source,
      exact hb },
    rw [A, B],
  end,
  right_inv := begin
    assume v,
    have B : e (e.to_local_homeomorph.symm (b, v)) = (b, v),
    { apply local_homeomorph.right_inv_on,
      rw bundle_trivialization.mem_target,
      exact hb },
    have C : (e (e.to_local_homeomorph.symm (b, v))).2 = v, by rw [B],
    conv_rhs { rw ← C },
    dsimp,
    congr,
    ext,
    { exact (bundle_trivialization.proj_symm_apply' _ hb).symm },
    { exact (cast_heq _ _).trans (by refl) },
  end,
  map_add' := λ v w, (e.linear _ hb).map_add v w,
  map_smul' := λ c v, (e.linear _ hb).map_smul c v,
  continuous_to_fun := begin
    refine continuous_snd.comp _,
    apply continuous_on.comp_continuous e.to_local_homeomorph.continuous_on
      (topological_vector_bundle.inducing R F E b).continuous (λ x, _),
    rw bundle_trivialization.mem_source,
    exact hb,
  end,
  continuous_inv_fun := begin
    rw (topological_vector_bundle.inducing R F E b).continuous_iff,
    dsimp,
    have : continuous (λ (z : F), (e.to_bundle_trivialization.to_local_homeomorph.symm) (b, z)),
    { apply e.to_local_homeomorph.symm.continuous_on.comp_continuous
        (continuous_const.prod_mk continuous_id') (λ z, _),
      simp only [bundle_trivialization.mem_target, hb, local_equiv.symm_source,
        local_homeomorph.symm_to_local_equiv] },
    convert this,
    ext z,
    { exact (bundle_trivialization.proj_symm_apply' _ hb).symm },
    { exact cast_heq _ _ },
  end }

@[simp] lemma trivialization.continuous_linear_equiv_at_apply (e : trivialization R F E) (b : B)
  (hb : b ∈ e.base_set) (y : E b) : e.continuous_linear_equiv_at b hb y = (e ⟨b, y⟩).2 := rfl

@[simp] lemma trivialization.continuous_linear_equiv_at_apply' (e : trivialization R F E)
  (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at (proj E x) (e.mem_source.1 hx) x.2 = (e x).2 :=
by { cases x, refl }

@[simp] lemma continuous_linear_equiv_apply {g : bundle_section E} {b : B}
  {e : trivialization R F E} (hb : b ∈ e.base_set) :
  e.continuous_linear_equiv_at b (right_inv.mem_base_set_right_inv_fst ↑g hb) (g b) =
  (e ↑(g b)).snd :=
by { simp only [trivialization.continuous_linear_equiv_at_apply, sigma.eta], refl, }

lemma trivialization.snd_map_add {g h : bundle_section E} {e : trivialization R F E} (b : B)
  (hb : b ∈ e.base_set) : (e ((g + h) b)).snd = (e (g b)).snd + (e (h b)).snd :=
begin
  rw [(continuous_linear_equiv_apply hb).symm, pi.add_apply, continuous_linear_equiv.map_add],
  refl,
end

lemma trivialization.snd_map_zero {e : trivialization R F E} (b : B) (hb : b ∈ e.base_set) :
  (e ((0 : bundle_section E) b)).snd = 0 :=
by rw [(continuous_linear_equiv_apply hb).symm, pi.zero_apply, continuous_linear_equiv.map_zero]

lemma trivialization.snd_map_smul {g : bundle_section E} {e : trivialization R F E} {r : R}
  (b : B) (hb : b ∈ e.base_set) :
  (e ((r • g) b)).snd = r • (e (g b)).snd :=
begin
  rw [(continuous_linear_equiv_apply hb).symm, pi.smul_apply, continuous_linear_equiv.map_smul],
  refl,
end

variables (R B F)

/-- Local trivialization for trivial bundle. -/
def trivial_bundle_trivialization : trivialization R F (bundle.trivial B F) :=
{ to_fun := λ x, (x.fst, x.snd),
  inv_fun := λ y, ⟨y.fst, y.snd⟩,
  source := univ,
  target := univ,
  map_source' := λ x h, mem_univ (x.fst, x.snd),
  map_target' :=λ y h,  mem_univ ⟨y.fst, y.snd⟩,
  left_inv' := λ x h, sigma.eq rfl rfl,
  right_inv' := λ x h, prod.ext rfl rfl,
  open_source := is_open_univ,
  open_target := is_open_univ,
  continuous_to_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [prod.topological_space, induced_inf, induced_compose], exact le_refl _, },
  continuous_inv_fun := by { rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced],
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose],
    exact le_refl _, },
  base_set := univ,
  open_base_set := is_open_univ,
  source_eq := rfl,
  target_eq := by simp only [univ_prod_univ],
  proj_to_fun := λ y hy, rfl,
  linear := λ x hx, ⟨λ y z, rfl, λ c y, rfl⟩ }

instance trivial_bundle.topological_vector_bundle :
  topological_vector_bundle R F (bundle.trivial B F) :=
{ locally_trivial := λ x, ⟨trivial_bundle_trivialization R B F, mem_univ x⟩,
  inducing := λ b, ⟨begin
    have : (λ (x : trivial B F b), x) = @id F, by { ext x, refl },
    simp only [total_space.topological_space, induced_inf, induced_compose, function.comp, proj,
      induced_const, top_inf_eq, trivial.proj_snd, id.def, trivial.topological_space, this,
      induced_id],
  end⟩ }

variables {R B F}

/- Not registered as an instance because of a metavariable. -/
lemma is_topological_vector_bundle_is_topological_fiber_bundle :
  is_topological_fiber_bundle F (proj E) :=
λ x, ⟨(trivialization_at R F E x).to_bundle_trivialization, mem_base_set_trivialization_at R F E x⟩

end topological_vector_bundle

/-! ### Constructing topological vector bundles -/

variables (B)

/-- Analogous construction of `topological_fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers.-/
@[nolint has_inhabited_instance]
structure topological_vector_bundle_core (ι : Type*) :=
(base_set          : ι → set B)
(is_open_base_set  : ∀ i, is_open (base_set i))
(index_at          : B → ι)
(mem_base_set_at   : ∀ x, x ∈ base_set (index_at x))
(coord_change      : ι → ι → B → (F →ₗ[R] F))
(coord_change_self : ∀ i, ∀ x ∈ base_set i, ∀ v, coord_change i i x v = v)
(coord_change_continuous : ∀ i j, continuous_on (λp : B × F, coord_change i j p.1 p.2)
                                               (set.prod ((base_set i) ∩ (base_set j)) univ))
(coord_change_comp : ∀ i j k, ∀ x ∈ (base_set i) ∩ (base_set j) ∩ (base_set k), ∀ v,
  (coord_change j k x) (coord_change i j x v) = coord_change i k x v)

attribute [simp, mfld_simps] topological_vector_bundle_core.mem_base_set_at

namespace topological_vector_bundle_core

variables {R B F} {ι : Type*} (Z : topological_vector_bundle_core R B F ι)

/-- Natural identification to a `topological_fiber_bundle_core`. -/
def to_topological_vector_bundle_core : topological_fiber_bundle_core ι B F :=
{ coord_change := λ i j b, Z.coord_change i j b, ..Z }

instance to_topological_vector_bundle_core_coe : has_coe (topological_vector_bundle_core R B F ι)
  (topological_fiber_bundle_core ι B F) := ⟨to_topological_vector_bundle_core⟩

include Z

lemma coord_change_linear_comp (i j k : ι): ∀ x ∈ (Z.base_set i) ∩ (Z.base_set j) ∩ (Z.base_set k),
  (Z.coord_change j k x).comp (Z.coord_change i j x) = Z.coord_change i k x :=
λ x hx, by { ext v, exact Z.coord_change_comp i j k x hx v }

/-- The index set of a topological vector bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_inhabited_instance]
def index := ι

/-- The base space of a topological vector bundle core, as a convenience function for dot notation-/
@[nolint unused_arguments, reducible]
def base := B

/-- The fiber of a topological vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance]
def fiber (x : B) := F

section fiber_instances

local attribute [reducible] fiber --just to record instances

instance topological_space_fiber (x : B) : topological_space (Z.fiber x) := by apply_instance
instance add_comm_monoid_fiber : ∀ (x : B), add_comm_monoid (Z.fiber x) := λ x, by apply_instance
instance module_fiber : ∀ (x : B), module R (Z.fiber x) := λ x, by apply_instance

end fiber_instances

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps] def proj : total_space Z.fiber → B := bundle.proj Z.fiber

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : local_homeomorph (B × F) (B × F) :=
topological_fiber_bundle_core.triv_change ↑Z i j

@[simp, mfld_simps] lemma mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (Z.triv_change i j).source ↔ p.1 ∈ Z.base_set i ∩ Z.base_set j :=
topological_fiber_bundle_core.mem_triv_change_source ↑Z i j p

variable (ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : topological_space (total_space Z.fiber) :=
topological_fiber_bundle_core.to_topological_space ι ↑Z

variables {ι} (b : B) (a : F)

@[simp, mfld_simps] lemma coe_cord_change (i j : ι) :
  topological_fiber_bundle_core.coord_change ↑Z i j b = Z.coord_change i j b := rfl

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : topological_vector_bundle.trivialization R F Z.fiber :=
{ linear := λ x hx,
  { map_add := λ v w, by simp only [linear_map.map_add] with mfld_simps,
    map_smul := λ r v, by simp only [linear_map.map_smul] with mfld_simps},
  ..topological_fiber_bundle_core.local_triv ↑Z i }

@[simp, mfld_simps] lemma mem_local_triv_source (i : ι) (p : total_space Z.fiber) :
  p ∈ (Z.local_triv i).source ↔ p.1 ∈ Z.base_set i :=
iff.rfl

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : topological_vector_bundle.trivialization R F Z.fiber :=
Z.local_triv (Z.index_at b)

lemma mem_source_at : (⟨b, a⟩ : total_space Z.fiber) ∈ (Z.local_triv_at b).source :=
by { rw [local_triv_at, mem_local_triv_source], exact Z.mem_base_set_at b }

@[simp, mfld_simps] lemma local_triv_at_apply : ((Z.local_triv_at b) ⟨b, a⟩) = ⟨b, a⟩ :=
topological_fiber_bundle_core.local_triv_at_apply Z b a

instance : topological_vector_bundle R F Z.fiber :=
{ inducing := λ b, ⟨ begin refine le_antisymm _ (λ s h, _),
    { rw ←continuous_iff_le_induced,
      exact topological_fiber_bundle_core.continuous_total_space_mk ↑Z b, },
    { refine is_open_induced_iff.mpr ⟨(Z.local_triv_at b).source ∩ (Z.local_triv_at b) ⁻¹'
        (Z.local_triv_at b).base_set.prod s, (continuous_on_open_iff
        (Z.local_triv_at b).open_source).mp (Z.local_triv_at b).continuous_to_fun _
        (is_open.prod (Z.local_triv_at b).open_base_set h), _⟩,
      rw [preimage_inter, ←preimage_comp, function.comp],
      simp only [id.def],
      refine ext_iff.mpr (λ a, ⟨λ ha, _, λ ha, ⟨Z.mem_base_set_at b, _⟩⟩),
      { simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply] at ha,
        exact ha.2.2, },
      { simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply],
        exact ⟨Z.mem_base_set_at b, ha⟩, } } end⟩,
  locally_trivial := λ b, ⟨Z.local_triv_at b, Z.mem_base_set_at b⟩, }

/-- The projection on the base of a topological vector bundle created from core is continuous -/
@[continuity] lemma continuous_proj : continuous Z.proj :=
topological_fiber_bundle_core.continuous_proj Z

/-- The projection on the base of a topological vector bundle created from core is an open map -/
lemma is_open_map_proj : is_open_map Z.proj :=
topological_fiber_bundle_core.is_open_map_proj Z

end topological_vector_bundle_core

section sections

/-! ### Sections of topological vector bundles -/

/-- Type synonim to allow to declare instances that depend on implicit parameters containing `R`
and `F`. -/
@[reducible, nolint unused_arguments]
def topological_vector_bundle.vector_bundle_section (R : Type*) {B : Type*} (F : Type*)
  (E : B → Type*) [topological_space F] [topological_space (total_space E)] [topological_space B] :=
continuous_bundle_section E

open topological_vector_bundle

variables {R B E F}

lemma right_inv.image_mem_trivialization_at_source (f : right_inv (proj E)) (b : B) :
  f b ∈ (trivialization_at R F E b).source :=
f.mem_base_set_image_mem_source (mem_base_set_trivialization_at R F E b)

variables (R F E)

lemma bundle_section.continuous_at_iff_continuous_within_at_triv_at (f : bundle_section E) (b : B) :
  continuous_at f b ↔ continuous_within_at (λ x, ((trivialization_at R F E b) (f x)).snd)
  (trivialization_at R F E b).base_set b :=
(f : right_inv (proj E)).continuous_at_iff_continuous_within_at (trivialization_at R F E b)
  (mem_base_set_trivialization_at R F E b)

variables {E}

section

include R F

lemma continuous.add_section [has_continuous_add F] {g h : bundle_section E} (hg : continuous g)
  (hh : continuous h) : continuous (↑(g + h) : B → total_space E) :=
continuous_iff_continuous_at.mpr (λ b, ((g + h).continuous_at_iff_continuous_within_at_triv_at R F E
  b).mpr (continuous_within_at.congr (continuous_add.continuous_at.comp_continuous_within_at
  (((g.continuous_at_iff_continuous_within_at_triv_at R F E b).mp hg.continuous_at).prod
  ((h.continuous_at_iff_continuous_within_at_triv_at R F E b).mp hh.continuous_at)))
  trivialization.snd_map_add (trivialization.snd_map_add b
  (mem_base_set_trivialization_at R F E b))))

lemma continuous.zero_section : continuous ((0 : bundle_section E) : B → total_space E) :=
continuous_iff_continuous_at.mpr (λ b,
  ((0 : bundle_section E).continuous_at_iff_continuous_within_at_triv_at R F E b).mpr
  (continuous_within_at_const.congr trivialization.snd_map_zero (trivialization.snd_map_zero b
  (mem_base_set_trivialization_at R F E b))))

variables {R} [topological_space R] [has_continuous_smul R F]

lemma continuous.smul_section {g : bundle_section E} (hg : continuous g) (r : R) :
  continuous ((r • g : bundle_section E) : B → total_space E) :=
continuous_iff_continuous_at.2 (λ b, ((r • g).continuous_at_iff_continuous_within_at_triv_at R F E
  b).mpr ((((g.continuous_at_iff_continuous_within_at_triv_at R F E b).mp
  hg.continuous_at).const_smul r).congr trivialization.snd_map_smul (trivialization.snd_map_smul b
  (mem_base_set_trivialization_at R F E b))))

end

instance [has_continuous_add F] : has_add (vector_bundle_section R F E) :=
⟨λ g h, { to_fun := g + h, continuous_to_fun := g.continuous.add_section R F h.continuous }⟩

instance : has_zero (vector_bundle_section R F E) :=
⟨ { to_fun := 0, continuous_to_fun := continuous.zero_section R F }⟩

instance : inhabited (vector_bundle_section R F E) := ⟨0⟩

variables (E) {R F}

@[simp] lemma coe_add [has_continuous_add F] (f g : vector_bundle_section R F E) :
  ⇑(f + g) = f + g := rfl

@[simp] lemma coe_zero : ⇑(0 : vector_bundle_section R F E) = 0 := rfl

variables {E} (R F)

instance [has_continuous_add F] : add_comm_monoid (vector_bundle_section R F E) :=
continuous_bundle_section.coe_injective.add_comm_monoid _ (coe_zero E) (coe_add E)

variable (E)

/-- The coercion to function is a monoid homomorphism. -/
@[simps] def coe_fn_add_monoid_hom [has_continuous_add F] :
  vector_bundle_section R F E →+ bundle_section E := ⟨coe_fn, coe_zero E, coe_add E⟩

variables {R F E} [topological_space R] [has_continuous_smul R F]

instance : has_scalar R (vector_bundle_section R F E) :=
⟨λ r g, { to_fun := r • g, continuous_to_fun := g.continuous_to_fun.smul_section F r }⟩

@[simp] lemma coe_smul (r : R) (f : vector_bundle_section R F E) : ⇑(r • f) = r • f := rfl

instance [has_continuous_add F] : module R (vector_bundle_section R F E) :=
continuous_bundle_section.coe_injective.module _ (coe_fn_add_monoid_hom R F E) coe_smul

end sections

end monoid

section group

open topological_vector_bundle

variables {E R F} [ring R] [∀ x, add_comm_group (E x)] [∀ x, module R (E x)]
  [add_comm_group F] [module R F] [∀ x, topological_space (E x)] [topological_vector_bundle R F E]

lemma trivialization.map_neg {g : bundle_section E}
  {e : trivialization R F E} (b : B) (hb : b ∈ e.base_set) :
  (e ((- (g : bundle_section E)) b)).snd = - (e ((g : right_inv (proj E)) b)).snd :=
begin
  rw [(continuous_linear_equiv_apply hb).symm, pi.neg_apply, continuous_linear_equiv.map_neg],
  refl,
end

lemma trivialization.snd_map_sub {g h : bundle_section E} {e : trivialization R F E} (b : B)
  (hb : b ∈ e.base_set) : (e ((g - h) b)).snd = (e (g b)).snd - (e (h b)).snd :=
begin
  rw [(continuous_linear_equiv_apply hb).symm, pi.sub_apply, continuous_linear_equiv.map_sub],
  refl,
end

variables (R F) [topological_add_group F]

section

include R F

lemma continuous.neg_section {g : bundle_section E} (hg : continuous g) :
  continuous (↑(- g) : B → total_space E) :=
continuous_iff_continuous_at.2 (λ b, ((- g).continuous_at_iff_continuous_within_at_triv_at
  R F E b).mpr ((((g.continuous_at_iff_continuous_within_at_triv_at R F E b).mp
  hg.continuous_at).neg).congr trivialization.map_neg (trivialization.map_neg b
  (mem_base_set_trivialization_at R F E b))))

end

instance : has_neg (vector_bundle_section R F E) :=
⟨λ g, { to_fun := - g, continuous_to_fun := g.continuous.neg_section R F }⟩

lemma continuous.sub_section {g h : bundle_section E} (hg : continuous g)
  (hh : continuous h) : continuous (↑(g - h) : B → total_space E) :=
continuous_iff_continuous_at.mpr (λ b, ((g - h).continuous_at_iff_continuous_within_at_triv_at
  R F E b).mpr (continuous_within_at.congr (continuous_sub.continuous_at.comp_continuous_within_at
  (((g.continuous_at_iff_continuous_within_at_triv_at R F E b).mp hg.continuous_at).prod
  ((h.continuous_at_iff_continuous_within_at_triv_at R F E b).mp hh.continuous_at)))
  trivialization.snd_map_sub (trivialization.snd_map_sub b
  (mem_base_set_trivialization_at R F E b))))

instance : has_sub (vector_bundle_section R F E) :=
⟨λ g h, { to_fun := g - h, continuous_to_fun := g.continuous.sub_section R F h.continuous }⟩

variables {R F} (f g : vector_bundle_section R F E)

@[simp] lemma coe_neg : ⇑(-f) = -f := rfl
@[simp] lemma coe_sub : ⇑(f - g) = f - g := rfl

instance : add_comm_group (vector_bundle_section R F E) :=
-- continuous_bundle_section.coe_injective.add_comm_group _ (coe_zero E) (coe_add E) coe_neg coe_sub
--  ↑    ↑    ↑    ↑    ↑    ↑    ↑    ↑    does not work... Why!?
{ add_left_neg :=  λ f, by { ext, simp only [coe_zero, add_left_neg, coe_neg, coe_add], },
  ..topological_vector_bundle.vector_bundle_section.has_neg R F,
  ..vector_bundle_section.add_comm_monoid R F, }

end group
