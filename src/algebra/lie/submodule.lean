/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie.subalgebra
import ring_theory.noetherian

/-!
# Lie submodules of a Lie algebra

In this file we define Lie submodules and Lie ideals, we construct the lattice structure on Lie
submodules and we use it to define various important operations, notably the Lie span of a subset
of a Lie module.

## Main definitions

  * `lie_submodule`
  * `lie_submodule.well_founded_of_noetherian`
  * `lie_submodule.lie_span`
  * `lie_submodule.map`
  * `lie_submodule.comap`
  * `lie_ideal`
  * `lie_ideal.map`
  * `lie_ideal.comap`

## Tags

lie algebra, lie submodule, lie ideal, lattice structure
-/

universes u v w w₁ w₂

section lie_submodule

variables (R : Type u) (L : Type v) (M : Type w)
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]

set_option old_structure_cmd true
/-- A Lie submodule of a Lie module is a submodule that is closed under the Lie bracket.
This is a sufficient condition for the subset itself to form a Lie module. -/
structure lie_submodule extends submodule R M :=
(lie_mem : ∀ {x : L} {m : M}, m ∈ carrier → ⁅x, m⁆ ∈ carrier)

attribute [nolint doc_blame] lie_submodule.to_submodule

namespace lie_submodule

variables {R L M} (N N' : lie_submodule R L M)

/-- The zero module is a Lie submodule of any Lie module. -/
instance : has_zero (lie_submodule R L M) :=
⟨{ lie_mem := λ x m h, by { rw ((submodule.mem_bot R).1 h), apply lie_zero, },
   ..(0 : submodule R M)}⟩

instance : inhabited (lie_submodule R L M) := ⟨0⟩

instance coe_submodule : has_coe (lie_submodule R L M) (submodule R M) := ⟨to_submodule⟩

@[norm_cast]
lemma coe_to_submodule : ((N : submodule R M) : set M) = N := rfl

instance has_mem : has_mem M (lie_submodule R L M) := ⟨λ x N, x ∈ (N : set M)⟩

@[simp] lemma mem_carrier {x : M} : x ∈ N.carrier ↔ x ∈ (N : set M) :=
iff.rfl

@[simp] lemma mem_mk_iff (S : set M) (h₁ h₂ h₃ h₄) {x : M} :
  x ∈ (⟨S, h₁, h₂, h₃, h₄⟩ : lie_submodule R L M) ↔ x ∈ S :=
iff.rfl

@[simp] lemma mem_coe_submodule {x : M} : x ∈ (N : submodule R M) ↔ x ∈ N := iff.rfl

lemma mem_coe {x : M} : x ∈ (N : set M) ↔ x ∈ N := iff.rfl

@[simp] lemma zero_mem : (0 : M) ∈ N := (N : submodule R M).zero_mem

@[simp] lemma coe_to_set_mk (S : set M) (h₁ h₂ h₃ h₄) :
  ((⟨S, h₁, h₂, h₃, h₄⟩ : lie_submodule R L M) : set M) = S := rfl

@[simp] lemma coe_to_submodule_mk (p : submodule R M) (h) :
  (({lie_mem := h, ..p} : lie_submodule R L M) : submodule R M) = p :=
by { cases p, refl, }

@[ext] lemma ext (h : ∀ m, m ∈ N ↔ m ∈ N') : N = N' :=
by { cases N, cases N', simp only [], ext m, exact h m, }

@[simp] lemma coe_to_submodule_eq_iff : (N : submodule R M) = (N' : submodule R M) ↔ N = N' :=
begin
  split; intros h,
  { ext, rw [← mem_coe_submodule, h], simp, },
  { rw h, },
end

/-- Copy of a lie_submodule with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (s : set M) (hs : s = ↑N) : lie_submodule R L M :=
{ carrier := s,
  zero_mem' := hs.symm ▸ N.zero_mem',
  add_mem'  := hs.symm ▸ N.add_mem',
  smul_mem' := hs.symm ▸ N.smul_mem',
  lie_mem   := hs.symm ▸ N.lie_mem, }

instance : lie_ring_module L N :=
{ bracket     := λ (x : L) (m : N), ⟨⁅x, m.val⁆, N.lie_mem m.property⟩,
  add_lie     := by { intros x y m, apply set_coe.ext, apply add_lie, },
  lie_add     := by { intros x m n, apply set_coe.ext, apply lie_add, },
  leibniz_lie := by { intros x y m, apply set_coe.ext, apply leibniz_lie, }, }

instance : lie_module R L N :=
{ lie_smul := by { intros t x y, apply set_coe.ext, apply lie_smul, },
  smul_lie := by { intros t x y, apply set_coe.ext, apply smul_lie, }, }

@[simp, norm_cast] lemma coe_zero : ((0 : N) : M) = (0 : M) := rfl

@[simp, norm_cast] lemma coe_add (m m' : N) : (↑(m + m') : M) = (m : M) + (m' : M) := rfl

@[simp, norm_cast] lemma coe_neg (m : N) : (↑(-m) : M) = -(m : M) := rfl

@[simp, norm_cast] lemma coe_sub (m m' : N) : (↑(m - m') : M) = (m : M) - (m' : M) := rfl

@[simp, norm_cast] lemma coe_smul (t : R) (m : N) : (↑(t • m) : M) = t • (m : M) := rfl

@[simp, norm_cast] lemma coe_bracket (x : L) (m : N) : (↑⁅x, m⁆ : M) = ⁅x, ↑m⁆ := rfl

end lie_submodule

section lie_ideal

variables (L)

/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
abbreviation lie_ideal := lie_submodule R L L

lemma lie_mem_right (I : lie_ideal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I := I.lie_mem h

lemma lie_mem_left (I : lie_ideal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I :=
 by { rw [←lie_skew, ←neg_lie], apply lie_mem_right, assumption, }

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
def lie_ideal_subalgebra (I : lie_ideal R L) : lie_subalgebra R L :=
{ lie_mem' := by { intros x y hx hy, apply lie_mem_right, exact hy, },
  ..I.to_submodule, }

instance : has_coe (lie_ideal R L) (lie_subalgebra R L) := ⟨λ I, lie_ideal_subalgebra R L I⟩

@[norm_cast] lemma lie_ideal.coe_to_subalgebra (I : lie_ideal R L) :
  ((I : lie_subalgebra R L) : set L) = I := rfl

@[norm_cast] lemma lie_ideal.coe_to_lie_subalgebra_to_submodule (I : lie_ideal R L) :
  ((I : lie_subalgebra R L) : submodule R L) = I := rfl

end lie_ideal

variables {R M}

lemma submodule.exists_lie_submodule_coe_eq_iff (p : submodule R M) :
  (∃ (N : lie_submodule R L M), ↑N = p) ↔ ∀ (x : L) (m : M), m ∈ p → ⁅x, m⁆ ∈ p :=
begin
  split,
  { rintros ⟨N, rfl⟩, exact N.lie_mem, },
  { intros h, use { lie_mem := h, ..p }, exact lie_submodule.coe_to_submodule_mk p _, },
end

namespace lie_subalgebra

variables {L}

/-- Given a Lie subalgebra `K ⊆ L`, if we view `L` as a `K`-module by restriction, it contains
a distinguished Lie submodule for the action of `K`, namely `K` itself. -/
def to_lie_submodule (K : lie_subalgebra R L) : lie_submodule R K L :=
{ lie_mem := λ x y hy, K.lie_mem x.property hy,
  .. (K : submodule R L) }

@[simp] lemma coe_to_lie_submodule (K : lie_subalgebra R L) :
  (K.to_lie_submodule : submodule R L) = K :=
rfl

@[simp] lemma mem_to_lie_submodule {K : lie_subalgebra R L} (x : L) :
  x ∈ K.to_lie_submodule ↔ x ∈ K :=
iff.rfl

lemma exists_lie_ideal_coe_eq_iff (K : lie_subalgebra R L) :
  (∃ (I : lie_ideal R L), ↑I = K) ↔ ∀ (x y : L), y ∈ K → ⁅x, y⁆ ∈ K :=
begin
  simp only [← coe_to_submodule_eq_iff, lie_ideal.coe_to_lie_subalgebra_to_submodule,
    submodule.exists_lie_submodule_coe_eq_iff L],
  exact iff.rfl,
end

lemma exists_nested_lie_ideal_coe_eq_iff {K K' : lie_subalgebra R L} (h : K ≤ K') :
  (∃ (I : lie_ideal R K'), ↑I = of_le h) ↔ ∀ (x y : L), x ∈ K' → y ∈ K → ⁅x, y⁆ ∈ K :=
begin
  simp only [exists_lie_ideal_coe_eq_iff, coe_bracket, mem_of_le],
  split,
  { intros h' x y hx hy, exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy, },
  { rintros h' ⟨x, hx⟩ ⟨y, hy⟩ hy', exact h' x y hx hy', },
end

end lie_subalgebra

end lie_submodule

namespace lie_submodule

variables {R : Type u} {L : Type v} {M : Type w}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [add_comm_group M] [module R M]
variables [lie_ring_module L M] [lie_module R L M]
variables (N N' : lie_submodule R L M) (I J : lie_ideal R L)

section lattice_structure

open set

lemma coe_injective : function.injective (coe : lie_submodule R L M → set M) :=
λ N N' h, by { cases N, cases N', simp only, exact h, }

lemma coe_submodule_injective : function.injective (coe : lie_submodule R L M → submodule R M) :=
λ N N' h, by { ext, rw [← mem_coe_submodule, h], refl, }

instance : partial_order (lie_submodule R L M) :=
{ le := λ N N', ∀ ⦃x⦄, x ∈ N → x ∈ N', -- Overriding `le` like this gives a better defeq.
  ..partial_order.lift (coe : lie_submodule R L M → set M) coe_injective }

lemma le_def : N ≤ N' ↔ (N : set M) ⊆ N' := iff.rfl

@[simp, norm_cast] lemma coe_submodule_le_coe_submodule : (N : submodule R M) ≤ N' ↔ N ≤ N' :=
iff.rfl

instance : has_bot (lie_submodule R L M) := ⟨0⟩

@[simp] lemma bot_coe : ((⊥ : lie_submodule R L M) : set M) = {0} := rfl

@[simp] lemma bot_coe_submodule : ((⊥ : lie_submodule R L M) : submodule R M) = ⊥ := rfl

@[simp] lemma mem_bot (x : M) : x ∈ (⊥ : lie_submodule R L M) ↔ x = 0 := mem_singleton_iff

instance : has_top (lie_submodule R L M) :=
⟨{ lie_mem := λ x m h, mem_univ ⁅x, m⁆,
   ..(⊤ : submodule R M) }⟩

@[simp] lemma top_coe : ((⊤ : lie_submodule R L M) : set M) = univ := rfl

@[simp] lemma top_coe_submodule : ((⊤ : lie_submodule R L M) : submodule R M) = ⊤ := rfl

@[simp] lemma mem_top (x : M) : x ∈ (⊤ : lie_submodule R L M) := mem_univ x

instance : has_inf (lie_submodule R L M) :=
⟨λ N N', { lie_mem := λ x m h, mem_inter (N.lie_mem h.1) (N'.lie_mem h.2),
            ..(N ⊓ N' : submodule R M) }⟩

instance : has_Inf (lie_submodule R L M) :=
⟨λ S, { lie_mem := λ x m h, by
        { simp only [submodule.mem_carrier, mem_Inter, submodule.Inf_coe, mem_set_of_eq,
            forall_apply_eq_imp_iff₂, exists_imp_distrib] at *,
          intros N hN, apply N.lie_mem (h N hN), },
        ..Inf {(s : submodule R M) | s ∈ S} }⟩

@[simp] theorem inf_coe : (↑(N ⊓ N') : set M) = N ∩ N' := rfl

@[simp] lemma Inf_coe_to_submodule (S : set (lie_submodule R L M)) :
  (↑(Inf S) : submodule R M) = Inf {(s : submodule R M) | s ∈ S} := rfl

@[simp] lemma Inf_coe (S : set (lie_submodule R L M)) : (↑(Inf S) : set M) = ⋂ s ∈ S, (s : set M) :=
begin
  rw [← lie_submodule.coe_to_submodule, Inf_coe_to_submodule, submodule.Inf_coe],
  ext m,
  simpa only [mem_Inter, mem_set_of_eq, forall_apply_eq_imp_iff₂, exists_imp_distrib],
end

lemma Inf_glb (S : set (lie_submodule R L M)) : is_glb S (Inf S) :=
begin
  have h : ∀ (N N' : lie_submodule R L M), (N : set M) ≤ N' ↔ N ≤ N', { intros, apply iff.rfl, },
  simp only [is_glb.of_image h, Inf_coe, is_glb_binfi],
end

/-- The set of Lie submodules of a Lie module form a complete lattice.

We provide explicit values for the fields `bot`, `top`, `inf` to get more convenient definitions
than we would otherwise obtain from `complete_lattice_of_Inf`.  -/
instance : complete_lattice (lie_submodule R L M) :=
{ bot          := ⊥,
  bot_le       := λ N _ h, by { rw mem_bot at h, rw h, exact N.zero_mem', },
  top          := ⊤,
  le_top       := λ _ _ _, trivial,
  inf          := (⊓),
  le_inf       := λ N₁ N₂ N₃ h₁₂ h₁₃ m hm, ⟨h₁₂ hm, h₁₃ hm⟩,
  inf_le_left  := λ _ _ _, and.left,
  inf_le_right := λ _ _ _, and.right,
  ..complete_lattice_of_Inf _ Inf_glb }

instance : add_comm_monoid (lie_submodule R L M) :=
{ add       := (⊔),
  add_assoc := λ _ _ _, sup_assoc,
  zero      := ⊥,
  zero_add  := λ _, bot_sup_eq,
  add_zero  := λ _, sup_bot_eq,
  add_comm  := λ _ _, sup_comm, }

@[simp] lemma add_eq_sup : N + N' = N ⊔ N' := rfl

@[norm_cast, simp] lemma sup_coe_to_submodule :
  (↑(N ⊔ N') : submodule R M) = (N : submodule R M) ⊔ (N' : submodule R M) :=
begin
  have aux : ∀ (x : L) m, m ∈ (N ⊔ N' : submodule R M) → ⁅x,m⁆ ∈ (N ⊔ N' : submodule R M),
  { simp only [submodule.mem_sup],
    rintro x m ⟨y, hy, z, hz, rfl⟩,
    refine ⟨⁅x, y⁆, N.lie_mem hy, ⁅x, z⁆, N'.lie_mem hz, (lie_add _ _ _).symm⟩ },
  refine le_antisymm (Inf_le ⟨{ lie_mem := aux, ..(N ⊔ N' : submodule R M) }, _⟩) _,
  { simp only [exists_prop, and_true, mem_set_of_eq, eq_self_iff_true, coe_to_submodule_mk,
      ← coe_submodule_le_coe_submodule, and_self, le_sup_left, le_sup_right] },
  { simp, },
end

@[norm_cast, simp] lemma inf_coe_to_submodule :
  (↑(N ⊓ N') : submodule R M) = (N : submodule R M) ⊓ (N' : submodule R M) := rfl

@[simp] lemma mem_inf (x : M) : x ∈ N ⊓ N' ↔ x ∈ N ∧ x ∈ N' :=
by rw [← mem_coe_submodule, ← mem_coe_submodule, ← mem_coe_submodule, inf_coe_to_submodule,
  submodule.mem_inf]

lemma mem_sup (x : M) : x ∈ N ⊔ N' ↔ ∃ (y ∈ N) (z ∈ N'), y + z = x :=
by { rw [← mem_coe_submodule, sup_coe_to_submodule, submodule.mem_sup], exact iff.rfl, }

lemma eq_bot_iff : N = ⊥ ↔ ∀ (m : M), m ∈ N → m = 0 :=
by { rw eq_bot_iff, exact iff.rfl, }

-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_bot : subsingleton (lie_submodule R L ↥(⊥ : lie_submodule R L M)) :=
begin
  apply subsingleton_of_bot_eq_top,
  ext ⟨x, hx⟩, change x ∈ ⊥ at hx, rw submodule.mem_bot at hx, subst hx,
  simp only [true_iff, eq_self_iff_true, submodule.mk_eq_zero, lie_submodule.mem_bot],
end

instance : is_modular_lattice (lie_submodule R L M) :=
{ sup_inf_le_assoc_of_le := λ N₁ N₂ N₃,
    by { simp only [← coe_submodule_le_coe_submodule, sup_coe_to_submodule, inf_coe_to_submodule],
         exact is_modular_lattice.sup_inf_le_assoc_of_le ↑N₂, }, }

variables (R L M)

lemma well_founded_of_noetherian [is_noetherian R M] :
  well_founded ((>) : lie_submodule R L M → lie_submodule R L M → Prop) :=
begin
  let f : ((>) : lie_submodule R L M → lie_submodule R L M → Prop) →r
          ((>) : submodule R M → submodule R M → Prop) :=
  { to_fun       := coe,
    map_rel' := λ N N' h, h, },
  apply f.well_founded, rw ← is_noetherian_iff_well_founded, apply_instance,
end

lemma subsingleton_iff : subsingleton M ↔ subsingleton (lie_submodule R L M) :=
(submodule.subsingleton_iff R).trans $ by
  rw [← subsingleton_iff_bot_eq_top, ← subsingleton_iff_bot_eq_top, ← coe_to_submodule_eq_iff,
    top_coe_submodule, bot_coe_submodule]

lemma nontrivial_iff : nontrivial M ↔ nontrivial (lie_submodule R L M) :=
not_iff_not.mp (
  (not_nontrivial_iff_subsingleton.trans $ subsingleton_iff R L M).trans
  not_nontrivial_iff_subsingleton.symm)

instance [nontrivial M] : nontrivial (lie_submodule R L M) := (nontrivial_iff R L M).mp ‹_›

variables {R L M}

section inclusion_maps

/-- The inclusion of a Lie submodule into its ambient space is a morphism of Lie modules. -/
def incl : N →ₗ⁅R,L⁆ M :=
{ map_lie' := λ x m, rfl,
  ..submodule.subtype (N : submodule R M) }

@[simp] lemma incl_apply (m : N) : N.incl m = m := rfl

lemma incl_eq_val : (N.incl : N → M) = subtype.val := rfl

variables {N N'} (h : N ≤ N')

/-- Given two nested Lie submodules `N ⊆ N'`, the inclusion `N ↪ N'` is a morphism of Lie modules.-/
def hom_of_le : N →ₗ⁅R,L⁆ N' :=
{ map_lie' := λ x m, rfl,
  ..submodule.of_le h }

@[simp] lemma coe_hom_of_le (m : N) : (hom_of_le h m : M) = m := rfl

lemma hom_of_le_apply (m : N) : hom_of_le h m = ⟨m.1, h m.2⟩ := rfl

lemma hom_of_le_injective : function.injective (hom_of_le h) :=
λ x y, by simp only [hom_of_le_apply, imp_self, subtype.mk_eq_mk, set_like.coe_eq_coe,
  subtype.val_eq_coe]

end inclusion_maps

section lie_span

variables (R L) (s : set M)
/-- The `lie_span` of a set `s ⊆ M` is the smallest Lie submodule of `M` that contains `s`. -/
def lie_span : lie_submodule R L M := Inf {N | s ⊆ N}

variables {R L s}

lemma mem_lie_span {x : M} : x ∈ lie_span R L s ↔ ∀ N : lie_submodule R L M, s ⊆ N → x ∈ N :=
by { change x ∈ (lie_span R L s : set M) ↔ _, erw Inf_coe, exact mem_bInter_iff, }

lemma subset_lie_span : s ⊆ lie_span R L s :=
by { intros m hm, erw mem_lie_span, intros N hN, exact hN hm, }

lemma submodule_span_le_lie_span : submodule.span R s ≤ lie_span R L s :=
by { rw submodule.span_le, apply subset_lie_span, }

lemma lie_span_le {N} : lie_span R L s ≤ N ↔ s ⊆ N :=
begin
  split,
  { exact subset.trans subset_lie_span, },
  { intros hs m hm, rw mem_lie_span at hm, exact hm _ hs, },
end

lemma lie_span_mono {t : set M} (h : s ⊆ t) : lie_span R L s ≤ lie_span R L t :=
by { rw lie_span_le, exact subset.trans h subset_lie_span, }

lemma lie_span_eq : lie_span R L (N : set M) = N :=
le_antisymm (lie_span_le.mpr rfl.subset) subset_lie_span

lemma coe_lie_span_submodule_eq_iff {p : submodule R M} :
  (lie_span R L (p : set M) : submodule R M) = p ↔ ∃ (N : lie_submodule R L M), ↑N = p :=
begin
  rw p.exists_lie_submodule_coe_eq_iff L, split; intros h,
  { intros x m hm, rw [← h, mem_coe_submodule], exact lie_mem _ (subset_lie_span hm), },
  { rw [← coe_to_submodule_mk p h, coe_to_submodule, coe_to_submodule_eq_iff, lie_span_eq], },
end

variables (R L M)

/-- `lie_span` forms a Galois insertion with the coercion from `lie_submodule` to `set`. -/
protected def gi : galois_insertion (lie_span R L : set M → lie_submodule R L M) coe :=
{ choice    := λ s _, lie_span R L s,
  gc        := λ s t, lie_span_le,
  le_l_u    := λ s, subset_lie_span,
  choice_eq := λ s h, rfl }

@[simp] lemma span_empty : lie_span R L (∅ : set M) = ⊥ :=
(lie_submodule.gi R L M).gc.l_bot

@[simp] lemma span_univ : lie_span R L (set.univ : set M) = ⊤ :=
eq_top_iff.2 $ set_like.le_def.2 $ subset_lie_span

variables {M}

lemma span_union (s t : set M) : lie_span R L (s ∪ t) = lie_span R L s ⊔ lie_span R L t :=
(lie_submodule.gi R L M).gc.l_sup

lemma span_Union {ι} (s : ι → set M) : lie_span R L (⋃ i, s i) = ⨆ i, lie_span R L (s i) :=
(lie_submodule.gi R L M).gc.l_supr

end lie_span

end lattice_structure

end lie_submodule

section lie_submodule_map_and_comap

variables {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}
variables [comm_ring R] [lie_ring L] [lie_algebra R L] [lie_ring L'] [lie_algebra R L']
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables [add_comm_group M'] [module R M'] [lie_ring_module L M'] [lie_module R L M']

namespace lie_submodule

variables (f : M →ₗ⁅R,L⁆ M') (N N₂ : lie_submodule R L M) (N' : lie_submodule R L M')

/-- A morphism of Lie modules `f : M → M'` pushes forward Lie submodules of `M` to Lie submodules
of `M'`. -/
def map : lie_submodule R L M' :=
{ lie_mem := λ x m' h, by
  { rcases h with ⟨m, hm, hfm⟩, use ⁅x, m⁆, split,
    { apply N.lie_mem hm, },
    { norm_cast at hfm, simp [hfm], }, },
  ..(N : submodule R M).map (f : M →ₗ[R] M') }

/-- A morphism of Lie modules `f : M → M'` pulls back Lie submodules of `M'` to Lie submodules of
`M`. -/
def comap : lie_submodule R L M :=
{ lie_mem := λ x m h, by { suffices : ⁅x, f m⁆ ∈ N', { simp [this], }, apply N'.lie_mem h, },
  ..(N' : submodule R M').comap (f : M →ₗ[R] M') }

variables {f N N₂ N'}

lemma map_le_iff_le_comap : map f N ≤ N' ↔ N ≤ comap f N' :=
set.image_subset_iff

variables (f)

lemma gc_map_comap : galois_connection (map f) (comap f) :=
λ N N', map_le_iff_le_comap

variables {f}

@[simp] lemma map_sup : (N ⊔ N₂).map f = N.map f ⊔ N₂.map f :=
(gc_map_comap f).l_sup

lemma mem_map (m' : M') : m' ∈ N.map f ↔ ∃ m, m ∈ N ∧ f m = m' :=
submodule.mem_map

@[simp] lemma mem_comap {m : M} : m ∈ comap f N' ↔ f m ∈ N' := iff.rfl

end lie_submodule

namespace lie_ideal

variables (f : L →ₗ⁅R⁆ L') (I I₂ : lie_ideal R L) (J : lie_ideal R L')

@[simp] lemma top_coe_lie_subalgebra : ((⊤ : lie_ideal R L) : lie_subalgebra R L) = ⊤ := rfl

/-- A morphism of Lie algebras `f : L → L'` pushes forward Lie ideals of `L` to Lie ideals of `L'`.

Note that unlike `lie_submodule.map`, we must take the `lie_span` of the image. Mathematically
this is because although `f` makes `L'` into a Lie module over `L`, in general the `L` submodules of
`L'` are not the same as the ideals of `L'`. -/
def map : lie_ideal R L' := lie_submodule.lie_span R L' $ (I : submodule R L).map (f : L →ₗ[R] L')

/-- A morphism of Lie algebras `f : L → L'` pulls back Lie ideals of `L'` to Lie ideals of `L`.

Note that `f` makes `L'` into a Lie module over `L` (turning `f` into a morphism of Lie modules)
and so this is a special case of `lie_submodule.comap` but we do not exploit this fact. -/
def comap : lie_ideal R L :=
{ lie_mem := λ x y h, by { suffices : ⁅f x, f y⁆ ∈ J, { simp [this], }, apply J.lie_mem h, },
  ..(J : submodule R L').comap (f : L →ₗ[R] L') }

@[simp] lemma map_coe_submodule (h : ↑(map f I) = f '' I) :
  (map f I : submodule R L') = (I : submodule R L).map f :=
by { rw [set_like.ext'_iff, lie_submodule.coe_to_submodule, h, submodule.map_coe], refl, }

@[simp] lemma comap_coe_submodule : (comap f J : submodule R L) = (J : submodule R L').comap f :=
rfl

lemma map_le : map f I ≤ J ↔ f '' I ⊆ J := lie_submodule.lie_span_le

variables {f I I₂ J}

lemma mem_map {x : L} (hx : x ∈ I) : f x ∈ map f I :=
by { apply lie_submodule.subset_lie_span, use x, exact ⟨hx, rfl⟩, }

@[simp] lemma mem_comap {x : L} : x ∈ comap f J ↔ f x ∈ J := iff.rfl

lemma map_le_iff_le_comap : map f I ≤ J ↔ I ≤ comap f J :=
by { rw map_le, exact set.image_subset_iff, }

variables (f)

lemma gc_map_comap : galois_connection (map f) (comap f) :=
λ I I', map_le_iff_le_comap

variables {f}

@[simp] lemma map_sup : (I ⊔ I₂).map f = I.map f ⊔ I₂.map f :=
(gc_map_comap f).l_sup

lemma map_comap_le : map f (comap f J) ≤ J :=
by { rw map_le_iff_le_comap, apply le_refl _, }

/-- See also `lie_ideal.map_comap_eq`. -/
lemma comap_map_le : I ≤ comap f (map f I) :=
by { rw ← map_le_iff_le_comap, apply le_refl _, }

@[mono] lemma map_mono : monotone (map f) :=
λ I₁ I₂ h,
by { rw lie_submodule.le_def at h, apply lie_submodule.lie_span_mono (set.image_subset ⇑f h), }

@[mono] lemma comap_mono : monotone (comap f) :=
λ J₁ J₂ h, by { rw lie_submodule.le_def at h ⊢, exact set.preimage_mono h, }

lemma map_of_image (h : f '' I = J) : I.map f = J :=
begin
  apply le_antisymm,
  { erw [lie_submodule.lie_span_le, submodule.map_coe, h], },
  { rw [lie_submodule.le_def, ← h], exact lie_submodule.subset_lie_span, },
end

/-- Note that this is not a special case of `lie_submodule.subsingleton_of_bot`. Indeed, given
`I : lie_ideal R L`, in general the two lattices `lie_ideal R I` and `lie_submodule R L I` are
different (though the latter does naturally inject into the former).

In other words, in general, ideals of `I`, regarded as a Lie algebra in its own right, are not the
same as ideals of `L` contained in `I`. -/
-- TODO[gh-6025]: make this an instance once safe to do so
lemma subsingleton_of_bot : subsingleton (lie_ideal R ↥(⊥ : lie_ideal R L)) :=
begin
  apply subsingleton_of_bot_eq_top,
  ext ⟨x, hx⟩, change x ∈ ⊥ at hx, rw submodule.mem_bot at hx, subst hx,
  simp only [true_iff, eq_self_iff_true, submodule.mk_eq_zero, lie_submodule.mem_bot],
end

end lie_ideal

namespace lie_hom

variables (f : L →ₗ⁅R⁆ L') (I : lie_ideal R L) (J : lie_ideal R L')

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
def ker : lie_ideal R L := lie_ideal.comap f ⊥

/-- The range of a morphism of Lie algebras as an ideal in the codomain. -/
def ideal_range : lie_ideal R L' := lie_submodule.lie_span R L' f.range

lemma ideal_range_eq_lie_span_range :
  f.ideal_range = lie_submodule.lie_span R L' f.range := rfl

lemma ideal_range_eq_map :
  f.ideal_range = lie_ideal.map f ⊤ :=
by { ext, simp only [ideal_range, range_eq_map], refl }

/-- The condition that the image of a morphism of Lie algebras is an ideal. -/
def is_ideal_morphism : Prop := (f.ideal_range : lie_subalgebra R L') = f.range

@[simp] lemma is_ideal_morphism_def :
  f.is_ideal_morphism ↔ (f.ideal_range : lie_subalgebra R L') = f.range := iff.rfl

lemma is_ideal_morphism_iff :
  f.is_ideal_morphism ↔ ∀ (x : L') (y : L), ∃ (z : L), ⁅x, f y⁆ = f z :=
begin
  simp only [is_ideal_morphism_def, ideal_range_eq_lie_span_range,
    ← lie_subalgebra.coe_to_submodule_eq_iff, ← f.range.coe_to_submodule,
    lie_ideal.coe_to_lie_subalgebra_to_submodule, lie_submodule.coe_lie_span_submodule_eq_iff,
    lie_subalgebra.mem_coe_submodule, mem_range, exists_imp_distrib,
    submodule.exists_lie_submodule_coe_eq_iff],
  split,
  { intros h x y, obtain ⟨z, hz⟩ := h x (f y) y rfl, use z, exact hz.symm, },
  { intros h x y z hz, obtain ⟨w, hw⟩ := h x z, use w, rw [← hw, hz], },
end

lemma range_subset_ideal_range : (f.range : set L') ⊆ f.ideal_range := lie_submodule.subset_lie_span

lemma map_le_ideal_range : I.map f ≤ f.ideal_range :=
begin
  rw f.ideal_range_eq_map,
  exact lie_ideal.map_mono le_top,
end

lemma ker_le_comap : f.ker ≤ J.comap f := lie_ideal.comap_mono bot_le

@[simp] lemma ker_coe_submodule : (ker f : submodule R L) = (f : L →ₗ[R] L').ker := rfl

@[simp] lemma mem_ker {x : L} : x ∈ ker f ↔ f x = 0 :=
show x ∈ (f.ker : submodule R L) ↔ _,
by simp only [ker_coe_submodule, linear_map.mem_ker, coe_to_linear_map]

lemma mem_ideal_range {x : L} : f x ∈ ideal_range f :=
begin
  rw ideal_range_eq_map,
  exact lie_ideal.mem_map (lie_submodule.mem_top x)
end

@[simp] lemma mem_ideal_range_iff (h : is_ideal_morphism f) {y : L'} :
  y ∈ ideal_range f ↔ ∃ (x : L), f x = y :=
begin
  rw f.is_ideal_morphism_def at h,
  rw [← lie_submodule.mem_coe, ← lie_ideal.coe_to_subalgebra, h, f.range_coe, set.mem_range],
end

lemma le_ker_iff : I ≤ f.ker ↔ ∀ x, x ∈ I → f x = 0 :=
begin
  split; intros h x hx,
  { specialize h hx, rw mem_ker at h, exact h, },
  { rw mem_ker, apply h x hx, },
end

lemma ker_eq_bot : f.ker = ⊥ ↔ function.injective f :=
by rw [← lie_submodule.coe_to_submodule_eq_iff, ker_coe_submodule, lie_submodule.bot_coe_submodule,
  linear_map.ker_eq_bot, coe_to_linear_map]

@[simp] lemma range_coe_submodule : (f.range : submodule R L') = (f : L →ₗ[R] L').range := rfl

lemma range_eq_top : f.range = ⊤ ↔ function.surjective f :=
begin
  rw [← lie_subalgebra.coe_to_submodule_eq_iff, range_coe_submodule,
    lie_subalgebra.top_coe_submodule],
  exact linear_map.range_eq_top,
end

@[simp] lemma ideal_range_eq_top_of_surjective (h : function.surjective f) : f.ideal_range = ⊤ :=
begin
  rw ← f.range_eq_top at h,
  rw [ideal_range_eq_lie_span_range, h, ← lie_subalgebra.coe_to_submodule,
    ← lie_submodule.coe_to_submodule_eq_iff, lie_submodule.top_coe_submodule,
      lie_subalgebra.top_coe_submodule, lie_submodule.coe_lie_span_submodule_eq_iff],
  use ⊤,
  exact lie_submodule.top_coe_submodule,
end

lemma is_ideal_morphism_of_surjective (h : function.surjective f) : f.is_ideal_morphism :=
by rw [is_ideal_morphism_def, f.ideal_range_eq_top_of_surjective h, f.range_eq_top.mpr h,
    lie_ideal.top_coe_lie_subalgebra]

end lie_hom

namespace lie_ideal

variables {f : L →ₗ⁅R⁆ L'} {I : lie_ideal R L} {J : lie_ideal R L'}

@[simp] lemma map_eq_bot_iff : I.map f = ⊥ ↔ I ≤ f.ker :=
by { rw ← le_bot_iff, exact lie_ideal.map_le_iff_le_comap }

lemma coe_map_of_surjective (h : function.surjective f) :
  (I.map f : submodule R L') = (I : submodule R L).map f :=
begin
  let J : lie_ideal R L' :=
  { lie_mem := λ x y hy,
    begin
      have hy' : ∃ (x : L), x ∈ I ∧ f x = y, { simpa [hy], },
      obtain ⟨z₂, hz₂, rfl⟩ := hy',
      obtain ⟨z₁, rfl⟩ := h x,
      simp only [lie_hom.coe_to_linear_map, set_like.mem_coe, set.mem_image,
        lie_submodule.mem_coe_submodule, submodule.mem_carrier, submodule.map_coe],
      use ⁅z₁, z₂⁆,
      exact ⟨I.lie_mem hz₂, f.map_lie z₁ z₂⟩,
    end,
    ..(I : submodule R L).map (f : L →ₗ[R] L'), },
  erw lie_submodule.coe_lie_span_submodule_eq_iff,
  use J,
  apply lie_submodule.coe_to_submodule_mk,
end

lemma mem_map_of_surjective {y : L'} (h₁ : function.surjective f) (h₂ : y ∈ I.map f) :
  ∃ (x : I), f x = y :=
begin
  rw [← lie_submodule.mem_coe_submodule, coe_map_of_surjective h₁, submodule.mem_map] at h₂,
  obtain ⟨x, hx, rfl⟩ := h₂,
  use ⟨x, hx⟩,
  refl,
end

lemma bot_of_map_eq_bot {I : lie_ideal R L} (h₁ : function.injective f) (h₂ : I.map f = ⊥) :
  I = ⊥ :=
begin
  rw ← f.ker_eq_bot at h₁, change comap f ⊥ = ⊥ at h₁,
  rw [eq_bot_iff, map_le_iff_le_comap, h₁] at h₂,
  rw eq_bot_iff, exact h₂,
end

/-- Given two nested Lie ideals `I₁ ⊆ I₂`, the inclusion `I₁ ↪ I₂` is a morphism of Lie algebras. -/
def hom_of_le {I₁ I₂ : lie_ideal R L} (h : I₁ ≤ I₂) : I₁ →ₗ⁅R⁆ I₂ :=
{ map_lie' := λ x y, rfl,
  ..submodule.of_le h, }

@[simp] lemma coe_hom_of_le {I₁ I₂ : lie_ideal R L} (h : I₁ ≤ I₂) (x : I₁) :
  (hom_of_le h x : L) = x := rfl

lemma hom_of_le_apply {I₁ I₂ : lie_ideal R L} (h : I₁ ≤ I₂) (x : I₁) :
  hom_of_le h x = ⟨x.1, h x.2⟩ := rfl

lemma hom_of_le_injective {I₁ I₂ : lie_ideal R L} (h : I₁ ≤ I₂) :
  function.injective (hom_of_le h) :=
λ x y, by simp only [hom_of_le_apply, imp_self, subtype.mk_eq_mk, set_like.coe_eq_coe,
  subtype.val_eq_coe]

@[simp] lemma map_sup_ker_eq_map : lie_ideal.map f (I ⊔ f.ker) = lie_ideal.map f I :=
begin
  suffices : lie_ideal.map f (I ⊔ f.ker) ≤ lie_ideal.map f I,
  { exact le_antisymm this (lie_ideal.map_mono le_sup_left), },
  apply lie_submodule.lie_span_mono,
  rintros x ⟨y, hy₁, hy₂⟩, rw ← hy₂,
  erw lie_submodule.mem_sup at hy₁, obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁, rw ← hy,
  rw [f.coe_to_linear_map, f.map_add, f.mem_ker.mp hz₂, add_zero], exact ⟨z₁, hz₁, rfl⟩,
end

@[simp] lemma map_comap_eq (h : f.is_ideal_morphism) : map f (comap f J) = f.ideal_range ⊓ J :=
begin
  apply le_antisymm,
  { rw le_inf_iff, exact ⟨f.map_le_ideal_range _, map_comap_le⟩, },
  { rw f.is_ideal_morphism_def at h,
    rw [lie_submodule.le_def, lie_submodule.inf_coe, ← coe_to_subalgebra, h],
    rintros y ⟨⟨x, h₁⟩, h₂⟩, rw ← h₁ at h₂ ⊢, exact mem_map h₂, },
end

@[simp] lemma comap_map_eq (h : ↑(map f I) = f '' I) : comap f (map f I) = I ⊔ f.ker :=
by rw [← lie_submodule.coe_to_submodule_eq_iff, comap_coe_submodule, I.map_coe_submodule f h,
  lie_submodule.sup_coe_to_submodule, f.ker_coe_submodule, linear_map.comap_map_eq]

variables (f I J)

/-- Regarding an ideal `I` as a subalgebra, the inclusion map into its ambient space is a morphism
of Lie algebras. -/
def incl : I →ₗ⁅R⁆ L := (I : lie_subalgebra R L).incl

@[simp] lemma incl_range : I.incl.range = I := (I : lie_subalgebra R L).incl_range

@[simp] lemma incl_apply (x : I) : I.incl x = x := rfl

@[simp] lemma incl_coe : (I.incl : I →ₗ[R] L) = (I : submodule R L).subtype := rfl

@[simp] lemma comap_incl_self : comap I.incl I = ⊤ :=
by { rw ← lie_submodule.coe_to_submodule_eq_iff, exact submodule.comap_subtype_self _, }

@[simp] lemma ker_incl : I.incl.ker = ⊥ :=
by rw [← lie_submodule.coe_to_submodule_eq_iff, I.incl.ker_coe_submodule,
  lie_submodule.bot_coe_submodule, incl_coe, submodule.ker_subtype]

@[simp] lemma incl_ideal_range : I.incl.ideal_range = I :=
begin
  rw [lie_hom.ideal_range_eq_lie_span_range, ← lie_subalgebra.coe_to_submodule,
    ← lie_submodule.coe_to_submodule_eq_iff, incl_range, coe_to_lie_subalgebra_to_submodule,
    lie_submodule.coe_lie_span_submodule_eq_iff],
  use I,
end

lemma incl_is_ideal_morphism : I.incl.is_ideal_morphism :=
begin
  rw [I.incl.is_ideal_morphism_def, incl_ideal_range],
  exact (I : lie_subalgebra R L).incl_range.symm,
end

end lie_ideal

end lie_submodule_map_and_comap

namespace lie_module_hom

variables {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variables [comm_ring R] [lie_ring L] [lie_algebra R L]
variables [add_comm_group M] [module R M] [lie_ring_module L M] [lie_module R L M]
variables [add_comm_group N] [module R N] [lie_ring_module L N] [lie_module R L N]
variables (f : M →ₗ⁅R,L⁆ N)

/-- The range of a morphism of Lie modules `f : M → N` is a Lie submodule of `N`.
See Note [range copy pattern]. -/
def range : lie_submodule R L N :=
(lie_submodule.map f ⊤).copy (set.range f) set.image_univ.symm

@[simp] lemma coe_range : (f.range : set N) = set.range f := rfl

@[simp] lemma coe_submodule_range : (f.range : submodule R N) = (f : M →ₗ[R] N).range := rfl

@[simp] lemma mem_range (n : N) : n ∈ f.range ↔ ∃ m, f m = n :=
iff.rfl

lemma map_top : lie_submodule.map f ⊤ = f.range :=
by { ext, simp [lie_submodule.mem_map], }

end lie_module_hom

section top_equiv_self

variables {R : Type u} {L : Type v}
variables [comm_ring R] [lie_ring L] [lie_algebra R L]

/-- The natural equivalence between the 'top' Lie subalgebra and the enclosing Lie algebra. -/
def lie_subalgebra.top_equiv_self : (⊤ : lie_subalgebra R L) ≃ₗ⁅R⁆ L :=
{ inv_fun   := λ x, ⟨x, set.mem_univ x⟩,
  left_inv  := λ x, by { ext, refl, },
  right_inv := λ x, rfl,
  ..(⊤ : lie_subalgebra R L).incl, }

@[simp] lemma lie_subalgebra.top_equiv_self_apply (x : (⊤ : lie_subalgebra R L)) :
  lie_subalgebra.top_equiv_self x = x := rfl

/-- The natural equivalence between the 'top' Lie ideal and the enclosing Lie algebra. -/
def lie_ideal.top_equiv_self : (⊤ : lie_ideal R L) ≃ₗ⁅R⁆ L :=
lie_subalgebra.top_equiv_self

@[simp] lemma lie_ideal.top_equiv_self_apply (x : (⊤ : lie_ideal R L)) :
  lie_ideal.top_equiv_self x = x := rfl

end top_equiv_self
