/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes
-/
import data.finset.order
import linear_algebra.direct_sum_module
import ring_theory.free_comm_ring
import ring_theory.ideal.operations
/-!
# Direct limit of modules, abelian groups, rings, and fields.

See Atiyah-Macdonald PP.32-33, Matsumura PP.269-270

Generalizes the notion of "union", or "gluing", of incomparable modules over the same ring,
or incomparable abelian groups, or rings, or fields.

It is constructed as a quotient of the free module (for the module case) or quotient of
the free commutative ring (for the ring case) instead of a quotient of the disjoint union
so as to make the operations (addition etc.) "computable".

-/
universes u v w u₁

open submodule

variables {R : Type u} [ring R]
variables {ι : Type v}
variables [dec_ι : decidable_eq ι] [directed_order ι]
variables (G : ι → Type w)

/-- A directed system is a functor from the category (directed poset) to another category.
This is used for abelian groups and rings and fields because their maps are not bundled.
See module.directed_system -/
class directed_system (f : Π i j, i ≤ j → G i → G j) : Prop :=
(map_self [] : ∀ i x h, f i i h x = x)
(map_map [] : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

namespace module

variables [Π i, add_comm_group (G i)] [Π i, module R (G i)]

/-- A directed system is a functor from the category (directed poset) to the category of
`R`-modules. -/
class directed_system (f : Π i j, i ≤ j → G i →ₗ[R] G j) : Prop :=
(map_self [] : ∀ i x h, f i i h x = x)
(map_map [] : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

variables (f : Π i j, i ≤ j → G i →ₗ[R] G j)

include dec_ι

/-- The direct limit of a directed system is the modules glued together along the maps. -/
def direct_limit : Type (max v w) :=
(span R $ { a | ∃ (i j) (H : i ≤ j) x,
  direct_sum.lof R ι G i x - direct_sum.lof R ι G j (f i j H x) = a }).quotient

namespace direct_limit

instance : add_comm_group (direct_limit G f) := quotient.add_comm_group _
instance : semimodule R (direct_limit G f) := quotient.semimodule _

instance : inhabited (direct_limit G f) := ⟨0⟩

variables (R ι)
/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →ₗ[R] direct_limit G f :=
(mkq _).comp $ direct_sum.lof R ι G i
variables {R ι G f}

@[simp] lemma of_f {i j hij x} : (of R ι G f j (f i j hij x)) = of R ι G f i x :=
eq.symm $ (submodule.quotient.eq _).2 $ subset_span ⟨i, j, hij, x, rfl⟩

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of [nonempty ι] (z : direct_limit G f) : ∃ i x, of R ι G f i x = z :=
nonempty.elim (by apply_instance) $ assume ind : ι,
quotient.induction_on' z $ λ z, direct_sum.induction_on z
  ⟨ind, 0, linear_map.map_zero _⟩
  (λ i x, ⟨i, x, rfl⟩)
  (λ p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x + f j k hjk y, by rw [linear_map.map_add, of_f, of_f, ihx, ihy]; refl⟩)

@[elab_as_eliminator]
protected theorem induction_on [nonempty ι] {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of R ι G f i x)) : C z :=
let ⟨i, x, h⟩ := exists_of z in h ▸ ih i x

variables {P : Type u₁} [add_comm_group P] [module R P] (g : Π i, G i →ₗ[R] P)
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

variables (R ι G f)
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : direct_limit G f →ₗ[R] P :=
liftq _ (direct_sum.to_module R ι P g)
  (span_le.2 $ λ a ⟨i, j, hij, x, hx⟩, by rw [← hx, mem_coe, linear_map.sub_mem_ker_iff,
    direct_sum.to_module_lof, direct_sum.to_module_lof, Hg])
variables {R ι G f}

omit Hg
lemma lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x :=
direct_sum.to_module_lof R _ _

theorem lift_unique [nonempty ι] (F : direct_limit G f →ₗ[R] P) (x) :
  F x = lift R ι G f (λ i, F.comp $ of R ι G f i)
    (λ i j hij x, by rw [linear_map.comp_apply, of_f]; refl) x :=
direct_limit.induction_on x $ λ i x, by rw lift_of; refl

section totalize
open_locale classical
variables (G f)
omit dec_ι

/-- `totalize G f i j` is a linear map from `G i` to `G j`, for *every* `i` and `j`.
If `i ≤ j`, then it is the map `f i j` that comes with the directed system `G`,
and otherwise it is the zero map. -/
noncomputable def totalize : Π i j, G i →ₗ[R] G j :=
λ i j, if h : i ≤ j then f i j h else 0
variables {G f}

lemma totalize_apply (i j x) :
  totalize G f i j x = if h : i ≤ j then f i j h x else 0 :=
if h : i ≤ j
  then by dsimp only [totalize]; rw [dif_pos h, dif_pos h]
  else by dsimp only [totalize]; rw [dif_neg h, dif_neg h, linear_map.zero_apply]
end totalize

variables [directed_system G f]
open_locale classical

lemma to_module_totalize_of_le {x : direct_sum ι G} {i j : ι}
  (hij : i ≤ j) (hx : ∀ k ∈ x.support, k ≤ i) :
  direct_sum.to_module R ι (G j) (λ k, totalize G f k j) x =
  f i j hij (direct_sum.to_module R ι (G i) (λ k, totalize G f k i) x) :=
begin
  rw [← @dfinsupp.sum_single ι G _ _ _ x],
  unfold dfinsupp.sum,
  simp only [linear_map.map_sum],
  refine finset.sum_congr rfl (λ k hk, _),
  rw direct_sum.single_eq_lof R k (x k),
  simp [totalize_apply, hx k hk, le_trans (hx k hk) hij, directed_system.map_map f]
end

lemma of.zero_exact_aux [nonempty ι] {x : direct_sum ι G}
  (H : submodule.quotient.mk x = (0 : direct_limit G f)) :
  ∃ j, (∀ k ∈ x.support, k ≤ j) ∧
    direct_sum.to_module R ι (G j) (λ i, totalize G f i j) x = (0 : G j) :=
nonempty.elim (by apply_instance) $ assume ind : ι,
span_induction ((quotient.mk_eq_zero _).1 H)
  (λ x ⟨i, j, hij, y, hxy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, begin
      clear_,
      subst hxy,
      split,
      { intros i0 hi0,
        rw [dfinsupp.mem_support_iff, direct_sum.sub_apply, ← direct_sum.single_eq_lof,
            ← direct_sum.single_eq_lof, dfinsupp.single_apply, dfinsupp.single_apply] at hi0,
        split_ifs at hi0 with hi hj hj, { rwa hi at hik }, { rwa hi at hik }, { rwa hj at hjk },
        exfalso, apply hi0, rw sub_zero },
      simp [linear_map.map_sub, totalize_apply, hik, hjk,
        directed_system.map_map f, direct_sum.apply_eq_component,
        direct_sum.component.of],
    end⟩)
  ⟨ind, λ _ h, (finset.not_mem_empty _ h).elim, linear_map.map_zero _⟩
  (λ x y ⟨i, hi, hxi⟩ ⟨j, hj, hyj⟩,
    let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, λ l hl,
      (finset.mem_union.1 (dfinsupp.support_add hl)).elim
        (λ hl, le_trans (hi _ hl) hik)
        (λ hl, le_trans (hj _ hl) hjk),
      by simp [linear_map.map_add, hxi, hyj,
          to_module_totalize_of_le hik hi,
          to_module_totalize_of_le hjk hj]⟩)
  (λ a x ⟨i, hi, hxi⟩,
    ⟨i, λ k hk, hi k (direct_sum.support_smul _ _ hk),
      by simp [linear_map.map_smul, hxi]⟩)

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact {i x} (H : of R ι G f i x = 0) :
  ∃ j hij, f i j hij x = (0 : G j) :=
by haveI : nonempty ι := ⟨i⟩; exact
let ⟨j, hj, hxj⟩ := of.zero_exact_aux H in
if hx0 : x = 0 then ⟨i, le_refl _, by simp [hx0]⟩
else
  have hij : i ≤ j, from hj _ $
    by simp [direct_sum.apply_eq_component, hx0],
  ⟨j, hij, by simpa [totalize_apply, hij] using hxj⟩

end direct_limit

end module


namespace add_comm_group

variables [Π i, add_comm_group (G i)]
include dec_ι

/-- The direct limit of a directed system is the abelian groups glued together along the maps. -/
def direct_limit (f : Π i j, i ≤ j → G i →+ G j) : Type* :=
@module.direct_limit ℤ _ ι _ _ G _ _
  (λ i j hij, (f i j hij).to_int_linear_map)

namespace direct_limit

variables (f : Π i j, i ≤ j → G i →+ G j)

omit dec_ι

protected lemma directed_system [directed_system G (λ i j h, f i j h)] :
  module.directed_system G (λ i j hij, (f i j hij).to_int_linear_map) :=
⟨directed_system.map_self (λ i j h, f i j h), directed_system.map_map (λ i j h, f i j h)⟩

include dec_ι

local attribute [instance] direct_limit.directed_system

instance : add_comm_group (direct_limit G f) :=
module.direct_limit.add_comm_group G (λ i j hij, (f i j hij).to_int_linear_map)

instance : inhabited (direct_limit G f) := ⟨0⟩

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →ₗ[ℤ] direct_limit G f :=
module.direct_limit.of ℤ ι G (λ i j hij, (f i j hij).to_int_linear_map) i
variables {G f}

@[simp] lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
module.direct_limit.of_f

@[elab_as_eliminator]
protected theorem induction_on [nonempty ι] {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of G f i x)) : C z :=
module.direct_limit.induction_on z ih

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
theorem of.zero_exact [directed_system G (λ i j h, f i j h)] (i x) (h : of G f i x = 0) :
  ∃ j hij, f i j hij x = 0 :=
module.direct_limit.of.zero_exact h

variables (P : Type u₁) [add_comm_group P]
variables (g : Π i, G i →+ P)
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variables (G f)
/-- The universal property of the direct limit: maps from the components to another abelian group
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
def lift : direct_limit G f →ₗ[ℤ] P :=
module.direct_limit.lift ℤ ι G (λ i j hij, (f i j hij).to_int_linear_map)
  (λ i, (g i).to_int_linear_map) Hg
variables {G f}

@[simp] lemma lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
module.direct_limit.lift_of _ _ _

lemma lift_unique [nonempty ι] (F : direct_limit G f →+ P) (x) :
  F x = lift G f P (λ i, F.comp (of G f i).to_add_monoid_hom)
    (λ i j hij x, by simp) x :=
direct_limit.induction_on x $ λ i x, by simp

end direct_limit

end add_comm_group


namespace ring

variables [Π i, comm_ring (G i)]

section
variables (f : Π i j, i ≤ j → G i → G j)

open free_comm_ring

/-- The direct limit of a directed system is the rings glued together along the maps. -/
def direct_limit : Type (max v w) :=
(ideal.span { a |
  (∃ i j H x, of (⟨j, f i j H x⟩ : Σ i, G i) - of ⟨i, x⟩ = a) ∨
  (∃ i, of (⟨i, 1⟩ : Σ i, G i) - 1 = a) ∨
  (∃ i x y, of (⟨i, x + y⟩ : Σ i, G i) - (of ⟨i, x⟩ + of ⟨i, y⟩) = a) ∨
  (∃ i x y, of (⟨i, x * y⟩ : Σ i, G i) - (of ⟨i, x⟩ * of ⟨i, y⟩) = a) }).quotient

namespace direct_limit

instance : comm_ring (direct_limit G f) :=
ideal.quotient.comm_ring _

instance : ring (direct_limit G f) :=
comm_ring.to_ring _

instance : inhabited (direct_limit G f) := ⟨0⟩

/-- The canonical map from a component to the direct limit. -/
def of (i) : G i →+* direct_limit G f :=
ring_hom.mk'
{ to_fun := λ x, ideal.quotient.mk _ (of (⟨i, x⟩ : Σ i, G i)),
  map_one' := ideal.quotient.eq.2 $ subset_span $ or.inr $ or.inl ⟨i, rfl⟩,
  map_mul' := λ x y, ideal.quotient.eq.2 $ subset_span $ or.inr $ or.inr $ or.inr ⟨i, x, y, rfl⟩, }
(λ x y, ideal.quotient.eq.2 $ subset_span $ or.inr $ or.inr $ or.inl ⟨i, x, y, rfl⟩)

variables {G f}

@[simp] lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
ideal.quotient.eq.2 $ subset_span $ or.inl ⟨i, j, hij, x, rfl⟩

/-- Every element of the direct limit corresponds to some element in
some component of the directed system. -/
theorem exists_of [nonempty ι] (z : direct_limit G f) : ∃ i x, of G f i x = z :=
nonempty.elim (by apply_instance) $ assume ind : ι,
quotient.induction_on' z $ λ x, free_abelian_group.induction_on_sub x
  ⟨ind, 0, (of _ _ ind).map_zero⟩
  (forall_multiplicative_iff.2 $ λ s, multiset.induction_on s
    ⟨ind, 1, (of _ _ ind).map_one⟩
    (λ a s ih, let ⟨i, x⟩ := a, ⟨j, y, hs⟩ := ih, ⟨k, hik, hjk⟩ := directed_order.directed i j in
      ⟨k, f i k hik x * f j k hjk y, by rw [(of _ _ _).map_mul, of_f, of_f, hs]; refl⟩))
  (λ p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x - f j k hjk y, by rw [(of _ _ _).map_sub, of_f, of_f, ihx, ihy]; refl⟩)

section
open_locale classical
open polynomial

variables {f' : Π i j, i ≤ j → G i →+* G j}

theorem polynomial.exists_of [nonempty ι] (q : polynomial (direct_limit G (λ i j h, f' i j h))) :
  ∃ i p, polynomial.map (of G (λ i j h, f' i j h) i) p = q :=
polynomial.induction_on q
  (λ z, let ⟨i, x, h⟩ := exists_of z in ⟨i, C x, by rw [map_C, h]⟩)
  (λ q₁ q₂ ⟨i₁, p₁, ih₁⟩ ⟨i₂, p₂, ih₂⟩, let ⟨i, h1, h2⟩ := directed_order.directed i₁ i₂ in
    ⟨i, p₁.map (f' i₁ i h1) + p₂.map (f' i₂ i h2),
     by { rw [polynomial.map_add, map_map, map_map, ← ih₁, ← ih₂],
      congr' 2; ext x; simp_rw [ring_hom.comp_apply, of_f] }⟩)
  (λ n z ih, let ⟨i, x, h⟩ := exists_of z in ⟨i, C x * X ^ (n + 1),
    by rw [polynomial.map_mul, map_C, h, polynomial.map_pow, map_X]⟩)

end

@[elab_as_eliminator] theorem induction_on [nonempty ι] {C : direct_limit G f → Prop}
  (z : direct_limit G f) (ih : ∀ i x, C (of G f i x)) : C z :=
let ⟨i, x, hx⟩ := exists_of z in hx ▸ ih i x

section of_zero_exact
open_locale classical

variables (f' : Π i j, i ≤ j → G i →+* G j)
variables [directed_system G (λ i j h, f' i j h)]
variables (G f)

lemma of.zero_exact_aux2 {x : free_comm_ring Σ i, G i} {s t} (hxs : is_supported x s) {j k}
  (hj : ∀ z : Σ i, G i, z ∈ s → z.1 ≤ j) (hk : ∀ z : Σ i, G i, z ∈ t → z.1 ≤ k)
  (hjk : j ≤ k) (hst : s ⊆ t) :
  f' j k hjk (lift (λ ix : s, f' ix.1.1 j (hj ix ix.2) ix.1.2) (restriction s x)) =
  lift (λ ix : t, f' ix.1.1 k (hk ix ix.2) ix.1.2) (restriction t x) :=
begin
  refine ring.in_closure.rec_on hxs _ _ _ _,
  { rw [(restriction _).map_one, (free_comm_ring.lift _).map_one, (f' j k hjk).map_one,
        (restriction _).map_one, (free_comm_ring.lift _).map_one] },
  { rw [(restriction _).map_neg, (restriction _).map_one,
        (free_comm_ring.lift _).map_neg, (free_comm_ring.lift _).map_one,
        (f' j k hjk).map_neg, (f' j k hjk).map_one,
        (restriction _).map_neg, (restriction _).map_one,
        (free_comm_ring.lift _).map_neg, (free_comm_ring.lift _).map_one] },
  { rintros _ ⟨p, hps, rfl⟩ n ih,
    rw [(restriction _).map_mul, (free_comm_ring.lift _).map_mul,
        (f' j k hjk).map_mul, ih,
        (restriction _).map_mul, (free_comm_ring.lift _).map_mul,
        restriction_of, dif_pos hps, lift_of, restriction_of, dif_pos (hst hps), lift_of],
    dsimp only,
    have := directed_system.map_map (λ i j h, f' i j h),
    dsimp only at this,
    rw this, refl },
  { rintros x y ihx ihy,
    rw [(restriction _).map_add, (free_comm_ring.lift _).map_add,
        (f' j k hjk).map_add, ihx, ihy,
        (restriction _).map_add, (free_comm_ring.lift _).map_add] }
end
variables {G f f'}

lemma of.zero_exact_aux [nonempty ι] {x : free_comm_ring Σ i, G i}
  (H : ideal.quotient.mk _ x = (0 : direct_limit G (λ i j h, f' i j h))) :
  ∃ j s, ∃ H : (∀ k : Σ i, G i, k ∈ s → k.1 ≤ j), is_supported x s ∧
    lift (λ ix : s, f' ix.1.1 j (H ix ix.2) ix.1.2) (restriction s x) = (0 : G j) :=
begin
  refine span_induction (ideal.quotient.eq_zero_iff_mem.1 H) _ _ _ _,
  { rintros x (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩),
    { refine ⟨j, {⟨i, x⟩, ⟨j, f' i j hij x⟩}, _,
        is_supported_sub (is_supported_of.2 $ or.inr rfl) (is_supported_of.2 $ or.inl rfl), _⟩,
      { rintros k (rfl | ⟨rfl | _⟩), exact hij, refl },
      { rw [(restriction _).map_sub, (free_comm_ring.lift _).map_sub,
            restriction_of, dif_pos, restriction_of, dif_pos, lift_of, lift_of],
        dsimp only,
        have := directed_system.map_map (λ i j h, f' i j h),
        dsimp only at this,
        rw this, exact sub_self _,
        exacts [or.inr rfl, or.inl rfl] } },
    { refine ⟨i, {⟨i, 1⟩}, _, is_supported_sub (is_supported_of.2 rfl) is_supported_one, _⟩,
      { rintros k (rfl|h), refl },
      { rw [(restriction _).map_sub, (free_comm_ring.lift _).map_sub, restriction_of, dif_pos,
          (restriction _).map_one, lift_of, (free_comm_ring.lift _).map_one],
        dsimp only, rw [(f' i i _).map_one, sub_self],
        { exact set.mem_singleton _ } } },
    { refine ⟨i, {⟨i, x+y⟩, ⟨i, x⟩, ⟨i, y⟩}, _,
        is_supported_sub (is_supported_of.2 $ or.inl rfl)
          (is_supported_add (is_supported_of.2 $ or.inr $ or.inl rfl)
            (is_supported_of.2 $ or.inr $ or.inr rfl)), _⟩,
      { rintros k (rfl | ⟨rfl | ⟨rfl | hk⟩⟩); refl },
      { rw [(restriction _).map_sub, (restriction _).map_add,
            restriction_of, restriction_of, restriction_of,
            dif_pos, dif_pos, dif_pos,
            (free_comm_ring.lift _).map_sub, (free_comm_ring.lift _).map_add,
            lift_of, lift_of, lift_of],
        dsimp only, rw (f' i i _).map_add, exact sub_self _,
        exacts [or.inl rfl, or.inr (or.inr rfl), or.inr (or.inl rfl)] } },
    { refine ⟨i, {⟨i, x*y⟩, ⟨i, x⟩, ⟨i, y⟩}, _,
        is_supported_sub (is_supported_of.2 $ or.inl rfl)
          (is_supported_mul (is_supported_of.2 $ or.inr $ or.inl rfl)
            (is_supported_of.2 $ or.inr $ or.inr rfl)), _⟩,
      { rintros k (rfl | ⟨rfl | ⟨rfl | hk⟩⟩); refl },
      { rw [(restriction _).map_sub, (restriction _).map_mul,
            restriction_of, restriction_of, restriction_of,
            dif_pos, dif_pos, dif_pos,
            (free_comm_ring.lift _).map_sub, (free_comm_ring.lift _).map_mul,
            lift_of, lift_of, lift_of],
        dsimp only, rw (f' i i _).map_mul,
        exacts [sub_self _, or.inl rfl, or.inr (or.inr rfl),
          or.inr (or.inl rfl)] } } },
  { refine nonempty.elim (by apply_instance) (assume ind : ι, _),
    refine ⟨ind, ∅, λ _, false.elim, is_supported_zero, _⟩,
    rw [(restriction _).map_zero, (free_comm_ring.lift _).map_zero] },
  { rintros x y ⟨i, s, hi, hxs, ihs⟩ ⟨j, t, hj, hyt, iht⟩,
    rcases directed_order.directed i j with ⟨k, hik, hjk⟩,
    have : ∀ z : Σ i, G i, z ∈ s ∪ t → z.1 ≤ k,
    { rintros z (hz | hz), exact le_trans (hi z hz) hik, exact le_trans (hj z hz) hjk },
    refine ⟨k, s ∪ t, this, is_supported_add (is_supported_upwards hxs $ set.subset_union_left s t)
      (is_supported_upwards hyt $ set.subset_union_right s t), _⟩,
    { rw [(restriction _).map_add, (free_comm_ring.lift _).map_add,
        ← of.zero_exact_aux2 G f' hxs hi this hik (set.subset_union_left s t),
        ← of.zero_exact_aux2 G f' hyt hj this hjk (set.subset_union_right s t),
        ihs, (f' i k hik).map_zero, iht, (f' j k hjk).map_zero, zero_add] } },
  { rintros x y ⟨j, t, hj, hyt, iht⟩, rw smul_eq_mul,
    rcases exists_finset_support x with ⟨s, hxs⟩,
    rcases (s.image sigma.fst).exists_le with ⟨i, hi⟩,
    rcases directed_order.directed i j with ⟨k, hik, hjk⟩,
    have : ∀ z : Σ i, G i, z ∈ ↑s ∪ t → z.1 ≤ k,
    { rintros z (hz | hz),
      exacts [(hi z.1 $ finset.mem_image.2 ⟨z, hz, rfl⟩).trans hik, (hj z hz).trans hjk] },
    refine ⟨k, ↑s ∪ t, this, is_supported_mul
      (is_supported_upwards hxs $ set.subset_union_left ↑s t)
      (is_supported_upwards hyt $ set.subset_union_right ↑s t), _⟩,
    rw [(restriction _).map_mul, (free_comm_ring.lift _).map_mul,
        ← of.zero_exact_aux2 G f' hyt hj this hjk (set.subset_union_right ↑s t),
        iht, (f' j k hjk).map_zero, mul_zero] }
end

/-- A component that corresponds to zero in the direct limit is already zero in some
bigger module in the directed system. -/
lemma of.zero_exact {i x} (hix : of G (λ i j h, f' i j h) i x = 0) :
  ∃ j (hij : i ≤ j), f' i j hij x = 0 :=
by haveI : nonempty ι := ⟨i⟩; exact
let ⟨j, s, H, hxs, hx⟩ := of.zero_exact_aux hix in
have hixs : (⟨i, x⟩ : Σ i, G i) ∈ s, from is_supported_of.1 hxs,
⟨j, H ⟨i, x⟩ hixs, by rw [restriction_of, dif_pos hixs, lift_of] at hx; exact hx⟩
end of_zero_exact

variables (f' : Π i j, i ≤ j → G i →+* G j)

/-- If the maps in the directed system are injective, then the canonical maps
from the components to the direct limits are injective. -/
theorem of_injective [directed_system G (λ i j h, f' i j h)]
  (hf : ∀ i j hij, function.injective (f' i j hij)) (i) :
  function.injective (of G (λ i j h, f' i j h) i) :=
begin
  suffices : ∀ x, of G (λ i j h, f' i j h) i x = 0 → x = 0,
  { intros x y hxy, rw ← sub_eq_zero_iff_eq, apply this,
    rw [(of G _ i).map_sub, hxy, sub_self] },
  intros x hx, rcases of.zero_exact hx with ⟨j, hij, hfx⟩,
  apply hf i j hij, rw [hfx, (f' i j hij).map_zero]
end

variables (P : Type u₁) [comm_ring P]
variables (g : Π i, G i →+* P)
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

open free_comm_ring

variables (G f)
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
def lift : direct_limit G f →+* P :=
ideal.quotient.lift _ (free_comm_ring.lift $ λ (x : Σ i, G i), g x.1 x.2) begin
  suffices : ideal.span _ ≤
    ideal.comap (free_comm_ring.lift (λ (x : Σ (i : ι), G i), g (x.fst) (x.snd))) ⊥,
  { intros x hx, exact (mem_bot P).1 (this hx) },
  rw ideal.span_le, intros x hx,
  rw [mem_coe, ideal.mem_comap, mem_bot],
  rcases hx with ⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩;
  simp only [ring_hom.map_sub, lift_of, Hg, ring_hom.map_one, ring_hom.map_add, ring_hom.map_mul,
      (g i).map_one, (g i).map_add, (g i).map_mul, sub_self]
end

variables {G f}
omit Hg

@[simp] lemma lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := free_comm_ring.lift_of _ _

theorem lift_unique [nonempty ι] (F : direct_limit G f →+* P) (x) :
  F x = lift G f P (λ i, F.comp $ of G f i) (λ i j hij x, by simp) x :=
direct_limit.induction_on x $ λ i x, by simp

end direct_limit

end

end ring


namespace field

variables [nonempty ι] [Π i, field (G i)]
variables (f : Π i j, i ≤ j → G i → G j)
variables (f' : Π i j, i ≤ j → G i →+* G j)

namespace direct_limit

instance nontrivial [directed_system G (λ i j h, f' i j h)] :
  nontrivial (ring.direct_limit G (λ i j h, f' i j h)) :=
⟨⟨0, 1, nonempty.elim (by apply_instance) $ assume i : ι, begin
  change (0 : ring.direct_limit G (λ i j h, f' i j h)) ≠ 1,
  rw ← (ring.direct_limit.of _ _ _).map_one,
  intros H, rcases ring.direct_limit.of.zero_exact H.symm with ⟨j, hij, hf⟩,
  rw (f' i j hij).map_one at hf,
  exact one_ne_zero hf
end ⟩⟩

theorem exists_inv {p : ring.direct_limit G f} : p ≠ 0 → ∃ y, p * y = 1 :=
ring.direct_limit.induction_on p $ λ i x H,
⟨ring.direct_limit.of G f i (x⁻¹), by erw [← (ring.direct_limit.of _ _ _).map_mul,
    mul_inv_cancel (assume h : x = 0, H $ by rw [h, (ring.direct_limit.of _ _ _).map_zero]),
    (ring.direct_limit.of _ _ _).map_one]⟩

section
open_locale classical

/-- Noncomputable multiplicative inverse in a direct limit of fields. -/
noncomputable def inv (p : ring.direct_limit G f) : ring.direct_limit G f :=
if H : p = 0 then 0 else classical.some (direct_limit.exists_inv G f H)

protected theorem mul_inv_cancel {p : ring.direct_limit G f} (hp : p ≠ 0) : p * inv G f p = 1 :=
by rw [inv, dif_neg hp, classical.some_spec (direct_limit.exists_inv G f hp)]

protected theorem inv_mul_cancel {p : ring.direct_limit G f} (hp : p ≠ 0) : inv G f p * p = 1 :=
by rw [_root_.mul_comm, direct_limit.mul_inv_cancel G f hp]

/-- Noncomputable field structure on the direct limit of fields. -/
protected noncomputable def field [directed_system G (λ i j h, f' i j h)] :
  field (ring.direct_limit G (λ i j h, f' i j h)) :=
{ inv := inv G (λ i j h, f' i j h),
  mul_inv_cancel := λ p, direct_limit.mul_inv_cancel G (λ i j h, f' i j h),
  inv_zero := dif_pos rfl,
  .. ring.direct_limit.comm_ring G (λ i j h, f' i j h),
  .. direct_limit.nontrivial G (λ i j h, f' i j h) }

end

end direct_limit

end field
