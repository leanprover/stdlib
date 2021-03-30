/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
import ring_theory.localization
import ring_theory.noetherian
import ring_theory.principal_ideal_domain
import tactic.field_simp

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R`, `P` the localization of `R` at `S`, and `f` the
natural ring hom from `R` to `P`.
 * `is_fractional` defines which `R`-submodules of `P` are fractional ideals
 * `fractional_ideal f` is the type of fractional ideals in `P`
 * `has_coe (ideal R) (fractional_ideal f)` instance
 * `comm_semiring (fractional_ideal f)` instance:
   the typical ideal operations generalized to fractional ideals
 * `lattice (fractional_ideal f)` instance
 * `map` is the pushforward of a fractional ideal along an algebra morphism

Let `K` be the localization of `R` at `R \ {0}` and `g` the natural ring hom from `R` to `K`.
 * `has_div (fractional_ideal g)` instance:
   the ideal quotient `I / J` (typically written $I : J$, but a `:` operator cannot be defined)

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `prod_one_self_div_eq` states that `1 / I` is the inverse of `I` if one exists
  * `is_noetherian` states that very fractional ideal of a noetherian integral domain is noetherian

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `fractional_ideal` to be the subtype of the predicate `is_fractional`,
instead of having `fractional_ideal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `I.1 + J.1 = (I + J).1` and `⊥.1 = 0.1`.

In `ring_theory.localization`, we define a copy of the localization map `f`'s codomain `P`
(`f.codomain`) so that the `R`-algebra instance on `P` can 'know' the map needed to induce
the `R`-algebra structure.

We don't assume that the localization is a field until we need it to define ideal quotients.
When this assumption is needed, we replace `S` with `non_zero_divisors R`, making the localization
a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/

open localization_map

namespace ring

section defs

variables {R : Type*} [comm_ring R] {S : submonoid R} {P : Type*} [comm_ring P]
  (f : localization_map S P)

/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def is_fractional (I : submodule R f.codomain) :=
∃ a ∈ S, ∀ b ∈ I, f.is_integer (f.to_map a * b)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

  More precisely, let `P` be a localization of `R` at some submonoid `S`,
  then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
  such that there is a nonzero `a : R` with `a I ⊆ R`.
-/
def fractional_ideal :=
{I : submodule R f.codomain // is_fractional f I}

end defs

namespace fractional_ideal

open set
open submodule

variables {R : Type*} [comm_ring R] {S : submonoid R} {P : Type*} [comm_ring P]
  {f : localization_map S P}

instance : has_coe (fractional_ideal f) (submodule R f.codomain) := ⟨λ I, I.val⟩

@[simp] lemma val_eq_coe (I : fractional_ideal f) : I.val = I := rfl

@[simp, norm_cast] lemma coe_mk (I : submodule R f.codomain) (hI : is_fractional f I) :
  (subtype.mk I hI : submodule R f.codomain) = I := rfl

instance : has_mem P (fractional_ideal f) := ⟨λ x I, x ∈ (I : submodule R f.codomain)⟩

/-- Fractional ideals are equal if their submodules are equal.

  Combined with `submodule.ext` this gives that fractional ideals are equal if
  they have the same elements.
-/
@[ext]
lemma ext {I J : fractional_ideal f} : (I : submodule R f.codomain) = J → I = J :=
subtype.ext_iff_val.mpr

lemma ext_iff {I J : fractional_ideal f} : (∀ x, (x ∈ I ↔ x ∈ J)) ↔ I = J :=
⟨ λ h, ext (submodule.ext h), λ h x, h ▸ iff.rfl ⟩

lemma fractional_of_subset_one (I : submodule R f.codomain)
  (h : I ≤ (submodule.span R {1})) :
  is_fractional f I :=
begin
  use [1, S.one_mem],
  intros b hb,
  rw [f.to_map.map_one, one_mul],
  rw ←submodule.one_eq_span at h,
  obtain ⟨b', b'_mem, b'_eq_b⟩ := h hb,
  rw (show b = f.to_map b', from b'_eq_b.symm),
  exact set.mem_range_self b',
end

lemma is_fractional_of_le {I : submodule R f.codomain} {J : fractional_ideal f}
  (hIJ : I ≤ J) : is_fractional f I :=
begin
  obtain ⟨a, a_mem, ha⟩ := J.2,
  use [a, a_mem],
  intros b b_mem,
  exact ha b (hIJ b_mem)
end

instance coe_to_fractional_ideal : has_coe (ideal R) (fractional_ideal f) :=
⟨ λ I, ⟨f.coe_submodule I, fractional_of_subset_one _ $ λ x ⟨y, hy, h⟩,
  submodule.mem_span_singleton.2 ⟨y, by rw ←h; exact mul_one _⟩⟩ ⟩

@[simp, norm_cast] lemma coe_coe_ideal (I : ideal R) :
  ((I : fractional_ideal f) : submodule R f.codomain) = f.coe_submodule I := rfl

@[simp] lemma mem_coe_ideal {x : f.codomain} {I : ideal R} :
  x ∈ (I : fractional_ideal f) ↔ ∃ (x' ∈ I), f.to_map x' = x :=
⟨ λ ⟨x', hx', hx⟩, ⟨x', hx', hx⟩,
  λ ⟨x', hx', hx⟩, ⟨x', hx', hx⟩ ⟩

instance : has_zero (fractional_ideal f) := ⟨(0 : ideal R)⟩

@[simp] lemma mem_zero_iff {x : P} : x ∈ (0 : fractional_ideal f) ↔ x = 0 :=
⟨ (λ ⟨x', x'_mem_zero, x'_eq_x⟩,
    have x'_eq_zero : x' = 0 := x'_mem_zero,
    by simp [x'_eq_x.symm, x'_eq_zero]),
  (λ hx, ⟨0, rfl, by simp [hx]⟩) ⟩

@[simp, norm_cast] lemma coe_zero : ↑(0 : fractional_ideal f) = (⊥ : submodule R f.codomain) :=
submodule.ext $ λ _, mem_zero_iff

@[simp, norm_cast] lemma coe_to_fractional_ideal_bot : ((⊥ : ideal R) : fractional_ideal f) = 0 :=
rfl

@[simp] lemma exists_mem_to_map_eq {x : R} {I : ideal R} (h : S ≤ non_zero_divisors R) :
  (∃ x', x' ∈ I ∧ f.to_map x' = f.to_map x) ↔ x ∈ I :=
⟨λ ⟨x', hx', eq⟩, f.injective h eq ▸ hx', λ h, ⟨x, h, rfl⟩⟩

lemma coe_to_fractional_ideal_injective (h : S ≤ non_zero_divisors R) :
  function.injective (coe : ideal R → fractional_ideal f) :=
λ I J heq, have
  ∀ (x : R), f.to_map x ∈ (I : fractional_ideal f) ↔ f.to_map x ∈ (J : fractional_ideal f) :=
λ x, heq ▸ iff.rfl,
ideal.ext (by { simpa only [mem_coe_ideal, exists_prop, exists_mem_to_map_eq h] using this })

lemma coe_to_fractional_ideal_eq_zero {I : ideal R} (hS : S ≤ non_zero_divisors R) :
  (I : fractional_ideal f) = 0 ↔ I = (⊥ : ideal R) :=
⟨λ h, coe_to_fractional_ideal_injective hS h,
 λ h, by rw [h, coe_to_fractional_ideal_bot]⟩

lemma coe_to_fractional_ideal_ne_zero {I : ideal R} (hS : S ≤ non_zero_divisors R) :
  (I : fractional_ideal f) ≠ 0 ↔ I ≠ (⊥ : ideal R) :=
not_iff_not.mpr (coe_to_fractional_ideal_eq_zero hS)

lemma coe_to_submodule_eq_bot {I : fractional_ideal f} :
  (I : submodule R f.codomain) = ⊥ ↔ I = 0 :=
⟨λ h, ext (by simp [h]),
 λ h, by simp [h] ⟩

lemma coe_to_submodule_ne_bot {I : fractional_ideal f} :
  ↑I ≠ (⊥ : submodule R f.codomain) ↔ I ≠ 0 :=
not_iff_not.mpr coe_to_submodule_eq_bot

instance : inhabited (fractional_ideal f) := ⟨0⟩

instance : has_one (fractional_ideal f) :=
⟨(1 : ideal R)⟩

lemma mem_one_iff {x : P} : x ∈ (1 : fractional_ideal f) ↔ ∃ x' : R, f.to_map x' = x :=
iff.intro (λ ⟨x', _, h⟩, ⟨x', h⟩) (λ ⟨x', h⟩, ⟨x', ⟨x', set.mem_univ _, rfl⟩, h⟩)

lemma coe_mem_one (x : R) : f.to_map x ∈ (1 : fractional_ideal f) :=
mem_one_iff.mpr ⟨x, rfl⟩

lemma one_mem_one : (1 : P) ∈ (1 : fractional_ideal f) :=
mem_one_iff.mpr ⟨1, f.to_map.map_one⟩

/-- `(1 : fractional_ideal f)` is defined as the R-submodule `f(R) ≤ K`.

However, this is not definitionally equal to `1 : submodule R K`,
which is proved in the actual `simp` lemma `coe_one`. -/
lemma coe_one_eq_coe_submodule_one :
  ↑(1 : fractional_ideal f) = f.coe_submodule (1 : ideal R) :=
rfl

@[simp, norm_cast] lemma coe_one :
  (↑(1 : fractional_ideal f) : submodule R f.codomain) = 1 :=
begin
  simp only [coe_one_eq_coe_submodule_one, ideal.one_eq_top],
  convert (submodule.one_eq_map_top).symm,
end

section lattice

/-!
### `lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/

instance : partial_order (fractional_ideal f) :=
{ le := λ I J, I.1 ≤ J.1,
  le_refl := λ I, le_refl I.1,
  le_antisymm := λ ⟨I, hI⟩ ⟨J, hJ⟩ hIJ hJI, by { congr, exact le_antisymm hIJ hJI },
  le_trans := λ _ _ _ hIJ hJK, le_trans hIJ hJK }

lemma le_iff_mem {I J : fractional_ideal f} : I ≤ J ↔ (∀ x ∈ I, x ∈ J) :=
iff.rfl

@[simp] lemma coe_le_coe {I J : fractional_ideal f} :
  (I : submodule R f.codomain) ≤ (J : submodule R f.codomain) ↔ I ≤ J :=
iff.rfl

lemma zero_le (I : fractional_ideal f) : 0 ≤ I :=
begin
  intros x hx,
  convert submodule.zero_mem _,
  simpa using hx
end

instance order_bot : order_bot (fractional_ideal f) :=
{ bot := 0,
  bot_le := zero_le,
  ..fractional_ideal.partial_order }

@[simp] lemma bot_eq_zero : (⊥ : fractional_ideal f) = 0 :=
rfl

@[simp] lemma le_zero_iff {I : fractional_ideal f} : I ≤ 0 ↔ I = 0 :=
le_bot_iff

lemma eq_zero_iff {I : fractional_ideal f} : I = 0 ↔ (∀ x ∈ I, x = (0 : P)) :=
⟨ (λ h x hx, by simpa [h, mem_zero_iff] using hx),
  (λ h, le_bot_iff.mp (λ x hx, mem_zero_iff.mpr (h x hx))) ⟩

lemma fractional_sup (I J : fractional_ideal f) : is_fractional f (I.1 ⊔ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  rcases J.2 with ⟨aJ, haJ, hJ⟩,
  use aI * aJ,
  use S.mul_mem haI haJ,
  intros b hb,
  rcases mem_sup.mp hb with
    ⟨bI, hbI, bJ, hbJ, hbIJ⟩,
  rw [←hbIJ, mul_add],
  apply is_integer_add,
  { rw [mul_comm aI, f.to_map.map_mul, mul_assoc],
    apply is_integer_smul (hI bI hbI), },
  { rw [f.to_map.map_mul, mul_assoc],
    apply is_integer_smul (hJ bJ hbJ) }
end

lemma fractional_inf (I J : fractional_ideal f) : is_fractional f (I.1 ⊓ J.1) :=
begin
  rcases I.2 with ⟨aI, haI, hI⟩,
  use aI,
  use haI,
  intros b hb,
  rcases mem_inf.mp hb with ⟨hbI, hbJ⟩,
  exact (hI b hbI)
end

instance lattice : lattice (fractional_ideal f) :=
{ inf := λ I J, ⟨I.1 ⊓ J.1, fractional_inf I J⟩,
  sup := λ I J, ⟨I.1 ⊔ J.1, fractional_sup I J⟩,
  inf_le_left := λ I J, show I.1 ⊓ J.1 ≤ I.1, from inf_le_left,
  inf_le_right := λ I J, show I.1 ⊓ J.1 ≤ J.1, from inf_le_right,
  le_inf := λ I J K hIJ hIK, show I.1 ≤ (J.1 ⊓ K.1), from le_inf hIJ hIK,
  le_sup_left := λ I J, show I.1 ≤ I.1 ⊔ J.1, from le_sup_left,
  le_sup_right := λ I J, show J.1 ≤ I.1 ⊔ J.1, from le_sup_right,
  sup_le := λ I J K hIK hJK, show (I.1 ⊔ J.1) ≤ K.1, from sup_le hIK hJK,
  ..fractional_ideal.partial_order }

instance : semilattice_sup_bot (fractional_ideal f) :=
{ ..fractional_ideal.order_bot, ..fractional_ideal.lattice }

end lattice

section semiring

instance : has_add (fractional_ideal f) := ⟨(⊔)⟩

@[simp]
lemma sup_eq_add (I J : fractional_ideal f) : I ⊔ J = I + J := rfl

@[simp, norm_cast]
lemma coe_add (I J : fractional_ideal f) : (↑(I + J) : submodule R f.codomain) = I + J := rfl

lemma fractional_mul (I J : fractional_ideal f) : is_fractional f (I.1 * J.1) :=
begin
  rcases I with ⟨I, aI, haI, hI⟩,
  rcases J with ⟨J, aJ, haJ, hJ⟩,
  use aI * aJ,
  use S.mul_mem haI haJ,
  intros b hb,
  apply submodule.mul_induction_on hb,
  { intros m hm n hn,
    obtain ⟨n', hn'⟩ := hJ n hn,
    rw [f.to_map.map_mul, mul_comm m, ←mul_assoc, mul_assoc _ _ n],
    erw ←hn', rw mul_assoc,
    apply hI,
    exact I.smul_mem (_ : R) hm },
  { rw [mul_zero],
    exact ⟨0, f.to_map.map_zero⟩ },
  { intros x y hx hy,
    rw [mul_add],
    apply is_integer_add hx hy },
  { intros r x hx,
    show f.is_integer (_ * (f.to_map r * x)),
    rw [←mul_assoc, ←f.to_map.map_mul, mul_comm _ r, f.to_map.map_mul, mul_assoc],
    apply is_integer_smul hx },
end

/-- `fractional_ideal.mul` is the product of two fractional ideals,
used to define the `has_mul` instance.

This is only an auxiliary definition: the preferred way of writing `I.mul J` is `I * J`.

Elaborated terms involving `fractional_ideal` tend to grow quite large,
so by making definitions irreducible, we hope to avoid deep unfolds.
-/
@[irreducible]
def mul (I J : fractional_ideal f) : fractional_ideal f :=
⟨I.1 * J.1, fractional_mul I J⟩

local attribute [semireducible] mul

instance : has_mul (fractional_ideal f) := ⟨λ I J, mul I J⟩

@[simp] lemma mul_eq_mul (I J : fractional_ideal f) : mul I J = I * J := rfl

@[simp, norm_cast]
lemma coe_mul (I J : fractional_ideal f) : (↑(I * J) : submodule R f.codomain) = I * J := rfl

lemma mul_left_mono (I : fractional_ideal f) : monotone ((*) I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul hx (h hy))

lemma mul_right_mono (I : fractional_ideal f) : monotone (λ J, J * I) :=
λ J J' h, mul_le.mpr (λ x hx y hy, mul_mem_mul (h hx) hy)

lemma mul_mem_mul {I J : fractional_ideal f} {i j : f.codomain} (hi : i ∈ I) (hj : j ∈ J) :
  i * j ∈ I * J := submodule.mul_mem_mul hi hj

lemma mul_le {I J K : fractional_ideal f} :
  I * J ≤ K ↔ (∀ (i ∈ I) (j ∈ J), i * j ∈ K) :=
submodule.mul_le

@[elab_as_eliminator] protected theorem mul_induction_on
  {I J : fractional_ideal f}
  {C : f.codomain → Prop} {r : f.codomain} (hr : r ∈ I * J)
  (hm : ∀ (i ∈ I) (j ∈ J), C (i * j))
  (h0 : C 0) (ha : ∀ x y, C x → C y → C (x + y))
  (hs : ∀ (r : R) x, C x → C (r • x)) : C r :=
submodule.mul_induction_on hr hm h0 ha hs

instance comm_semiring : comm_semiring (fractional_ideal f) :=
{ add_assoc := λ I J K, sup_assoc,
  add_comm := λ I J, sup_comm,
  add_zero := λ I, sup_bot_eq,
  zero_add := λ I, bot_sup_eq,
  mul_assoc := λ I J K, ext (submodule.mul_assoc _ _ _),
  mul_comm := λ I J, ext (submodule.mul_comm _ _),
  mul_one := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x hx y ⟨y', y'_mem_R, y'_eq_y⟩,
      rw [←y'_eq_y, mul_comm],
      exact submodule.smul_mem _ (_ : R) hx },
    { have : x * 1 ∈ (I * 1) := mul_mem_mul h one_mem_one,
      rwa [mul_one] at this }
  end,
  one_mul := λ I, begin
    ext,
    split; intro h,
    { apply mul_le.mpr _ h,
      rintros x ⟨x', x'_mem_R, x'_eq_x⟩ y hy,
      rw ←x'_eq_x,
      exact submodule.smul_mem _ (_ : R) hy },
    { have : 1 * x ∈ (1 * I) := mul_mem_mul one_mem_one h,
      rwa [one_mul] at this }
  end,
  mul_zero := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hy])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  zero_mul := λ I, eq_zero_iff.mpr (λ x hx, submodule.mul_induction_on hx
    (λ x hx y hy, by simp [mem_zero_iff.mp hx])
    rfl
    (λ x y hx hy, by simp [hx, hy])
    (λ r x hx, by simp [hx])),
  left_distrib := λ I J K, ext (mul_add _ _ _),
  right_distrib := λ I J K, ext (add_mul _ _ _),
  ..fractional_ideal.has_zero,
  ..fractional_ideal.has_add,
  ..fractional_ideal.has_one,
  ..fractional_ideal.has_mul }

section order

lemma add_le_add_left {I J : fractional_ideal f} (hIJ : I ≤ J) (J' : fractional_ideal f) :
  J' + I ≤ J' + J :=
sup_le_sup_left hIJ J'

lemma mul_le_mul_left {I J : fractional_ideal f} (hIJ : I ≤ J) (J' : fractional_ideal f) :
  J' * I ≤ J' * J :=
mul_le.mpr (λ k hk j hj, mul_mem_mul hk (hIJ hj))

lemma le_self_mul_self {I : fractional_ideal f} (hI: 1 ≤ I) : I ≤ I * I :=
begin
  convert mul_left_mono I hI,
  exact (mul_one I).symm
end

lemma mul_self_le_self {I : fractional_ideal f} (hI: I ≤ 1) : I * I ≤ I :=
begin
  convert mul_left_mono I hI,
  exact (mul_one I).symm
end

lemma coe_ideal_le_one {I : ideal R} : (I : fractional_ideal f) ≤ 1 :=
λ x hx, let ⟨y, _, hy⟩ := fractional_ideal.mem_coe_ideal.mp hx
  in fractional_ideal.mem_one_iff.mpr ⟨y, hy⟩

lemma le_one_iff_exists_coe_ideal {J : fractional_ideal f} :
  J ≤ (1 : fractional_ideal f) ↔ ∃ (I : ideal R), ↑I = J :=
begin
  split,
  { intro hJ,
    refine ⟨⟨{x : R | f.to_map x ∈ J}, _, _, _⟩, _⟩,
    { rw [mem_set_of_eq, ring_hom.map_zero],
      exact J.val.zero_mem },
    { intros a b ha hb,
      rw [mem_set_of_eq, ring_hom.map_add],
      exact J.val.add_mem ha hb },
    { intros c x hx,
      rw [smul_eq_mul, mem_set_of_eq, ring_hom.map_mul],
      exact J.val.smul_mem c hx },
    { ext x,
      split,
      { rintros ⟨y, hy, eq_y⟩,
        rwa ← eq_y },
      { intro hx,
        obtain ⟨y, eq_x⟩ := fractional_ideal.mem_one_iff.mp (hJ hx),
        rw ← eq_x at *,
        exact ⟨y, hx, rfl⟩ } } },
  { rintro ⟨I, hI⟩,
    rw ← hI,
    apply coe_ideal_le_one },
end

end order

variables {P' : Type*} [comm_ring P'] {f' : localization_map S P'}
variables {P'' : Type*} [comm_ring P''] {f'' : localization_map S P''}

lemma fractional_map (g : f.codomain →ₐ[R] f'.codomain) (I : fractional_ideal f) :
  is_fractional f' (submodule.map g.to_linear_map I.1) :=
begin
  rcases I with ⟨I, a, a_nonzero, hI⟩,
  use [a, a_nonzero],
  intros b hb,
  obtain ⟨b', b'_mem, hb'⟩ := submodule.mem_map.mp hb,
  obtain ⟨x, hx⟩ := hI b' b'_mem,
  use x,
  erw [←g.commutes, hx, g.map_smul, hb'],
  refl
end

/-- `I.map g` is the pushforward of the fractional ideal `I` along the algebra morphism `g` -/
def map (g : f.codomain →ₐ[R] f'.codomain) :
  fractional_ideal f → fractional_ideal f' :=
λ I, ⟨submodule.map g.to_linear_map I.1, fractional_map g I⟩

@[simp, norm_cast] lemma coe_map (g : f.codomain →ₐ[R] f'.codomain) (I : fractional_ideal f) :
  ↑(map g I) = submodule.map g.to_linear_map I := rfl

@[simp] lemma mem_map {I : fractional_ideal f} {g : f.codomain →ₐ[R] f'.codomain}
  {y : f'.codomain} : y ∈ I.map g ↔ ∃ x, x ∈ I ∧ g x = y :=
submodule.mem_map

variables (I J : fractional_ideal f) (g : f.codomain →ₐ[R] f'.codomain)

@[simp] lemma map_id : I.map (alg_hom.id _ _) = I :=
ext (submodule.map_id I.1)

@[simp] lemma map_comp (g' : f'.codomain →ₐ[R] f''.codomain) :
  I.map (g'.comp g) = (I.map g).map g' :=
ext (submodule.map_comp g.to_linear_map g'.to_linear_map I.1)

@[simp, norm_cast] lemma map_coe_ideal (I : ideal R) :
  (I : fractional_ideal f).map g = I :=
begin
  ext x,
  simp only [coe_coe_ideal, mem_coe_submodule],
  split,
  { rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩,
    exact ⟨y, hy, (g.commutes y).symm⟩ },
  { rintro ⟨y, hy, rfl⟩,
    exact ⟨_, ⟨y, hy, rfl⟩, g.commutes y⟩ },
end

@[simp] lemma map_one :
  (1 : fractional_ideal f).map g = 1 :=
map_coe_ideal g 1

@[simp] lemma map_zero :
  (0 : fractional_ideal f).map g = 0 :=
map_coe_ideal g 0

@[simp] lemma map_add : (I + J).map g = I.map g + J.map g :=
ext (submodule.map_sup _ _ _)

@[simp] lemma map_mul : (I * J).map g = I.map g * J.map g :=
ext (submodule.map_mul _ _ _)

@[simp] lemma map_map_symm (g : f.codomain ≃ₐ[R] f'.codomain) :
  (I.map (g : f.codomain →ₐ[R] f'.codomain)).map (g.symm : f'.codomain →ₐ[R] f.codomain) = I :=
by rw [←map_comp, g.symm_comp, map_id]

@[simp] lemma map_symm_map (I : fractional_ideal f') (g : f.codomain ≃ₐ[R] f'.codomain) :
  (I.map (g.symm : f'.codomain →ₐ[R] f.codomain)).map (g : f.codomain →ₐ[R] f'.codomain) = I :=
by rw [←map_comp, g.comp_symm, map_id]

/-- If `g` is an equivalence, `map g` is an isomorphism -/
def map_equiv (g : f.codomain ≃ₐ[R] f'.codomain) :
  fractional_ideal f ≃+* fractional_ideal f' :=
{ to_fun := map g,
  inv_fun := map g.symm,
  map_add' := λ I J, map_add I J _,
  map_mul' := λ I J, map_mul I J _,
  left_inv := λ I, by { rw [←map_comp, alg_equiv.symm_comp, map_id] },
  right_inv := λ I, by { rw [←map_comp, alg_equiv.comp_symm, map_id] } }

@[simp] lemma coe_fun_map_equiv (g : f.codomain ≃ₐ[R] f'.codomain) :
  ⇑(map_equiv g) = map g :=
rfl

@[simp] lemma map_equiv_apply (g : f.codomain ≃ₐ[R] f'.codomain) (I : fractional_ideal f) :
  map_equiv g I = map ↑g I := rfl

@[simp] lemma map_equiv_symm (g : f.codomain ≃ₐ[R] f'.codomain) :
  (map_equiv g).symm = map_equiv g.symm := rfl

@[simp] lemma map_equiv_refl :
  map_equiv alg_equiv.refl = ring_equiv.refl (fractional_ideal f) :=
ring_equiv.ext (λ x, by simp)

lemma is_fractional_span_iff {s : set f.codomain} :
is_fractional f (span R s) ↔ ∃ a ∈ S, ∀ (b : P), b ∈ s → f.is_integer (f.to_map a * b) :=
⟨ λ ⟨a, a_mem, h⟩, ⟨a, a_mem, λ b hb, h b (subset_span hb)⟩,
  λ ⟨a, a_mem, h⟩, ⟨a, a_mem, λ b hb, span_induction hb
    h
    (by { rw mul_zero, exact f.is_integer_zero })
    (λ x y hx hy, by { rw mul_add, exact is_integer_add hx hy })
    (λ s x hx, by { rw algebra.mul_smul_comm, exact is_integer_smul hx }) ⟩ ⟩

lemma is_fractional_of_fg {I : submodule R f.codomain} (hI : I.fg) :
  is_fractional f I :=
begin
  rcases hI with ⟨I, rfl⟩,
  rcases localization_map.exist_integer_multiples_of_finset f I with ⟨⟨s, hs1⟩, hs⟩,
  rw is_fractional_span_iff,
  exact ⟨s, hs1, hs⟩,
end

/-- `canonical_equiv f f'` is the canonical equivalence between the fractional
ideals in `f.codomain` and in `f'.codomain` -/
@[irreducible]
noncomputable def canonical_equiv (f : localization_map S P) (f' : localization_map S P') :
  fractional_ideal f ≃+* fractional_ideal f' :=
map_equiv
  { commutes' := λ r, ring_equiv_of_ring_equiv_eq _ _ _,
    ..ring_equiv_of_ring_equiv f f' (ring_equiv.refl R)
      (by rw [ring_equiv.to_monoid_hom_refl, submonoid.map_id]) }

@[simp] lemma mem_canonical_equiv_apply {I : fractional_ideal f} {x : f'.codomain} :
  x ∈ canonical_equiv f f' I ↔
    ∃ y ∈ I, @localization_map.map _ _ _ _ _ _ _ f (ring_hom.id _) _ (λ ⟨y, hy⟩, hy) _ _ f' y = x :=
begin
  rw [canonical_equiv, map_equiv_apply, mem_map],
  exact ⟨λ ⟨y, mem, eq⟩, ⟨y, mem, eq⟩, λ ⟨y, mem, eq⟩, ⟨y, mem, eq⟩⟩
end

@[simp] lemma canonical_equiv_symm (f : localization_map S P) (f' : localization_map S P') :
  (canonical_equiv f f').symm = canonical_equiv f' f :=
ring_equiv.ext $ λ I, fractional_ideal.ext_iff.mp $ λ x,
by { erw [mem_canonical_equiv_apply, canonical_equiv, map_equiv_symm, map_equiv, mem_map],
    exact ⟨λ ⟨y, mem, eq⟩, ⟨y, mem, eq⟩, λ ⟨y, mem, eq⟩, ⟨y, mem, eq⟩⟩ }

@[simp] lemma canonical_equiv_flip (f : localization_map S P) (f' : localization_map S P') (I) :
  canonical_equiv f f' (canonical_equiv f' f I) = I :=
by rw [←canonical_equiv_symm, ring_equiv.symm_apply_apply]

end semiring

section fraction_map

/-!
### `fraction_map` section

This section concerns fractional ideals in the field of fractions,
i.e. the type `fractional_ideal g` when `g` is a `fraction_map R K`.
-/

variables {K K' : Type*} [field K] [field K'] {g : fraction_map R K} {g' : fraction_map R K'}
variables {I J : fractional_ideal g} (h : g.codomain →ₐ[R] g'.codomain)

/-- Nonzero fractional ideals contain a nonzero integer. -/
lemma exists_ne_zero_mem_is_integer [nontrivial R] (hI : I ≠ 0) :
  ∃ x ≠ (0 : R), g.to_map x ∈ I :=
begin
  obtain ⟨y, y_mem, y_not_mem⟩ := submodule.exists_of_lt (bot_lt_iff_ne_bot.mpr hI),
  have y_ne_zero : y ≠ 0 := by simpa using y_not_mem,
  obtain ⟨z, ⟨x, hx⟩⟩ := g.exists_integer_multiple y,
  refine ⟨x, _, _⟩,
  { rw [ne.def, ← g.to_map_eq_zero_iff, hx],
    exact mul_ne_zero (g.to_map_ne_zero_of_mem_non_zero_divisors _) y_ne_zero },
  { rw hx,
    exact smul_mem _ (_ : R) y_mem }
end

lemma map_ne_zero [nontrivial R] (hI : I ≠ 0) : I.map h ≠ 0 :=
begin
  obtain ⟨x, x_ne_zero, hx⟩ := exists_ne_zero_mem_is_integer hI,
  contrapose! x_ne_zero with map_eq_zero,
  refine g'.to_map_eq_zero_iff.mp (eq_zero_iff.mp map_eq_zero _ (mem_map.mpr _)),
  exact ⟨g.to_map x, hx, h.commutes x⟩,
end

@[simp] lemma map_eq_zero_iff [nontrivial R] : I.map h = 0 ↔ I = 0 :=
⟨imp_of_not_imp_not _ _ (map_ne_zero _),
 λ hI, hI.symm ▸ map_zero h⟩

end fraction_map

section quotient

/-!
### `quotient` section

This section defines the ideal quotient of fractional ideals.

In this section we need that each non-zero `y : R` has an inverse in
the localization, i.e. that the localization is a field. We satisfy this
assumption by taking `S = non_zero_divisors R`, `R`'s localization at which
is a field because `R` is a domain.
-/

open_locale classical

variables {R₁ : Type*} [integral_domain R₁] {K : Type*} [field K] {g : fraction_map R₁ K}

instance : nontrivial (fractional_ideal g) :=
⟨⟨0, 1, λ h,
  have this : (1 : K) ∈ (0 : fractional_ideal g) :=
    by rw ←g.to_map.map_one; convert coe_mem_one _,
  one_ne_zero (mem_zero_iff.mp this) ⟩⟩

lemma fractional_div_of_nonzero {I J : fractional_ideal g} (h : J ≠ 0) :
  is_fractional g (I.1 / J.1) :=
begin
  rcases I with ⟨I, aI, haI, hI⟩,
  rcases J with ⟨J, aJ, haJ, hJ⟩,
  obtain ⟨y, mem_J, not_mem_zero⟩ := exists_of_lt (bot_lt_iff_ne_bot.mpr h),
  obtain ⟨y', hy'⟩ := hJ y mem_J,
  use (aI * y'),
  split,
  { apply (non_zero_divisors R₁).mul_mem haI (mem_non_zero_divisors_iff_ne_zero.mpr _),
    intro y'_eq_zero,
    have : g.to_map aJ * y = 0 := by rw [←hy', y'_eq_zero, g.to_map.map_zero],
    obtain aJ_zero | y_zero := mul_eq_zero.mp this,
    { have : aJ = 0 := g.to_map.injective_iff.1 g.injective _ aJ_zero,
      have : aJ ≠ 0 := mem_non_zero_divisors_iff_ne_zero.mp haJ,
      contradiction },
    { exact not_mem_zero (mem_zero_iff.mpr y_zero) } },
  intros b hb,
  rw [g.to_map.map_mul, mul_assoc, mul_comm _ b, hy'],
  exact hI _ (hb _ (submodule.smul_mem _ aJ mem_J)),
end

noncomputable instance fractional_ideal_has_div :
  has_div (fractional_ideal g) :=
⟨ λ I J, if h : J = 0 then 0 else ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ ⟩

variables {I J : fractional_ideal g} [ J ≠ 0 ]

@[simp] lemma div_zero {I : fractional_ideal g} :
  I / 0 = 0 :=
dif_pos rfl

lemma div_nonzero {I J : fractional_ideal g} (h : J ≠ 0) :
  (I / J) = ⟨I.1 / J.1, fractional_div_of_nonzero h⟩ :=
dif_neg h

@[simp] lemma coe_div {I J : fractional_ideal g} (hJ : J ≠ 0) :
  (↑(I / J) : submodule R₁ g.codomain) = ↑I / (↑J : submodule R₁ g.codomain) :=
begin
  unfold has_div.div,
  simp only [dif_neg hJ, coe_mk, val_eq_coe],
end

lemma mem_div_iff_of_nonzero {I J : fractional_ideal g} (h : J ≠ 0) {x} :
  x ∈ I / J ↔ ∀ y ∈ J, x * y ∈ I :=
by { rw div_nonzero h, exact submodule.mem_div_iff_forall_mul_mem }

lemma mul_one_div_le_one {I : fractional_ideal g} : I * (1 / I) ≤ 1 :=
begin
  by_cases hI : I = 0,
  { rw [hI, div_zero, mul_zero],
    exact zero_le 1 },
  { rw [← coe_le_coe, coe_mul, coe_div hI, coe_one],
    apply submodule.mul_one_div_le_one },
end

lemma le_self_mul_one_div {I : fractional_ideal g} (hI : I ≤ (1 : fractional_ideal g)) :
  I ≤ I * (1 / I) :=
begin
  by_cases hI_nz : I = 0,
  { rw [hI_nz, div_zero, mul_zero], exact zero_le 0 },
  { rw [← coe_le_coe, coe_mul, coe_div hI_nz, coe_one],
    rw [← coe_le_coe, coe_one] at hI,
    exact submodule.le_self_mul_one_div hI },
end

lemma le_div_iff_of_nonzero {I J J' : fractional_ideal g} (hJ' : J' ≠ 0) :
  I ≤ J / J' ↔ ∀ (x ∈ I) (y ∈ J'), x * y ∈ J :=
⟨ λ h x hx, (mem_div_iff_of_nonzero hJ').mp (h hx),
  λ h x hx, (mem_div_iff_of_nonzero hJ').mpr (h x hx) ⟩

lemma le_div_iff_mul_le {I J J' : fractional_ideal g} (hJ' : J' ≠ 0) : I ≤ J / J' ↔ I * J' ≤ J :=
begin
  rw div_nonzero hJ',
  convert submodule.le_div_iff_mul_le using 1,
  rw [val_eq_coe, val_eq_coe, ←coe_mul],
  refl,
end

@[simp] lemma div_one {I : fractional_ideal g} : I / 1 = I :=
begin
  rw [div_nonzero (@one_ne_zero (fractional_ideal g) _ _)],
  ext,
  split; intro h,
  { convert mem_div_iff_forall_mul_mem.mp h 1
      (g.to_map.map_one ▸ coe_mem_one 1), simp },
  { apply mem_div_iff_forall_mul_mem.mpr,
    rintros y ⟨y', _, y_eq_y'⟩,
    rw mul_comm,
    convert submodule.smul_mem _ y' h,
    rw ←y_eq_y',
    refl }
end

lemma ne_zero_of_mul_eq_one (I J : fractional_ideal g) (h : I * J = 1) : I ≠ 0 :=
λ hI, @zero_ne_one (fractional_ideal g) _ _ (by { convert h, simp [hI], })


theorem eq_one_div_of_mul_eq_one (I J : fractional_ideal g) (h : I * J = 1) :
  J = 1 / I :=
begin
  have hI : I ≠ 0 := ne_zero_of_mul_eq_one I J h,
  suffices h' : I * (1 / I) = 1,
  { exact (congr_arg units.inv $
      @units.ext _ _ (units.mk_of_mul_eq_one _ _ h) (units.mk_of_mul_eq_one _ _ h') rfl) },
  apply le_antisymm,
  { apply mul_le.mpr _,
    intros x hx y hy,
    rw mul_comm,
    exact (mem_div_iff_of_nonzero hI).mp hy x hx },
  rw ← h,
  apply mul_left_mono I,
  apply (le_div_iff_of_nonzero hI).mpr _,
  intros y hy x hx,
  rw mul_comm,
  exact mul_mem_mul hx hy,
end

theorem mul_div_self_cancel_iff {I : fractional_ideal g} :
  I * (1 / I) = 1 ↔ ∃ J, I * J = 1 :=
⟨λ h, ⟨(1 / I), h⟩, λ ⟨J, hJ⟩, by rwa [← eq_one_div_of_mul_eq_one I J hJ]⟩

variables {K' : Type*} [field K'] {g' : fraction_map R₁ K'}

@[simp] lemma map_div (I J : fractional_ideal g) (h : g.codomain ≃ₐ[R₁] g'.codomain) :
  (I / J).map (h : g.codomain →ₐ[R₁] g'.codomain) = I.map h / J.map h :=
begin
  by_cases H : J = 0,
  { rw [H, div_zero, map_zero, div_zero] },
  { ext x,
    simp [div_nonzero H, div_nonzero (map_ne_zero _ H), submodule.map_div] }
end

@[simp] lemma map_one_div (I : fractional_ideal g) (h : g.codomain ≃ₐ[R₁] g'.codomain) :
  (1 / I).map (h : g.codomain →ₐ[R₁] g'.codomain) = 1 / I.map h :=
by rw [map_div, map_one]

end quotient

section principal_ideal_ring

variables {R₁ : Type*} [integral_domain R₁] {K : Type*} [field K] {g : fraction_map R₁ K}

open_locale classical

open submodule submodule.is_principal

lemma is_fractional_span_singleton (x : f.codomain) : is_fractional f (span R {x}) :=
let ⟨a, ha⟩ := f.exists_integer_multiple x in
is_fractional_span_iff.mpr ⟨ a.1, a.2, λ x hx, (mem_singleton_iff.mp hx).symm ▸ ha⟩

/-- `span_singleton x` is the fractional ideal generated by `x` if `0 ∉ S` -/
@[irreducible]
def span_singleton (x : f.codomain) : fractional_ideal f :=
⟨span R {x}, is_fractional_span_singleton x⟩

local attribute [semireducible] span_singleton

@[simp] lemma coe_span_singleton (x : f.codomain) :
  (span_singleton x : submodule R f.codomain) = span R {x} := rfl

@[simp] lemma mem_span_singleton {x y : f.codomain} :
  x ∈ span_singleton y ↔ ∃ (z : R), z • y = x :=
submodule.mem_span_singleton

lemma mem_span_singleton_self (x : f.codomain) :
  x ∈ span_singleton x :=
mem_span_singleton.mpr ⟨1, one_smul _ _⟩

lemma eq_span_singleton_of_principal (I : fractional_ideal f)
  [is_principal (I : submodule R f.codomain)] :
  I = span_singleton (generator (I : submodule R f.codomain)) :=
ext (span_singleton_generator I.1).symm

lemma is_principal_iff (I : fractional_ideal f) :
  is_principal (I : submodule R f.codomain) ↔ ∃ x, I = span_singleton x :=
⟨λ h, ⟨@generator _ _ _ _ _ I.1 h, @eq_span_singleton_of_principal _ _ _ _ _ _ I h⟩,
 λ ⟨x, hx⟩, { principal := ⟨x, trans (congr_arg _ hx) (coe_span_singleton x)⟩ } ⟩

@[simp] lemma span_singleton_zero : span_singleton (0 : f.codomain) = 0 :=
by { ext, simp [submodule.mem_span_singleton, eq_comm] }

lemma span_singleton_eq_zero_iff {y : f.codomain} : span_singleton y = 0 ↔ y = 0 :=
⟨λ h, span_eq_bot.mp (by simpa using congr_arg subtype.val h : span R {y} = ⊥) y (mem_singleton y),
 λ h, by simp [h] ⟩

lemma span_singleton_ne_zero_iff {y : f.codomain} : span_singleton y ≠ 0 ↔ y ≠ 0 :=
not_congr span_singleton_eq_zero_iff

@[simp] lemma span_singleton_one : span_singleton (1 : f.codomain) = 1 :=
begin
  ext,
  refine mem_span_singleton.trans ((exists_congr _).trans mem_one_iff.symm),
  intro x',
  refine eq.congr (mul_one _) rfl,
end

@[simp]
lemma span_singleton_mul_span_singleton (x y : f.codomain) :
  span_singleton x * span_singleton y = span_singleton (x * y) :=
begin
  ext,
  simp_rw [coe_mul, coe_span_singleton, span_mul_span, singleton.is_mul_hom.map_mul]
end

@[simp]
lemma coe_ideal_span_singleton (x : R) :
  (↑(span R {x} : ideal R) : fractional_ideal f) = span_singleton (f.to_map x) :=
begin
  ext y,
  refine mem_coe_ideal.trans (iff.trans _ mem_span_singleton.symm),
  split,
  { rintros ⟨y', hy', rfl⟩,
    obtain ⟨x', rfl⟩ := submodule.mem_span_singleton.mp hy',
    use x',
    rw [smul_eq_mul, f.to_map.map_mul],
    refl },
  { rintros ⟨y', rfl⟩,
    exact ⟨y' * x, submodule.mem_span_singleton.mpr ⟨y', rfl⟩, f.to_map.map_mul _ _⟩ }
end

@[simp]
lemma canonical_equiv_span_singleton (f : localization_map S P) {P'} [comm_ring P']
  (f' : localization_map S P') (x : f.codomain) :
  canonical_equiv f f' (span_singleton x) =
    span_singleton (f.map (show ∀ (y : S), ring_hom.id _ y.1 ∈ S, from λ y, y.2) f' x) :=
begin
  apply ext_iff.mp,
  intro y,
  split; intro h,
  { apply mem_span_singleton.mpr,
    obtain ⟨x', hx', rfl⟩ := mem_canonical_equiv_apply.mp h,
    obtain ⟨z, rfl⟩ := mem_span_singleton.mp hx',
    use z,
    rw localization_map.map_smul,
    refl },
  { apply mem_canonical_equiv_apply.mpr,
    obtain ⟨z, rfl⟩ := mem_span_singleton.mp h,
    use f.to_map z * x,
    use mem_span_singleton.mpr ⟨z, rfl⟩,
    rw [ring_hom.map_mul, localization_map.map_eq],
    refl }
end

lemma mem_singleton_mul {x y : f.codomain} {I : fractional_ideal f} :
  y ∈ span_singleton x * I ↔ ∃ y' ∈ I, y = x * y' :=
begin
  split,
  { intro h,
    apply fractional_ideal.mul_induction_on h,
    { intros x' hx' y' hy',
      obtain ⟨a, ha⟩ := mem_span_singleton.mp hx',
      use [a • y', I.1.smul_mem a hy'],
      rw [←ha, algebra.mul_smul_comm, algebra.smul_mul_assoc] },
    { exact ⟨0, I.1.zero_mem, (mul_zero x).symm⟩ },
    { rintros _ _ ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩,
      exact ⟨y + y', I.1.add_mem hy hy', (mul_add _ _ _).symm⟩ },
    { rintros r _ ⟨y', hy', rfl⟩,
      exact ⟨r • y', I.1.smul_mem r hy', (algebra.mul_smul_comm _ _ _).symm ⟩ } },
  { rintros ⟨y', hy', rfl⟩,
    exact mul_mem_mul (mem_span_singleton.mpr ⟨1, one_smul _ _⟩) hy' }
end

lemma one_div_span_singleton (x : g.codomain) :
  1 / span_singleton x = span_singleton (x⁻¹) :=
if h : x = 0 then by simp [h] else (eq_one_div_of_mul_eq_one _ _ (by simp [h])).symm

@[simp] lemma div_span_singleton (J : fractional_ideal g) (d : g.codomain) :
  J / span_singleton d = span_singleton (d⁻¹) * J :=
begin
  rw ← one_div_span_singleton,
  by_cases hd : d = 0,
  { simp only [hd, span_singleton_zero, div_zero, zero_mul] },
  have h_spand : span_singleton d ≠ 0 := mt span_singleton_eq_zero_iff.mp hd,
  apply le_antisymm,
  { intros x hx,
    rw [val_eq_coe, coe_div h_spand, submodule.mem_div_iff_forall_mul_mem] at hx,
    specialize hx d (mem_span_singleton_self d),
    have h_xd : x = d⁻¹ * (x * d), { field_simp },
    rw [val_eq_coe, coe_mul, one_div_span_singleton, h_xd],
    exact submodule.mul_mem_mul (mem_span_singleton_self _) hx },
  { rw [le_div_iff_mul_le h_spand, mul_assoc, mul_left_comm, one_div_span_singleton,
    span_singleton_mul_span_singleton, inv_mul_cancel hd, span_singleton_one, mul_one],
    exact le_refl J },
end

lemma exists_eq_span_singleton_mul (I : fractional_ideal g) :
  ∃ (a : R₁) (aI : ideal R₁), a ≠ 0 ∧ I = span_singleton (g.to_map a)⁻¹ * aI :=
begin
  obtain ⟨a_inv, nonzero, ha⟩ := I.2,
  have nonzero := mem_non_zero_divisors_iff_ne_zero.mp nonzero,
  have map_a_nonzero := mt g.to_map_eq_zero_iff.mp nonzero,
  use a_inv,
  use (span_singleton (g.to_map a_inv) * I).1.comap g.lin_coe,
  split, exact nonzero,
  ext,
  refine iff.trans _ mem_singleton_mul.symm,
  split,
  { intro hx,
    obtain ⟨x', hx'⟩ := ha x hx,
    refine ⟨g.to_map x', mem_coe_ideal.mpr ⟨x', (mem_singleton_mul.mpr ⟨x, hx, hx'⟩), rfl⟩, _⟩,
    erw [hx', ←mul_assoc, inv_mul_cancel map_a_nonzero, one_mul] },
  { rintros ⟨y, hy, rfl⟩,
    obtain ⟨x', hx', rfl⟩ := mem_coe_ideal.mp hy,
    obtain ⟨y', hy', hx'⟩ := mem_singleton_mul.mp hx',
    rw lin_coe_apply at hx',
    erw [hx', ←mul_assoc, inv_mul_cancel map_a_nonzero, one_mul],
    exact hy' }
end

instance is_principal {R} [integral_domain R] [is_principal_ideal_ring R] {f : fraction_map R K}
  (I : fractional_ideal f) : (I : submodule R f.codomain).is_principal :=
begin
  obtain ⟨a, aI, -, ha⟩ := exists_eq_span_singleton_mul I,
  use (f.to_map a)⁻¹ * f.to_map (generator aI),
  suffices : I = span_singleton ((f.to_map a)⁻¹ * f.to_map (generator aI)),
  { exact congr_arg subtype.val this },
  conv_lhs { rw [ha, ←span_singleton_generator aI] },
  rw [coe_ideal_span_singleton (generator aI), span_singleton_mul_span_singleton]
end

end principal_ideal_ring

variables {R₁ : Type*} [integral_domain R₁]
variables {K : Type*} [field K] {g : fraction_map R₁ K}

local attribute [instance] classical.prop_decidable

lemma is_noetherian_zero : is_noetherian R₁ (0 : fractional_ideal g) :=
is_noetherian_submodule.mpr (λ I (hI : I ≤ (0 : fractional_ideal g)),
  by { rw coe_zero at hI, rw le_bot_iff.mp hI, exact fg_bot })

lemma is_noetherian_iff {I : fractional_ideal g} :
  is_noetherian R₁ I ↔ ∀ J ≤ I, (J : submodule R₁ g.codomain).fg :=
is_noetherian_submodule.trans ⟨λ h J hJ, h _ hJ, λ h J hJ, h ⟨J, is_fractional_of_le hJ⟩ hJ⟩

lemma is_noetherian_coe_to_fractional_ideal [is_noetherian_ring R₁] (I : ideal R₁) :
  is_noetherian R₁ (I : fractional_ideal g) :=
begin
  rw is_noetherian_iff,
  intros J hJ,
  obtain ⟨J, rfl⟩ := le_one_iff_exists_coe_ideal.mp (le_trans hJ coe_ideal_le_one),
  exact fg_map (is_noetherian.noetherian J),
end

lemma is_noetherian_span_singleton_inv_to_map_mul (x : R₁) {I : fractional_ideal g}
  (hI : is_noetherian R₁ I) :
  is_noetherian R₁ (span_singleton (g.to_map x)⁻¹ * I : fractional_ideal g) :=
begin
  by_cases hx : x = 0,
  { rw [hx, g.to_map.map_zero, _root_.inv_zero, span_singleton_zero, zero_mul],
    exact is_noetherian_zero },
  have h_gx : g.to_map x ≠ 0,
    from mt (g.to_map.injective_iff.mp (fraction_map.injective g) x) hx,
  have h_spanx : span_singleton (g.to_map x) ≠ (0 : fractional_ideal g),
    from span_singleton_ne_zero_iff.mpr h_gx,

  rw is_noetherian_iff at ⊢ hI,
  intros J hJ,
  rw [← div_span_singleton, le_div_iff_mul_le h_spanx] at hJ,
  obtain ⟨s, hs⟩ := hI _ hJ,
  use s * {(g.to_map x)⁻¹},
  rw [finset.coe_mul, finset.coe_singleton, ← span_mul_span, hs, ← coe_span_singleton, ← coe_mul,
      mul_assoc, span_singleton_mul_span_singleton, mul_inv_cancel h_gx,
      span_singleton_one, mul_one],
end

/-- Every fractional ideal of a noetherian integral domain is noetherian. -/
theorem is_noetherian [is_noetherian_ring R₁] (I : fractional_ideal g) : is_noetherian R₁ I :=
begin
  obtain ⟨d, J, h_nzd, rfl⟩ := exists_eq_span_singleton_mul I,
  apply is_noetherian_span_singleton_inv_to_map_mul,
  apply is_noetherian_coe_to_fractional_ideal,
end

end fractional_ideal

end ring
