/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.regular_mono

/-!
# Kernel pairs

This file defines what it means for a parallel pair of morphisms `a b : R ⟶ X` to be the kernel pair
for a morphism `f`.
Some properties of kernel pairs are given, namely allowing one to transfer between
the kernel pair of `f₁ ≫ f₂` to the kernel pair of `f₁`.
It is also proved that if `f` is a coequalizer of some pair, and `a`,`b` is a kernel pair for `f` then
it is a coequalizer of `a`,`b`.

## Implementation

The definition is essentially just a wrapper for `is_limit (pullback_cone.mk _ _ _)`, but the
constructions given here are useful, yet awkward to present in that language, so a basic API
is developed here.

## TODO

- Internal equivalence relations (or congruences) and the fact that every kernel pair induces one,
  and the converse in an effective regular category (WIP by b-mehta).

-/

universes v u u₂

namespace category_theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u} [category.{v} C]

variables {R X Y Z : C} (f : X ⟶ Y) (a b : R ⟶ X)

/--
`is_kernel_pair f a b` expresses that `(a, b)` is a kernel pair for `f`, i.e. `a ≫ f = b ≫ f`
and the square
  R → X
  ↓   ↓
  X → Y
is a pullback square.
This is essentially just a convenience wrapper over `is_limit (pullback_cone.mk _ _ _)`.
-/
structure is_kernel_pair :=
(comm : a ≫ f = b ≫ f)
(is_limit : is_limit (pullback_cone.mk _ _ comm))

attribute [reassoc] is_kernel_pair.comm

namespace is_kernel_pair

/-- The data expressing that `(a, b)` is a kernel pair is subsingleton. -/
instance : subsingleton (is_kernel_pair f a b) :=
⟨λ P Q, by { cases P, cases Q, congr, }⟩

/-- If `f` is a monomorphism, then `(𝟙 _, 𝟙 _)`  is a kernel pair for `f`. -/
def id_of_mono [mono f] : is_kernel_pair f (𝟙 _) (𝟙 _) :=
{ comm := rfl,
  is_limit :=
  pullback_cone.is_limit_aux' _ $ λ s,
  begin
    refine ⟨s.snd, _, comp_id _, λ m m₁ m₂, _⟩,
    { rw [← cancel_mono f, s.condition, pullback_cone.mk_fst, cancel_mono f],
      apply comp_id },
    rw [← m₂],
    apply (comp_id _).symm,
  end }

instance [mono f] : inhabited (is_kernel_pair f (𝟙 _) (𝟙 _)) := ⟨id_of_mono f⟩

variables {f a b}

/--
Given a pair of morphisms `p`, `q` to `X` which factor through `f`, they factor through any kernel
pair of `f`.
-/
def lift' {S : C} (k : is_kernel_pair f a b) (p q : S ⟶ X) (w : p ≫ f = q ≫ f) :
  { t : S ⟶ R // t ≫ a = p ∧ t ≫ b = q } :=
pullback_cone.is_limit.lift' k.is_limit _ _ w

/--
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `a ≫ f₁ = b ≫ f₁`, then `(a,b)` is a kernel pair for
just `f₁`.
That is, to show that `(a,b)` is a kernel pair for `f₁` it suffices to only show the square
commutes, rather than to additionally show it's a pullback.
-/
def cancel_right {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} (comm : a ≫ f₁ = b ≫ f₁) (big_k : is_kernel_pair (f₁ ≫ f₂) a b) :
  is_kernel_pair f₁ a b :=
{ comm := comm,
  is_limit := pullback_cone.is_limit_aux' _ $ λ s,
  begin
    let s' : pullback_cone (f₁ ≫ f₂) (f₁ ≫ f₂) := pullback_cone.mk s.fst s.snd (s.condition_assoc _),
    refine ⟨big_k.is_limit.lift s',
            big_k.is_limit.fac _ walking_cospan.left,
            big_k.is_limit.fac _ walking_cospan.right,
            λ m m₁ m₂, _⟩,
    apply big_k.is_limit.hom_ext,
    refine ((pullback_cone.mk a b _) : pullback_cone (f₁ ≫ f₂) _).equalizer_ext _ _,
    apply m₁.trans (big_k.is_limit.fac s' walking_cospan.left).symm,
    apply m₂.trans (big_k.is_limit.fac s' walking_cospan.right).symm,
  end }

/--
If `(a,b)` is a kernel pair for `f₁ ≫ f₂` and `f₂` is mono, then `(a,b)` is a kernel pair for
just `f₁`.
The converse of `comp_of_mono`.
-/
def cancel_right_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [mono f₂] (big_k : is_kernel_pair (f₁ ≫ f₂) a b) :
  is_kernel_pair f₁ a b :=
cancel_right (begin rw [← cancel_mono f₂, assoc, assoc, big_k.comm] end) big_k

/--
If `(a,b)` is a kernel pair for `f₁` and `f₂` is mono, then `(a,b)` is a kernel pair for `f₁ ≫ f₂`.
The converse of `cancel_right_of_mono`.
-/
def comp_of_mono {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} [mono f₂] (small_k : is_kernel_pair f₁ a b) :
  is_kernel_pair (f₁ ≫ f₂) a b :=
{ comm := by rw [small_k.comm_assoc],
  is_limit := pullback_cone.is_limit_aux' _ $ λ s,
  begin
    refine ⟨_, _, _, _⟩,
    apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).1,
    rw [← cancel_mono f₂, assoc, s.condition, assoc],
    apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.1,
    apply (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.2,
    intros m m₁ m₂,
    apply small_k.is_limit.hom_ext,
    refine ((pullback_cone.mk a b _) : pullback_cone f₁ _).equalizer_ext _ _,
    rwa (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.1,
    rwa (pullback_cone.is_limit.lift' small_k.is_limit s.fst s.snd _).2.2,
  end }

/--
If `(a,b)` is the kernel pair of `f`, and `f` is a coequalizer morphism for some parallel pair, then
`f` is a coequalizer morphism of `a` and `b`.
-/
def to_coequalizer (k : is_kernel_pair f a b) [r : regular_epi f] :
  is_colimit (cofork.of_π f k.comm) :=
begin
  let t := k.is_limit.lift (pullback_cone.mk _ _ r.w),
  have ht : t ≫ a = r.left := k.is_limit.fac _ walking_cospan.left,
  have kt : t ≫ b = r.right := k.is_limit.fac _ walking_cospan.right,
  apply cofork.is_colimit.mk _ _ _ _,
  { intro s,
    apply (cofork.is_colimit.desc' r.is_colimit s.π _).1,
    rw [← ht, assoc, s.condition, reassoc_of kt] },
  { intro s,
    apply (cofork.is_colimit.desc' r.is_colimit s.π _).2 },
  { intros s m w,
    apply r.is_colimit.hom_ext,
    rintro ⟨⟩,
    change (r.left ≫ f) ≫ m = (r.left ≫ f) ≫ _,
    rw [assoc, assoc],
    congr' 1,
    erw (cofork.is_colimit.desc' r.is_colimit s.π _).2,
    apply w walking_parallel_pair.one,
    erw (cofork.is_colimit.desc' r.is_colimit s.π _).2,
    apply w walking_parallel_pair.one }
end

end is_kernel_pair
end category_theory
