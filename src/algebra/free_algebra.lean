/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import algebra.algebra.subalgebra
import algebra.monoid_algebra
import linear_algebra
import data.equiv.transfer_instance

/-!
# Free Algebras

Given a commutative semiring `R`, and a type `X`, we construct the free unital, associative
`R`-algebra on `X`.

## Notation

1. `free_algebra R X` is the free algebra itself. It is endowed with an `R`-algebra structure.
2. `free_algebra.ι R` is the function `X → free_algebra R X`.
3. Given a function `f : X → A` to an R-algebra `A`, `lift R f` is the lift of `f` to an
  `R`-algebra morphism `free_algebra R X → A`.

## Theorems

1. `ι_comp_lift` states that the composition `(lift R f) ∘ (ι R)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism `g : free_algebra R X → A` is
  given whose composition with `ι R` is `f`, then one has `g = lift R f`.
3. `hom_ext` is a variant of `lift_unique` in the form of an extensionality theorem.
4. `lift_comp_ι` is a combination of `ι_comp_lift` and `lift_unique`. It states that the lift
  of the composition of an algebra morphism with `ι` is the algebra morphism itself.
5. `equiv_monoid_algebra_free_monoid : free_algebra R X ≃ₐ[R] monoid_algebra R (free_monoid X)`
6. An inductive principle `induction`.
7. Statements about the natural grading of the free algebra `grades x i`: `grades.map_algebra_map`,
  `grades.map_algebra_ι`, and `grades.map_grades`.

## Implementation details

We construct the free algebra on `X` as a quotient of an inductive type `free_algebra.pre` by an
inductively defined relation `free_algebra.rel`. Explicitly, the construction involves three steps:
1. We construct an inductive type `free_algebra.pre R X`, the terms of which should be thought
  of as representatives for the elements of `free_algebra R X`.
  It is the free type with maps from `R` and `X`, and with two binary operations `add` and `mul`.
2. We construct an inductive relation `free_algebra.rel R X` on `free_algebra.pre R X`.
  This is the smallest relation for which the quotient is an `R`-algebra where addition resp.
  multiplication are induced by `add` resp. `mul` from 1., and for which the map from `R` is the
  structure map for the algebra.
3. The free algebra `free_algebra R X` is the quotient of `free_algebra.pre R X` by
  the relation `free_algebra.rel R X`.
-/

variables (R : Type*) [comm_semiring R]
variables (X : Type*)

namespace free_algebra

/--
This inductive type is used to express representatives of the free algebra.
-/
inductive pre
| of : X → pre
| of_scalar : R → pre
| add : pre → pre → pre
| mul : pre → pre → pre

namespace pre

instance : inhabited (pre R X) := ⟨of_scalar 0⟩

-- Note: These instances are only used to simplify the notation.
/-- Coercion from `X` to `pre R X`. Note: Used for notation only. -/
def has_coe_generator : has_coe X (pre R X) := ⟨of⟩
/-- Coercion from `R` to `pre R X`. Note: Used for notation only. -/
def has_coe_semiring : has_coe R (pre R X) := ⟨of_scalar⟩
/-- Multiplication in `pre R X` defined as `pre.mul`. Note: Used for notation only. -/
def has_mul : has_mul (pre R X) := ⟨mul⟩
/-- Addition in `pre R X` defined as `pre.add`. Note: Used for notation only. -/
def has_add : has_add (pre R X) := ⟨add⟩
/-- Zero in `pre R X` defined as the image of `0` from `R`. Note: Used for notation only. -/
def has_zero : has_zero (pre R X) := ⟨of_scalar 0⟩
/-- One in `pre R X` defined as the image of `1` from `R`. Note: Used for notation only. -/
def has_one : has_one (pre R X) := ⟨of_scalar 1⟩
/--
Scalar multiplication defined as multiplication by the image of elements from `R`.
Note: Used for notation only.
-/
def has_scalar : has_scalar R (pre R X) := ⟨λ r m, mul (of_scalar r) m⟩

end pre

local attribute [instance]
  pre.has_coe_generator pre.has_coe_semiring pre.has_mul pre.has_add pre.has_zero
  pre.has_one pre.has_scalar

/--
Given a function from `X` to an `R`-algebra `A`, `lift_fun` provides a lift of `f` to a function
from `pre R X` to `A`. This is mainly used in the construction of `free_algebra.lift`.
-/
def lift_fun {A : Type*} [semiring A] [algebra R A] (f : X → A) : pre R X → A :=
  λ t, pre.rec_on t f (algebra_map _ _) (λ _ _, (+)) (λ _ _, (*))

/--
An inductively defined relation on `pre R X` used to force the initial algebra structure on
the associated quotient.
-/
inductive rel : (pre R X) → (pre R X) → Prop
-- force `of_scalar` to be a central semiring morphism
| add_scalar {r s : R} : rel ↑(r + s) (↑r + ↑s)
| mul_scalar {r s : R} : rel ↑(r * s) (↑r * ↑s)
| central_scalar {r : R} {a : pre R X} : rel (r * a) (a * r)
-- commutative additive semigroup
| add_assoc {a b c : pre R X} : rel (a + b + c) (a + (b + c))
| add_comm {a b : pre R X} : rel (a + b) (b + a)
| zero_add {a : pre R X} : rel (0 + a) a
-- multiplicative monoid
| mul_assoc {a b c : pre R X} : rel (a * b * c) (a * (b * c))
| one_mul {a : pre R X} : rel (1 * a) a
| mul_one {a : pre R X} : rel (a * 1) a
-- distributivity
| left_distrib {a b c : pre R X} : rel (a * (b + c)) (a * b + a * c)
| right_distrib {a b c : pre R X} : rel ((a + b) * c) (a * c + b * c)
-- other relations needed for semiring
| zero_mul {a : pre R X} : rel (0 * a) 0
| mul_zero {a : pre R X} : rel (a * 0) 0
-- compatibility
| add_compat_left {a b c : pre R X} : rel a b → rel (a + c) (b + c)
| add_compat_right {a b c : pre R X} : rel a b → rel (c + a) (c + b)
| mul_compat_left {a b c : pre R X} : rel a b → rel (a * c) (b * c)
| mul_compat_right {a b c : pre R X} : rel a b → rel (c * a) (c * b)

end free_algebra

/--
The free algebra for the type `X` over the commutative semiring `R`.
-/
def free_algebra := quot (free_algebra.rel R X)

namespace free_algebra

local attribute [instance]
  pre.has_coe_generator pre.has_coe_semiring pre.has_mul pre.has_add pre.has_zero
  pre.has_one pre.has_scalar

instance : semiring (free_algebra R X) :=
{ add := quot.map₂ (+) (λ _ _ _, rel.add_compat_right) (λ _ _ _, rel.add_compat_left),
  add_assoc := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, exact quot.sound rel.add_assoc },
  zero := quot.mk _ 0,
  zero_add := by { rintro ⟨⟩, exact quot.sound rel.zero_add },
  add_zero := begin
    rintros ⟨⟩,
    change quot.mk _ _ = _,
    rw [quot.sound rel.add_comm, quot.sound rel.zero_add],
  end,
  add_comm := by { rintros ⟨⟩ ⟨⟩, exact quot.sound rel.add_comm },
  mul := quot.map₂ (*) (λ _ _ _, rel.mul_compat_right) (λ _ _ _, rel.mul_compat_left),
  mul_assoc := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, exact quot.sound rel.mul_assoc },
  one := quot.mk _ 1,
  one_mul := by { rintros ⟨⟩, exact quot.sound rel.one_mul },
  mul_one := by { rintros ⟨⟩, exact quot.sound rel.mul_one },
  left_distrib := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, exact quot.sound rel.left_distrib },
  right_distrib := by { rintros ⟨⟩ ⟨⟩ ⟨⟩, exact quot.sound rel.right_distrib },
  zero_mul := by { rintros ⟨⟩, exact quot.sound rel.zero_mul },
  mul_zero := by { rintros ⟨⟩, exact quot.sound rel.mul_zero } }

instance : inhabited (free_algebra R X) := ⟨0⟩

instance : has_scalar R (free_algebra R X) :=
{ smul := λ r a, quot.lift_on a (λ x, quot.mk _ $ ↑r * x) $
  λ a b h, quot.sound (rel.mul_compat_right h) }

instance : algebra R (free_algebra R X) :=
{ to_fun := λ r, quot.mk _ r,
  map_one' := rfl,
  map_mul' := λ _ _, quot.sound rel.mul_scalar,
  map_zero' := rfl,
  map_add' := λ _ _, quot.sound rel.add_scalar,
  commutes' := λ _, by { rintros ⟨⟩, exact quot.sound rel.central_scalar },
  smul_def' := λ _ _, rfl }

instance {S : Type*} [comm_ring S] : ring (free_algebra S X) := algebra.semiring_to_ring S

variables {X}

/--
The canonical function `X → free_algebra R X`.
-/
def ι : X → free_algebra R X := λ m, quot.mk _ m

@[simp] lemma quot_mk_eq_ι (m : X) : quot.mk (free_algebra.rel R X) m = ι R m := rfl

variables {A : Type*} [semiring A] [algebra R A]

/-- Internal definition used to define `lift` -/
private def lift_aux (f : X → A) : (free_algebra R X →ₐ[R] A) :=
{ to_fun := λ a, quot.lift_on a (lift_fun _ _ f) $ λ a b h,
  begin
    induction h,
    { exact (algebra_map R A).map_add h_r h_s, },
    { exact (algebra_map R A).map_mul h_r h_s },
    { apply algebra.commutes },
    { change _ + _ + _ = _ + (_ + _),
      rw add_assoc },
    { change _ + _ = _ + _,
      rw add_comm, },
    { change (algebra_map _ _ _) + lift_fun R X f _ = lift_fun R X f _,
      simp, },
    { change _ * _ * _ = _ * (_ * _),
      rw mul_assoc },
    { change (algebra_map _ _ _) * lift_fun R X f _ = lift_fun R X f _,
      simp, },
    { change lift_fun R X f _ * (algebra_map _ _ _) = lift_fun R X f _,
      simp, },
    { change _ * (_ + _) = _ * _ + _ * _,
      rw left_distrib, },
    { change (_ + _) * _ = _ * _ + _ * _,
      rw right_distrib, },
    { change (algebra_map _ _ _) * _ = algebra_map _ _ _,
      simp },
    { change _ * (algebra_map _ _ _) = algebra_map _ _ _,
      simp },
    repeat { change lift_fun R X f _ + lift_fun R X f _ = _,
      rw h_ih,
      refl, },
    repeat { change lift_fun R X f _ * lift_fun R X f _ = _,
      rw h_ih,
      refl, },
  end,
  map_one' := by { change algebra_map _ _ _ = _, simp },
  map_mul' := by { rintros ⟨⟩ ⟨⟩, refl },
  map_zero' := by { change algebra_map _ _ _ = _, simp },
  map_add' := by { rintros ⟨⟩ ⟨⟩, refl },
  commutes' := by tauto }

/--
Given a function `f : X → A` where `A` is an `R`-algebra, `lift R f` is the unique lift
of `f` to a morphism of `R`-algebras `free_algebra R X → A`.
-/
def lift : (X → A) ≃ (free_algebra R X →ₐ[R] A) :=
{ to_fun := lift_aux R,
  inv_fun := λ F, F ∘ (ι R),
  left_inv := λ f, by {ext, refl},
  right_inv := λ F, by {
    ext x,
    rcases x,
    induction x,
    case pre.of : {
      change ((F : free_algebra R X → A) ∘ (ι R)) _ = _,
      refl },
    case pre.of_scalar : {
      change algebra_map _ _ x = F (algebra_map _ _ x),
      rw alg_hom.commutes F x, },
    case pre.add : a b ha hb {
      change lift_aux R (F ∘ ι R) (quot.mk _ _ + quot.mk _ _) = F (quot.mk _ _ + quot.mk _ _),
      rw [alg_hom.map_add, alg_hom.map_add, ha, hb], },
    case pre.mul : a b ha hb {
      change lift_aux R (F ∘ ι R) (quot.mk _ _ * quot.mk _ _) = F (quot.mk _ _ * quot.mk _ _),
      rw [alg_hom.map_mul, alg_hom.map_mul, ha, hb], }, }, }

@[simp] lemma lift_aux_eq (f : X → A) : lift_aux R f = lift R f := rfl

@[simp]
lemma lift_symm_apply (F : free_algebra R X →ₐ[R] A) : (lift R).symm F = F ∘ (ι R) := rfl

variables {R X}

@[simp]
theorem ι_comp_lift (f : X → A) :
  (lift R f : free_algebra R X → A) ∘ (ι R) = f := by {ext, refl}

@[simp]
theorem lift_ι_apply (f : X → A) (x) :
  lift R f (ι R x) = f x := rfl

@[simp]
theorem lift_unique (f : X → A) (g : free_algebra R X →ₐ[R] A) :
  (g : free_algebra R X → A) ∘ (ι R) = f ↔ g = lift R f :=
(lift R).symm_apply_eq

/-!
At this stage we set the basic definitions as `@[irreducible]`, so from this point onwards one
should only use the universal properties of the free algebra, and consider the actual implementation
as a quotient of an inductive type as completely hidden.

Of course, one still has the option to locally make these definitions `semireducible` if so desired,
and Lean is still willing in some circumstances to do unification based on the underlying
definition.
-/
attribute [irreducible] ι lift
-- Marking `free_algebra` irreducible makes `ring` instances inaccessible on quotients.
-- https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/algebra.2Esemiring_to_ring.20breaks.20semimodule.20typeclass.20lookup/near/212580241
-- For now, we avoid this by not marking it irreducible.

@[simp]
theorem lift_comp_ι (g : free_algebra R X →ₐ[R] A) :
  lift R ((g : free_algebra R X → A) ∘ (ι R)) = g :=
by { rw ←lift_symm_apply, exact (lift R).apply_symm_apply g }

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem hom_ext {f g : free_algebra R X →ₐ[R] A}
  (w : ((f : free_algebra R X → A) ∘ (ι R)) = ((g : free_algebra R X → A) ∘ (ι R))) : f = g :=
begin
  rw [←lift_symm_apply, ←lift_symm_apply] at w,
  exact (lift R).symm.injective w,
end

/--
The free algebra on `X` is "just" the monoid algebra on the free monoid on `X`.

This would be useful when constructing linear maps out of a free algebra,
for example.
-/
noncomputable
def equiv_monoid_algebra_free_monoid : free_algebra R X ≃ₐ[R] monoid_algebra R (free_monoid X) :=
alg_equiv.of_alg_hom
  (lift R (λ x, (monoid_algebra.of R (free_monoid X)) (free_monoid.of x)))
  ((monoid_algebra.lift R (free_monoid X) (free_algebra R X)) (free_monoid.lift (ι R)))
begin
  apply monoid_algebra.alg_hom_ext, intro x,
  apply free_monoid.rec_on x,
  { simp, refl, },
  { intros x y ih, simp at ih, simp [ih], }
end
(by { ext, simp, })

instance [nontrivial R] : nontrivial (free_algebra R X) :=
equiv_monoid_algebra_free_monoid.to_equiv.nontrivial

section
open_locale classical

/-- The left-inverse of `algebra_map`. -/
def algebra_map_inv : free_algebra R X →ₐ[R] R :=
lift R (0 : X → R)

lemma algebra_map_left_inverse :
  function.left_inverse algebra_map_inv (algebra_map R $ free_algebra R X) :=
λ x, by simp [algebra_map_inv]

-- this proof is copied from the approach in `free_abelian_group.of_injective`
lemma ι_injective [nontrivial R] : function.injective (ι R : X → free_algebra R X) :=
λ x y hoxy, classical.by_contradiction $ assume hxy : x ≠ y,
  let f : free_algebra R X →ₐ[R] R := lift R (λ z, if x = z then (1 : R) else 0) in
  have hfx1 : f (ι R x) = 1, from (lift_ι_apply _ _).trans $ if_pos rfl,
  have hfy1 : f (ι R y) = 1, from hoxy ▸ hfx1,
  have hfy0 : f (ι R y) = 0, from (lift_ι_apply _ _).trans $ if_neg hxy,
  one_ne_zero $ hfy1.symm.trans hfy0

end

end free_algebra

/- There is something weird in the above namespace that breaks the typeclass resolution of
`has_coe_to_sort` below. Closing it and reopening it fixes it... -/
namespace free_algebra

/-- An induction principle for the free algebra.

If `C` holds for the `algebra_map` of `r : R` into `free_algebra R X`, the `ι` of `x : X`, and is
preserved under addition and muliplication, then it holds for all of `free_algebra R X`.
-/
@[elab_as_eliminator]
lemma induction {C : free_algebra R X → Prop}
  (h_grade0 : ∀ r, C (algebra_map R (free_algebra R X) r))
  (h_grade1 : ∀ x, C (ι R x))
  (h_mul : ∀ a b, C a → C b → C (a * b))
  (h_add : ∀ a b, C a → C b → C (a + b))
  (a : free_algebra R X) :
  C a :=
begin
  -- the arguments are enough to construct a subalgebra, and a mapping into it from X
  let s : subalgebra R (free_algebra R X) := {
    carrier := C,
    mul_mem' := h_mul,
    add_mem' := h_add,
    algebra_map_mem' := h_grade0, },
  let of : X → s := subtype.coind (ι R) h_grade1,
  -- the mapping through the subalgebra is the identity
  have of_id : alg_hom.id R (free_algebra R X) = s.val.comp (lift R of),
  { ext,
    simp [of, subtype.coind], },
  -- finding a proof is finding an element of the subalgebra
  convert subtype.prop (lift R of a),
  simp [alg_hom.ext_iff] at of_id,
  exact of_id a,
end

variables {R X}

/--
Separate an element of the free algebra into its ℕ-graded components.

This is defined as an `alg_hom` to `add_monoid_algebra` so that algebra operators can be moved
before and after the mapping.
-/
noncomputable
def grades : (free_algebra R X) →ₐ[R] add_monoid_algebra (free_algebra R X) ℕ :=
lift R $ finsupp.single 1 ∘ ι R

/-- Recombining the grades recovers the original element-/
lemma sum_id_grades :
  (add_monoid_algebra.sum_id R).comp grades = alg_hom.id R (free_algebra R X) :=
begin
  ext,
  simp [grades, add_monoid_algebra.sum_id_apply, finsupp.sum_single_index],
end

noncomputable
instance : has_coe (add_monoid_algebra (free_algebra R X) ℕ) (free_algebra R X) := ⟨
  (add_monoid_algebra.sum_id R : add_monoid_algebra (free_algebra R X) ℕ →ₐ[R] (free_algebra R X))
⟩

@[simp, norm_cast]
lemma coe_def (x : add_monoid_algebra (free_algebra R X) ℕ) : (x : free_algebra R X) = add_monoid_algebra.sum_id R x := rfl


/-- An element of `R` lifted with `algebra_map` has a single grade 0 element -/
lemma grades.map_algebra_map (r : R) :
  grades (algebra_map R (free_algebra R X) r) = finsupp.single 0 (algebra_map R _ r) :=
by simp

/-- An element of `X` lifted with the canonical `ι R` function has a single grade 1 element -/
lemma grades.map_ι (x : X) :
  grades (ι R x) = finsupp.single 1 (ι R x) :=
by simp [grades]

-- note this is true for any `zero_hom`, not just `grades`. Of course, then we need to repeat this
-- for `add_monoid_hom`, `add_equiv`, `linear_map`, `ring_hom`, `ring_equiv`, `alg_hom`, ...
private lemma map_single_apply (x : free_algebra R X) (i j : ℕ) :
  grades (finsupp.single i x j) = finsupp.single i (grades x) j :=
by rw [finsupp.single_apply, finsupp.single_apply, apply_ite grades, grades.map_zero]

/-- The grade-`i` part consists only of itself -/
@[simp]
lemma grades.map_grades (x : free_algebra R X) (i : ℕ) :
  grades (grades x i) = finsupp.single i (grades x i) :=
begin
  induction x using free_algebra.induction generalizing i,
  case h_grade0 : {
    rw [grades.map_algebra_map, map_single_apply, grades.map_algebra_map,
      finsupp.single_of_single_apply],
  },
  case h_grade1 : {
    rw [grades.map_ι, map_single_apply, grades.map_ι,
      finsupp.single_of_single_apply],
  },
  case h_add : x y hx hy {
    rw [grades.map_add, finsupp.add_apply, grades.map_add, finsupp.single_add, hx, hy],
  },
  case h_mul : f g hx hy {
    rw grades.map_mul,
    rw add_monoid_algebra.mul_def,
    simp_rw [finsupp.sum_apply],

    -- pull the sums to the outside
    have : finsupp.single i = finsupp.single_add_hom i := rfl,
    rw this,
    simp_rw alg_hom.map_finsupp_sum,
    simp_rw add_monoid_hom.map_finsupp_sum,
    simp_rw finsupp.sum,
    congr, ext1 fi,
    congr, ext1 gi,
    rw ←this,

    -- this proof now resembles the other three
    rw [map_single_apply, grades.map_mul,
      finsupp.single_of_single_apply],
    rw [hx, hy, add_monoid_algebra.single_mul_single],
  },
end

/-- The star ring formed by reversing the elements of products -/
instance : star_ring (free_algebra R X) :=
{ star := opposite.unop ∘ lift R (opposite.op ∘ ι R),
  star_involutive := λ x, by {
    unfold has_star.star,
    simp only [function.comp_apply],
    refine free_algebra.induction R X _ _ _ _ x; intros; simp [*] },
  star_mul := λ a b, by simp,
  star_add := λ a b, by simp }

@[simp]
lemma star_ι (x : X) : star (ι R x) = (ι R x) :=
by simp [star, has_star.star]

@[simp]
lemma star_algebra_map (r : R) : star (algebra_map R (free_algebra R X) r) = (algebra_map R _ r) :=
by simp [star, has_star.star]

/-- `star` as an `alg_equiv` -/
def star_hom : free_algebra R X ≃ₐ[R] (free_algebra R X)ᵒᵖ :=
{ commutes' := λ r, by simp [star_algebra_map],
  ..star_ring_equiv }
end free_algebra
