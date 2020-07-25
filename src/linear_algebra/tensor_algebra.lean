/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Topaz.
-/

import ring_theory.algebra
import linear_algebra

/-!
# Tensor Algebras

Given a commutative semiring R, and an R-module M, we construct the tensor algebra of M.
This is the free R-algebra generated by the module M.

## Notation

1. `tensor_algebra R M` is the tensor algebra itself.
  It is endowed with an R-algebra structure.
2. `univ R M` is the R-linear map `M → tensor_algebra R M`.
3. Given a linear map `f : M → A` to an R-algebra A,
  `lift R M f` is the lift of `f` to an R-algebra morphism
  `tensor_algebra R M → A`.

## Theorems

1. `univ_comp_lift` states that the composition
  `(lift R M f) ∘ (univ R M)` is identical to `f`.
2. `lift_unique` states that whenever an R-algebra morphism
  `g : tensor_algebra R M → A` is given whose composision with `univ R M` is `f`,
  then one has `g = lift R M f`.
-/

universes u1 u2 u3

variables (R : Type u1) [comm_semiring R]
variables (M : Type u2) [add_comm_group M] [semimodule R M]

namespace tensor_algebra

/--
This inductive type is used to express representatives
of the tensor algebra.
-/
inductive pre
| of : M → pre
| of_scalar : R → pre
| add : pre → pre → pre
| mul : pre → pre → pre

namespace pre

instance : inhabited (pre R M) := ⟨of_scalar 0⟩

-- Note: These instances are only used to simplify the notation.
/-- Coercion from `M` to `pre R M`. Note: Used for notation only. -/
def has_coe_module : has_coe M (pre R M) := ⟨of⟩
/-- Coercion from `R` to `pre R M`. Note: Used for notation only. -/
def has_coe_semiring : has_coe R (pre R M) := ⟨of_scalar⟩
/-- Multiplication in `pre R M` defined as `pre.mul`. Note: Used for notation only. -/
def has_mul : has_mul (pre R M) := ⟨mul⟩
/-- Addition in `pre R M` defined as `pre.add`. Note: Used for notation only. -/
def has_add : has_add (pre R M) := ⟨add⟩
/-- Zero in `pre R M` defined as the image of `0` from `R`. Note: Used for notation only. -/
def has_zero : has_zero (pre R M) := ⟨of_scalar 0⟩
/-- One in `pre R M` defined as the image of `1` from `R`. Note: Used for notation only. -/
def has_one : has_one (pre R M) := ⟨of_scalar 1⟩
/--
Scalar multiplication defined as multiplication by the image
of elements from `R`.
Note: Used for notation only.
-/
def has_scalar : has_scalar R (pre R M) := ⟨λ r m, mul (of_scalar r) m⟩

end pre

local attribute [instance]
  pre.has_coe_module pre.has_coe_semiring pre.has_mul pre.has_add pre.has_zero
  pre.has_one pre.has_scalar

/--
Given a linear map from `M` to an `R`-algebra `A`, `lift_fun` provides
a lift of `f` to a function from `pre R M` to `A`.
This is mainly used in the construction of `tensor_algebra.lift` below.
-/
def lift_fun {A : Type u3} [semiring A] [algebra R A] (f : M →ₗ[R] A) : pre R M → A :=
  λ t, pre.rec_on t f (algebra_map _ _) (λ _ _, (+)) (λ _ _, (*))

/--
An inductively defined relation on `pre R M`
used to force the initial algebra structure on the associated quotient.
-/
inductive rel : (pre R M) → (pre R M) → Prop
-- force of to be linear
| add_lin {a b : M} : rel ↑(a+b) (↑a + ↑b)
| smul_lin {r : R} {a : M} : rel ↑(r • a) (↑r * ↑a)
-- force of_scalar to be a central semiring morphism
| add_scalar {r s : R} : rel ↑(r + s) (↑r + ↑s)
| mul_scalar {r s : R} : rel ↑(r * s) (↑r * ↑s)
| central_scalar {r : R} {a : pre R M} : rel (r * a) (a * r)
-- commutative additive semigroup
| add_assoc {a b c : pre R M} : rel (a + b + c) (a + (b + c))
| add_comm {a b : pre R M} : rel (a + b) (b + a)
| zero_add {a : pre R M} : rel (0 + a) a
-- multiplicative monoid
| mul_assoc {a b c : pre R M} : rel (a * b * c) (a * (b * c))
| one_mul {a : pre R M} : rel (1 * a) a
| mul_one {a : pre R M} : rel (a * 1) a
-- distributivity
| left_distrib {a b c : pre R M} : rel (a * (b + c)) (a * b + a * c)
| right_distrib {a b c : pre R M} : rel ((a + b) * c) (a * c + b * c)
-- other relations needed for semiring
| zero_mul {a : pre R M} : rel (0 * a) 0
| mul_zero {a : pre R M} : rel (a * 0) 0
-- compatibility
| add_compat_left {a b c : pre R M} : rel a b → rel (a + c) (b + c)
| add_compat_right {a b c : pre R M} : rel a b → rel (c + a) (c + b)
| mul_compat_left {a b c : pre R M} : rel a b → rel (a * c) (b * c)
| mul_compat_right {a b c : pre R M} : rel a b → rel (c * a) (c * b)

end tensor_algebra

/--
The tensor algebra of the module `M` over the commutative semiring `R`.
-/
def tensor_algebra := quot (tensor_algebra.rel R M)

namespace tensor_algebra

local attribute [instance]
  pre.has_coe_module pre.has_coe_semiring pre.has_mul pre.has_add pre.has_zero
  pre.has_one pre.has_scalar

instance : semiring (tensor_algebra R M) :=
{ add := λ a b, quot.lift_on a (λ x, quot.lift_on b (λ y, quot.mk (rel R M) (x + y))
  begin
    intros a b h,
    dsimp only [],
    apply quot.sound,
    apply rel.add_compat_right h,
  end)
  begin
    intros a b h,
    dsimp only [],
    congr,
    ext,
    apply quot.sound,
    apply rel.add_compat_left h,
  end,
  add_assoc := λ a b c,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quot.sound,
    apply rel.add_assoc,
  end,
  zero := quot.mk _ 0,
  zero_add := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quot.sound,
    apply rel.zero_add,
  end,
  add_zero := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    change quot.mk _ _ = _,
    rw quot.sound rel.add_comm,
    apply quot.sound,
    apply rel.zero_add,
  end,
  add_comm := λ a b,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    apply quot.sound,
    apply rel.add_comm,
  end,
  mul := λ a b, quot.lift_on a (λ x, quot.lift_on b (λ y, quot.mk _ (x * y))
  begin
    intros a b h,
    dsimp only [],
    apply quot.sound,
    apply rel.mul_compat_right h,
  end)
  begin
    intros a b h,
    dsimp only [],
    congr,
    ext,
    apply quot.sound,
    apply rel.mul_compat_left h,
  end,
  mul_assoc := λ a b c,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quot.sound,
    apply rel.mul_assoc,
  end,
  one := quot.mk _ 1,
  one_mul := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quot.sound,
    apply rel.one_mul,
  end,
  mul_one := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quot.sound,
    apply rel.mul_one,
  end,
  left_distrib := λ a b c,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quot.sound,
    apply rel.left_distrib,
  end,
  right_distrib := λ a b c,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    rcases quot.exists_rep b with ⟨b,rfl⟩,
    rcases quot.exists_rep c with ⟨c,rfl⟩,
    apply quot.sound,
    apply rel.right_distrib,
  end,
  zero_mul := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quot.sound,
    apply rel.zero_mul,
  end,
  mul_zero := λ a,
  begin
    rcases quot.exists_rep a with ⟨a,rfl⟩,
    apply quot.sound,
    apply rel.mul_zero,
  end }

instance : inhabited (tensor_algebra R M) := ⟨0⟩

instance : has_scalar R (tensor_algebra R M) :=
{ smul := λ r a, quot.lift_on a (λ x, quot.mk _ $ ↑r * x)
begin
  intros a b h,
  dsimp only [],
  apply quot.sound,
  apply rel.mul_compat_right h,
end }

instance : algebra R (tensor_algebra R M) :=
{ to_fun := λ r, quot.mk _ ↑r,
  map_one' := rfl,
  map_mul' := λ a b, by apply quot.sound; apply rel.mul_scalar,
  map_zero' := rfl,
  map_add' := λ a b, by apply quot.sound; apply rel.add_scalar,
  commutes' := λ r x,
  begin
    dsimp only [],
    rcases quot.exists_rep x with ⟨x,rfl⟩,
    apply quot.sound,
    apply rel.central_scalar,
  end,
  smul_def' := λ r x, by refl }

/--
The universal linear map `M →ₗ[R] tensor_algebra R M`.
-/
def univ : M →ₗ[R] (tensor_algebra R M) :=
{ to_fun := λ m, quot.mk _ m,
  map_add' := λ x y, by apply quot.sound; apply rel.add_lin,
  map_smul' := λ r x, by apply quot.sound; apply rel.smul_lin }

/--
Given a linear map `f : M → A` where `A` is an `R`-algebra,
`lift R M f` is the unique lift of `f` to a morphism of `R`-algebras
`tensor_algebra R M → A`.
-/
def lift {A : Type u3} [semiring A] [algebra R A] (f : M →ₗ[R] A) : tensor_algebra R M →ₐ[R] A :=
{ to_fun := λ a, quot.lift_on a (lift_fun _ _ f) $ λ a b h,
  begin
    induction h,
    { change f _ = f _ + f _, simp, },
    { change f _ = (algebra_map _ _ _) * f _, rw linear_map.map_smul,
      exact algebra.smul_def h_r (f h_a) },
    { change algebra_map _ _ _ = algebra_map _ _ _ + algebra_map _ _ _,
      exact (algebra_map R A).map_add h_r h_s },
    { change algebra_map _ _ _ = algebra_map _ _ _ * algebra_map _ _ _,
      exact (algebra_map R A).map_mul h_r h_s },
    { let G := lift_fun R M f,
      change (algebra_map _ _ _) * G _ = G _,
      exact algebra.commutes h_r (G h_a) },
    { change _ + _ + _ = _ + (_ + _), rw add_assoc },
    { change _ + _ = _ + _, rw add_comm, },
    { let G := lift_fun R M f,
      change (algebra_map _ _ _) + G _ = G _, simp, },
    { change _ * _ * _ = _ * (_ * _), rw mul_assoc },
    { let G := lift_fun R M f,
      change (algebra_map _ _ _) * G _ = G _, simp, },
    { let G := lift_fun R M f,
      change G _ * (algebra_map _ _ _)= G _, simp, },
    { change _ * (_ + _) = _ * _ + _ * _, rw left_distrib, },
    { change (_ + _) * _ = _ * _ + _ * _, rw right_distrib, },
    repeat { set G := lift_fun R M f,
      change G _ + G _ = G _ + G _, rw h_ih, },
    repeat { set G := lift_fun R M f,
      change G _ * G _ = G _ * G _, rw h_ih, },
    { change (algebra_map _ _ _) * _ = algebra_map _ _ _, simp },
    { change _ * (algebra_map _ _ _) = algebra_map _ _ _, simp },
  end,
  map_one' := by change algebra_map _ _ _ = _; simp,
  map_mul' :=
  begin
    intros x y,
    rcases quot.exists_rep x with ⟨x,rfl⟩,
    rcases quot.exists_rep y with ⟨y,rfl⟩,
    refl,
  end,
  map_zero' := by change algebra_map _ _ _ = _; simp,
  map_add' :=
  begin
    intros x y,
    rcases quot.exists_rep x with ⟨x,rfl⟩,
    rcases quot.exists_rep y with ⟨y,rfl⟩,
    refl,
  end,
  commutes' := by tauto }

variables {R M}

theorem univ_comp_lift {A : Type u3} [semiring A] [algebra R A] (f : M →ₗ[R] A) :
  (lift R M f).to_linear_map.comp (univ R M) = f := by {ext, refl}

theorem lift_unique {A : Type u3} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (g : tensor_algebra R M →ₐ[R] A) : g.to_linear_map.comp (univ R M) = f → g = lift R M f :=
begin
  intro hyp,
  ext,
  rcases quot.exists_rep x with ⟨x,rfl⟩,
  let G := lift_fun R M f,
  induction x,
  { change (g.to_linear_map.comp (univ R M)) _ = _,
    rw hyp, refl },
  { change g (algebra_map R _ _) = algebra_map _ _ _,
    exact alg_hom.commutes g x },
  { change g (quot.mk _ x_a + quot.mk _ x_a_1) = _,
    rw alg_hom.map_add,
    rw x_ih_a, rw x_ih_a_1,
    refl },
  { change g (quot.mk _ x_a * quot.mk _ x_a_1) = _,
    rw alg_hom.map_mul,
    rw x_ih_a, rw x_ih_a_1,
    refl },
end

theorem hom_ext {A : Type u3} [semiring A] [algebra R A] {f g : tensor_algebra R M →ₐ[R] A} :
  f.to_linear_map.comp (univ R M) = g.to_linear_map.comp (univ R M) → f = g :=
begin
  intro hyp,
  let h := f.to_linear_map.comp (univ R M),
  have : f = lift R M h, by apply lift_unique; refl,
  rw this, clear this,
  symmetry, apply lift_unique,
  rw ←hyp,
end

end tensor_algebra
