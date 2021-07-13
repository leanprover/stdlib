/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import algebra.free_monoid
import group_theory.congruence
/-!
# The free product of groups or monoids
Given an `ι`-indexed family `M` of monoids, we define their free product (categorical coproduct)
`free_product M`.

When `M i` are all groups, `free_product M` is also a group (and the coproduct in the category of
groups).

## Main definitions

- `free_product M`: the free product, defined as a quotient of a free monoid.
- `free_product.of {i} : M i →* free_product M`.
- `free_product.lift : (Π {i}, M i →* N) ≃ (free_product M →* N)`: the universal property.

## Remarks

There are many answers to the question "what is the free product of a family `M` of monoids?", and
they are all equivalent but not obviously equivalent. We provide one almost tautological answer,
namely `free_product M`, which is a quotient of the type of words in the alphabet `Σ i, M i`. It's
straightforward to define and easy to prove its universal property. But this answer is not
completely satisfactory, because it's difficult to tell when two elements `x y : free_product M` are
distinct since `free_product M` is defined as a quotient. Soon a second answer will be given, in
terms of reduced words, which lets you show that distinct elements are distinct.

There is also a completely tautological, maximally inefficient answer given by
`algebra.category.Mon.colimits`. Whereas `free_product M` at least ensures that (any instance of)
associativity holds by reflexivity, in this answer associativity holds because of quotienting. Yet
another answer, which is constructively more satisfying, can be obtained by showing that
`free_product.rel` is confluent.

## References

[van der Waerden, *Free products of groups*][MR25465]

-/

variables {ι : Type*} (M : Π i : ι, Type*) [Π i, monoid (M i)]

/-- A relation on the free monoid on alphabet `Σ i, M i`, relating `⟨i, 1⟩` with `1` and
`⟨i, x⟩ * ⟨i, y⟩` with `⟨i, x * y⟩`. -/
inductive free_product.rel : free_monoid (Σ i, M i) → free_monoid (Σ i, M i) → Prop
| of_one (i : ι) : free_product.rel (free_monoid.of ⟨i, 1⟩) 1
| of_mul {i : ι} (x y : M i) : free_product.rel (free_monoid.of ⟨i, x⟩ * free_monoid.of ⟨i, y⟩)
  (free_monoid.of ⟨i, x * y⟩)

/-- The free product (categorical coproduct) of an indexed family of monoids. -/
@[derive [monoid, inhabited]]
def free_product : Type* := (con_gen (free_product.rel M)).quotient

namespace free_product

variable {M}

/-- The inclusion of a summand into the free product. -/
def of {i : ι} : M i →* free_product M :=
{ to_fun   := λ x, con.mk' _ (free_monoid.of $ sigma.mk i x),
  map_one' := (con.eq _).mpr (con_gen.rel.of _ _ (free_product.rel.of_one i)),
  map_mul' := λ x y, eq.symm $ (con.eq _).mpr (con_gen.rel.of _ _ (free_product.rel.of_mul x y)) }

lemma of_apply {i} (m : M i) : of m = con.mk' _ (free_monoid.of $ sigma.mk i m) := rfl

variables {N : Type*} [monoid N]

/-- See note [partially-applied ext lemmas]. -/
@[ext] lemma ext_hom (f g : free_product M →* N) (h : ∀ i, f.comp (of : M i →* _) = g.comp of) :
  f = g :=
(monoid_hom.cancel_right con.mk'_surjective).mp $ free_monoid.hom_eq $ λ ⟨i, x⟩,
  by rw [monoid_hom.comp_apply, monoid_hom.comp_apply, ←of_apply,
    ←monoid_hom.comp_apply, ←monoid_hom.comp_apply, h]

/-- A map out of the free product corresponds to a family of maps out of the summands. This is the
universal property of the free product, charaterizing it as a categorical coproduct. -/
@[simps symm_apply]
def lift : (Π i, M i →* N) ≃ (free_product M →* N) :=
{ to_fun := λ fi, con.lift _ (free_monoid.lift $ λ p : Σ i, M i, fi p.fst p.snd) $ con.con_gen_le
    begin
      simp_rw [con.rel_eq_coe, con.ker_rel],
      rintros _ _ (i | ⟨i, x, y⟩),
      { change free_monoid.lift _ (free_monoid.of _) = free_monoid.lift _ 1,
        simp only [monoid_hom.map_one, free_monoid.lift_eval_of], },
      { change free_monoid.lift _ (free_monoid.of _ * free_monoid.of _) =
          free_monoid.lift _ (free_monoid.of _),
        simp only [monoid_hom.map_mul, free_monoid.lift_eval_of], }
    end,
  inv_fun := λ f i, f.comp of,
  left_inv := by { intro fi, ext i x,
    rw [monoid_hom.comp_apply, of_apply, con.lift_mk', free_monoid.lift_eval_of], },
  right_inv := by { intro f, ext i x,
    simp only [monoid_hom.comp_apply, of_apply, con.lift_mk', free_monoid.lift_eval_of], } }

@[simp] lemma lift_of {N} [monoid N] (fi : Π i, M i →* N) {i} (m : M i) :
  lift fi (of m) = fi i m :=
by conv_rhs { rw [←lift.symm_apply_apply fi, lift_symm_apply, monoid_hom.comp_apply] }

@[elab_as_eliminator]
lemma induction_on {C : free_product M → Prop}
  (m : free_product M)
  (h_one : C 1)
  (h_of : ∀ {i} (m : M i), C (of m))
  (h_mul : ∀ {x y}, C x → C y → C (x * y)) :
  C m :=
begin
  apply con.induction_on m,
  intro m',
  apply m'.rec_on,
  { rw con.coe_one, exact h_one, },
  { rintros ⟨i, x⟩ m'' ih, rw con.coe_mul, exact h_mul (h_of x) ih },
end

section group

variables (G : ι → Type*) [∀ i, group (G i)]

instance : has_inv (free_product G) :=
{ inv := opposite.unop ∘ lift (λ i, (of : G i →* _).op.comp (mul_equiv.inv' (G i)).to_monoid_hom) }

lemma inv_def (x : free_product G) : x⁻¹ = opposite.unop
  (lift (λ i, (of : G i →* _).op.comp (mul_equiv.inv' (G i)).to_monoid_hom) x) := rfl

instance : group (free_product G) :=
{ mul_left_inv := begin
    intro m,
    rw inv_def,
    apply m.induction_on,
    { rw [monoid_hom.map_one, opposite.unop_one, one_mul], },
    { intros i m, change of m⁻¹ * of m = 1, rw [←of.map_mul, mul_left_inv, of.map_one], },
    { intros x y hx hy,
      rw [monoid_hom.map_mul, opposite.unop_mul, mul_assoc, ←mul_assoc _ x y, hx, one_mul, hy], },
  end,
  ..free_product.has_inv G,
  ..free_product.monoid G }

end group

end free_product
