/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import algebra.module
import algebra.algebra.basic
import ring_theory.ideal.basic

/-!
# Transfer algebraic structures across `equiv`s

In this file we prove theorems of the following form: if `β` has a
group structure and `α ≃ β` then `α` has a group structure, and
similarly for monoids, semigroups, rings, integral domains, fields and
so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

## Tags

equiv, group, ring, field, module, algebra
-/

universes u v
variables {α : Type u} {β : Type v}

namespace equiv


section instances

variables (e : α ≃ β)

/-- Transfer `has_one` across an `equiv` -/
@[to_additive "Transfer `has_zero` across an `equiv`"]
protected def has_one [has_one β] : has_one α := ⟨e.symm 1⟩
@[to_additive]
lemma one_def [has_one β] : @has_one.one _ (equiv.has_one e) = e.symm 1 := rfl

/-- Transfer `has_mul` across an `equiv` -/
@[to_additive "Transfer `has_add` across an `equiv`"]
protected def has_mul [has_mul β] : has_mul α := ⟨λ x y, e.symm (e x * e y)⟩
@[to_additive]
lemma mul_def [has_mul β] (x y : α) :
  @has_mul.mul _ (equiv.has_mul e) x y = e.symm (e x * e y) := rfl

/-- Transfer `has_div` across an `equiv` -/
@[to_additive "Transfer `has_sub` across an `equiv`"]
protected def has_div [has_div β] : has_div α := ⟨λ x y, e.symm (e x / e y)⟩
@[to_additive]
lemma div_def [has_div β] (x y : α) :
@has_div.div _ (equiv.has_div e) x y = e.symm (e x / e y) := rfl

/-- Transfer `has_inv` across an `equiv` -/
@[to_additive "Transfer `has_neg` across an `equiv`"]
protected def has_inv [has_inv β] : has_inv α := ⟨λ x, e.symm (e x)⁻¹⟩
@[to_additive]
lemma inv_def [has_inv β] (x : α) : @has_inv.inv _ (equiv.has_inv e) x = e.symm (e x)⁻¹ := rfl

/-- Transfer `has_scalar` across an `equiv` -/
protected def has_scalar {R : Type*} [has_scalar R β] : has_scalar R α  :=
⟨λ r x, e.symm (r • (e x))⟩
lemma smul_def {R : Type*} [has_scalar R β] (r : R) (x : α) :
  @has_scalar.smul _ _ (equiv.has_scalar e) r x = e.symm (r • (e x)) := rfl

/--
An equivalence `e : α ≃ β` gives a multiplicative equivalence `α ≃* β`
where the multiplicative structure on `α` is
the one obtained by transporting a multiplicative structure on `β` back along `e`.
-/
@[to_additive
"An equivalence `e : α ≃ β` gives a additive equivalence `α ≃+ β`
where the additive structure on `α` is
the one obtained by transporting an additive structure on `β` back along `e`."]
def mul_equiv (e : α ≃ β) [has_mul β] :
  by { letI := equiv.has_mul e, exact α ≃* β } :=
begin
  introsI,
  exact
  { map_mul' := λ x y, by { apply e.symm.injective, simp, refl, },
    ..e }
end

@[simp, to_additive] lemma mul_equiv_apply (e : α ≃ β) [has_mul β] (a : α) :
  (mul_equiv e) a = e a := rfl

@[to_additive] lemma mul_equiv_symm_apply (e : α ≃ β) [has_mul β] (b : β) :
  by { letI := equiv.has_mul e, exact (mul_equiv e).symm b = e.symm b } :=
begin
  intros, refl,
end

/--
An equivalence `e : α ≃ β` gives a ring equivalence `α ≃+* β`
where the ring structure on `α` is
the one obtained by transporting a ring structure on `β` back along `e`.
-/
def ring_equiv (e : α ≃ β) [has_add β] [has_mul β] :
  by { letI := equiv.has_add e, letI := equiv.has_mul e, exact α ≃+* β } :=
begin
  introsI,
  exact
  { map_add' := λ x y, by { apply e.symm.injective, simp, refl, },
    map_mul' := λ x y, by { apply e.symm.injective, simp, refl, },
    ..e }
end

@[simp] lemma ring_equiv_apply (e : α ≃ β) [has_add β] [has_mul β] (a : α) :
  (ring_equiv e) a = e a := rfl

lemma ring_equiv_symm_apply (e : α ≃ β) [has_add β] [has_mul β] (b : β) :
  by { letI := equiv.has_add e, letI := equiv.has_mul e, exact (ring_equiv e).symm b = e.symm b } :=
begin
  intros, refl,
end

/-- Transfer `semigroup` across an `equiv` -/
@[to_additive "Transfer `add_semigroup` across an `equiv`"]
protected def semigroup [semigroup β] : semigroup α :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..equiv.has_mul e }

/-- Transfer `comm_semigroup` across an `equiv` -/
@[to_additive "Transfer `add_comm_semigroup` across an `equiv`"]
protected def comm_semigroup [comm_semigroup β] : comm_semigroup α :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..equiv.semigroup e }

/-- Transfer `monoid` across an `equiv` -/
@[to_additive "Transfer `add_monoid` across an `equiv`"]
protected def monoid [monoid β] : monoid α :=
{ one_mul := by simp [mul_def, one_def],
  mul_one := by simp [mul_def, one_def],
  ..equiv.semigroup e,
  ..equiv.has_one e }

/-- Transfer `comm_monoid` across an `equiv` -/
@[to_additive "Transfer `add_comm_monoid` across an `equiv`"]
protected def comm_monoid [comm_monoid β] : comm_monoid α :=
{ ..equiv.comm_semigroup e,
  ..equiv.monoid e }

/-- Transfer `group` across an `equiv` -/
@[to_additive "Transfer `add_group` across an `equiv`"]
protected def group [group β] : group α :=
{ mul_left_inv := by simp [mul_def, inv_def, one_def],
  div_eq_mul_inv := λ a b, by rw [div_def, div_eq_mul_inv, mul_def, inv_def, e.apply_symm_apply],
  ..equiv.monoid e,
  ..equiv.has_inv e,
  ..equiv.has_div e }

/-- Transfer `comm_group` across an `equiv` -/
@[to_additive "Transfer `add_comm_group` across an `equiv`"]
protected def comm_group [comm_group β] : comm_group α :=
{ ..equiv.group e,
  ..equiv.comm_semigroup e }

/-- Transfer `semiring` across an `equiv` -/
protected def semiring [semiring β] : semiring α :=
{ right_distrib := by simp [mul_def, add_def, add_mul],
  left_distrib := by simp [mul_def, add_def, mul_add],
  zero_mul := by simp [mul_def, zero_def],
  mul_zero := by simp [mul_def, zero_def],
  ..equiv.has_zero e,
  ..equiv.has_mul e,
  ..equiv.has_add e,
  ..equiv.monoid e,
  ..equiv.add_comm_monoid e }

/-- Transfer `comm_semiring` across an `equiv` -/
protected def comm_semiring [comm_semiring β] : comm_semiring α :=
{ ..equiv.semiring e,
  ..equiv.comm_monoid e }

/-- Transfer `ring` across an `equiv` -/
protected def ring [ring β] : ring α :=
{ ..equiv.semiring e,
  ..equiv.add_comm_group e }

/-- Transfer `comm_ring` across an `equiv` -/
protected def comm_ring [comm_ring β] : comm_ring α :=
{ ..equiv.comm_monoid e,
  ..equiv.ring e }

/-- Transfer `nonzero` across an `equiv` -/
protected theorem nontrivial [nontrivial β] : nontrivial α :=
let ⟨x, y, h⟩ := exists_pair_ne β in ⟨⟨e.symm x, e.symm y, e.symm.injective.ne h⟩⟩

/-- Transfer `domain` across an `equiv` -/
protected def domain [domain β] : domain α :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by simp [mul_def, zero_def, equiv.eq_symm_apply],
  ..equiv.ring e,
  ..equiv.nontrivial e }

/-- Transfer `integral_domain` across an `equiv` -/
protected def integral_domain [integral_domain β] : integral_domain α :=
{ ..equiv.domain e,
  ..equiv.comm_ring e }

/-- Transfer `division_ring` across an `equiv` -/
protected def division_ring [division_ring β] : division_ring α :=
{ mul_inv_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact mul_inv_cancel,
  inv_zero := by simp [zero_def, inv_def],
  div_eq_mul_inv := λ a b, by rw [div_def, div_eq_mul_inv, mul_def, inv_def, e.apply_symm_apply],
  ..equiv.has_zero e,
  ..equiv.has_one e,
  ..equiv.has_div e,
  ..equiv.domain e,
  ..equiv.has_inv e }

/-- Transfer `field` across an `equiv` -/
protected def field [field β] : field α :=
{ ..equiv.integral_domain e,
  ..equiv.division_ring e }

section R
variables (R : Type*)
include R

section
variables [monoid R]

/-- Transfer `mul_action` across an `equiv` -/
protected def mul_action (e : α ≃ β) [mul_action R β] : mul_action R α :=
{ one_smul := by simp [smul_def],
  mul_smul := by simp [smul_def, mul_smul],
  ..equiv.has_scalar e }

/-- Transfer `distrib_mul_action` across an `equiv` -/
protected def distrib_mul_action (e : α ≃ β) [add_comm_monoid β] :
  begin
    letI := equiv.add_comm_monoid e,
    exact Π [distrib_mul_action R β], distrib_mul_action R α
  end :=
begin
  intros,
  letI := equiv.add_comm_monoid e,
  exact (
  { smul_zero := by simp [zero_def, smul_def],
    smul_add := by simp [add_def, smul_def, smul_add],
    ..equiv.mul_action R e } : distrib_mul_action R α)
end

end

section
variables [semiring R]

/-- Transfer `semimodule` across an `equiv` -/
protected def semimodule (e : α ≃ β) [add_comm_monoid β] :
  begin
    letI := equiv.add_comm_monoid e,
    exact Π [semimodule R β], semimodule R α
  end :=
begin
  introsI,
  exact (
  { zero_smul := by simp [zero_def, smul_def],
    add_smul := by simp [add_def, smul_def, add_smul],
    ..equiv.distrib_mul_action R e } : semimodule R α)
end

/--
An equivalence `e : α ≃ β` gives a linear equivalence `α ≃ₗ[R] β`
where the `R`-module structure on `α` is
the one obtained by transporting an `R`-module structure on `β` back along `e`.
-/
def linear_equiv (e : α ≃ β) [add_comm_monoid β] [semimodule R β] :
  begin
    letI := equiv.add_comm_monoid e,
    letI := equiv.semimodule R e,
    exact α ≃ₗ[R] β
  end :=
begin
  introsI,
  exact
  { map_smul' := λ r x, by { apply e.symm.injective, simp, refl, },
    ..equiv.add_equiv e }
end

end

section
variables [comm_semiring R]

/-- Transfer `algebra` across an `equiv` -/
protected def algebra (e : α ≃ β) [semiring β] :
  begin
    letI := equiv.semiring e,
    exact Π [algebra R β], algebra R α
  end :=
begin
  introsI,
  fapply ring_hom.to_algebra',
  { exact ((ring_equiv e).symm : β →+* α).comp (algebra_map R β), },
  { intros r x,
    simp only [function.comp_app, ring_hom.coe_comp],
    have p := ring_equiv_symm_apply e,
    dsimp at p,
    erw p, clear p,
    apply (ring_equiv e).injective,
    simp only [(ring_equiv e).map_mul],
    simp [algebra.commutes], }
end

/--
An equivalence `e : α ≃ β` gives an algebra equivalence `α ≃ₐ[R] β`
where the `R`-algebra structure on `α` is
the one obtained by transporting an `R`-algebra structure on `β` back along `e`.
-/
def alg_equiv (e : α ≃ β) [semiring β] [algebra R β] :
  begin
    letI := equiv.semiring e,
    letI := equiv.algebra R e,
    exact α ≃ₐ[R] β
  end :=
begin
  introsI,
  exact
  { commutes' := λ r, by { apply e.symm.injective, simp, refl, },
    ..equiv.ring_equiv e }
end

end
end R

end instances
end equiv

namespace ring_equiv

protected lemma local_ring {A B : Type*} [comm_ring A] [local_ring A] [comm_ring B] (e : A ≃+* B) :
  local_ring B :=
begin
  haveI := e.symm.to_equiv.nontrivial,
  refine @local_of_surjective A B _ _ _ _ e e.to_equiv.surjective,
end

end ring_equiv
