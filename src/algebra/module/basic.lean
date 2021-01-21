/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
import algebra.big_operators.basic
import group_theory.group_action.group
import tactic.nth_rewrite

/-!
# Modules over a ring

In this file we define

* `semimodule R M` : an additive commutative monoid `M` is a `semimodule` over a
  `semiring` `R` if for `r : R` and `x : M` their "scalar multiplication `r • x : M` is defined, and
  the operation `•` satisfies some natural associativity and distributivity axioms similar to those
  on a ring.

* `module R M` : same as `semimodule R M` but assumes that `R` is a `ring` and `M` is an
  additive commutative group.

* `vector_space k M` : same as `semimodule k M` and `module k M` but assumes that `k` is a `field`
  and `M` is an additive commutative group.

* `linear_map R M M₂`, `M →ₗ[R] M₂` : a linear map between two R-`semimodule`s.

## Implementation notes

* `vector_space` and `module` are abbreviations for `semimodule R M`.

## Tags

semimodule, module, vector space
-/

open function
open_locale big_operators

universes u u' v w x y z
variables {R : Type u} {k : Type u'} {S : Type v} {M : Type w} {M₂ : Type x} {M₃ : Type y}
  {ι : Type z}

/-- A semimodule is a generalization of vector spaces to a scalar semiring.
  It consists of a scalar semiring `R` and an additive monoid of "vectors" `M`,
  connected by a "scalar multiplication" operation `r • x : M`
  (where `r : R` and `x : M`) with some natural associativity and
  distributivity axioms similar to those on a ring. -/
@[protect_proj] class semimodule (R : Type u) (M : Type v) [semiring R]
  [add_comm_monoid M] extends distrib_mul_action R M :=
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(zero_smul : ∀x : M, (0 : R) • x = 0)

section add_comm_monoid
variables [semiring R] [add_comm_monoid M] [semimodule R M] (r s : R) (x y : M)

theorem add_smul : (r + s) • x = r • x + s • x := semimodule.add_smul r s x
variables (R)
@[simp] theorem zero_smul : (0 : R) • x = 0 := semimodule.zero_smul x

theorem two_smul : (2 : R) • x = x + x := by rw [bit0, add_smul, one_smul]

theorem two_smul' : (2 : R) • x = bit0 x := two_smul R x

/-- Pullback a `semimodule` structure along an injective additive monoid homomorphism. -/
protected def function.injective.semimodule [add_comm_monoid M₂] [has_scalar R M₂] (f : M₂ →+ M)
  (hf : injective f) (smul : ∀ (c : R) x, f (c • x) = c • f x) :
  semimodule R M₂ :=
{ smul := (•),
  add_smul := λ c₁ c₂ x, hf $ by simp only [smul, f.map_add, add_smul],
  zero_smul := λ x, hf $ by simp only [smul, zero_smul, f.map_zero],
  .. hf.distrib_mul_action f smul }

/-- Pushforward a `semimodule` structure along a surjective additive monoid homomorphism. -/
protected def function.surjective.semimodule [add_comm_monoid M₂] [has_scalar R M₂] (f : M →+ M₂)
  (hf : surjective f) (smul : ∀ (c : R) x, f (c • x) = c • f x) :
  semimodule R M₂ :=
{ smul := (•),
  add_smul := λ c₁ c₂ x, by { rcases hf x with ⟨x, rfl⟩,
    simp only [add_smul, ← smul, ← f.map_add] },
  zero_smul := λ x, by { rcases hf x with ⟨x, rfl⟩, simp only [← f.map_zero, ← smul, zero_smul] },
  .. hf.distrib_mul_action f smul }

variable (M)

/-- `(•)` as an `add_monoid_hom`. -/
def smul_add_hom : R →+ M →+ M :=
{ to_fun := const_smul_hom M,
  map_zero' := add_monoid_hom.ext $ λ r, by simp,
  map_add' := λ x y, add_monoid_hom.ext $ λ r, by simp [add_smul] }

variables {R M}

@[simp] lemma smul_add_hom_apply (r : R) (x : M) :
  smul_add_hom R M r x = r • x := rfl

lemma semimodule.eq_zero_of_zero_eq_one (zero_eq_one : (0 : R) = 1) : x = 0 :=
by rw [←one_smul R x, ←zero_eq_one, zero_smul]

lemma list.sum_smul {l : list R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_list_sum l

lemma multiset.sum_smul {l : multiset R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_multiset_sum l

lemma finset.sum_smul {f : ι → R} {s : finset ι} {x : M} :
  (∑ i in s, f i) • x = (∑ i in s, (f i) • x) :=
((smul_add_hom R M).flip x).map_sum f s

end add_comm_monoid

variables (R)

/-- An `add_comm_monoid` that is a `semimodule` over a `ring` carries a natural `add_comm_group`
structure. -/
def semimodule.add_comm_monoid_to_add_comm_group [ring R] [add_comm_monoid M] [semimodule R M] :
  add_comm_group M :=
{ neg          := λ a, (-1 : R) • a,
  add_left_neg := λ a, show (-1 : R) • a + a = 0, by {
    nth_rewrite 1 ← one_smul _ a,
    rw [← add_smul, add_left_neg, zero_smul] },
  ..(infer_instance : add_comm_monoid M), }

variables {R}

section add_comm_group

variables (R M) [semiring R] [add_comm_group M]

/-- A structure containing most informations as in a semimodule, except the fields `zero_smul`
and `smul_zero`. As these fields can be deduced from the other ones when `M` is an `add_comm_group`,
this provides a way to construct a semimodule structure by checking less properties, in
`semimodule.of_core`. -/
@[nolint has_inhabited_instance]
structure semimodule.core extends has_scalar R M :=
(smul_add : ∀(r : R) (x y : M), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : R) (x : M), (r + s) • x = r • x + s • x)
(mul_smul : ∀(r s : R) (x : M), (r * s) • x = r • s • x)
(one_smul : ∀x : M, (1 : R) • x = x)

variables {R M}

/-- Define `semimodule` without proving `zero_smul` and `smul_zero` by using an auxiliary
structure `semimodule.core`, when the underlying space is an `add_comm_group`. -/
def semimodule.of_core (H : semimodule.core R M) : semimodule R M :=
by letI := H.to_has_scalar; exact
{ zero_smul := λ x, (add_monoid_hom.mk' (λ r : R, r • x) (λ r s, H.add_smul r s x)).map_zero,
  smul_zero := λ r, (add_monoid_hom.mk' ((•) r) (H.smul_add r)).map_zero,
  ..H }

end add_comm_group

/--
Modules are defined as an `abbreviation` for semimodules,
if the base semiring is a ring.
(A previous definition made `module` a structure
defined to be `semimodule`.)
This has as advantage that modules are completely transparent
for type class inference, which means that all instances for semimodules
are immediately picked up for modules as well.
A cosmetic disadvantage is that one can not extend modules as such,
in definitions such as `normed_space`.
The solution is to extend `semimodule` instead.
-/
library_note "module definition"

/-- A module is the same as a semimodule, except the scalar semiring is actually
  a ring.
  This is the traditional generalization of spaces like `ℤ^n`, which have a natural
  addition operation and a way to multiply them by elements of a ring, but no multiplication
  operation between vectors. -/
abbreviation module (R : Type u) (M : Type v) [ring R] [add_comm_group M] :=
semimodule R M

/--
To prove two semimodule structures on a fixed `add_comm_monoid` agree,
it suffices to check the scalar multiplications agree.
-/
-- We'll later use this to show `semimodule ℕ M` and `module ℤ M` are subsingletons.
@[ext]
lemma semimodule_ext {R : Type*} [semiring R] {M : Type*} [add_comm_monoid M] (P Q : semimodule R M)
  (w : ∀ (r : R) (m : M), by { haveI := P, exact r • m } = by { haveI := Q, exact r • m }) :
  P = Q :=
begin
  unfreezingI { rcases P with ⟨⟨⟨⟨P⟩⟩⟩⟩, rcases Q with ⟨⟨⟨⟨Q⟩⟩⟩⟩ },
  congr,
  funext r m,
  exact w r m,
  all_goals { apply proof_irrel_heq },
end

section module
variables [ring R] [add_comm_group M] [module R M] (r s : R) (x y : M)

@[simp] theorem neg_smul : -r • x = - (r • x) :=
eq_neg_of_add_eq_zero (by rw [← add_smul, add_left_neg, zero_smul])

variables (R)
theorem neg_one_smul (x : M) : (-1 : R) • x = -x := by simp
variables {R}

theorem sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y :=
by simp [add_smul, sub_eq_add_neg]

theorem smul_eq_zero {R E : Type*} [division_ring R] [add_comm_group E] [module R E]
  {c : R} {x : E} :
  c • x = 0 ↔ c = 0 ∨ x = 0 :=
⟨λ h, or_iff_not_imp_left.2 $ λ hc, (units.mk0 c hc).smul_eq_zero.1 h,
  λ h, h.elim (λ hc, hc.symm ▸ zero_smul R x) (λ hx, hx.symm ▸ smul_zero c)⟩

end module

/-- A semimodule over a `subsingleton` semiring is a `subsingleton`. We cannot register this
as an instance because Lean has no way to guess `R`. -/
theorem semimodule.subsingleton (R M : Type*) [semiring R] [subsingleton R] [add_comm_monoid M]
  [semimodule R M] :
  subsingleton M :=
⟨λ x y, by rw [← one_smul R x, ← one_smul R y, subsingleton.elim (1:R) 0, zero_smul, zero_smul]⟩

@[priority 910] -- see Note [lower instance priority]
instance semiring.to_semimodule [semiring R] : semimodule R R :=
{ smul := (*),
  smul_add := mul_add,
  add_smul := add_mul,
  mul_smul := mul_assoc,
  one_smul := one_mul,
  zero_smul := zero_mul,
  smul_zero := mul_zero }

@[simp] lemma smul_eq_mul [semiring R] {a a' : R} : a • a' = a * a' := rfl

/-- A ring homomorphism `f : R →+* M` defines a module structure by `r • x = f r * x`. -/
def ring_hom.to_semimodule [semiring R] [semiring S] (f : R →+* S) : semimodule R S :=
{ smul := λ r x, f r * x,
  smul_add := λ r x y, by unfold has_scalar.smul; rw [mul_add],
  add_smul := λ r s x, by unfold has_scalar.smul; rw [f.map_add, add_mul],
  mul_smul := λ r s x, by unfold has_scalar.smul; rw [f.map_mul, mul_assoc],
  one_smul := λ x, show f 1 * x = _, by rw [f.map_one, one_mul],
  zero_smul := λ x, show f 0 * x = 0, by rw [f.map_zero, zero_mul],
  smul_zero := λ r, mul_zero (f r) }

/--
Vector spaces are defined as an `abbreviation` for semimodules,
if the base ring is a field.
(A previous definition made `vector_space` a structure
defined to be `module`.)
This has as advantage that vector spaces are completely transparent
for type class inference, which means that all instances for semimodules
are immediately picked up for vector spaces as well.
A cosmetic disadvantage is that one can not extend vector spaces as such,
in definitions such as `normed_space`.
The solution is to extend `semimodule` instead.
-/
library_note "vector space definition"

/-- A vector space is the same as a module, except the scalar ring is actually
  a field. (This adds commutativity of the multiplication and existence of inverses.)
  This is the traditional generalization of spaces like `ℝ^n`, which have a natural
  addition operation and a way to multiply them by real numbers, but no multiplication
  operation between vectors. -/
abbreviation vector_space (R : Type u) (M : Type v) [field R] [add_comm_group M] :=
semimodule R M

section add_comm_monoid

variables [semiring R] [add_comm_monoid M] [semimodule R M]

/-- The natural ℕ-semimodule structure on any `add_comm_monoid`. -/
-- We don't make this a global instance, as it results in too many instances,
-- and confusing ambiguity in the notation `n • x` when `n : ℕ`.
def add_comm_monoid.nat_semimodule : semimodule ℕ M :=
{ smul := nsmul,
  smul_add := λ _ _ _, nsmul_add _ _ _,
  add_smul := λ _ _ _, add_nsmul _ _ _,
  mul_smul := λ _ _ _, mul_nsmul _ _ _,
  one_smul := one_nsmul,
  zero_smul := zero_nsmul,
  smul_zero := nsmul_zero }

section
local attribute [instance] add_comm_monoid.nat_semimodule
/-- `nsmul` is defined as the `smul` action of `add_comm_monoid.nat_semimodule`. -/
lemma nsmul_def (n : ℕ) (x : M) :
  n •ℕ x = n • x :=
rfl
end

section
variables (R)
/-- `nsmul` is equal to any other semimodule structure via a cast. -/
lemma nsmul_eq_smul_cast (n : ℕ) (b : M) :
  n •ℕ b = (n : R) • b :=
begin
  rw nsmul_def,
  induction n with n ih,
  { rw [nat.cast_zero, zero_smul, zero_smul] },
  { rw [nat.succ_eq_add_one, nat.cast_succ, add_smul, add_smul, one_smul, ih, one_smul] }
end
end

/-- `nsmul` is equal to any `ℕ`-semimodule structure. -/
lemma nsmul_eq_smul [semimodule ℕ M] (n : ℕ) (b : M) : n •ℕ b = n • b :=
by rw [nsmul_eq_smul_cast ℕ, n.cast_id]

/-- All `ℕ`-semimodule structures are equal. -/
instance add_comm_monoid.nat_semimodule.subsingleton : subsingleton (semimodule ℕ M) :=
⟨λ P Q, by {
  ext n,
  rw [←nsmul_eq_smul, ←nsmul_eq_smul], }⟩

/-- Note this does not depend on the `nat_semimodule` definition above, to avoid issues when
diamonds occur in finding `semimodule ℕ M` instances. -/
instance add_comm_monoid.nat_is_scalar_tower [semimodule ℕ R] [semimodule ℕ M] :
  is_scalar_tower ℕ R M :=
{ smul_assoc := λ n x y, nat.rec_on n
    (by simp only [zero_smul])
    (λ n ih, by simp only [nat.succ_eq_add_one, add_smul, one_smul, ih]) }

instance add_comm_monoid.nat_smul_comm_class [semimodule ℕ M] : smul_comm_class ℕ R M :=
{ smul_comm := λ n r m, nat.rec_on n
    (by simp only [zero_smul, smul_zero])
    (λ n ih, by simp only [nat.succ_eq_add_one, add_smul, one_smul, ←ih, smul_add]) }

-- `smul_comm_class.symm` is not registered as an instance, as it would cause a loop
instance add_comm_monoid.nat_smul_comm_class' [semimodule ℕ M] : smul_comm_class R ℕ M :=
smul_comm_class.symm _ _ _

end add_comm_monoid

section add_comm_group

variables [semiring S] [ring R] [add_comm_group M] [semimodule S M] [semimodule R M]

/-- The natural ℤ-module structure on any `add_comm_group`. -/
-- We don't immediately make this a global instance, as it results in too many instances,
-- and confusing ambiguity in the notation `n • x` when `n : ℤ`.
-- We do turn it into a global instance, but only at the end of this file,
-- and I remain dubious whether this is a good idea.
def add_comm_group.int_module : module ℤ M :=
{ smul := gsmul,
  smul_add := λ _ _ _, gsmul_add _ _ _,
  add_smul := λ _ _ _, add_gsmul _ _ _,
  mul_smul := λ _ _ _, gsmul_mul _ _ _,
  one_smul := one_gsmul,
  zero_smul := zero_gsmul,
  smul_zero := gsmul_zero }

section
local attribute [instance] add_comm_group.int_module
/-- `gsmul` is defined as the `smul` action of `add_comm_group.int_module`. -/
lemma gsmul_def (n : ℤ) (x : M) : gsmul n x = n • x := rfl
end

section
variables (R)
/-- `gsmul` is equal to any other module structure via a cast. -/
lemma gsmul_eq_smul_cast (n : ℤ) (b : M) : gsmul n b = (n : R) • b :=
begin
  rw gsmul_def,
  induction n using int.induction_on with p hp n hn,
  { rw [int.cast_zero, zero_smul, zero_smul] },
  { rw [int.cast_add, int.cast_one, add_smul, add_smul, one_smul, one_smul, hp] },
  { rw [int.cast_sub, int.cast_one, sub_smul, sub_smul, one_smul, one_smul, hn] },
end
end

/-- `gsmul` is equal to any `ℤ`-module structure. -/
lemma gsmul_eq_smul [semimodule ℤ M] (n : ℤ) (b : M) : n •ℤ b = n • b :=
by rw [gsmul_eq_smul_cast ℤ, n.cast_id]

/-- All `ℤ`-module structures are equal. -/
instance add_comm_group.int_module.subsingleton : subsingleton (semimodule ℤ M) :=
⟨λ P Q, by {
  ext n,
  rw [←gsmul_eq_smul, ←gsmul_eq_smul], }⟩

instance add_comm_group.int_is_scalar_tower [semimodule ℤ R] [semimodule ℤ M] :
  is_scalar_tower ℤ R M :=
{ smul_assoc := λ n x y, int.induction_on n
    (by simp only [zero_smul])
    (λ n ih, by simp only [one_smul, add_smul, ih])
    (λ n ih, by simp only [one_smul, sub_smul, ih]) }

instance add_comm_group.int_smul_comm_class [semimodule ℤ M] : smul_comm_class ℤ S M :=
{ smul_comm := λ n x y, int.induction_on n
    (by simp only [zero_smul, smul_zero])
    (λ n ih, by simp only [one_smul, add_smul, smul_add, ih])
    (λ n ih, by simp only [one_smul, sub_smul, smul_sub, ih]) }

-- `smul_comm_class.symm` is not registered as an instance, as it would cause a loop
instance add_comm_group.int_smul_comm_class' [semimodule ℤ M] : smul_comm_class S ℤ M :=
smul_comm_class.symm _ _ _

end add_comm_group

namespace add_monoid_hom

-- We prove this without using the `add_comm_group.int_module` instance, so the `•`s here
-- come from whatever the local `module ℤ` structure actually is.
lemma map_int_module_smul
  [add_comm_group M] [add_comm_group M₂]
  [module ℤ M] [module ℤ M₂] (f : M →+ M₂) (x : ℤ) (a : M) : f (x • a) = x • f a :=
by simp only [←gsmul_eq_smul, f.map_gsmul]

lemma map_int_cast_smul
  [ring R] [add_comm_group M] [add_comm_group M₂] [module R M] [module R M₂]
  (f : M →+ M₂) (x : ℤ) (a : M) : f ((x : R) • a) = (x : R) • f a :=
by simp only [←gsmul_eq_smul_cast, f.map_gsmul]

lemma map_nat_cast_smul
  [semiring R] [add_comm_monoid M] [add_comm_monoid M₂]
  [semimodule R M] [semimodule R M₂] (f : M →+ M₂) (x : ℕ) (a : M) :
  f ((x : R) • a) = (x : R) • f a :=
by simp only [←nsmul_eq_smul_cast, f.map_nsmul]

lemma map_rat_cast_smul {R : Type*} [division_ring R] [char_zero R]
  {E : Type*} [add_comm_group E] [module R E] {F : Type*} [add_comm_group F] [module R F]
  (f : E →+ F) (c : ℚ) (x : E) :
  f ((c : R) • x) = (c : R) • f x :=
begin
  have : ∀ (x : E) (n : ℕ), 0 < n → f (((n⁻¹ : ℚ) : R) • x) = ((n⁻¹ : ℚ) : R) • f x,
  { intros x n hn,
    replace hn : (n : R) ≠ 0 := nat.cast_ne_zero.2 (ne_of_gt hn),
    conv_rhs { congr, skip, rw [← one_smul R x, ← mul_inv_cancel hn, mul_smul] },
    rw [f.map_nat_cast_smul, smul_smul, rat.cast_inv, rat.cast_coe_nat,
      inv_mul_cancel hn, one_smul] },
  refine c.num_denom_cases_on (λ m n hn hmn, _),
  rw [rat.mk_eq_div, div_eq_mul_inv, rat.cast_mul, int.cast_coe_nat, mul_smul, mul_smul,
    rat.cast_coe_int, f.map_int_cast_smul, this _ n hn]
end

lemma map_rat_module_smul {E : Type*} [add_comm_group E] [vector_space ℚ E]
  {F : Type*} [add_comm_group F] [module ℚ F] (f : E →+ F) (c : ℚ) (x : E) :
  f (c • x) = c • f x :=
rat.cast_id c ▸ f.map_rat_cast_smul c x

@[simp] lemma nat_smul_apply [add_monoid M] [add_comm_monoid M₂]
  [semimodule ℕ (M →+ M₂)] [semimodule ℕ M₂]
  (n : ℕ) (f : M →+ M₂) (a : M) :
  (n • f) a = n • (f a) :=
begin
  induction n with n IH,
  { simp only [zero_smul, zero_apply] },
  { simp only [nat.succ_eq_add_one, add_smul, IH, one_smul, add_apply] }
end

@[simp] lemma int_smul_apply [add_monoid M] [add_comm_group M₂]
  [module ℤ (M →+ M₂)] [module ℤ M₂]
  (n : ℤ) (f : M →+ M₂) (a : M) :
  (n • f) a = n • (f a) :=
begin
  apply int.induction_on' n 0,
  { simp only [zero_smul, zero_apply] },
  all_goals
  { intros k hk IH,
    simp only [add_smul, sub_smul, IH, one_smul, add_apply, sub_apply] }
end

end add_monoid_hom

section module_division_ring
/-! Some tests for the vanishing of elements in modules over division rings. -/

variables (R) [division_ring R] [add_comm_group M] [module R M]

lemma smul_nat_eq_zero [semimodule ℕ M] [char_zero R] {v : M} {n : ℕ} :
  n • v = 0 ↔ n = 0 ∨ v = 0 :=
by { rw [←nsmul_eq_smul, nsmul_eq_smul_cast R, smul_eq_zero], simp }

lemma eq_zero_of_smul_two_eq_zero [semimodule ℕ M] [char_zero R] {v : M} (hv : 2 • v = 0) : v = 0 :=
((smul_nat_eq_zero R).mp hv).resolve_left (by norm_num)

lemma eq_zero_of_eq_neg [char_zero R] {v : M} (hv : v = - v) : v = 0 :=
begin
  -- any semimodule will do
  haveI : semimodule ℕ M := add_comm_monoid.nat_semimodule,
  refine eq_zero_of_smul_two_eq_zero R _,
  rw ←nsmul_eq_smul,
  convert add_eq_zero_iff_eq_neg.mpr hv,
  abel
end

lemma ne_neg_of_ne_zero [char_zero R] {v : R} (hv : v ≠ 0) : v ≠ -v :=
λ h, have semimodule ℕ R := add_comm_monoid.nat_semimodule, by exactI hv (eq_zero_of_eq_neg R h)

end module_division_ring

-- We finally turn on these instances globally. By doing this here, we ensure that none of the
-- lemmas about nat semimodules above are specific to these instances.
attribute [instance] add_comm_monoid.nat_semimodule add_comm_group.int_module
