/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.module.pi
import algebra.ordered_pi
import algebra.module.prod

/-!
# Ordered semimodules

In this file we define

* `ordered_semimodule R M` : an ordered additive commutative monoid `M` is an `ordered_semimodule`
  over an `ordered_semiring` `R` if the scalar product respects the order relation on the
  monoid and on the ring. There is a correspondence between this structure and convex cones,
  which is proven in `analysis/convex/cone.lean`.

## Implementation notes

* We choose to define `ordered_semimodule` as a `Prop`-valued mixin, so that it can be
  used for both modules and algebras
  (the axioms for an "ordered algebra" are exactly that the algebra is ordered as a module).
* To get ordered modules and ordered vector spaces, it suffices to the replace the
  `order_add_comm_monoid` and the `ordered_semiring` as desired.

## References

* https://en.wikipedia.org/wiki/Ordered_vector_space

## Tags

ordered semimodule, ordered module, ordered vector space
-/


/--
An ordered semimodule is an ordered additive commutative monoid
with a partial order in which the scalar multiplication is compatible with the order.
-/
@[protect_proj, ancestor semimodule]
class ordered_semimodule (R M : Type*)
  [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] : Prop :=
(smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, a < b → 0 < c → c • a < c • b)
(lt_of_smul_lt_smul_of_pos : ∀ {a b : M}, ∀ {c : R}, c • a < c • b → 0 < c → a < b)

section ordered_semimodule

variables {R M : Type*}
  [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M] [ordered_semimodule R M]
  {a b : M} {c : R}

lemma smul_lt_smul_of_pos : a < b → 0 < c → c • a < c • b := ordered_semimodule.smul_lt_smul_of_pos

lemma smul_le_smul_of_nonneg (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c • a ≤ c • b :=
begin
  by_cases H₁ : c = 0,
  { simp [H₁, zero_smul] },
  { by_cases H₂ : a = b,
    { rw H₂ },
    { exact le_of_lt
        (smul_lt_smul_of_pos (lt_of_le_of_ne h₁ H₂) (lt_of_le_of_ne h₂ (ne.symm H₁))), } }
end

lemma eq_of_smul_eq_smul_of_pos_of_le (h₁ : c • a = c • b) (hc : 0 < c) (hle : a ≤ b) :
  a = b :=
hle.lt_or_eq.resolve_left $ λ hlt, (smul_lt_smul_of_pos hlt hc).ne h₁

lemma lt_of_smul_lt_smul_of_nonneg (h : c • a < c • b) (hc : 0 ≤ c) : a < b :=
hc.eq_or_lt.elim (λ hc, false.elim $ lt_irrefl (0:M) $ by rwa [← hc, zero_smul, zero_smul] at h)
  (ordered_semimodule.lt_of_smul_lt_smul_of_pos h)

lemma smul_lt_smul_iff_of_pos (hc : 0 < c) : c • a < c • b ↔ a < b :=
⟨λ h, lt_of_smul_lt_smul_of_nonneg h hc.le, λ h, smul_lt_smul_of_pos h hc⟩

lemma smul_pos_iff_of_pos (hc : 0 < c) : 0 < c • a ↔ 0 < a :=
calc 0 < c • a ↔ c • 0 < c • a : by rw smul_zero
           ... ↔ 0 < a         : smul_lt_smul_iff_of_pos hc

end ordered_semimodule

/-- If `R` is a linear ordered semifield, then it suffices to verify only the first axiom of
`ordered_semimodule`. Moreover, it suffices to verify that `a < b` and `0 < c` imply
`c • a ≤ c • b`. We have no semifields in `mathlib`, so we use the assumption `∀ c ≠ 0, is_unit c`
instead. -/
lemma ordered_semimodule.mk'' {R M : Type*} [linear_ordered_semiring R] [ordered_add_comm_monoid M]
  [semimodule R M] (hR : ∀ {c : R}, c ≠ 0 → is_unit c)
  (hlt : ∀ ⦃a b : M⦄ ⦃c : R⦄, a < b → 0 < c → c • a ≤ c • b) :
  ordered_semimodule R M :=
begin
  have hlt' : ∀ ⦃a b : M⦄ ⦃c : R⦄, a < b → 0 < c → c • a < c • b,
  { refine λ a b c hab hc, (hlt hab hc).lt_of_ne _,
    rw [ne.def, (hR hc.ne').smul_left_cancel],
    exact hab.ne },
  refine { smul_lt_smul_of_pos := hlt', .. },
  intros a b c h hc,
  rcases (hR hc.ne') with ⟨c, rfl⟩,
  rw [← c.inv_smul_smul a, ← c.inv_smul_smul b],
  refine hlt' h (pos_of_mul_pos_left _ hc.le),
  simp only [c.mul_inv, zero_lt_one]
end

/-- If `R` is a linear ordered field, then it suffices to verify only the first axiom of
`ordered_semimodule`. -/
lemma ordered_semimodule.mk' {k M : Type*} [linear_ordered_field k] [ordered_add_comm_monoid M]
  [semimodule k M] (hlt : ∀ ⦃a b : M⦄ ⦃c : k⦄, a < b → 0 < c → c • a ≤ c • b) :
  ordered_semimodule k M :=
ordered_semimodule.mk'' (λ c hc, is_unit.mk0 _ hc) hlt

instance linear_ordered_semiring.to_ordered_semimodule  {R : Type*} [linear_ordered_semiring R] :
  ordered_semimodule R R :=
{ smul_lt_smul_of_pos        := ordered_semiring.mul_lt_mul_of_pos_left,
  lt_of_smul_lt_smul_of_pos  := λ _ _ _ h hc, lt_of_mul_lt_mul_left h hc.le }

section field

variables {k M N : Type*} [linear_ordered_field k]
  [ordered_add_comm_group M] [semimodule k M] [ordered_semimodule k M]
  [ordered_add_comm_group N] [semimodule k N] [ordered_semimodule k N]
  {a b : M} {c : k}

lemma smul_le_smul_iff_of_pos (hc : 0 < c) : c • a ≤ c • b ↔ a ≤ b :=
⟨λ h, inv_smul_smul' hc.ne' a ▸ inv_smul_smul' hc.ne' b ▸
  smul_le_smul_of_nonneg h (inv_nonneg.2 hc.le),
  λ h, smul_le_smul_of_nonneg h hc.le⟩

lemma smul_le_smul_iff_of_neg (hc : c < 0) : c • a ≤ c • b ↔ b ≤ a :=
begin
  rw [← neg_neg c, neg_smul, neg_smul (-c), neg_le_neg_iff, smul_le_smul_iff_of_pos (neg_pos.2 hc)],
  apply_instance,
end

lemma smul_lt_iff_of_pos (hc : 0 < c) : c • a < b ↔ a < c⁻¹ • b :=
calc c • a < b ↔ c • a < c • c⁻¹ • b : by rw [smul_inv_smul' hc.ne']
... ↔ a < c⁻¹ • b : smul_lt_smul_iff_of_pos hc

lemma smul_le_iff_of_pos (hc : 0 < c) : c • a ≤ b ↔ a ≤ c⁻¹ • b :=
calc c • a ≤ b ↔ c • a ≤ c • c⁻¹ • b : by rw [smul_inv_smul' hc.ne']
... ↔ a ≤ c⁻¹ • b : smul_le_smul_iff_of_pos hc

lemma le_smul_iff_of_pos (hc : 0 < c) : a ≤ c • b ↔ c⁻¹ • a ≤ b :=
calc a ≤ c • b ↔ c • c⁻¹ • a ≤ c • b : by rw [smul_inv_smul' hc.ne']
... ↔ c⁻¹ • a ≤ b : smul_le_smul_iff_of_pos hc

instance prod.ordered_semimodule : ordered_semimodule k (M × N) :=
ordered_semimodule.mk' $ λ v u c h hc,
  ⟨smul_le_smul_of_nonneg h.1.1 hc.le, smul_le_smul_of_nonneg h.1.2 hc.le⟩

instance pi.ordered_semimodule {ι : Type*} {M : ι → Type*} [Π i, ordered_add_comm_group (M i)]
  [Π i, semimodule k (M i)] [∀ i, ordered_semimodule k (M i)] :
  ordered_semimodule k (Π i : ι, M i) :=
begin
  refine (ordered_semimodule.mk' $ λ v u c h hc i, _),
  change c • v i ≤ c • u i,
  exact smul_le_smul_of_nonneg (h.le i) hc.le,
end

-- Sometimes Lean fails to apply the dependent version to non-dependent functions,
-- so we define another instance
instance pi.ordered_semimodule' {ι : Type*} {M : Type*} [ordered_add_comm_group M]
  [semimodule k M] [ordered_semimodule k M] :
  ordered_semimodule k (ι → M) :=
pi.ordered_semimodule

end field


section order_dual

variables {R M : Type*}

instance [semiring R] [ordered_add_comm_monoid M] [semimodule R M] : has_scalar R (order_dual M) :=
{ smul := @has_scalar.smul R M _ }

instance [semiring R] [ordered_add_comm_monoid M] [semimodule R M] : mul_action R (order_dual M) :=
{ one_smul := @mul_action.one_smul R M _ _,
  mul_smul := @mul_action.mul_smul R M _ _ }

instance [semiring R] [ordered_add_comm_monoid M] [semimodule R M] :
  distrib_mul_action R (order_dual M) :=
{ smul_add := @distrib_mul_action.smul_add R M _ _ _,
  smul_zero := @distrib_mul_action.smul_zero R M _ _ _ }

instance [semiring R] [ordered_add_comm_monoid M] [semimodule R M] : semimodule R (order_dual M) :=
{ add_smul := @semimodule.add_smul R M _ _ _,
  zero_smul := @semimodule.zero_smul R M _ _ _ }

instance [ordered_semiring R] [ordered_add_comm_monoid M] [semimodule R M]
  [ordered_semimodule R M] :
  ordered_semimodule R (order_dual M) :=
{ smul_lt_smul_of_pos := λ a b, @ordered_semimodule.smul_lt_smul_of_pos R M _ _ _ _ b a,
  lt_of_smul_lt_smul_of_pos := λ a b,
    @ordered_semimodule.lt_of_smul_lt_smul_of_pos R M _ _ _ _ b a }

end order_dual
