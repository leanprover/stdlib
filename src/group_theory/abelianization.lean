/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Michael Howes

The functor Grp → Ab which is the left adjoint
of the forgetful functor Ab → Grp.
-/

import group_theory.quotient_group
import tactic.group

-- IMPLEMENTATION ISSUE WARNING
-- WE USED TO DO SUBGROUPS USING `is_subgroup`, -- WE
-- NOW DO THEM USING `subgroup`

-- mathematicians can ignore this
universes u v

-- let G be a group
variables (G : Type u) [group G]

-- this is bad style. This is a definition, so it should have a docstring
/-- The commutator subgroup of a group G is the normal subgroup
  generated by the commutators [p,q]=`p*q*p⁻¹*q⁻¹` -/
@[derive subgroup.normal]
def commutator : subgroup G :=
subgroup.normal_closure {x | ∃ p q, p * q * p⁻¹ * q⁻¹ = x}

/-- The abelianization of G is the quotient of G by its commutator subgroup -/
def abelianization : Type u :=
quotient_group.quotient (commutator G)

namespace abelianization
-- in here we will prove theorems about the abelianization of a group.

local attribute [instance] quotient_group.left_rel

instance : comm_group (abelianization G) :=
{ mul_comm := λ x y, quotient.induction_on₂' x y $ λ a b,
  begin
    apply quotient.sound,
    clear x y,
    show (a * b)⁻¹ * (b * a) ∈ commutator G,
    apply subgroup.subset_normal_closure,
    dsimp,
    use b⁻¹, use a⁻¹,
    group, -- an algorithm to solve questions like this
    -- advert. Interested in building an algorithm to
    -- solve questions in group theory like this?
    -- Do and do my exercises in my Wednesday LFTCM session
  end,
.. quotient_group.group _ }

instance : inhabited (abelianization G) := ⟨1⟩

variable {G}

/-- `of` is the canonical projection from G to its abelianization. -/
def of : G →* abelianization G :=
{ to_fun := quotient_group.mk,
  map_one' := rfl,
  map_mul' := λ x y, rfl }

section lift
-- so far -- built Gᵃᵇ and proved it's an abelian group.
-- defined `of : G → Gᵃᵇ`

-- let A be an abelian group and let f be a group hom from G to A
variables {A : Type v} [comm_group A] (f : G →* A)

lemma commutator_subset_ker : commutator G ≤ f.ker :=
-- proving this lemma is like solving a puzzle
begin
  /- G gp, A ab gp, f : G → A group hom.
    wanna prove commutator of H is contained in the kernel of f.
    maths proof: commutator is generated by things of the form xyx⁻¹y⁻¹
    so just need to check on commutators.
    apply f, we get `f(x)*f(y)*f(x⁻¹)*f(y⁻¹)` and this is in an abelian
    group so it's 1.
  -/
  apply subgroup.normal_closure_le_normal,
  { apply_instance },
  { intros x,
    dsimp,
    rintros ⟨p, q, rfl⟩,
    norm_cast,
    rw monoid_hom.mem_ker,
    simp,
    -- annoying that there was no comm_group tactic.
    rw mul_right_comm,
    simp }
end
-- subgroup.normal_closure_le_normal (by apply_instance) (λ x ⟨p,q,w⟩, (is_group_hom.mem_ker f).2
--   (by {rw ←w, simp [is_mul_hom.map_mul f, is_group_hom.map_inv f, mul_comm]}))

-- -- FIXME why is the apply_instance needed?

-- goal: if G -> A is a group hom, then it factors through G^ᵃᵇ
-- this is the universal property of the abelianization
def lift : abelianization G →* A :=
quotient_group.lift _ f (λ x h, sorry)

@[simp] lemma lift.of (x : G) : lift f (of x) = f x :=
rfl

theorem lift.unique
  (g : abelianization G →* A)
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
quotient_group.induction_on x hg

end lift

end abelianization
