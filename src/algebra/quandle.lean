/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.zmod.basic
import tactic.group

/-!
# Racks and Quandles

This file defines racks and quandles, algebraic structures for sets
that bijectively act on themselves with a self-distributivity
property.  If `R` is a rack and `act : R → (R ≃ R)` is the self-action,
then the self-distributivity is, equivalently, that
```
act (act x y) = act x * act y * (act x)⁻¹
```
where multiplication is composition in `R ≃ R` as a group.
Quandles are racks such that `act x x = x` for all `x`.

One example of a quandle (not yet in mathlib) is the action of a Lie
algebra on itself, defined by `act x y = Ad (exp x) y`.

Quandles and racks were independently developed by multiple
mathematicians.  David Joyce introduced quandles in his thesis
[Joyce1982] to define an algebraic invariant of knot and link
complements that is analogous to the fundamental group of the
exterior, and he showed that the quandle associated to an oriented
knot is invariant up to orientation-reversed mirror image.  Racks were
used by Fenn and Rourke for framed codimension-2 knots and
links.[FennRourke1992]

The name "rack" came from wordplay by Conway and Wraith for the "wrack
and ruin" of forgetting everything but the conjugation operation for a
group.

## Main definitions

* `shelf` is a type with a self-distributive action
* `rack` is a shelf whose action for each element is invertible
* `quandle` is a rack whose action for an element fixes that element
* `quandle.conj` defines a quandle of a group acting on itself by conjugation.
* `shelf_hom` is homomorphisms of shelves, racks, and quandles.
* `rack.envel_group` gives the universal group the rack maps to as a conjugation quandle.
* `rack.opp` gives the rack with the action replaced by its inverse.

## Main statements
* `rack.envel_group` is left adjoint to `quandle.conj` (`to_envel_group.map`).
  The universality statements are `to_envel_group.univ` and `to_envel_group.univ_uniq`.

## Notation

The following notation is localized in `quandles`:

* `x ◃ y` is `shelf.act x y`
* `x ◃⁻¹ y` is `rack.inv_act x y`
* `S →◃ S'` is `shelf_hom S S'`

Use `open_locale quandles` to use these.

## Todo

* If g is the Lie algebra of a Lie group G, then (x ◃ y) = Ad (exp x) x forms a quandle
* If X is a symmetric space, then each point has a corresponding involution that acts on X, forming a quandle.
* Alexander quandle with `a ◃ b = t * b + (1 - t) * b`, with `a` and `b` elements of a module over Z[t,t⁻¹].
* If G is a group, H a subgroup, and z in H, then there is a quandle `(G/H;z)` defined by
  `yH ◃ xH = yzy⁻¹xH`.  Every homogeneous quandle (i.e., a quandle Q whose automorphism group acts
  transitively on Q as a set) is isomorphic to such a quandle.
  There is a generalization to this arbitrary quandles in [Joyce's paper (Theorem 7.2)][Joyce1982].

## Tags

rack, quandle
-/
open opposite

universes u v

/--
A *shelf* is a structure with a self-distributive binary operation.
The binary operation is regarded as a left action of the type on itself.
-/
class shelf (α : Type u) :=
(act : α → α → α)
(self_distrib : ∀ {x y z : α}, act x (act y z) = act (act x y) (act x z))

/--
The type of homomorphisms between shelves.
This is also the notion of rack and quandle homomorphisms.
-/
@[ext]
structure shelf_hom (S₁ : Type*) (S₂ : Type*) [shelf S₁] [shelf S₂] :=
(to_fun : S₁ → S₂)
(map_act' : ∀ {x y : S₁}, to_fun (shelf.act x y) = shelf.act (to_fun x) (to_fun y))

/--
A *rack* is an automorphic set (a set with an action on itself by
bijections) that is self-distributive.  It is a shelf such that each
element's action is invertible.

The notations `x ◃ y` and `x ◃⁻¹ y` denote the action and the
inverse action, respectively, and they are right associative.
-/
class rack (α : Type u) extends shelf α :=
(inv_act : α → α → α)
(left_inv : ∀ x, function.left_inverse (inv_act x) (act x))
(right_inv : ∀ x, function.right_inverse (inv_act x) (act x))

localized "infixr ` ◃ `:65 := shelf.act" in quandles
localized "infixr ` ◃⁻¹ `:65 := rack.inv_act" in quandles
localized "infixr ` →◃ `:25 := shelf_hom" in quandles

open_locale quandles

namespace rack
variables {R : Type*} [rack R]

lemma self_distrib {x y z : R} : x ◃ (y ◃ z) = (x ◃ y) ◃ (x ◃ z) :=
shelf.self_distrib

/--
A rack acts on itself by equivalences.
-/
def act (x : R) : R ≃ R :=
{ to_fun := shelf.act x,
  inv_fun := inv_act x,
  left_inv := left_inv x,
  right_inv := right_inv x }

@[simp] lemma act_apply (x y : R) : act x y = x ◃ y := rfl
@[simp] lemma act_symm_apply (x y : R) : (act x).symm y = x ◃⁻¹ y := rfl
@[simp] lemma inv_act_apply (x y : R) : (act x)⁻¹ y = x ◃⁻¹ y := rfl

@[simp] lemma inv_act_act_eq (x y : R) : x ◃⁻¹ x ◃ y = y := left_inv x y
@[simp] lemma act_inv_act_eq (x y : R) : x ◃ x ◃⁻¹ y = y := right_inv x y

lemma left_cancel (x : R) {y y' : R} : x ◃ y = x ◃ y' ↔ y = y' :=
by { split, apply (act x).injective, rintro rfl, refl }

lemma left_cancel_inv (x : R) {y y' : R} : x ◃⁻¹ y = x ◃⁻¹ y' ↔ y = y' :=
by { split, apply (act x).symm.injective, rintro rfl, refl }

lemma self_distrib_inv {x y z : R} : x ◃⁻¹ y ◃⁻¹ z = (x ◃⁻¹ y) ◃⁻¹ (x ◃⁻¹ z) :=
begin
  rw [←left_cancel (x ◃⁻¹ y), right_inv, ←left_cancel x, right_inv, self_distrib],
  repeat {rw right_inv },
end

/--
The *adjoint action* of a rack on itself is `op'`, and the adjoint
action of `x ◃ y` is the conjugate of the action of `y` by the action
of `x`. It is another way to understand the self-distributivity axiom.

This is used in the natural rack homomorphism `to_conj` from `R` to
`conj (R ≃ R)` defined by `op'`.
-/
lemma ad_conj {R : Type*} [rack R] (x y : R) :
  act (x ◃ y) = act x * act y * (act x)⁻¹ :=
begin
  apply @mul_right_cancel _ _ _ (act x), ext z,
  simp only [inv_mul_cancel_right],
  apply self_distrib.symm,
end

/--
The opposite rack, swapping the roles of `◃` and `◃⁻¹`.
-/
instance opposite_rack : rack Rᵒᵖ :=
{ act := λ x y, op (inv_act (unop x) (unop y)),
  self_distrib := λ (x y z : Rᵒᵖ), begin
    op_induction x, op_induction y, op_induction z,
    simp only [unop_op, op_inj_iff],
    exact self_distrib_inv,
  end,
  inv_act := λ x y, op (shelf.act (unop x) (unop y)),
  left_inv := λ x y, begin
    op_induction x, op_induction y, simp,
  end,
  right_inv := λ x y, begin
    op_induction x, op_induction y, simp,
  end }

@[simp] lemma op_act_op_eq {x y : R} : (op x) ◃ (op y) = op (x ◃⁻¹ y) := rfl
@[simp] lemma op_inv_act_op_eq {x y : R} : (op x) ◃⁻¹ (op y) = op (x ◃ y) := rfl

@[simp]
lemma self_act_act_eq {x y : R} : (x ◃ x) ◃ y = x ◃ y :=
by { rw [←right_inv x y, ←self_distrib] }

@[simp]
lemma self_inv_act_inv_act_eq {x y : R} : (x ◃⁻¹ x) ◃⁻¹ y = x ◃⁻¹ y :=
by { have h := @self_act_act_eq _ _ (op x) (op y), simpa using h }

@[simp]
lemma self_act_inv_act_eq {x y : R} : (x ◃ x) ◃⁻¹ y = x ◃⁻¹ y :=
by { rw ←left_cancel (x ◃ x), rw right_inv, rw self_act_act_eq, rw right_inv }

@[simp]
lemma self_inv_act_act_eq {x y : R} : (x ◃⁻¹ x) ◃ y = x ◃ y :=
by { have h := @self_act_inv_act_eq _ _ (op x) (op y), simpa using h }

lemma self_act_eq_iff_eq {x y : R} : x ◃ x = y ◃ y ↔ x = y :=
begin
  split, swap, rintro rfl, refl,
  intro h,
  transitivity (x ◃ x) ◃⁻¹ (x ◃ x),
  rw [←left_cancel (x ◃ x), right_inv, self_act_act_eq],
  rw [h, ←left_cancel (y ◃ y), right_inv, self_act_act_eq],
end

lemma self_inv_act_eq_iff_eq {x y : R} : x ◃⁻¹ x = y ◃⁻¹ y ↔ x = y :=
by { have h := @self_act_eq_iff_eq _ _ (op x) (op y), simpa using h }

/--
The map `x ↦ x ◃ x` is a bijection.  (This has applications for the
regular isotopy version of the Reidemeister I move for knot diagrams.)
-/
def self_apply_equiv (R : Type*) [rack R] : R ≃ R :=
{ to_fun := λ x, x ◃ x,
  inv_fun := λ x, x ◃⁻¹ x,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp }

/--
An involutory rack is one for which `rack.op R x` is an involution for every x.
-/
def is_involutory (R : Type*) [rack R] : Prop := ∀ x : R, function.involutive (shelf.act x)

lemma involutory_inv_act_eq_act {R : Type*} [rack R] (h : is_involutory R) (x y : R) :
  x ◃⁻¹ y = x ◃ y :=
begin
  rw [←left_cancel x, right_inv],
  exact ((h x).left_inverse y).symm,
end

/--
An abelian rack is one for which the mediality axiom holds.
-/
def is_abelian (R : Type*) [rack R] : Prop :=
∀ (x y z w : R), (x ◃ y) ◃ (z ◃ w) = (x ◃ z) ◃ (y ◃ w)

/--
Associative racks are uninteresting.
-/
lemma assoc_iff_id {R : Type*} [rack R] {x y z : R} :
  x ◃ y ◃ z = (x ◃ y) ◃ z ↔ x ◃ z = z :=
by { rw self_distrib, rw left_cancel }

end rack

namespace shelf_hom
variables {S₁ : Type*} {S₂ : Type*} {S₃ : Type*} [shelf S₁] [shelf S₂] [shelf S₃]

instance : has_coe_to_fun (S₁ →◃ S₂) :=
⟨_, shelf_hom.to_fun⟩

@[simp] lemma to_fun_eq_coe (f : S₁ →◃ S₂) : f.to_fun = f := rfl

@[simp] lemma map_act (f : S₁ →◃ S₂) {x y : S₁} : f (x ◃ y) = f x ◃ f y := map_act' f

/-- The identity homomorphism -/
def id (S : Type*) [shelf S] : S →◃ S :=
{ to_fun := id,
  map_act' := by simp }

instance inhabited (S : Type*) [shelf S] : inhabited (S →◃ S) :=
⟨id S⟩

/-- The composition of shelf homomorphisms -/
def comp (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) : S₁ →◃ S₃ :=
{ to_fun := g.to_fun ∘ f.to_fun,
  map_act' := by simp }

@[simp]
lemma comp_apply (g : S₂ →◃ S₃) (f : S₁ →◃ S₂) (x : S₁) :
  (g.comp f) x = g (f x) := rfl

end shelf_hom

/--
A quandle is a rack such that each automorphism fixes its corresponding element.
-/
class quandle (α : Type*) extends rack α :=
(fix : ∀ {x : α}, act x x = x)

namespace quandle
open rack
variables {Q : Type*} [quandle Q]

attribute [simp] fix

@[simp]
lemma fix_inv {x : Q} : x ◃⁻¹ x = x :=
by { rw ←left_cancel x, simp }

instance opposite_quandle : quandle Qᵒᵖ :=
{ fix := λ x, by { op_induction x, simp } }

/--
The conjugation quandle of a group.  Each element of the group acts by
the corresponding inner automorphism.
-/
@[nolint has_inhabited_instance]
def conj (G : Type*) := G

instance conj.quandle (G : Type*) [group G] : quandle (conj G) :=
{ act := (λ x, @mul_aut.conj G _ x),
  self_distrib := λ x y z, begin
    dsimp only [mul_equiv.to_equiv_apply, mul_aut.conj_apply, conj],
    group,
  end,
  inv_act := (λ x, (@mul_aut.conj G _ x).symm),
  left_inv := λ x y, by { dsimp [act, conj], group },
  right_inv := λ x y, by { dsimp [act, conj], group },
  fix := λ x, by simp }

@[simp]
lemma conj_act_eq_conj {G : Type*} [group G] (x y : conj G) :
  x ◃ y = ((x : G) * (y : G) * (x : G)⁻¹ : G) := rfl

lemma conj_swap {G : Type*} [group G] (x y : conj G) :
  x ◃ y = y ↔ y ◃ x = x :=
begin
  dsimp, split,
  repeat { intro h, conv_rhs { rw eq_mul_inv_of_mul_eq (eq_mul_inv_of_mul_eq h) }, simp, },
end

/--
`conj` is functorial
-/
def conj.map {G : Type*} {H : Type*} [group G] [group H] (f : G →* H) : conj G →◃ conj H :=
{ to_fun := f,
  map_act' := by simp }

instance {G : Type*} {H : Type*} [group G] [group H] : has_lift (G →* H) (conj G →◃ conj H) :=
{ lift := conj.map }

/--
The dihedral quandle. This is the conjugation quandle of the dihedral group restrict to flips.

Used for Fox n-colorings of knots.
-/
@[nolint has_inhabited_instance]
def dihedral (n : ℕ) := zmod n

/--
The operation for the dihedral quandle.  It does not need to be an equivalence
because it is an involution (see `dihedral_act.inv`).
-/
def dihedral_act (n : ℕ) (a : zmod n) : zmod n → zmod n :=
λ b, 2 * a - b

lemma dihedral_act.inv (n : ℕ) (a : zmod n) : function.involutive (dihedral_act n a) :=
by { intro b, dsimp [dihedral_act], ring }

instance (n : ℕ) : quandle (dihedral n) :=
{ act := dihedral_act n,
  self_distrib := λ x y z, begin
    dsimp [function.involutive.to_equiv, dihedral_act], ring,
  end,
  inv_act := dihedral_act n,
  left_inv := λ x, (dihedral_act.inv n x).left_inverse,
  right_inv := λ x, (dihedral_act.inv n x).right_inverse,
  fix := λ x, begin
    dsimp [function.involutive.to_equiv, dihedral_act], ring,
  end }

end quandle

namespace rack

/--
This is the natural rack homomorphism to the conjugation quandle of the group `R ≃ R`
that acts on the rack.
-/
def to_conj (R : Type*) [rack R] : R →◃ quandle.conj (R ≃ R) :=
{ to_fun := act,
  map_act' := ad_conj }

section envel_group

/-!
### Universal enveloping group of a rack

The universal enveloping group `envel_group R` of a rack `R` is the
universal group such that every rack homomorphism `R →◃ conj G` is
induced by a unique group homomorphism `envel_group R →* G`.
For quandles, Joyce called this group `AdConj R`.

The `envel_group` functor is left adjoint to the `conj` forgetful
functor, and the way we construct the enveloping group is via a
technique that should work for left adjoints of forgetful functors in
general.  It involves thinking a little about 2-categories, but the
payoff is that the map `envel_group R →* G` has a nice description.

Let's think of a group as being a one-object category.  The first step
is to define `pre_envel_group`, which gives formal expressions for all
the 1-morphisms and includes the unit element, elements of `R`,
multiplication, and inverses.  To introduce relations, the second step
is to define `pre_envel_group_rel'`, which gives formal expressions
for all 2-morphisms between the 1-morphisms.  The 2-morphisms include
associativity, multiplication by the unit, multiplication by inverses,
compatibility with multiplication and inverses (`congr_mul` and
`congr_inv`), the axioms for an equivalence relation, and,
importantly, the relationship between conjugation and the rack action
(see `rack.ad_conj`).

None of this forms a 2-category yet, for example due to lack of
associativity of `trans`.  The `pre_envel_group_rel` relation is a
`Prop`-valued version of `pre_envel_group_rel'`, and making it
`Prop`-valued essentially introduces enough 3-isomorphisms so that
every pair of compatible 2-morphisms is isomorphic.  Now, while
composition in `pre_envel_group` does not strictly satisfy the category
axioms, `pre_envel_group` and `pre_envel_group_rel'` do form a weak
2-category.

Since we just want a 1-category, the last step is to quotient
`pre_envel_group` by `pre_envel_group_rel'`, and the result is the
group `envel_group`.

For a homomorphism `f : R →◃ conj G`, how does
`envel_group.map f : envel_group R →* G` work?  Let's think of `G` as
being a 2-category with one object, a 1-morphism per element of `G`,
and a single 2-morphism called `eq.refl` for each 1-morphism.  We
define the map using a "higher `quotient.lift`" -- not only do we
evaluate elements of `pre_envel_group` as expressions in `G` (this is
`to_envel_group.map_aux`), but we evaluate elements of
`pre_envel_group'` as expressions of 2-morphisms of `G` (this is
`to_envel_group.map_aux.well_def`).  That is to say,
`to_envel_group.map_aux.well_def` recursively evaluates formal
expressions of 2-morphisms as equality proofs in `G`.  Now that all
morphisms are accounted for, the map descends to a homomorphism
`envel_group R →* G`.

Note: `Type`-valued relations are not common.  The fact it is
`Type`-valued is what makes `to_envel_group.map_aux.well_def` have
well-founded recursion.
-/

/--
Free generators of the enveloping group.
-/
inductive pre_envel_group (R : Type u) : Type u
| unit : pre_envel_group
| incl (x : R) : pre_envel_group
| mul (a b : pre_envel_group) : pre_envel_group
| inv (a : pre_envel_group) : pre_envel_group

instance pre_envel_group.inhabited (R : Type u) : inhabited (pre_envel_group R) :=
⟨pre_envel_group.unit⟩

open pre_envel_group

/--
Relations for the enveloping group. This is a type-valued relation because
`to_envel_group.map_aux.well_def` inducts on it to show `to_envel_group.map`
is well-defined.  The relation `pre_envel_group_rel` is the `Prop`-valued version,
which is used to define `envel_group` itself.
-/
inductive pre_envel_group_rel' (R : Type u) [rack R] : pre_envel_group R → pre_envel_group R → Type u
| refl {a : pre_envel_group R} : pre_envel_group_rel' a a
| symm {a b : pre_envel_group R} (hab : pre_envel_group_rel' a b) : pre_envel_group_rel' b a
| trans {a b c : pre_envel_group R}
  (hab : pre_envel_group_rel' a b) (hbc : pre_envel_group_rel' b c) : pre_envel_group_rel' a c
| congr_mul {a b a' b' : pre_envel_group R}
  (ha : pre_envel_group_rel' a a') (hb : pre_envel_group_rel' b b') :
  pre_envel_group_rel' (mul a b) (mul a' b')
| congr_inv {a a' : pre_envel_group R} (ha : pre_envel_group_rel' a a') :
  pre_envel_group_rel' (inv a) (inv a')
| assoc (a b c : pre_envel_group R) : pre_envel_group_rel' (mul (mul a b) c) (mul a (mul b c))
| one_mul (a : pre_envel_group R) : pre_envel_group_rel' (mul unit a) a
| mul_one (a : pre_envel_group R) : pre_envel_group_rel' (mul a unit) a
| mul_left_inv (a : pre_envel_group R) : pre_envel_group_rel' (mul (inv a) a) unit
| act_incl (x y : R) :
  pre_envel_group_rel' (mul (mul (incl x) (incl y)) (inv (incl x))) (incl (x ◃ y))

instance pre_envel_group_rel'.inhabited (R : Type u) [rack R] :
  inhabited (pre_envel_group_rel' R unit unit) :=
⟨pre_envel_group_rel'.refl⟩

/--
The `pre_envel_group_rel` relation as a `Prop`.  Used as the relation for `pre_envel_group.setoid`.
-/
inductive pre_envel_group_rel (R : Type u) [rack R] : pre_envel_group R → pre_envel_group R → Prop
| rel {a b : pre_envel_group R} (r : pre_envel_group_rel' R a b) : pre_envel_group_rel a b

/--
A quick way to convert a `pre_envel_group_rel'` to a `pre_envel_group_rel`.
-/
lemma pre_envel_group_rel'.rel {R : Type u} [rack R] {a b : pre_envel_group R} :
  pre_envel_group_rel' R a b → pre_envel_group_rel R a b :=
pre_envel_group_rel.rel

@[refl]
lemma pre_envel_group_rel.refl {R : Type u} [rack R] {a : pre_envel_group R} :
  pre_envel_group_rel R a a :=
pre_envel_group_rel.rel pre_envel_group_rel'.refl

@[symm]
lemma pre_envel_group_rel.symm {R : Type u} [rack R] {a b : pre_envel_group R} :
  pre_envel_group_rel R a b → pre_envel_group_rel R b a
| ⟨r⟩ := r.symm.rel

@[trans]
lemma pre_envel_group_rel.trans {R : Type u} [rack R] {a b c : pre_envel_group R} :
  pre_envel_group_rel R a b → pre_envel_group_rel R b c → pre_envel_group_rel R a c
| ⟨rab⟩ ⟨rbc⟩ := (rab.trans rbc).rel

instance pre_envel_group.setoid (R : Type*) [rack R] : setoid (pre_envel_group R) :=
{ r := pre_envel_group_rel R,
  iseqv := begin
    split, apply pre_envel_group_rel.refl,
    split, apply pre_envel_group_rel.symm,
    apply pre_envel_group_rel.trans
  end }

/--
The universal enveloping group for the rack R.
-/
def envel_group (R : Type*) [rack R] := quotient (pre_envel_group.setoid R)

-- Define the `group` instances in two steps so `inv` can be inferred correctly.
-- TODO: is there a non-invasive way of defining the instance directly?
instance (R : Type*) [rack R] : div_inv_monoid (envel_group R) :=
{ mul := λ a b, quotient.lift_on₂ a b
                  (λ a b, ⟦pre_envel_group.mul a b⟧)
                  (λ a b a' b' ⟨ha⟩ ⟨hb⟩,
                    quotient.sound (pre_envel_group_rel'.congr_mul ha hb).rel),
  one := ⟦unit⟧,
  inv := λ a, quotient.lift_on a
                (λ a, ⟦pre_envel_group.inv a⟧)
                (λ a a' ⟨ha⟩,
                  quotient.sound (pre_envel_group_rel'.congr_inv ha).rel),
  mul_assoc := λ a b c,
    quotient.induction_on₃ a b c (λ a b c, quotient.sound (pre_envel_group_rel'.assoc a b c).rel),
  one_mul := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_envel_group_rel'.one_mul a).rel),
  mul_one := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_envel_group_rel'.mul_one a).rel),}

instance (R : Type*) [rack R] : group (envel_group R) :=
{ mul_left_inv := λ a,
    quotient.induction_on a (λ a, quotient.sound (pre_envel_group_rel'.mul_left_inv a).rel),
  .. envel_group.div_inv_monoid _ }

instance envel_group.inhabited (R : Type*) [rack R] : inhabited (envel_group R) := ⟨1⟩

/--
The canonical homomorphism from a rack to its enveloping group.
Satisfies universal properties given by `to_envel_group.map` and `to_envel_group.univ`.
-/
def to_envel_group (R : Type*) [rack R] : R →◃ quandle.conj (envel_group R) :=
{ to_fun := λ x, ⟦incl x⟧,
  map_act' := λ x y, quotient.sound (pre_envel_group_rel'.act_incl x y).symm.rel }

/--
The preliminary definition of the induced map from the enveloping group.
See `to_envel_group.map`.
-/
def to_envel_group.map_aux {R : Type*} [rack R] {G : Type*} [group G]
  (f : R →◃ quandle.conj G) : pre_envel_group R → G
| unit := 1
| (incl x) := f x
| (mul a b) := to_envel_group.map_aux a * to_envel_group.map_aux b
| (inv a) := (to_envel_group.map_aux a)⁻¹

namespace to_envel_group.map_aux
open pre_envel_group_rel'

/--
Show that `to_envel_group.map_aux` sends equivalent expressions to equal terms.
-/
lemma well_def {R : Type*} [rack R] {G : Type*} [group G] (f : R →◃ quandle.conj G) :
  Π {a b : pre_envel_group R}, pre_envel_group_rel' R a b →
  to_envel_group.map_aux f a = to_envel_group.map_aux f b
| a b refl := rfl
| a b (symm h) := (well_def h).symm
| a b (trans hac hcb) := eq.trans (well_def hac) (well_def hcb)
| _ _ (congr_mul ha hb) := by { simp [to_envel_group.map_aux, well_def ha, well_def hb] }
| _ _ (congr_inv ha) := by { simp [to_envel_group.map_aux, well_def ha] }
| _ _ (assoc a b c) := by { apply mul_assoc }
| _ _ (one_mul a) := by { simp [to_envel_group.map_aux] }
| _ _ (mul_one a) := by { simp [to_envel_group.map_aux] }
| _ _ (mul_left_inv a) := by { simp [to_envel_group.map_aux] }
| _ _ (act_incl x y) := by { simp [to_envel_group.map_aux] }

end to_envel_group.map_aux

/--
Given a map from a rack to a group, lift it to being a map from the enveloping group.
More precisely, the `envel_group` functor is left adjoint to `quandle.conj`.
-/
def to_envel_group.map {R : Type*} [rack R] {G : Type*} [group G] :
  (R →◃ quandle.conj G) ≃ (envel_group R →* G) :=
{ to_fun := λ f,
  { to_fun := λ x, quotient.lift_on x (to_envel_group.map_aux f)
                    (λ a b ⟨hab⟩, to_envel_group.map_aux.well_def f hab),
    map_one' := begin
      change quotient.lift_on ⟦unit⟧ (to_envel_group.map_aux f) _ = 1,
      simp [to_envel_group.map_aux],
    end,
    map_mul' := λ x y, quotient.induction_on₂ x y (λ x y, begin
      change quotient.lift_on ⟦mul x y⟧ (to_envel_group.map_aux f) _ = _,
      simp [to_envel_group.map_aux],
    end) },
  inv_fun := λ F, (quandle.conj.map F).comp (to_envel_group R),
  left_inv := λ f, by { ext, refl },
  right_inv := λ F, monoid_hom.ext $ λ x, quotient.induction_on x $ λ x, begin
    induction x,
    { exact F.map_one.symm, },
    { refl, },
    { have hm : ⟦x_a.mul x_b⟧ = @has_mul.mul (envel_group R) _ ⟦x_a⟧ ⟦x_b⟧ := rfl,
      rw [hm, F.map_mul, monoid_hom.map_mul, ←x_ih_a, ←x_ih_b] },
    { have hm : ⟦x_a.inv⟧ = @has_inv.inv (envel_group R) _ ⟦x_a⟧ := rfl,
      rw [hm, F.map_inv, monoid_hom.map_inv, x_ih], }
  end, }

/--
Given a homomorphism from a rack to a group, it factors through the enveloping group.
-/
lemma to_envel_group.univ (R : Type*) [rack R] (G : Type*) [group G]
  (f : R →◃ quandle.conj G) :
  (quandle.conj.map (to_envel_group.map f)).comp (to_envel_group R) = f :=
to_envel_group.map.symm_apply_apply f

/--
The homomorphism `to_envel_group.map f` is the unique map that fits into the commutative
triangle in `to_envel_group.univ`.
-/
lemma to_envel_group.univ_uniq (R : Type*) [rack R] (G : Type*) [group G]
  (f : R →◃ quandle.conj G)
  (g : envel_group R →* G) (h : f = (quandle.conj.map g).comp (to_envel_group R)) :
  g = to_envel_group.map f :=
h.symm ▸ (to_envel_group.map.apply_symm_apply g).symm

/--
The induced group homomorphism from the enveloping group into bijections of the rack,
using `rack.to_conj`. Satisfies the property `envel_action_prop`.

This gives the rack `R` the structure of an augmented rack over `envel_group R`.
-/
def envel_action {R : Type*} [rack R] : envel_group R →* (R ≃ R) :=
to_envel_group.map (to_conj R)

@[simp]
lemma envel_action_prop {R : Type*} [rack R] (x y : R) :
  envel_action (to_envel_group R x) y = x ◃ y := rfl

end envel_group

end rack
