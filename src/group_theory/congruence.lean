/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import data.setoid.basic
import algebra.group.pi
import algebra.group.prod
import data.equiv.mul_add
import group_theory.submonoid.operations

/-!
# Congruence relations

This file defines congruence relations: equivalence relations that preserve a binary operation,
which in this case is multiplication or addition. The principal definition is a `structure`
extending a `setoid` (an equivalence relation), and the inductive definition of the smallest
congruence relation containing a binary relation is also given (see `con_gen`).

The file also proves basic properties of the quotient of a type by a congruence relation, and the
complete lattice of congruence relations on a type. We then establish an order-preserving bijection
between the set of congruence relations containing a congruence relation `c` and the set of
congruence relations on the quotient by `c`.

The second half of the file concerns congruence relations on monoids, in which case the
quotient by the congruence relation is also a monoid. There are results about the universal
property of quotients of monoids, and the isomorphism theorems for monoids.

## Implementation notes

The inductive definition of a congruence relation could be a nested inductive type, defined using
the equivalence closure of a binary relation `eqv_gen`, but the recursor generated does not work.
A nested inductive definition could conceivably shorten proofs, because they would allow invocation
of the corresponding lemmas about `eqv_gen`.

The lemmas `refl`, `symm` and `trans` are not tagged with `@[refl]`, `@[symm]`, and `@[trans]`
respectively as these tags do not work on a structure coerced to a binary relation.

There is a coercion from elements of a type to the element's equivalence class under a
congruence relation.

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid, isomorphism theorems
-/

variables (M : Type*) {N : Type*} {P : Type*}

set_option old_structure_cmd true

open function setoid

/-- A congruence relation on a type with an addition is an equivalence relation which
    preserves addition. -/
structure add_con [has_add M] extends setoid M :=
(add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z))

/-- A congruence relation on a type with a multiplication is an equivalence relation which
    preserves multiplication. -/
@[to_additive add_con] structure con [has_mul M] extends setoid M :=
(mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z))

/-- The equivalence relation underlying an additive congruence relation. -/
add_decl_doc add_con.to_setoid

/-- The equivalence relation underlying a multiplicative congruence relation. -/
add_decl_doc con.to_setoid

variables {M}

/-- The inductively defined smallest additive congruence relation containing a given binary
    relation. -/
inductive add_con_gen.rel [has_add M] (r : M → M → Prop) : M → M → Prop
| of : Π x y, r x y → add_con_gen.rel x y
| refl : Π x, add_con_gen.rel x x
| symm : Π x y, add_con_gen.rel x y → add_con_gen.rel y x
| trans : Π x y z, add_con_gen.rel x y → add_con_gen.rel y z → add_con_gen.rel x z
| add : Π w x y z, add_con_gen.rel w x → add_con_gen.rel y z → add_con_gen.rel (w + y) (x + z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
    relation. -/
@[to_additive add_con_gen.rel]
inductive con_gen.rel [has_mul M] (r : M → M → Prop) : M → M → Prop
| of : Π x y, r x y → con_gen.rel x y
| refl : Π x, con_gen.rel x x
| symm : Π x y, con_gen.rel x y → con_gen.rel y x
| trans : Π x y z, con_gen.rel x y → con_gen.rel y z → con_gen.rel x z
| mul : Π w x y z, con_gen.rel w x → con_gen.rel y z → con_gen.rel (w * y) (x * z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
    relation. -/
@[to_additive add_con_gen "The inductively defined smallest additive congruence relation containing
a given binary relation."]
def con_gen [has_mul M] (r : M → M → Prop) : con M :=
⟨con_gen.rel r, ⟨con_gen.rel.refl, con_gen.rel.symm, con_gen.rel.trans⟩, con_gen.rel.mul⟩

namespace con

section
variables [has_mul M] [has_mul N] [has_mul P] (c : con M)

@[to_additive]
instance : inhabited (con M) :=
⟨con_gen empty_relation⟩

/-- A coercion from a congruence relation to its underlying binary relation. -/
@[to_additive "A coercion from an additive congruence relation to its underlying binary relation."]
instance : has_coe_to_fun (con M) := ⟨_, λ c, λ x y, c.r x y⟩

@[simp, to_additive] lemma rel_eq_coe (c : con M) : c.r = c := rfl

/-- Congruence relations are reflexive. -/
@[to_additive "Additive congruence relations are reflexive."]
protected lemma refl (x) : c x x := c.2.1 x

/-- Congruence relations are symmetric. -/
@[to_additive "Additive congruence relations are symmetric."]
protected lemma symm : ∀ {x y}, c x y → c y x := λ _ _ h, c.2.2.1 h

/-- Congruence relations are transitive. -/
@[to_additive "Additive congruence relations are transitive."]
protected lemma trans : ∀ {x y z}, c x y → c y z → c x z :=
λ _ _ _ h, c.2.2.2 h

/-- Multiplicative congruence relations preserve multiplication. -/
@[to_additive "Additive congruence relations preserve addition."]
protected lemma mul : ∀ {w x y z}, c w x → c y z → c (w * y) (x * z) :=
λ _ _ _ _ h1 h2, c.3 h1 h2

/-- Given a type `M` with a multiplication, a congruence relation `c` on `M`, and elements of `M`
    `x, y`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`. -/
@[to_additive "Given a type `M` with an addition, `x, y ∈ M`, and an additive congruence relation
`c` on `M`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`."]
instance : has_mem (M × M) (con M) := ⟨λ x c, c x.1 x.2⟩

variables {c}

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
@[to_additive "The map sending an additive congruence relation to its underlying binary relation
is injective."]
lemma ext' {c d : con M} (H : c.r = d.r) : c = d :=
by cases c; cases d; simpa using H

/-- Extensionality rule for congruence relations. -/
@[ext, to_additive "Extensionality rule for additive congruence relations."]
lemma ext {c d : con M} (H : ∀ x y, c x y ↔ d x y) : c = d :=
ext' $ by ext; apply H

attribute [ext] add_con.ext

/-- The map sending a congruence relation to its underlying equivalence relation is injective. -/
@[to_additive "The map sending an additive congruence relation to its underlying equivalence
relation is injective."]
lemma to_setoid_inj {c d : con M} (H : c.to_setoid = d.to_setoid) : c = d :=
ext $ ext_iff.1 H

/-- Iff version of extensionality rule for congruence relations. -/
@[to_additive "Iff version of extensionality rule for additive congruence relations."]
lemma ext_iff {c d : con M} : (∀ x y, c x y ↔ d x y) ↔ c = d :=
⟨ext, λ h _ _, h ▸ iff.rfl⟩

/-- Two congruence relations are equal iff their underlying binary relations are equal. -/
@[to_additive "Two additive congruence relations are equal iff their underlying binary relations
are equal."]
lemma ext'_iff {c d : con M} : c.r = d.r ↔ c = d :=
⟨ext', λ h, h ▸ rfl⟩

/-- The kernel of a multiplication-preserving function as a congruence relation. -/
@[to_additive "The kernel of an addition-preserving function as an additive congruence relation."]
def mul_ker (f : M → P) (h : ∀ x y, f (x * y) = f x * f y) : con M :=
{ r := λ x y, f x = f y,
  iseqv := ⟨λ _, rfl, λ _ _, eq.symm, λ _ _ _, eq.trans⟩,
  mul' := λ _ _ _ _ h1 h2, by rw [h, h1, h2, h] }

/-- Given types with multiplications `M, N`, the product of two congruence relations `c` on `M` and
    `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁` is related to `y₁`
    by `c` and `x₂` is related to `y₂` by `d`. -/
@[to_additive prod "Given types with additions `M, N`, the product of two congruence relations
`c` on `M` and `d` on `N`: `(x₁, x₂), (y₁, y₂) ∈ M × N` are related by `c.prod d` iff `x₁`
is related to `y₁` by `c` and `x₂` is related to `y₂` by `d`."]
protected def prod (c : con M) (d : con N) : con (M × N) :=
{ mul' := λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩, ..c.to_setoid.prod d.to_setoid }

/-- The product of an indexed collection of congruence relations. -/
@[to_additive "The product of an indexed collection of additive congruence relations."]
def pi {ι : Type*} {f : ι → Type*} [Π i, has_mul (f i)]
  (C : Π i, con (f i)) : con (Π i, f i) :=
{ mul' := λ _ _ _ _ h1 h2 i, (C i).mul (h1 i) (h2 i), ..@pi_setoid _ _ $ λ i, (C i).to_setoid }

variables (c)

@[simp, to_additive] lemma coe_eq : c.to_setoid.r = c := rfl

-- Quotients

/-- Defining the quotient by a congruence relation of a type with a multiplication. -/
@[to_additive "Defining the quotient by an additive congruence relation of a type with
an addition."]
protected def quotient := quotient $ c.to_setoid

/-- Coercion from a type with a multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
@[to_additive "Coercion from a type with an addition to its quotient by an additive congruence
relation", priority 0]
instance : has_coe_t M c.quotient := ⟨@quotient.mk _ c.to_setoid⟩

/-- The quotient by a decidable congruence relation has decidable equality. -/
@[to_additive "The quotient by a decidable additive congruence relation has decidable equality."]
instance [d : ∀ a b, decidable (c a b)] : decidable_eq c.quotient :=
@quotient.decidable_eq M c.to_setoid d

/-- The function on the quotient by a congruence relation `c` induced by a function that is
    constant on `c`'s equivalence classes. -/
@[elab_as_eliminator, to_additive "The function on the quotient by a congruence relation `c`
induced by a function that is constant on `c`'s equivalence classes."]
protected def lift_on {β} {c : con M} (q : c.quotient) (f : M → β)
  (h : ∀ a b, c a b → f a = f b) : β := quotient.lift_on' q f h

/-- The binary function on the quotient by a congruence relation `c` induced by a binary function
    that is constant on `c`'s equivalence classes. -/
@[elab_as_eliminator, to_additive "The binary function on the quotient by a congruence relation `c`
induced by a binary function that is constant on `c`'s equivalence classes."]
protected def lift_on₂ {β} {c : con M} (q r : c.quotient) (f : M → M → β)
  (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → c a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β := quotient.lift_on₂' q r f h

variables {c}

/-- The inductive principle used to prove propositions about the elements of a quotient by a
    congruence relation. -/
@[elab_as_eliminator, to_additive "The inductive principle used to prove propositions about
the elements of a quotient by an additive congruence relation."]
protected lemma induction_on {C : c.quotient → Prop} (q : c.quotient) (H : ∀ x : M, C x) : C q :=
quotient.induction_on' q H

/-- A version of `con.induction_on` for predicates which take two arguments. -/
@[elab_as_eliminator, to_additive "A version of `add_con.induction_on` for predicates which take
two arguments."]
protected lemma induction_on₂ {d : con N} {C : c.quotient → d.quotient → Prop}
  (p : c.quotient) (q : d.quotient) (H : ∀ (x : M) (y : N), C x y) : C p q :=
quotient.induction_on₂' p q H

variables (c)

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
    element of the quotient by `c`. -/
@[simp, to_additive "Two elements are related by an additive congruence relation `c` iff they
are represented by the same element of the quotient by `c`."]
protected lemma eq {a b : M} : (a : c.quotient) = b ↔ c a b :=
quotient.eq'

/-- The multiplication induced on the quotient by a congruence relation on a type with a
    multiplication. -/
@[to_additive "The addition induced on the quotient by an additive congruence relation on a type
with an addition."]
instance has_mul : has_mul c.quotient :=
⟨λ x y, quotient.lift_on₂' x y (λ w z, ((w * z : M) : c.quotient))
     $ λ _ _ _ _ h1 h2, c.eq.2 $ c.mul h1 h2⟩

/-- The kernel of the quotient map induced by a congruence relation `c` equals `c`. -/
@[simp, to_additive "The kernel of the quotient map induced by an additive congruence relation
`c` equals `c`."]
lemma mul_ker_mk_eq : mul_ker (coe : M → c.quotient) (λ x y, rfl) = c :=
ext $ λ x y, quotient.eq'

variables {c}

/-- The coercion to the quotient of a congruence relation commutes with multiplication (by
    definition). -/
@[simp, to_additive "The coercion to the quotient of an additive congruence relation commutes with
addition (by definition)."]
lemma coe_mul (x y : M) : (↑(x * y) : c.quotient) = ↑x * ↑y := rfl

/-- Definition of the function on the quotient by a congruence relation `c` induced by a function
    that is constant on `c`'s equivalence classes. -/
@[simp, to_additive "Definition of the function on the quotient by an additive congruence
relation `c` induced by a function that is constant on `c`'s equivalence classes."]
protected lemma lift_on_coe {β} (c : con M) (f : M → β)
  (h : ∀ a b, c a b → f a = f b) (x : M) :
  con.lift_on (x : c.quotient) f h = f x := rfl

/-- Makes an isomorphism of quotients by two congruence relations, given that the relations are
    equal. -/
@[to_additive "Makes an additive isomorphism of quotients by two additive congruence relations,
given that the relations are equal."]
protected def congr {c d : con M} (h : c = d) :  c.quotient ≃* d.quotient :=
{ map_mul' := λ x y, by rcases x; rcases y; refl,
  ..quotient.congr (equiv.refl M) $ by apply ext_iff.2 h }

-- The complete lattice of congruence relations on a type

/-- For congruence relations `c, d` on a type `M` with a multiplication, `c ≤ d` iff `∀ x y ∈ M`,
    `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
@[to_additive "For additive congruence relations `c, d` on a type `M` with an addition, `c ≤ d` iff
`∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`."]
instance : has_le (con M) := ⟨λ c d, ∀ ⦃x y⦄, c x y → d x y⟩

/-- Definition of `≤` for congruence relations. -/
@[to_additive "Definition of `≤` for additive congruence relations."]
theorem le_def {c d : con M} : c ≤ d ↔ ∀ {x y}, c x y → d x y := iff.rfl

/-- The infimum of a set of congruence relations on a given type with a multiplication. -/
@[to_additive "The infimum of a set of additive congruence relations on a given type with
an addition."]
instance : has_Inf (con M) :=
⟨λ S, ⟨λ x y, ∀ c : con M, c ∈ S → c x y,
⟨λ x c hc, c.refl x, λ _ _ h c hc, c.symm $ h c hc,
 λ _ _ _ h1 h2 c hc, c.trans (h1 c hc) $ h2 c hc⟩,
 λ _ _ _ _ h1 h2 c hc, c.mul (h1 c hc) $ h2 c hc⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying equivalence relation. -/
@[to_additive "The infimum of a set of additive congruence relations is the same as the infimum of
the set's image under the map to the underlying equivalence relation."]
lemma Inf_to_setoid (S : set (con M)) : (Inf S).to_setoid = Inf (to_setoid '' S) :=
setoid.ext' $ λ x y, ⟨λ h r ⟨c, hS, hr⟩, by rw ←hr; exact h c hS,
  λ h c hS, h c.to_setoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
    under the map to the underlying binary relation. -/
@[to_additive "The infimum of a set of additive congruence relations is the same as the infimum
of the set's image under the map to the underlying binary relation."]
lemma Inf_def (S : set (con M)) : (Inf S).r = Inf (r '' S) :=
by { ext, simp only [Inf_image, infi_apply, infi_Prop_eq], refl }

@[to_additive]
instance : partial_order (con M) :=
{ le := (≤),
  lt := λ c d, c ≤ d ∧ ¬d ≤ c,
  le_refl := λ c _ _, id,
  le_trans := λ c1 c2 c3 h1 h2 x y h, h2 $ h1 h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ c d hc hd, ext $ λ x y, ⟨λ h, hc h, λ h, hd h⟩ }

/-- The complete lattice of congruence relations on a given type with a multiplication. -/
@[to_additive "The complete lattice of additive congruence relations on a given type with
an addition."]
instance : complete_lattice (con M) :=
{ inf := λ c d, ⟨(c.to_setoid ⊓ d.to_setoid).1, (c.to_setoid ⊓ d.to_setoid).2,
                  λ _ _ _ _ h1 h2, ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩⟩,
  inf_le_left := λ _ _ _ _ h, h.1,
  inf_le_right := λ _ _ _ _ h, h.2,
  le_inf := λ _ _ _ hb hc _ _ h, ⟨hb h, hc h⟩,
  top := { mul' := by tauto, ..setoid.complete_lattice.top},
  le_top := λ _ _ _ h, trivial,
  bot := { mul' := λ _ _ _ _ h1 h2, h1 ▸ h2 ▸ rfl, ..setoid.complete_lattice.bot},
  bot_le := λ c x y h, h ▸ c.refl x,
  .. complete_lattice_of_Inf (con M) $ assume s,
    ⟨λ r hr x y h, (h : ∀ r ∈ s, (r : con M) x y) r hr, λ r hr x y h r' hr', hr hr' h⟩ }

/-- The infimum of two congruence relations equals the infimum of the underlying binary
    operations. -/
@[to_additive "The infimum of two additive congruence relations equals the infimum of the
underlying binary operations."]
lemma inf_def {c d : con M} : (c ⊓ d).r = c.r ⊓ d.r := rfl

/-- Definition of the infimum of two congruence relations. -/
@[to_additive "Definition of the infimum of two additive congruence relations."]
theorem inf_iff_and {c d : con M} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y := iff.rfl

/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
    the infimum of the set of congruence relations containing `r`. -/
@[to_additive add_con_gen_eq "The inductively defined smallest additive congruence relation
containing a binary relation `r` equals the infimum of the set of additive congruence relations
containing `r`."]
theorem con_gen_eq (r : M → M → Prop) :
  con_gen r = Inf {s : con M | ∀ x y, r x y → s x y} :=
le_antisymm
  (λ x y H, con_gen.rel.rec_on H (λ _ _ h _ hs, hs _ _ h) (con.refl _) (λ _ _ _, con.symm _)
    (λ _ _ _ _ _, con.trans _)
    $ λ w x y z _ _ h1 h2 c hc, c.mul (h1 c hc) $ h2 c hc)
  (Inf_le (λ _ _, con_gen.rel.of _ _))

/-- The smallest congruence relation containing a binary relation `r` is contained in any
    congruence relation containing `r`. -/
@[to_additive add_con_gen_le "The smallest additive congruence relation containing a binary
relation `r` is contained in any additive congruence relation containing `r`."]
theorem con_gen_le {r : M → M → Prop} {c : con M} (h : ∀ x y, r x y → c.r x y) :
  con_gen r ≤ c :=
by rw con_gen_eq; exact Inf_le h

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
    containing `s` contains the smallest congruence relation containing `r`. -/
@[to_additive add_con_gen_mono "Given binary relations `r, s` with `r` contained in `s`, the
smallest additive congruence relation containing `s` contains the smallest additive congruence
relation containing `r`."]
theorem con_gen_mono {r s : M → M → Prop} (h : ∀ x y, r x y → s x y) :
  con_gen r ≤ con_gen s :=
con_gen_le $ λ x y hr, con_gen.rel.of _ _ $ h x y hr

/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
@[simp, to_additive add_con_gen_of_add_con "Additive congruence relations equal the smallest
additive congruence relation in which they are contained."]
lemma con_gen_of_con (c : con M) : con_gen c = c :=
le_antisymm (by rw con_gen_eq; exact Inf_le (λ _ _, id)) con_gen.rel.of

/-- The map sending a binary relation to the smallest congruence relation in which it is
    contained is idempotent. -/
@[simp, to_additive add_con_gen_idem "The map sending a binary relation to the smallest additive
congruence relation in which it is contained is idempotent."]
lemma con_gen_idem (r : M → M → Prop) :
  con_gen (con_gen r) = con_gen r :=
con_gen_of_con _

/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
    the binary relation '`x` is related to `y` by `c` or `d`'. -/
@[to_additive sup_eq_add_con_gen "The supremum of additive congruence relations `c, d` equals the
smallest additive congruence relation containing the binary relation '`x` is related to `y`
by `c` or `d`'."]
lemma sup_eq_con_gen (c d : con M) :
  c ⊔ d = con_gen (λ x y, c x y ∨ d x y) :=
begin
  rw con_gen_eq,
  apply congr_arg Inf,
  simp only [le_def, or_imp_distrib, ← forall_and_distrib]
end

/-- The supremum of two congruence relations equals the smallest congruence relation containing
    the supremum of the underlying binary operations. -/
@[to_additive "The supremum of two additive congruence relations equals the smallest additive
congruence relation containing the supremum of the underlying binary operations."]
lemma sup_def {c d : con M} : c ⊔ d = con_gen (c.r ⊔ d.r) :=
by rw sup_eq_con_gen; refl

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
    containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by
    `c`'. -/
@[to_additive Sup_eq_add_con_gen "The supremum of a set of additive congruence relations `S` equals
the smallest additive congruence relation containing the binary relation 'there exists `c ∈ S`
such that `x` is related to `y` by `c`'."]
lemma Sup_eq_con_gen (S : set (con M)) :
  Sup S = con_gen (λ x y, ∃ c : con M, c ∈ S ∧ c x y) :=
begin
  rw con_gen_eq,
  apply congr_arg Inf,
  ext,
  exact ⟨λ h _ _ ⟨r, hr⟩, h hr.1 hr.2,
         λ h r hS _ _ hr, h _ _ ⟨r, hS, hr⟩⟩,
end

/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
    containing the supremum of the set's image under the map to the underlying binary relation. -/
@[to_additive "The supremum of a set of additive congruence relations is the same as the smallest
additive congruence relation containing the supremum of the set's image under the map to the
underlying binary relation."]
lemma Sup_def {S : set (con M)} : Sup S = con_gen (Sup (r '' S)) :=
begin
  rw [Sup_eq_con_gen, Sup_image],
  congr' with x y,
  simp only [Sup_image, supr_apply, supr_Prop_eq, exists_prop, rel_eq_coe]
end

variables (M)

/-- There is a Galois insertion of congruence relations on a type with a multiplication `M` into
    binary relations on `M`. -/
@[to_additive "There is a Galois insertion of additive congruence relations on a type with
an addition `M` into binary relations on `M`."]
protected noncomputable def gi : @galois_insertion (M → M → Prop) (con M) _ _ con_gen r :=
{ choice := λ r h, con_gen r,
  gc := λ r c, ⟨λ H _ _ h, H $ con_gen.rel.of _ _ h, λ H, con_gen_of_con c ▸ con_gen_mono H⟩,
  le_l_u := λ x, (con_gen_of_con x).symm ▸ le_refl x,
  choice_eq := λ _ _, rfl }

variables {M} (c)


/-- Given a function `f`, the smallest congruence relation containing the binary relation on `f`'s
    image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)`
    by a congruence relation `c`.' -/
@[to_additive "Given a function `f`, the smallest additive congruence relation containing the
binary relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the
elements of `f⁻¹(y)` by an additive congruence relation `c`.'"]
def map_gen (f : M → N) : con N :=
con_gen $ λ x y, ∃ a b, f a = x ∧ f b = y ∧ c a b

/-- Given a surjective multiplicative-preserving function `f` whose kernel is contained in a
    congruence relation `c`, the congruence relation on `f`'s codomain defined by '`x ≈ y` iff the
    elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/
@[to_additive "Given a surjective addition-preserving function `f` whose kernel is contained in
an additive congruence relation `c`, the additive congruence relation on `f`'s codomain defined
by '`x ≈ y` iff the elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.'"]
def map_of_surjective (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (h : mul_ker f H ≤ c)
  (hf : surjective f) : con N :=
{ mul' := λ w x y z ⟨a, b, hw, hx, h1⟩ ⟨p, q, hy, hz, h2⟩,
    ⟨a * p, b * q, by rw [H, hw, hy], by rw [H, hx, hz], c.mul h1 h2⟩,
  ..c.to_setoid.map_of_surjective f h hf }

/-- A specialization of 'the smallest congruence relation containing a congruence relation `c`
    equals `c`'. -/
@[to_additive "A specialization of 'the smallest additive congruence relation containing
an additive congruence relation `c` equals `c`'."]
lemma map_of_surjective_eq_map_gen {c : con M} {f : M → N} (H : ∀ x y, f (x * y) = f x * f y)
  (h : mul_ker f H ≤ c) (hf : surjective f) :
  c.map_gen f = c.map_of_surjective f H h hf :=
by rw ←con_gen_of_con (c.map_of_surjective f H h hf); refl

/-- Given types with multiplications `M, N` and a congruence relation `c` on `N`, a
    multiplication-preserving map `f : M → N` induces a congruence relation on `f`'s domain
    defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' -/
@[to_additive "Given types with additions `M, N` and an additive congruence relation `c` on `N`,
an addition-preserving map `f : M → N` induces an additive congruence relation on `f`'s domain
defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' "]
def comap (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (c : con N) : con M :=
{ mul' := λ w x y z h1 h2, show c (f (w * y)) (f (x * z)), by rw [H, H]; exact c.mul h1 h2,
  ..c.to_setoid.comap f }

section
open quotient

/-- Given a congruence relation `c` on a type `M` with a multiplication, the order-preserving
    bijection between the set of congruence relations containing `c` and the congruence relations
    on the quotient of `M` by `c`. -/
@[to_additive "Given an additive congruence relation `c` on a type `M` with an addition,
the order-preserving bijection between the set of additive congruence relations containing `c` and
the additive congruence relations on the quotient of `M` by `c`."]
def correspondence : {d // c ≤ d} ≃o (con c.quotient) :=
{ to_fun := λ d, d.1.map_of_surjective coe _
    (by rw mul_ker_mk_eq; exact d.2) $ @exists_rep _ c.to_setoid,
  inv_fun := λ d, ⟨comap (coe : M → c.quotient) (λ x y, rfl) d, λ _ _ h,
    show d _ _, by rw c.eq.2 h; exact d.refl _ ⟩,
  left_inv := λ d, subtype.ext_iff_val.2 $ ext $ λ _ _,
    ⟨λ h, let ⟨a, b, hx, hy, H⟩ := h in
      d.1.trans (d.1.symm $ d.2 $ c.eq.1 hx) $ d.1.trans H $ d.2 $ c.eq.1 hy,
     λ h, ⟨_, _, rfl, rfl, h⟩⟩,
  right_inv := λ d, let Hm : mul_ker (coe : M → c.quotient) (λ x y, rfl) ≤
        comap (coe : M → c.quotient) (λ x y, rfl) d :=
      λ x y h, show d _ _, by rw mul_ker_mk_eq at h; exact c.eq.2 h ▸ d.refl _ in
    ext $ λ x y, ⟨λ h, let ⟨a, b, hx, hy, H⟩ := h in hx ▸ hy ▸ H,
      con.induction_on₂ x y $ λ w z h, ⟨w, z, rfl, rfl, h⟩⟩,
  map_rel_iff' := λ s t, ⟨λ h _ _ hs, let ⟨a, b, hx, hy, ht⟩ := h ⟨_, _, rfl, rfl, hs⟩ in
      t.1.trans (t.1.symm $ t.2 $ eq_rel.1 hx) $ t.1.trans ht $ t.2 $ eq_rel.1 hy,
      λ h _ _ hs, let ⟨a, b, hx, hy, Hs⟩ := hs in ⟨a, b, hx, hy, h Hs⟩⟩ }

end

end

section mul_one_class

variables {M} [mul_one_class M] [mul_one_class N] [mul_one_class P] (c : con M)

/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive "The quotient of an `add_monoid` by an additive congruence relation is
an `add_monoid`."]
instance mul_one_class : mul_one_class c.quotient :=
{ one := ((1 : M) : c.quotient),
  mul := (*),
  mul_one := λ x, quotient.induction_on' x $ λ _, congr_arg coe $ mul_one _,
  one_mul := λ x, quotient.induction_on' x $ λ _, congr_arg coe $ one_mul _ }

variables {c}

/-- The 1 of the quotient of a monoid by a congruence relation is the equivalence class of the
    monoid's 1. -/
@[simp, to_additive "The 0 of the quotient of an `add_monoid` by an additive congruence relation
is the equivalence class of the `add_monoid`'s 0."]
lemma coe_one : ((1 : M) : c.quotient) = 1 := rfl

variables (M c)

/-- The submonoid of `M × M` defined by a congruence relation on a monoid `M`. -/
@[to_additive "The `add_submonoid` of `M × M` defined by an additive congruence
relation on an `add_monoid` `M`."]
protected def submonoid : submonoid (M × M) :=
{ carrier := { x | c x.1 x.2 },
  one_mem' := c.iseqv.1 1,
  mul_mem' := λ _ _, c.mul }

variables {M c}

/-- The congruence relation on a monoid `M` from a submonoid of `M × M` for which membership
    is an equivalence relation. -/
@[to_additive "The additive congruence relation on an `add_monoid` `M` from
an `add_submonoid` of `M × M` for which membership is an equivalence relation."]
def of_submonoid (N : submonoid (M × M)) (H : equivalence (λ x y, (x, y) ∈ N)) : con M :=
{ r := λ x y, (x, y) ∈ N,
  iseqv := H,
  mul' := λ _ _ _ _, N.mul_mem }

/-- Coercion from a congruence relation `c` on a monoid `M` to the submonoid of `M × M` whose
    elements are `(x, y)` such that `x` is related to `y` by `c`. -/
@[to_additive "Coercion from a congruence relation `c` on an `add_monoid` `M`
to the `add_submonoid` of `M × M` whose elements are `(x, y)` such that `x`
is related to `y` by `c`."]
instance to_submonoid : has_coe (con M) (submonoid (M × M)) := ⟨λ c, c.submonoid M⟩

@[to_additive] lemma mem_coe {c : con M} {x y} :
  (x, y) ∈ (↑c : submonoid (M × M)) ↔ (x, y) ∈ c := iff.rfl

@[to_additive]
theorem to_submonoid_inj (c d : con M) (H : (c : submonoid (M × M)) = d) : c = d :=
ext $ λ x y, show (x, y) ∈ (c : submonoid (M × M)) ↔ (x, y) ∈ ↑d, by rw H

@[to_additive]
lemma le_iff {c d : con M} : c ≤ d ↔ (c : submonoid (M × M)) ≤ d :=
⟨λ h x H, h H, λ h x y hc, h $ show (x, y) ∈ c, from hc⟩

/-- The kernel of a monoid homomorphism as a congruence relation. -/
@[to_additive "The kernel of an `add_monoid` homomorphism as an additive congruence relation."]
def ker (f : M →* P) : con M := mul_ker f f.3

/-- The definition of the congruence relation defined by a monoid homomorphism's kernel. -/
@[to_additive "The definition of the additive congruence relation defined by an `add_monoid`
homomorphism's kernel."]
lemma ker_rel (f : M →* P) {x y} : ker f x y ↔ f x = f y := iff.rfl

/-- There exists an element of the quotient of a monoid by a congruence relation (namely 1). -/
@[to_additive "There exists an element of the quotient of an `add_monoid` by a congruence relation
(namely 0)."]
instance quotient.inhabited : inhabited c.quotient := ⟨((1 : M) : c.quotient)⟩

variables (c)

/-- The natural homomorphism from a monoid to its quotient by a congruence relation. -/
@[to_additive "The natural homomorphism from an `add_monoid` to its quotient by an additive
congruence relation."]
def mk' : M →* c.quotient := ⟨coe, rfl, λ _ _, rfl⟩

variables (x y : M)

/-- The kernel of the natural homomorphism from a monoid to its quotient by a congruence
    relation `c` equals `c`. -/
@[simp, to_additive "The kernel of the natural homomorphism from an `add_monoid` to its quotient by
an additive congruence relation `c` equals `c`."]
lemma mk'_ker : ker c.mk' = c := ext $ λ _ _, c.eq

variables {c}

/-- The natural homomorphism from a monoid to its quotient by a congruence relation is
    surjective. -/
@[to_additive "The natural homomorphism from an `add_monoid` to its quotient by a congruence
relation is surjective."]
lemma mk'_surjective : surjective c.mk' :=
λ x, by rcases x; exact ⟨x, rfl⟩

@[simp, to_additive] lemma comp_mk'_apply (g : c.quotient →* P) {x} :
  g.comp c.mk' x = g x := rfl

/-- The elements related to `x ∈ M`, `M` a monoid, by the kernel of a monoid homomorphism are
    those in the preimage of `f(x)` under `f`. -/
@[to_additive "The elements related to `x ∈ M`, `M` an `add_monoid`, by the kernel of
an `add_monoid` homomorphism are those in the preimage of `f(x)` under `f`. "]
lemma ker_apply_eq_preimage {f : M →* P} (x) : (ker f) x = f ⁻¹' {f x} :=
set.ext $ λ x,
  ⟨λ h, set.mem_preimage.2 $ set.mem_singleton_iff.2 h.symm,
   λ h, (set.mem_singleton_iff.1 $ set.mem_preimage.1 h).symm⟩

/-- Given a monoid homomorphism `f : N → M` and a congruence relation `c` on `M`, the congruence
    relation induced on `N` by `f` equals the kernel of `c`'s quotient homomorphism composed with
    `f`. -/
@[to_additive "Given an `add_monoid` homomorphism `f : N → M` and an additive congruence relation
`c` on `M`, the additive congruence relation induced on `N` by `f` equals the kernel of `c`'s
quotient homomorphism composed with `f`."]
lemma comap_eq {f : N →* M} : comap f f.map_mul c = ker (c.mk'.comp f) :=
ext $ λ x y, show c _ _ ↔ c.mk' _ = c.mk' _, by rw ←c.eq; refl

variables (c) (f : M →* P)

/-- The homomorphism on the quotient of a monoid by a congruence relation `c` induced by a
    homomorphism constant on `c`'s equivalence classes. -/
@[to_additive "The homomorphism on the quotient of an `add_monoid` by an additive congruence
relation `c` induced by a homomorphism constant on `c`'s equivalence classes."]
def lift (H : c ≤ ker f) : c.quotient →* P :=
{ to_fun := λ x, con.lift_on x f $ λ _ _ h, H h,
  map_one' := by rw ←f.map_one; refl,
  map_mul' := λ x y, con.induction_on₂ x y $ λ m n, f.map_mul m n ▸ rfl }

variables {c f}

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[simp, to_additive "The diagram describing the universal property for quotients of `add_monoid`s
commutes."]
lemma lift_mk' (H : c ≤ ker f) (x) :
  c.lift f H (c.mk' x) = f x := rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[simp, to_additive "The diagram describing the universal property for quotients of `add_monoid`s
commutes."]
lemma lift_coe (H : c ≤ ker f) (x : M) :
  c.lift f H x = f x := rfl

/-- The diagram describing the universal property for quotients of monoids commutes. -/
@[simp, to_additive "The diagram describing the universal property for quotients of `add_monoid`s
commutes."]
theorem lift_comp_mk' (H : c ≤ ker f) :
  (c.lift f H).comp c.mk' = f := by ext; refl

/-- Given a homomorphism `f` from the quotient of a monoid by a congruence relation, `f` equals the
    homomorphism on the quotient induced by `f` composed with the natural map from the monoid to
    the quotient. -/
@[simp, to_additive "Given a homomorphism `f` from the quotient of an `add_monoid` by an additive
congruence relation, `f` equals the homomorphism on the quotient induced by `f` composed with the
natural map from the `add_monoid` to the quotient."]
lemma lift_apply_mk' (f : c.quotient →* P) :
  c.lift (f.comp c.mk') (λ x y h, show f ↑x = f ↑y, by rw c.eq.2 h) = f :=
by ext; rcases x; refl

/-- Homomorphisms on the quotient of a monoid by a congruence relation are equal if they
    are equal on elements that are coercions from the monoid. -/
@[to_additive "Homomorphisms on the quotient of an `add_monoid` by an additive congruence relation
are equal if they are equal on elements that are coercions from the `add_monoid`."]
lemma lift_funext (f g : c.quotient →* P) (h : ∀ a : M, f a = g a) : f = g :=
begin
  rw [←lift_apply_mk' f, ←lift_apply_mk' g],
  congr' 1,
  exact monoid_hom.ext_iff.2 h,
end

/-- The uniqueness part of the universal property for quotients of monoids. -/
@[to_additive "The uniqueness part of the universal property for quotients of `add_monoid`s."]
theorem lift_unique (H : c ≤ ker f) (g : c.quotient →* P)
  (Hg : g.comp c.mk' = f) : g = c.lift f H :=
lift_funext g (c.lift f H) $ λ x, by rw [lift_coe H, ←comp_mk'_apply, Hg]

/-- Given a congruence relation `c` on a monoid and a homomorphism `f` constant on `c`'s
    equivalence classes, `f` has the same image as the homomorphism that `f` induces on the
    quotient. -/
@[to_additive "Given an additive congruence relation `c` on an `add_monoid` and a homomorphism `f`
constant on `c`'s equivalence classes, `f` has the same image as the homomorphism that `f` induces
on the quotient."]
theorem lift_range (H : c ≤ ker f) : (c.lift f H).mrange = f.mrange :=
submonoid.ext $ λ x, ⟨by rintros ⟨⟨y⟩, hy⟩; exact ⟨y, hy⟩, λ ⟨y, hy⟩, ⟨↑y, hy⟩⟩

/-- Surjective monoid homomorphisms constant on a congruence relation `c`'s equivalence classes
    induce a surjective homomorphism on `c`'s quotient. -/
@[to_additive "Surjective `add_monoid` homomorphisms constant on an additive congruence
relation `c`'s equivalence classes induce a surjective homomorphism on `c`'s quotient."]
lemma lift_surjective_of_surjective (h : c ≤ ker f) (hf : surjective f) :
  surjective (c.lift f h) :=
λ y, exists.elim (hf y) $ λ w hw, ⟨w, (lift_mk' h w).symm ▸ hw⟩

variables (c f)

/-- Given a monoid homomorphism `f` from `M` to `P`, the kernel of `f` is the unique congruence
    relation on `M` whose induced map from the quotient of `M` to `P` is injective. -/
@[to_additive "Given an `add_monoid` homomorphism `f` from `M` to `P`, the kernel of `f`
is the unique additive congruence relation on `M` whose induced map from the quotient of `M`
to `P` is injective."]
lemma ker_eq_lift_of_injective (H : c ≤ ker f) (h : injective (c.lift f H)) :
  ker f = c :=
to_setoid_inj $ ker_eq_lift_of_injective f H h

variables {c}

/-- The homomorphism induced on the quotient of a monoid by the kernel of a monoid homomorphism. -/
@[to_additive "The homomorphism induced on the quotient of an `add_monoid` by the kernel
of an `add_monoid` homomorphism."]
def ker_lift : (ker f).quotient →* P :=
(ker f).lift f $ λ _ _, id

variables {f}

/-- The diagram described by the universal property for quotients of monoids, when the congruence
    relation is the kernel of the homomorphism, commutes. -/
@[simp, to_additive "The diagram described by the universal property for quotients
of `add_monoid`s, when the additive congruence relation is the kernel of the homomorphism,
commutes."]
lemma ker_lift_mk (x : M) :  ker_lift f x = f x := rfl

/-- Given a monoid homomorphism `f`, the induced homomorphism on the quotient by `f`'s kernel has
    the same image as `f`. -/
@[simp, to_additive "Given an `add_monoid` homomorphism `f`, the induced homomorphism
on the quotient by `f`'s kernel has the same image as `f`."]
lemma ker_lift_range_eq : (ker_lift f).mrange = f.mrange :=
lift_range $ λ _ _, id

/-- A monoid homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
@[to_additive "An `add_monoid` homomorphism `f` induces an injective homomorphism on the quotient
by `f`'s kernel."]
lemma ker_lift_injective (f : M →* P) : injective (ker_lift f) :=
λ x y, quotient.induction_on₂' x y $ λ _ _, (ker f).eq.2

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, `d`'s quotient
    map induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
@[to_additive "Given additive congruence relations `c, d` on an `add_monoid` such that `d`
contains `c`, `d`'s quotient map induces a homomorphism from the quotient by `c` to the quotient
by `d`."]
def map (c d : con M) (h : c ≤ d) : c.quotient →* d.quotient :=
c.lift d.mk' $ λ x y hc, show (ker d.mk') x y, from
  (mk'_ker d).symm ▸ h hc

/-- Given congruence relations `c, d` on a monoid such that `d` contains `c`, the definition of
    the homomorphism from the quotient by `c` to the quotient by `d` induced by `d`'s quotient
    map. -/
@[to_additive "Given additive congruence relations `c, d` on an `add_monoid` such that `d`
contains `c`, the definition of the homomorphism from the quotient by `c` to the quotient by `d`
induced by `d`'s quotient map."]
lemma map_apply {c d : con M} (h : c ≤ d) (x) :
  c.map d h x = c.lift d.mk' (λ x y hc, d.eq.2 $ h hc) x := rfl

variables (c)

/-- The first isomorphism theorem for monoids. -/
@[to_additive "The first isomorphism theorem for `add_monoid`s."]
noncomputable def quotient_ker_equiv_range (f : M →* P) : (ker f).quotient ≃* f.mrange :=
{ map_mul' := monoid_hom.map_mul _,
  ..equiv.of_bijective
      ((@mul_equiv.to_monoid_hom (ker_lift f).mrange _ _ _
        $ mul_equiv.submonoid_congr ker_lift_range_eq).comp (ker_lift f).mrange_restrict) $
      (equiv.bijective _).comp
        ⟨λ x y h, ker_lift_injective f $ by rcases x; rcases y; injections,
         λ ⟨w, z, hz⟩, ⟨z, by rcases hz; rcases _x; refl⟩⟩ }

/-- The first isomorphism theorem for monoids in the case of a homomorphism with right inverse. -/
@[to_additive "The first isomorphism theorem for `add_monoid`s in the case of a homomorphism
with right inverse.", simps]
def quotient_ker_equiv_of_right_inverse (f : M →* P) (g : P → M)
  (hf : function.right_inverse g f) :
  (ker f).quotient ≃* P :=
{ to_fun := ker_lift f,
  inv_fun := coe ∘ g,
  left_inv := λ x, ker_lift_injective _ (by rw [function.comp_app, ker_lift_mk, hf]),
  right_inv := hf,
  .. ker_lift f }

/-- The first isomorphism theorem for monoids in the case of a surjective homomorphism.

For a `computable` version, see `con.quotient_ker_equiv_of_right_inverse`.
-/
@[to_additive "The first isomorphism theorem for `add_monoid`s in the case of a surjective
homomorphism.

For a `computable` version, see `add_con.quotient_ker_equiv_of_right_inverse`.
"]
noncomputable def quotient_ker_equiv_of_surjective (f : M →* P) (hf : surjective f) :
  (ker f).quotient ≃* P :=
quotient_ker_equiv_of_right_inverse _ _ hf.has_right_inverse.some_spec

/-- The second isomorphism theorem for monoids. -/
@[to_additive "The second isomorphism theorem for `add_monoid`s."]
noncomputable def comap_quotient_equiv (f : N →* M) :
  (comap f f.map_mul c).quotient ≃* (c.mk'.comp f).mrange :=
(con.congr comap_eq).trans $ quotient_ker_equiv_range $ c.mk'.comp f

/-- The third isomorphism theorem for monoids. -/
@[to_additive "The third isomorphism theorem for `add_monoid`s."]
def quotient_quotient_equiv_quotient (c d : con M) (h : c ≤ d) :
  (ker (c.map d h)).quotient ≃* d.quotient :=
{ map_mul' := λ x y, con.induction_on₂ x y $ λ w z, con.induction_on₂ w z $ λ a b,
    show _ = d.mk' a * d.mk' b, by rw ←d.mk'.map_mul; refl,
  ..quotient_quotient_equiv_quotient c.to_setoid d.to_setoid h }

end mul_one_class

section monoids

/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive "The quotient of an `add_monoid` by an additive congruence relation is
an `add_monoid`."]
instance monoid {M : Type*} [monoid M] (c : con M): monoid c.quotient :=
{ one := ((1 : M) : c.quotient),
  mul := (*),
  mul_assoc := λ x y z, quotient.induction_on₃' x y z
               $ λ _ _ _, congr_arg coe $ mul_assoc _ _ _,
  .. c.mul_one_class }

/-- The quotient of a `comm_monoid` by a congruence relation is a `comm_monoid`. -/
@[to_additive "The quotient of an `add_comm_monoid` by an additive congruence
relation is an `add_comm_monoid`."]
instance comm_monoid {M : Type*} [comm_monoid M] (c : con M) :
  comm_monoid c.quotient :=
{ mul_comm := λ x y, con.induction_on₂ x y $ λ w z, by rw [←coe_mul, ←coe_mul, mul_comm],
  ..c.monoid}

end monoids

section groups

variables {M} [group M] [group N] [group P] (c : con M)

/-- Multiplicative congruence relations preserve inversion. -/
@[to_additive "Additive congruence relations preserve negation."]
protected lemma inv : ∀ {w x}, c w x → c w⁻¹ x⁻¹ :=
λ x y h, by simpa using c.symm (c.mul (c.mul (c.refl x⁻¹) h) (c.refl y⁻¹))

/-- The inversion induced on the quotient by a congruence relation on a type with a
    inversion. -/
@[to_additive "The negation induced on the quotient by an additive congruence relation on a type
with an negation."]
instance has_inv : has_inv c.quotient :=
⟨λ x, quotient.lift_on' x (λ w, ((w⁻¹ : M) : c.quotient))
     $ λ x y h, c.eq.2 $ c.inv h⟩

/-- The quotient of a group by a congruence relation is a group. -/
@[to_additive "The quotient of an `add_group` by an additive congruence relation is
an `add_group`."]
instance group : group c.quotient :=
{ inv := λ x, x⁻¹,
  mul_left_inv := λ x, show x⁻¹ * x = 1,
    from quotient.induction_on' x $ λ _, congr_arg coe $ mul_left_inv _,
  .. con.monoid c}

end groups

end con
