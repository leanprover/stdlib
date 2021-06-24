/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
import algebra.group.to_additive
import tactic.basic

/-!
# Typeclasses for (semi)groups and monoid

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(add_)?(comm_)?(semigroup|monoid|group)`, where `add_` means that
the class uses additive notation and `comm_` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `algebra.group.basic`.
-/

set_option old_structure_cmd true

universe u

/- Additive "sister" structures.
   Example, add_semigroup mirrors semigroup.
   These structures exist just to help automation.
   In an alternative design, we could have the binary operation as an
   extra argument for semigroup, monoid, group, etc. However, the lemmas
   would be hard to index since they would not contain any constant.
   For example, mul_assoc would be

   lemma mul_assoc {α : Type u} {op : α → α → α} [semigroup α op] :
                   ∀ a b c : α, op (op a b) c = op a (op b c) :=
    semigroup.mul_assoc

   The simplifier cannot effectively use this lemma since the pattern for
   the left-hand-side would be

        ?op (?op ?a ?b) ?c

   Remark: we use a tactic for transporting theorems from the multiplicative fragment
   to the additive one.
-/

section has_mul

variables {G : Type u} [has_mul G]

/-- `left_mul g` denotes left multiplication by `g` -/
@[to_additive "`left_add g` denotes left addition by `g`"]
def left_mul : G → G → G := λ g : G, λ x : G, g * x

/-- `right_mul g` denotes right multiplication by `g` -/
@[to_additive "`right_add g` denotes right addition by `g`"]
def right_mul : G → G → G := λ g : G, λ x : G, x * g

end has_mul

/-- A semigroup is a type with an associative `(*)`. -/
@[protect_proj, ancestor has_mul] class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
/-- An additive semigroup is a type with an associative `(+)`. -/
@[protect_proj, ancestor has_add] class add_semigroup (G : Type u) extends has_add G :=
(add_assoc : ∀ a b c : G, a + b + c = a + (b + c))
attribute [to_additive] semigroup

section semigroup
variables {G : Type u} [semigroup G]

@[no_rsimp, to_additive]
lemma mul_assoc : ∀ a b c : G, a * b * c = a * (b * c) :=
semigroup.mul_assoc

@[to_additive]
instance semigroup.to_is_associative : is_associative G (*) :=
⟨mul_assoc⟩

end semigroup

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[protect_proj, ancestor semigroup]
class comm_semigroup (G : Type u) extends semigroup G :=
(mul_comm : ∀ a b : G, a * b = b * a)

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[protect_proj, ancestor add_semigroup]
class add_comm_semigroup (G : Type u) extends add_semigroup G :=
(add_comm : ∀ a b : G, a + b = b + a)
attribute [to_additive] comm_semigroup

section comm_semigroup
variables {G : Type u} [comm_semigroup G]

@[no_rsimp, to_additive]
lemma mul_comm : ∀ a b : G, a * b = b * a :=
comm_semigroup.mul_comm

@[to_additive]
instance comm_semigroup.to_is_commutative : is_commutative G (*) :=
⟨mul_comm⟩

end comm_semigroup

/-- A `left_cancel_semigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[protect_proj, ancestor semigroup]
class left_cancel_semigroup (G : Type u) extends semigroup G :=
(mul_left_cancel : ∀ a b c : G, a * b = a * c → b = c)
/-- An `add_left_cancel_semigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[protect_proj, ancestor add_semigroup]
class add_left_cancel_semigroup (G : Type u) extends add_semigroup G :=
(add_left_cancel : ∀ a b c : G, a + b = a + c → b = c)
attribute [to_additive add_left_cancel_semigroup] left_cancel_semigroup

section left_cancel_semigroup
variables {G : Type u} [left_cancel_semigroup G] {a b c : G}

@[to_additive]
lemma mul_left_cancel : a * b = a * c → b = c :=
left_cancel_semigroup.mul_left_cancel a b c

@[to_additive]
lemma mul_left_cancel_iff : a * b = a * c ↔ b = c :=
⟨mul_left_cancel, congr_arg _⟩

@[to_additive]
theorem mul_right_injective (a : G) : function.injective ((*) a) :=
λ b c, mul_left_cancel

@[simp, to_additive]
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
(mul_right_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_right (a : G) {b c : G} : a * b ≠ a * c ↔ b ≠ c :=
(mul_right_injective a).ne_iff

end left_cancel_semigroup

/-- A `right_cancel_semigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[protect_proj, ancestor semigroup]
class right_cancel_semigroup (G : Type u) extends semigroup G :=
(mul_right_cancel : ∀ a b c : G, a * b = c * b → a = c)

/-- An `add_right_cancel_semigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[protect_proj, ancestor add_semigroup]
class add_right_cancel_semigroup (G : Type u) extends add_semigroup G :=
(add_right_cancel : ∀ a b c : G, a + b = c + b → a = c)
attribute [to_additive add_right_cancel_semigroup] right_cancel_semigroup

section right_cancel_semigroup
variables {G : Type u} [right_cancel_semigroup G] {a b c : G}

@[to_additive]
lemma mul_right_cancel : a * b = c * b → a = c :=
right_cancel_semigroup.mul_right_cancel a b c

@[to_additive]
lemma mul_right_cancel_iff : b * a = c * a ↔ b = c :=
⟨mul_right_cancel, congr_arg _⟩

@[to_additive]
theorem mul_left_injective (a : G) : function.injective (λ x, x * a) :=
λ b c, mul_right_cancel

@[simp, to_additive]
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
(mul_left_injective a).eq_iff

@[to_additive]
theorem mul_ne_mul_left (a : G) {b c : G} : b * a ≠ c * a ↔ b ≠ c :=
(mul_left_injective a).ne_iff

end right_cancel_semigroup

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
@[ancestor has_one has_mul]
class mul_one_class (M : Type u) extends has_one M, has_mul M :=
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)

/-- Typeclass for expressing that a type `M` with addition and a zero satisfies
`0 + a = a` and `a + 0 = a` for all `a : M`. -/
@[ancestor has_zero has_add]
class add_zero_class (M : Type u) extends has_zero M, has_add M :=
(zero_add : ∀ (a : M), 0 + a = a)
(add_zero : ∀ (a : M), a + 0 = a)

attribute [to_additive] mul_one_class

section mul_one_class
variables {M : Type u} [mul_one_class M]

@[ematch, simp, to_additive]
lemma one_mul : ∀ a : M, 1 * a = a :=
mul_one_class.one_mul

@[ematch, simp, to_additive]
lemma mul_one : ∀ a : M, a * 1 = a :=
mul_one_class.mul_one

@[to_additive]
instance mul_one_class.to_is_left_id : is_left_id M (*) 1 :=
⟨ mul_one_class.one_mul ⟩

@[to_additive]
instance mul_one_class.to_is_right_id : is_right_id M (*) 1 :=
⟨ mul_one_class.mul_one ⟩

end mul_one_class



section
variables {M : Type u}

-- use `x * npow_rec n x` and not `npow_rec n x * x` in the definition to make sure that
-- definitional unfolding of `npow_rec` is blocked, to avoid deep recursion issues.
/-- The fundamental power operation in a monoid. `npow_rec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def npow_rec [has_one M] [has_mul M] : ℕ → M → M
| 0     a := 1
| (n+1) a := a * npow_rec n a

/-- The fundamental scalar multiplication in an additive monoid. `nsmul_rec n a = a+a+...+a` n
times. Use instead `n • a`, which has better definitional behavior. -/
def nsmul_rec [has_zero M] [has_add M] : ℕ → M → M
| 0     a := 0
| (n+1) a := a + nsmul_rec n a

attribute [to_additive] npow_rec

end


/-- Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = metric_space` and `P = topological_space`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `metric_space` / `topological_space`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `topological_space`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `metric_space` and
`topological_space` called `uniform_space`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`uniform_space.of_core` or `real_inner_product.of_core`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/
library_note "forgetful inheritance"

/-- `try_refl_tac` solves goals of the form `∀ a b, f a b = g a b`,
if they hold by definition. -/
meta def try_refl_tac : tactic unit := `[intros; refl]

/-!
### Design note on `add_monoid` and `monoid`

An `add_monoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `polynomial ℕ` would have two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself).

To solve this issue, we embed an `ℕ`-action in the definition of an `add_monoid` (which is by
default equal to the naive action `a + ... + a`, but can be adjusted when needed), and declare
a `has_scalar ℕ α` instance using this action. See Note [forgetful inheritance] for more
explanations on this pattern.

For example, when we define `polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `add_monoid`). In this way, the two natural `has_scalar ℕ (polynomial ℕ)` instances are defeq.

The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.

Nice notation and a basic theory for the power function on monoids and the `ℕ`-action on additive
monoids are built in the file `algebra.group_power.basic`. For now, we only register the most basic
properties that we need right away.

In the definition, we use `n.succ` instead of `n + 1` in the `nsmul_succ'` and `npow_succ'` fields
to make sure that `to_additive` is not confused (otherwise, it would try to convert `1 : ℕ`
to `0 : ℕ`).
-/

/-- An `add_monoid` is an `add_semigroup` with an element `0` such that `0 + a = a + 0 = a`. -/
@[ancestor add_semigroup add_zero_class]
class add_monoid (M : Type u) extends add_semigroup M, add_zero_class M :=
(nsmul : ℕ → M → M := nsmul_rec)
(nsmul_zero' : ∀ x, nsmul 0 x = 0 . try_refl_tac)
(nsmul_succ' : ∀ (n : ℕ) x, nsmul n.succ x = x + nsmul n x . try_refl_tac)

export add_monoid (nsmul)

/-- A `monoid` is a `semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[ancestor semigroup mul_one_class, to_additive]
class monoid (M : Type u) extends semigroup M, mul_one_class M :=
(npow : ℕ → M → M := npow_rec)
(npow_zero' : ∀ x, npow 0 x = 1 . try_refl_tac)
(npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x . try_refl_tac)

export monoid (npow)

section monoid
variables {M : Type u} [monoid M]

@[to_additive]
lemma left_inv_eq_right_inv {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c :=
by rw [←one_mul c, ←hba, mul_assoc, hac, mul_one b]

end monoid

lemma npow_one {M : Type u} [monoid M] (x : M) :
  npow 1 x = x :=
by simp [monoid.npow_succ', monoid.npow_zero']

lemma nsmul_one' {M : Type u} [add_monoid M] (x : M) :
  nsmul 1 x = x :=
by simp [add_monoid.nsmul_succ', add_monoid.nsmul_zero']

attribute [to_additive nsmul_one'] npow_one

@[to_additive nsmul_add']
lemma npow_add {M : Type u} [monoid M] (m n : ℕ) (x : M) :
  npow (m + n) x = npow m x * npow n x :=
begin
  induction m with m ih,
  { rw [nat.zero_add, monoid.npow_zero', one_mul], },
  { rw [nat.succ_add, monoid.npow_succ', monoid.npow_succ', ih, ← mul_assoc] }
end

/-- An additive commutative monoid is an additive monoid with commutative `(+)`. -/
@[protect_proj, ancestor add_monoid add_comm_semigroup]
class add_comm_monoid (M : Type u) extends add_monoid M, add_comm_semigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[protect_proj, ancestor monoid comm_semigroup, to_additive]
class comm_monoid (M : Type u) extends monoid M, comm_semigroup M

section left_cancel_monoid

/-- An additive monoid in which addition is left-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_left_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor add_left_cancel_semigroup add_monoid]
class add_left_cancel_monoid (M : Type u) extends add_left_cancel_semigroup M, add_monoid M

/-- A monoid in which multiplication is left-cancellative. -/
@[protect_proj, ancestor left_cancel_semigroup monoid, to_additive add_left_cancel_monoid]
class left_cancel_monoid (M : Type u) extends left_cancel_semigroup M, monoid M

end left_cancel_monoid

section right_cancel_monoid

/-- An additive monoid in which addition is right-cancellative.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor add_right_cancel_semigroup add_monoid]
class add_right_cancel_monoid (M : Type u) extends add_right_cancel_semigroup M, add_monoid M

/-- A monoid in which multiplication is right-cancellative. -/
@[protect_proj, ancestor right_cancel_semigroup monoid, to_additive add_right_cancel_monoid]
class right_cancel_monoid (M : Type u) extends right_cancel_semigroup M, monoid M

end right_cancel_monoid

section cancel_monoid

/-- An additive monoid in which addition is cancellative on both sides.
Main examples are `ℕ` and groups. This is the right typeclass for many sum lemmas, as having a zero
is useful to define the sum over the empty set, so `add_right_cancel_semigroup` is not enough. -/
@[protect_proj, ancestor add_left_cancel_monoid add_right_cancel_monoid]
class add_cancel_monoid (M : Type u)
  extends add_left_cancel_monoid M, add_right_cancel_monoid M

/-- A monoid in which multiplication is cancellative. -/
@[protect_proj, ancestor left_cancel_monoid right_cancel_monoid, to_additive add_cancel_monoid]
class cancel_monoid (M : Type u) extends left_cancel_monoid M, right_cancel_monoid M

/-- Commutative version of add_cancel_monoid. -/
@[protect_proj, ancestor add_left_cancel_monoid add_comm_monoid]
class add_cancel_comm_monoid (M : Type u) extends add_left_cancel_monoid M, add_comm_monoid M

/-- Commutative version of cancel_monoid. -/
@[protect_proj, ancestor left_cancel_monoid comm_monoid, to_additive add_cancel_comm_monoid]
class cancel_comm_monoid (M : Type u) extends left_cancel_monoid M, comm_monoid M

@[priority 100, to_additive] -- see Note [lower instance priority]
instance cancel_comm_monoid.to_cancel_monoid (M : Type u) [cancel_comm_monoid M] :
  cancel_monoid M :=
{ mul_right_cancel := λ a b c h, mul_left_cancel $ by rw [mul_comm, h, mul_comm],
  .. ‹cancel_comm_monoid M› }

end cancel_monoid

/-- The fundamental power operation in a group. `gpow_rec n a = a*a*...*a` n times, for integer `n`.
Use instead `a ^ n`,  which has better definitional behavior. -/
def gpow_rec {M : Type*} [has_one M] [has_mul M] [has_inv M] : ℤ → M → M
| (int.of_nat n) a := npow_rec n a
| -[1+ n]    a := (npow_rec n.succ a) ⁻¹

/-- The fundamental scalar multiplication in an additive group. `gsmul_rec n a = a+a+...+a` n
times, for integer `n`. Use instead `n • a`, which has better definitional behavior. -/
def gsmul_rec {M : Type*} [has_zero M] [has_add M] [has_neg M]: ℤ → M → M
| (int.of_nat n) a := nsmul_rec n a
| -[1+ n]    a := - (nsmul_rec n.succ a)

attribute [to_additive] gpow_rec

/-- A `div_inv_monoid` is a `monoid` with operations `/` and `⁻¹` satisfying
`div_eq_mul_inv : ∀ a b, a / b = a * b⁻¹`.

This is the immediate common ancestor of `group` and `group_with_zero`,
in order to deduplicate the name `div_eq_mul_inv`.
The default for `div` is such that `a / b = a * b⁻¹` holds by definition.

Adding `div` as a field rather than defining `a / b := a * b⁻¹` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_div (foo X)` instance but no
`∀ X, has_inv (foo X)`, e.g. when `foo X` is a `euclidean_domain`. Suppose we
also have an instance `∀ X [cromulent X], group_with_zero (foo X)`. Then the
`(/)` coming from `group_with_zero_has_div` cannot be definitionally equal to
the `(/)` coming from `foo.has_div`.

In the same way, adding a `gpow` field makes it possible to avoid definitional failures
in diamonds. See the definition of `monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj, ancestor monoid has_inv has_div]
class div_inv_monoid (G : Type u) extends monoid G, has_inv G, has_div G :=
(div := λ a b, a * b⁻¹)
(div_eq_mul_inv : ∀ a b : G, a / b = a * b⁻¹ . try_refl_tac)
(gpow : ℤ → G → G := gpow_rec)
(gpow_zero' : ∀ (a : G), gpow 0 a = 1 . try_refl_tac)
(gpow_succ' :
  ∀ (n : ℕ) (a : G), gpow (int.of_nat n.succ) a = a * gpow (int.of_nat n) a  . try_refl_tac)
(gpow_neg' :
  ∀ (n : ℕ) (a : G), gpow (-[1+ n]) a = (gpow n.succ a) ⁻¹ . try_refl_tac)

export div_inv_monoid (gpow)

/-- A `sub_neg_monoid` is an `add_monoid` with unary `-` and binary `-` operations
satisfying `sub_eq_add_neg : ∀ a b, a - b = a + -b`.

The default for `sub` is such that `a - b = a + -b` holds by definition.

Adding `sub` as a field rather than defining `a - b := a + -b` allows us to
avoid certain classes of unification failures, for example:
Let `foo X` be a type with a `∀ X, has_sub (foo X)` instance but no
`∀ X, has_neg (foo X)`. Suppose we also have an instance
`∀ X [cromulent X], add_group (foo X)`. Then the `(-)` coming from
`add_group.has_sub` cannot be definitionally equal to the `(-)` coming from
`foo.has_sub`.

In the same way, adding a `gsmul` field makes it possible to avoid definitional failures
in diamonds. See the definition of `add_monoid` and Note [forgetful inheritance] for more
explanations on this.
-/
@[protect_proj, ancestor add_monoid has_neg has_sub]
class sub_neg_monoid (G : Type u) extends add_monoid G, has_neg G, has_sub G :=
(sub := λ a b, a + -b)
(sub_eq_add_neg : ∀ a b : G, a - b = a + -b . try_refl_tac)
(gsmul : ℤ → G → G := gsmul_rec)
(gsmul_zero' : ∀ (a : G), gsmul 0 a = 0 . try_refl_tac)
(gsmul_succ' :
  ∀ (n : ℕ) (a : G), gsmul (int.of_nat n.succ) a = a + gsmul (int.of_nat n) a  . try_refl_tac)
(gsmul_neg' :
  ∀ (n : ℕ) (a : G), gsmul (-[1+ n]) a = - (gsmul n.succ a) . try_refl_tac)

export sub_neg_monoid (gsmul)

attribute [to_additive sub_neg_monoid] div_inv_monoid

@[to_additive]
lemma div_eq_mul_inv {G : Type u} [div_inv_monoid G] :
  ∀ a b : G, a / b = a * b⁻¹ :=
div_inv_monoid.div_eq_mul_inv

/-- A `group` is a `monoid` with an operation `⁻¹` satisfying `a⁻¹ * a = 1`.

There is also a division operation `/` such that `a / b = a * b⁻¹`,
with a default so that `a / b = a * b⁻¹` holds by definition.
-/
@[protect_proj, ancestor div_inv_monoid]
class group (G : Type u) extends div_inv_monoid G :=
(mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

/-- An `add_group` is an `add_monoid` with a unary `-` satisfying `-a + a = 0`.

There is also a binary operation `-` such that `a - b = a + -b`,
with a default so that `a - b = a + -b` holds by definition.
-/
@[protect_proj, ancestor sub_neg_monoid]
class add_group (A : Type u) extends sub_neg_monoid A :=
(add_left_neg : ∀ a : A, -a + a = 0)

attribute [to_additive] group

/-- Abbreviation for `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.

Useful because it corresponds to the fact that `Grp` is a subcategory of `Mon`.
Not an instance since it duplicates `@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)`.
-/
@[to_additive
"Abbreviation for `@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`.

Useful because it corresponds to the fact that `AddGroup` is a subcategory of `AddMon`.
Not an instance since it duplicates
`@sub_neg_monoid.to_add_monoid _ (@add_group.to_sub_neg_monoid _ _)`."]
def group.to_monoid (G : Type u) [group G] : monoid G :=
@div_inv_monoid.to_monoid _ (@group.to_div_inv_monoid _ _)

section group
variables {G : Type u} [group G] {a b c : G}

@[simp, to_additive]
lemma mul_left_inv : ∀ a : G, a⁻¹ * a = 1 :=
group.mul_left_inv

@[to_additive] lemma inv_mul_self (a : G) : a⁻¹ * a = 1 := mul_left_inv a

@[simp, to_additive]
lemma inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b :=
by rw [← mul_assoc, mul_left_inv, one_mul]

@[simp, to_additive]
lemma inv_eq_of_mul_eq_one (h : a * b = 1) : a⁻¹ = b :=
left_inv_eq_right_inv (inv_mul_self a) h

@[simp, to_additive]
lemma inv_inv (a : G) : (a⁻¹)⁻¹ = a :=
inv_eq_of_mul_eq_one (mul_left_inv a)

@[simp, to_additive]
lemma mul_right_inv (a : G) : a * a⁻¹ = 1 :=
have a⁻¹⁻¹ * a⁻¹ = 1 := mul_left_inv a⁻¹,
by rwa [inv_inv] at this

@[to_additive] lemma mul_inv_self (a : G) : a * a⁻¹ = 1 := mul_right_inv a

@[simp, to_additive]
lemma mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a :=
by rw [mul_assoc, mul_right_inv, mul_one]

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance group.to_cancel_monoid : cancel_monoid G :=
{ mul_right_cancel := λ a b c h, by rw [← mul_inv_cancel_right a b, h, mul_inv_cancel_right],
  mul_left_cancel := λ a b c h, by rw [← inv_mul_cancel_left a b, h, inv_mul_cancel_left],
  ..‹group G› }

end group

/-- A commutative group is a group with commutative `(*)`. -/
@[protect_proj, ancestor group comm_monoid]
class comm_group (G : Type u) extends group G, comm_monoid G
/-- An additive commutative group is an additive group with commutative `(+)`. -/
@[protect_proj, ancestor add_group add_comm_monoid]
class add_comm_group (G : Type u) extends add_group G, add_comm_monoid G
attribute [to_additive] comm_group
attribute [instance, priority 300] add_comm_group.to_add_comm_monoid

section comm_group

variables {G : Type u} [comm_group G]

@[priority 100, to_additive]    -- see Note [lower instance priority]
instance comm_group.to_cancel_comm_monoid : cancel_comm_monoid G :=
{ ..‹comm_group G›,
  ..group.to_cancel_monoid }

end comm_group
