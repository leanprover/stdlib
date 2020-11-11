/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import group_theory.coset
import tactic

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

open_locale big_operators
open function

/-- Typeclass for types with a scalar multiplication operation, denoted `•` (`\bu`) -/
class has_scalar (α : Type u) (γ : Type v) := (smul : α → γ → γ)

infixr ` • `:73 := has_scalar.smul

/-- Typeclass for multiplicative actions by monoids. This generalizes group actions. -/
@[protect_proj] class mul_action (α : Type u) (β : Type v) [monoid α] extends has_scalar α β :=
(one_smul : ∀ b : β, (1 : α) • b = b)
(mul_smul : ∀ (x y : α) (b : β), (x * y) • b = x • y • b)

/-- A typeclass mixin saying that two actions on the same space commute. -/
class smul_comm_class (M N α : Type*) [has_scalar M α] [has_scalar N α] : Prop :=
(smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a)

export mul_action (mul_smul) smul_comm_class (smul_comm)

/-- Commutativity of actions is a symmetric relation. This lemma can't be an instance because this
would cause a loop in the instance search graph. -/
lemma smul_comm_class.symm (M N α : Type*) [has_scalar M α] [has_scalar N α]
  [smul_comm_class M N α] : smul_comm_class N M α :=
⟨λ a' a b, (smul_comm a a' b).symm⟩

instance smul_comm_class_self (M α : Type*) [comm_monoid M] [mul_action M α] :
  smul_comm_class M M α :=
⟨λ a a' b, by rw [← mul_smul, mul_comm, mul_smul]⟩

section
variables [monoid α] [mul_action α β]

lemma smul_smul (a₁ a₂ : α) (b : β) : a₁ • a₂ • b = (a₁ * a₂) • b := (mul_smul _ _ _).symm

variable (α)
@[simp] theorem one_smul (b : β) : (1 : α) • b = b := mul_action.one_smul _

variables {α}

@[simp] lemma units.inv_smul_smul (u : units α) (x : β) :
  (↑u⁻¹:α) • (u:α) • x = x :=
by rw [smul_smul, u.inv_mul, one_smul]

@[simp] lemma units.smul_inv_smul (u : units α) (x : β) :
  (u:α) • (↑u⁻¹:α) • x = x :=
by rw [smul_smul, u.mul_inv, one_smul]

/-- If a monoid `α` acts on `β`, then each `u : units α` defines a permutation of `β`. -/
def units.smul_perm_hom : units α →* equiv.perm β :=
{ to_fun := λ u, ⟨λ x, (u:α) • x, λ x, (↑u⁻¹:α) • x, u.inv_smul_smul, u.smul_inv_smul⟩,
  map_one' := equiv.ext $ one_smul α,
  map_mul' := λ u₁ u₂, equiv.ext $ mul_smul (u₁:α) u₂ }

@[simp] lemma units.smul_left_cancel (u : units α) {x y : β} :
  (u:α) • x = (u:α) • y ↔ x = y :=
u.smul_perm_hom.apply_eq_iff_eq

lemma units.smul_eq_iff_eq_inv_smul (u : units α) {x y : β} :
  (u:α) • x = y ↔ x = (↑u⁻¹:α) • y :=
u.smul_perm_hom.apply_eq_iff_eq_symm_apply

lemma is_unit.smul_left_cancel {a : α} (ha : is_unit a) {x y : β} :
  a • x = a • y ↔ x = y :=
let ⟨u, hu⟩ := ha in hu ▸ u.smul_left_cancel

/-- Pullback a multiplicative action along an injective map respecting `•`. -/
protected def function.injective.mul_action [has_scalar α γ] (f : γ → β)
  (hf : injective f) (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  mul_action α γ :=
{ smul := (•),
  one_smul := λ x, hf $ (smul _ _).trans $ one_smul _ (f x),
  mul_smul := λ c₁ c₂ x, hf $ by simp only [smul, mul_smul] }

/-- Pushforward a multiplicative action along a surjective map respecting `•`. -/
protected def function.surjective.mul_action [has_scalar α γ] (f : β → γ) (hf : surjective f)
  (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  mul_action α γ :=
{ smul := (•),
  one_smul := λ y, by { rcases hf y with ⟨x, rfl⟩, rw [← smul, one_smul] },
  mul_smul := λ c₁ c₂ y, by { rcases hf y with ⟨x, rfl⟩, simp only [← smul, mul_smul] } }

section gwz

variables {G : Type*} [group_with_zero G] [mul_action G β]

@[simp]
lemma inv_smul_smul' {c : G} (hc : c ≠ 0) (x : β) : c⁻¹ • c • x = x :=
(units.mk0 c hc).inv_smul_smul x

@[simp]
lemma smul_inv_smul' {c : G} (hc : c ≠ 0) (x : β) : c • c⁻¹ • x = x :=
(units.mk0 c hc).smul_inv_smul x

lemma inv_smul_eq_iff' {a : G} (ha : a ≠ 0) {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
by { split; intro h, rw [← h, smul_inv_smul' ha], rw [h, inv_smul_smul' ha] }

lemma eq_inv_smul_iff' {a : G} (ha : a ≠ 0) {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
by { split; intro h, rw [h, smul_inv_smul' ha], rw [← h, inv_smul_smul' ha] }

end gwz

variables (p : Prop) [decidable p]

lemma ite_smul (a₁ a₂ : α) (b : β) : (ite p a₁ a₂) • b = ite p (a₁ • b) (a₂ • b) :=
by split_ifs; refl

lemma smul_ite (a : α) (b₁ b₂ : β) : a • (ite p b₁ b₂) = ite p (a • b₁) (a • b₂) :=
by split_ifs; refl

end

section compatible_scalar

/-- An instance of `is_scalar_tower M N α` states that the multiplicative
action of `M` on `α` is determined by the multiplicative actions of `M` on `N`
and `N` on `α`. -/
class is_scalar_tower (M N α : Type*) [has_scalar M N] [has_scalar N α] [has_scalar M α] : Prop :=
(smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • (y • z))

@[simp] lemma smul_assoc {M N} [has_scalar M N] [has_scalar N α] [has_scalar M α]
  [is_scalar_tower M N α] (x : M) (y : N) (z : α) :
  (x • y) • z = x • y • z :=
is_scalar_tower.smul_assoc x y z

@[simp] lemma smul_one_smul {M} (N) [monoid N] [has_scalar M N] [mul_action N α] [has_scalar M α]
  [is_scalar_tower M N α] (x : M) (y : α) :
  (x • (1 : N)) • y = x • y :=
by rw [smul_assoc, one_smul]

end compatible_scalar

namespace mul_action

variables (α) [monoid α]

/-- The regular action of a monoid on itself by left multiplication. -/
def regular : mul_action α α :=
{ smul := λ a₁ a₂, a₁ * a₂,
  one_smul := λ a, one_mul a,
  mul_smul := λ a₁ a₂ a₃, mul_assoc _ _ _, }

variables [mul_action α β]

section regular

local attribute [instance] regular

instance is_scalar_tower.left : is_scalar_tower α α β :=
⟨λ x y z, mul_smul x y z⟩

end regular

/-- The orbit of an element under an action. -/
def orbit (b : β) := set.range (λ x : α, x • b)

variable {α}

lemma mem_orbit_iff {b₁ b₂ : β} : b₂ ∈ orbit α b₁ ↔ ∃ x : α, x • b₁ = b₂ :=
iff.rfl

@[simp] lemma mem_orbit (b : β) (x : α) : x • b ∈ orbit α b :=
⟨x, rfl⟩

@[simp] lemma mem_orbit_self (b : β) : b ∈ orbit α b :=
⟨1, by simp [mul_action.one_smul]⟩

variable (α)

/-- The stabilizer of an element under an action, i.e. what sends the element to itself. Note
that this is a set: for the group stabilizer see `stabilizer`. -/
def stabilizer_carrier (b : β) : set α :=
{x : α | x • b = b}

variable {α}

@[simp] lemma mem_stabilizer_iff {b : β} {x : α} :
  x ∈ stabilizer_carrier α b ↔ x • b = b := iff.rfl

variables (α) (β)

/-- The set of elements fixed under the whole action. -/
def fixed_points : set β := {b : β | ∀ x : α, x • b = b}

/-- `fixed_by g` is the subfield of elements fixed by `g`. -/
def fixed_by (g : α) : set β :=
{ x | g • x = x }

theorem fixed_eq_Inter_fixed_by : fixed_points α β = ⋂ g : α, fixed_by α β g :=
set.ext $ λ x, ⟨λ hx, set.mem_Inter.2 $ λ g, hx g, λ hx g, by exact (set.mem_Inter.1 hx g : _)⟩

variables {α} (β)

@[simp] lemma mem_fixed_points {b : β} :
  b ∈ fixed_points α β ↔ ∀ x : α, x • b = b := iff.rfl

@[simp] lemma mem_fixed_by {g : α} {b : β} :
  b ∈ fixed_by α β g ↔ g • b = b := iff.rfl

lemma mem_fixed_points' {b : β} : b ∈ fixed_points α β ↔
  (∀ b', b' ∈ orbit α b → b' = b) :=
⟨λ h b h₁, let ⟨x, hx⟩ := mem_orbit_iff.1 h₁ in hx ▸ h x,
λ h b, mem_stabilizer_iff.2 (h _ (mem_orbit _ _))⟩

/-- An action of `α` on `β` and a monoid homomorphism `γ → α` induce an action of `γ` on `β`. -/
def comp_hom [monoid γ] (g : γ →* α) :
  mul_action γ β :=
{ smul := λ x b, (g x) • b,
  one_smul := by simp [g.map_one, mul_action.one_smul],
  mul_smul := by simp [g.map_mul, mul_action.mul_smul] }

variables (α) {β}

/-- The stabilizer of a point `b` as a submonoid of `α`. -/
def stabilizer.submonoid (b : β) : submonoid α :=
{ carrier := stabilizer_carrier α b,
  one_mem' := one_smul _ b,
  mul_mem' := λ a a' (ha : a • b = b) (hb : a' • b = b),
    by rw [mem_stabilizer_iff, ←smul_smul, hb, ha] }

variables (α β)

/-- Embedding induced by action. -/
def to_fun : β ↪ (α → β) :=
⟨λ y x, x • y, λ y₁ y₂ H, one_smul α y₁ ▸ one_smul α y₂ ▸ by convert congr_fun H 1⟩

variables {α β}

@[simp] lemma to_fun_apply (x : α) (y : β) : mul_action.to_fun α β y x = x • y :=
rfl

end mul_action


section
variables [group α] [mul_action α β]

@[simp] lemma inv_smul_smul (c : α) (x : β) : c⁻¹ • c • x = x :=
(to_units c).inv_smul_smul x

@[simp] lemma smul_inv_smul (c : α) (x : β) : c • c⁻¹ • x = x :=
(to_units c).smul_inv_smul x

lemma inv_smul_eq_iff {a : α} {x y : β} : a⁻¹ • x = y ↔ x = a • y :=
begin
  split;
  rintro rfl,
  {rw smul_inv_smul},
  {rw inv_smul_smul},
end

lemma eq_inv_smul_iff {a : α} {x y : β} : x = a⁻¹ • y ↔ a • x = y :=
begin
  split;
  rintro rfl,
  {rw smul_inv_smul},
  {rw inv_smul_smul},
end

namespace mul_action
variable (α)

/-- The stabilizer of an element under an action, i.e. what sends the element to itself.
A subgroup.-/
def stabilizer (b : β) : subgroup α :=
{ inv_mem' := λ a (ha : a • b = b), show a⁻¹ • b = b, by rw [inv_smul_eq_iff, ha]
  ..stabilizer.submonoid α b
}

variable (β)

/-- Given an action of a group `α` on a set `β`, each `g : α` defines a permutation of `β`. -/
def to_perm : α →* equiv.perm β :=
units.smul_perm_hom.comp to_units.to_monoid_hom

variables {α} {β}

protected lemma bijective (g : α) : bijective (λ b : β, g • b) :=
(to_perm α β g).bijective

lemma orbit_eq_iff {a b : β} :
   orbit α a = orbit α b ↔ a ∈ orbit α b:=
⟨λ h, h ▸ mem_orbit_self _,
λ ⟨x, (hx : x • b = a)⟩, set.ext (λ c, ⟨λ ⟨y, (hy : y • a = c)⟩, ⟨y * x,
  show (y * x) • b = c, by rwa [mul_action.mul_smul, hx]⟩,
  λ ⟨y, (hy : y • b = c)⟩, ⟨y * x⁻¹,
    show (y * x⁻¹) • a = c, by
      conv {to_rhs, rw [← hy, ← mul_one y, ← inv_mul_self x, ← mul_assoc,
        mul_action.mul_smul, hx]}⟩⟩)⟩

variables (α) {β}

/-- The stabilizer of a point `b` as a subgroup of `α`. -/
def stabilizer.subgroup (b : β) : subgroup α :=
{ inv_mem' := λ x (hx : x • b = b), show x⁻¹ • b = b,
    by rw [← hx, ← mul_action.mul_smul, inv_mul_self, mul_action.one_smul, hx],
  ..stabilizer.submonoid α b }

variables {β}

@[simp] lemma mem_orbit_smul (g : α) (a : β) : a ∈ orbit α (g • a) :=
⟨g⁻¹, by simp⟩

@[simp] lemma smul_mem_orbit_smul (g h : α) (a : β) : g • a ∈ orbit α (h • a) :=
⟨g * h⁻¹, by simp [mul_smul]⟩

variables (α) (β)
/-- The relation "in the same orbit". -/
def orbit_rel : setoid β :=
{ r := λ a b, a ∈ orbit α b,
  iseqv := ⟨mem_orbit_self, λ a b, by simp [orbit_eq_iff.symm, eq_comm],
    λ a b, by simp [orbit_eq_iff.symm, eq_comm] {contextual := tt}⟩ }

variables {α β}

open quotient_group mul_action

/-- Action on left cosets. -/
def mul_left_cosets (H : subgroup α)
  (x : α) (y : quotient H) : quotient H :=
quotient.lift_on' y (λ y, quotient_group.mk ((x : α) * y))
  (λ a b (hab : _ ∈ H), quotient_group.eq.2
    (by rwa [mul_inv_rev, ← mul_assoc, mul_assoc (a⁻¹), inv_mul_self, mul_one]))

instance quotient (H : subgroup α) : mul_action α (quotient H) :=
{ smul := mul_left_cosets H,
  one_smul := λ a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [subgroup.one_mem])),
  mul_smul := λ x y a, quotient.induction_on' a (λ a, quotient_group.eq.2
    (by simp [mul_inv_rev, subgroup.one_mem, mul_assoc])) }

instance mul_left_cosets_comp_subtype_val (H I : subgroup α)  :
  mul_action I (quotient H) :=
mul_action.comp_hom (quotient H) (subgroup.subtype I)

variables (α) {β} (x : β)

/-- The canonical map from the quotient of the stabilizer to the set. -/
def of_quotient_stabilizer (g : quotient (mul_action.stabilizer α x)) : β :=
quotient.lift_on' g (•x) $ λ g1 g2 H,
calc  g1 • x
    = g1 • (g1⁻¹ * g2) • x : congr_arg _ H.symm
... = g2 • x : by rw [smul_smul, mul_inv_cancel_left]

@[simp] theorem of_quotient_stabilizer_mk (g : α) :
  of_quotient_stabilizer α x (quotient_group.mk g) = g • x :=
rfl

theorem of_quotient_stabilizer_mem_orbit (g) : of_quotient_stabilizer α x g ∈ orbit α x :=
quotient.induction_on' g $ λ g, ⟨g, rfl⟩

theorem of_quotient_stabilizer_smul (g : α) (g' : quotient (mul_action.stabilizer α x)) :
  of_quotient_stabilizer α x (g • g') = g • of_quotient_stabilizer α x g' :=
quotient.induction_on' g' $ λ _, mul_smul _ _ _

theorem injective_of_quotient_stabilizer : function.injective (of_quotient_stabilizer α x) :=
λ y₁ y₂, quotient.induction_on₂' y₁ y₂ $ λ g₁ g₂ (H : g₁ • x = g₂ • x), quotient.sound' $
show (g₁⁻¹ * g₂) • x = x, by rw [mul_smul, ← H, inv_smul_smul]

/-- Orbit-stabilizer theorem. -/
noncomputable def orbit_equiv_quotient_stabilizer (b : β) :
  orbit α b ≃ quotient (stabilizer α b) :=
equiv.symm $ equiv.of_bijective
  (λ g, ⟨of_quotient_stabilizer α b g, of_quotient_stabilizer_mem_orbit α b g⟩)
  ⟨λ x y hxy, injective_of_quotient_stabilizer α b (by convert congr_arg subtype.val hxy),
  λ ⟨b, ⟨g, hgb⟩⟩, ⟨g, subtype.eq hgb⟩⟩

@[simp] theorem orbit_equiv_quotient_stabilizer_symm_apply (b : β) (a : α) :
  ((orbit_equiv_quotient_stabilizer α b).symm a : β) = a • b :=
rfl

end mul_action

end

/-- Typeclass for multiplicative actions on additive structures. This generalizes group modules. -/
class distrib_mul_action (α : Type u) (β : Type v) [monoid α] [add_monoid β] extends mul_action α β :=
(smul_add : ∀(r : α) (x y : β), r • (x + y) = r • x + r • y)
(smul_zero : ∀(r : α), r • (0 : β) = 0)

section
variables [monoid α] [add_monoid β] [distrib_mul_action α β]

theorem smul_add (a : α) (b₁ b₂ : β) : a • (b₁ + b₂) = a • b₁ + a • b₂ :=
distrib_mul_action.smul_add _ _ _

@[simp] theorem smul_zero (a : α) : a • (0 : β) = 0 :=
distrib_mul_action.smul_zero _

/-- Pullback a distributive multiplicative action along an injective additive monoid
homomorphism. -/
protected def function.injective.distrib_mul_action [add_monoid γ] [has_scalar α γ] (f : γ →+ β)
  (hf : injective f) (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  distrib_mul_action α γ :=
{ smul := (•),
  smul_add := λ c x y, hf $ by simp only [smul, f.map_add, smul_add],
  smul_zero := λ c, hf $ by simp only [smul, f.map_zero, smul_zero],
  .. hf.mul_action f smul }

/-- Pushforward a distributive multiplicative action along a surjective additive monoid
homomorphism.-/
protected def function.surjective.distrib_mul_action [add_monoid γ] [has_scalar α γ] (f : β →+ γ)
  (hf : surjective f) (smul : ∀ (c : α) x, f (c • x) = c • f x) :
  distrib_mul_action α γ :=
{ smul := (•),
  smul_add := λ c x y, by { rcases hf x with ⟨x, rfl⟩, rcases hf y with ⟨y, rfl⟩,
    simp only [smul_add, ← smul, ← f.map_add] },
  smul_zero := λ c, by simp only [← f.map_zero, ← smul, smul_zero],
  .. hf.mul_action f smul }

theorem units.smul_eq_zero (u : units α) {x : β} : (u : α) • x = 0 ↔ x = 0 :=
⟨λ h, by rw [← u.inv_smul_smul x, h, smul_zero], λ h, h.symm ▸ smul_zero _⟩

theorem units.smul_ne_zero (u : units α) {x : β} : (u : α) • x ≠ 0 ↔ x ≠ 0 :=
not_congr u.smul_eq_zero

@[simp] theorem is_unit.smul_eq_zero {u : α} (hu : is_unit u) {x : β} :
  u • x = 0 ↔ x = 0 :=
exists.elim hu $ λ u hu, hu ▸ u.smul_eq_zero

variable (β)

/-- Scalar multiplication by `r` as an `add_monoid_hom`. -/
def const_smul_hom (r : α) : β →+ β :=
{ to_fun := (•) r,
  map_zero' := smul_zero r,
  map_add' := smul_add r }

variable {β}

@[simp] lemma const_smul_hom_apply (r : α) (x : β) :
  const_smul_hom β r x = r • x := rfl

lemma list.smul_sum {r : α} {l : list β} :
  r • l.sum = (l.map ((•) r)).sum :=
(const_smul_hom β r).map_list_sum l

end

section
variables [monoid α] [add_comm_monoid β] [distrib_mul_action α β]

lemma multiset.smul_sum {r : α} {s : multiset β} :
  r • s.sum = (s.map ((•) r)).sum :=
(const_smul_hom β r).map_multiset_sum s

lemma finset.smul_sum {r : α} {f : γ → β} {s : finset γ} :
  r • ∑ x in s, f x = ∑ x in s, r • f x :=
(const_smul_hom β r).map_sum f s

end

section
variables [monoid α] [add_group β] [distrib_mul_action α β]

@[simp] theorem smul_neg (r : α) (x : β) : r • (-x) = -(r • x) :=
eq_neg_of_add_eq_zero $ by rw [← smul_add, neg_add_self, smul_zero]

theorem smul_sub (r : α) (x y : β) : r • (x - y) = r • x - r • y :=
by rw [sub_eq_add_neg, sub_eq_add_neg, smul_add, smul_neg]

end

section
open equiv

/-- This constructs the natural permutation group on `G` that is used to show Cayley's theorem-/
def group_to_perm (G : Type*) [group G] : G →* perm G :=
{ to_fun := λ g,
  { to_fun := λ h, g * h,
    inv_fun := λ h, g⁻¹ * h,
    left_inv := fun h, by group,
    right_inv := λ h, by group },
  map_one' := by {ext, simp},
  map_mul' := λ x y, by { ext, simp, group } }

instance (G : Type*) [group G] : inhabited (G →* perm G) := group_to_perm G

end
