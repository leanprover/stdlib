/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import algebra.group.hom
import algebra.group.type_tags
import algebra.group.units_hom

/-!
# Multiplicative and additive equivs

In this file we define two extensions of `equiv` called `add_equiv` and `mul_equiv`, which are
datatypes representing isomorphisms of `add_monoid`s/`add_group`s and `monoid`s/`group`s.

## Notations

* ``infix ` ≃* `:25 := mul_equiv``
* ``infix ` ≃+ `:25 := add_equiv``

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Implementation notes

The fields for `mul_equiv`, `add_equiv` now avoid the unbundled `is_mul_hom` and `is_add_hom`, as
these are deprecated.

## Tags

equiv, mul_equiv, add_equiv
-/

variables {A : Type*} {B : Type*} {M : Type*} {N : Type*}
  {P : Type*} {Q : Type*} {G : Type*} {H : Type*}

set_option old_structure_cmd true

/-- add_equiv α β is the type of an equiv α ≃ β which preserves addition. -/
@[ancestor equiv add_hom]
structure add_equiv (A B : Type*) [has_add A] [has_add B] extends A ≃ B, add_hom A B

/-- The `equiv` underlying an `add_equiv`. -/
add_decl_doc add_equiv.to_equiv
/-- The `add_hom` underlying a `add_equiv`. -/
add_decl_doc add_equiv.to_add_hom

/-- `mul_equiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[ancestor equiv mul_hom, to_additive]
structure mul_equiv (M N : Type*) [has_mul M] [has_mul N] extends M ≃ N, mul_hom M N

/-- The `equiv` underlying a `mul_equiv`. -/
add_decl_doc mul_equiv.to_equiv
/-- The `mul_hom` underlying a `mul_equiv`. -/
add_decl_doc mul_equiv.to_mul_hom

infix ` ≃* `:25 := mul_equiv
infix ` ≃+ `:25 := add_equiv

namespace mul_equiv

@[to_additive]
instance [has_mul M] [has_mul N] : has_coe_to_fun (M ≃* N) := ⟨_, mul_equiv.to_fun⟩

variables [has_mul M] [has_mul N] [has_mul P] [has_mul Q]

@[simp, to_additive]
lemma to_fun_eq_coe {f : M ≃* N} : f.to_fun = f := rfl

@[to_additive]
lemma coe_to_equiv {f : M ≃* N} : ⇑f.to_equiv = f := rfl

@[simp, to_additive]
lemma coe_to_mul_hom {f : M ≃* N} : ⇑f.to_mul_hom = f := rfl

@[simp, to_additive]
lemma coe_fn_to_equiv {f : M ≃* N} : (f.to_equiv : M → N) = f := rfl

/-- A multiplicative isomorphism preserves multiplication (canonical form). -/
@[simp, to_additive]
lemma map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y := f.map_mul'

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[to_additive "Makes an additive isomorphism from a bijection which preserves addition."]
def mk' (f : M ≃ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N :=
⟨f.1, f.2, f.3, f.4, h⟩

@[to_additive]
protected lemma bijective (e : M ≃* N) : function.bijective e := e.to_equiv.bijective

@[to_additive]
protected lemma injective (e : M ≃* N) : function.injective e := e.to_equiv.injective

@[to_additive]
protected lemma surjective (e : M ≃* N) : function.surjective e := e.to_equiv.surjective

/-- The identity map is a multiplicative isomorphism. -/
@[refl, to_additive "The identity map is an additive isomorphism."]
def refl (M : Type*) [has_mul M] : M ≃* M :=
{ map_mul' := λ _ _, rfl,
..equiv.refl _}

instance : inhabited (M ≃* M) := ⟨refl M⟩

/-- The inverse of an isomorphism is an isomorphism. -/
@[symm, to_additive "The inverse of an isomorphism is an isomorphism."]
def symm (h : M ≃* N) : N ≃* M :=
{ map_mul' := λ n₁ n₂, h.injective $
    begin
      have : ∀ x, h (h.to_equiv.symm.to_fun x) = x := h.to_equiv.apply_symm_apply,
      simp only [this, h.map_mul]
    end,
  .. h.to_equiv.symm}

/-- See Note [custom simps projection] -/
-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting
-- in the whole file.
@[to_additive add_equiv.simps.inv_fun "See Note custom simps projection"]
def simps.inv_fun (e : M ≃* N) : N → M := e.symm

initialize_simps_projections add_equiv (to_fun → apply, inv_fun → symm_apply)
initialize_simps_projections mul_equiv (to_fun → apply, inv_fun → symm_apply)

@[simp, to_additive]
theorem to_equiv_symm (f : M ≃* N) : f.symm.to_equiv = f.to_equiv.symm := rfl

@[simp, to_additive]
theorem coe_mk (f : M → N) (g h₁ h₂ h₃) : ⇑(mul_equiv.mk f g h₁ h₂ h₃) = f := rfl

@[simp, to_additive]
lemma symm_symm : ∀ (f : M ≃* N), f.symm.symm = f
| ⟨f, g, h₁, h₂, h₃⟩ := rfl

@[to_additive]
lemma symm_bijective : function.bijective (symm : (M ≃* N) → (N ≃* M)) :=
equiv.bijective ⟨symm, symm, symm_symm, symm_symm⟩

@[simp, to_additive]
theorem symm_mk (f : M → N) (g h₁ h₂ h₃) :
  (mul_equiv.mk f g h₁ h₂ h₃).symm =
  { to_fun := g, inv_fun := f, ..(mul_equiv.mk f g h₁ h₂ h₃).symm} := rfl

/-- Transitivity of multiplication-preserving isomorphisms -/
@[trans, to_additive "Transitivity of addition-preserving isomorphisms"]
def trans (h1 : M ≃* N) (h2 : N ≃* P) : (M ≃* P) :=
{ map_mul' := λ x y, show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y),
    by rw [h1.map_mul, h2.map_mul],
  ..h1.to_equiv.trans h2.to_equiv }

/-- e.right_inv in canonical form -/
@[simp, to_additive]
lemma apply_symm_apply (e : M ≃* N) : ∀ y, e (e.symm y) = y :=
e.to_equiv.apply_symm_apply

/-- e.left_inv in canonical form -/
@[simp, to_additive]
lemma symm_apply_apply (e : M ≃* N) : ∀ x, e.symm (e x) = x :=
e.to_equiv.symm_apply_apply

@[simp, to_additive]
theorem refl_apply (m : M) : refl M m = m := rfl

@[simp, to_additive]
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[simp, to_additive] theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
e.injective.eq_iff

@[to_additive]
lemma apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
e.to_equiv.apply_eq_iff_eq_symm_apply

@[to_additive]
lemma symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
e.to_equiv.symm_apply_eq

@[to_additive]
lemma eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
e.to_equiv.eq_symm_apply

/-- Two multiplicative isomorphisms agree if they are defined by the
    same underlying function. -/
@[ext, to_additive
  "Two additive isomorphisms agree if they are defined by the same underlying function."]
lemma ext {f g : mul_equiv M N} (h : ∀ x, f x = g x) : f = g :=
begin
  have h₁ : f.to_equiv = g.to_equiv := equiv.ext h,
  cases f, cases g, congr,
  { exact (funext h) },
  { exact congr_arg equiv.inv_fun h₁ }
end

attribute [ext] add_equiv.ext

@[to_additive]
lemma ext_iff {f g : mul_equiv M N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, ext⟩

@[simp, to_additive] lemma mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) :
  (⟨e, e', h₁, h₂, h₃⟩ : M ≃* N) = e := ext $ λ _, rfl

@[simp, to_additive] lemma mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) :
  (mul_equiv.mk f ⇑e h₁ h₂ h₃ : N ≃* M) = e.symm :=
symm_bijective.injective $ ext $ λ x, rfl

@[to_additive]
protected lemma congr_arg {f : mul_equiv M N} : Π {x x' : M}, x = x' → f x = f x'
| _ _ rfl := rfl

@[to_additive]
protected lemma congr_fun {f g : mul_equiv M N} (h : f = g) (x : M) : f x = g x := h ▸ rfl

/-- The `mul_equiv` between two monoids with a unique element. -/
@[to_additive "The `add_equiv` between two add_monoids with a unique element."]
def mul_equiv_of_unique_of_unique {M N}
  [unique M] [unique N] [has_mul M] [has_mul N] : M ≃* N :=
{ map_mul' := λ _ _, subsingleton.elim _ _,
  ..equiv_of_unique_of_unique }

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive] instance {M N} [unique M] [unique N] [has_mul M] [has_mul N] : unique (M ≃* N) :=
{ default := mul_equiv_of_unique_of_unique ,
  uniq := λ _, ext $ λ x, subsingleton.elim _ _}

/-!
## Monoids
-/

/-- A multiplicative equiv of monoids sends 1 to 1 (and is hence a monoid isomorphism). -/
@[simp, to_additive]
lemma map_one {M N} [monoid M] [monoid N] (h : M ≃* N) : h 1 = 1 :=
by rw [←mul_one (h 1), ←h.apply_symm_apply 1, ←h.map_mul, one_mul]

@[simp, to_additive]
lemma map_eq_one_iff {M N} [monoid M] [monoid N] (h : M ≃* N) {x : M} :
  h x = 1 ↔ x = 1 :=
h.map_one ▸ h.to_equiv.apply_eq_iff_eq

@[to_additive]
lemma map_ne_one_iff {M N} [monoid M] [monoid N] (h : M ≃* N) {x : M} :
  h x ≠ 1 ↔ x ≠ 1 :=
⟨mt h.map_eq_one_iff.2, mt h.map_eq_one_iff.1⟩

/-- A bijective `monoid` homomorphism is an isomorphism -/
@[to_additive "A bijective `add_monoid` homomorphism is an isomorphism"]
noncomputable def of_bijective {M N} [monoid M] [monoid N] (f : M →* N)
  (hf : function.bijective f) : M ≃* N :=
{ map_mul' := f.map_mul',
  ..equiv.of_bijective f hf }

/--
Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[to_additive "Extract the forward direction of an additive equivalence
as an addition-preserving function."]
def to_monoid_hom {M N} [monoid M] [monoid N] (h : M ≃* N) : (M →* N) :=
{ map_one' := h.map_one, .. h }

@[simp, to_additive]
lemma coe_to_monoid_hom {M N} [monoid M] [monoid N] (e : M ≃* N) :
  ⇑e.to_monoid_hom = e :=
rfl

@[to_additive] lemma to_monoid_hom_injective
  {M N} [monoid M] [monoid N] : function.injective (to_monoid_hom : (M ≃* N) → M →* N) :=
λ f g h, mul_equiv.ext (monoid_hom.ext_iff.1 h)


/--
A multiplicative analogue of `equiv.arrow_congr`,
where the equivalence between the targets is multiplicative.
-/
@[simps apply,
  to_additive "An additive analogue of `equiv.arrow_congr`,
where the equivalence between the targets is additive."]
def arrow_congr {M N P Q : Type*} [monoid P] [monoid Q]
  (f : M ≃ N) (g : P ≃* Q) : (M → P) ≃* (N → Q) :=
{ to_fun := λ h n, g (h (f.symm n)),
  inv_fun := λ k m, g.symm (k (f m)),
  left_inv := λ h, by { ext, simp, },
  right_inv := λ k, by { ext, simp, },
  map_mul' := λ h k, by { ext, simp, }, }

/--
A multiplicative analogue of `equiv.arrow_congr`,
for multiplicative maps from a monoid to a commutative monoid.
-/
@[simps apply,
  to_additive "An additive analogue of `equiv.arrow_congr`,
for additive maps from an additive monoid to a commutative additive monoid."]
def monoid_hom_congr {M N P Q} [monoid M] [monoid N] [comm_monoid P] [comm_monoid Q]
  (f : M ≃* N) (g : P ≃* Q) : (M →* P) ≃* (N →* Q) :=
{ to_fun := λ h,
  g.to_monoid_hom.comp (h.comp f.symm.to_monoid_hom),
  inv_fun := λ k,
  g.symm.to_monoid_hom.comp (k.comp f.to_monoid_hom),
  left_inv := λ h, by { ext, simp, },
  right_inv := λ k, by { ext, simp, },
  map_mul' := λ h k, by { ext, simp, }, }

/-!
# Groups
-/

/-- A multiplicative equivalence of groups preserves inversion. -/
@[simp, to_additive]
lemma map_inv [group G] [group H] (h : G ≃* H) (x : G) : h x⁻¹ = (h x)⁻¹ :=
h.to_monoid_hom.map_inv x

end mul_equiv

-- We don't use `to_additive` to generate definition because it fails to tell Lean about
-- equational lemmas

/-- Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id` and
`f.comp g = id`, returns an additive equivalence with `to_fun = f` and `inv_fun = g`.  This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
monoid homomorphisms. -/
def add_monoid_hom.to_add_equiv [add_monoid M] [add_monoid N] (f : M →+ N) (g : N →+ M)
  (h₁ : g.comp f = add_monoid_hom.id _) (h₂ : f.comp g = add_monoid_hom.id _) :
  M ≃+ N :=
{ to_fun := f,
  inv_fun := g,
  left_inv := add_monoid_hom.congr_fun h₁,
  right_inv := add_monoid_hom.congr_fun h₂,
  map_add' := f.map_add }

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns an multiplicative equivalence with `to_fun = f` and `inv_fun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[to_additive]
def monoid_hom.to_mul_equiv [monoid M] [monoid N] (f : M →* N) (g : N →* M)
  (h₁ : g.comp f = monoid_hom.id _) (h₂ : f.comp g = monoid_hom.id _) :
  M ≃* N :=
{ to_fun := f,
  inv_fun := g,
  left_inv := monoid_hom.congr_fun h₁,
  right_inv := monoid_hom.congr_fun h₂,
  map_mul' := f.map_mul }

@[simp, to_additive]
lemma monoid_hom.coe_to_mul_equiv [monoid M] [monoid N] (f : M →* N) (g : N →* M) (h₁ h₂) :
  ⇑(f.to_mul_equiv g h₁ h₂) = f := rfl

/-- An additive equivalence of additive groups preserves subtraction. -/
lemma add_equiv.map_sub [add_group A] [add_group B] (h : A ≃+ B) (x y : A) :
  h (x - y) = h x - h y :=
h.to_add_monoid_hom.map_sub x y

instance add_equiv.inhabited {M : Type*} [has_add M] : inhabited (M ≃+ M) := ⟨add_equiv.refl M⟩

/-- A group is isomorphic to its group of units. -/
@[to_additive to_add_units "An additive group is isomorphic to its group of additive units"]
def to_units {G} [group G] : G ≃* units G :=
{ to_fun := λ x, ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩,
  inv_fun := coe,
  left_inv := λ x, rfl,
  right_inv := λ u, units.ext rfl,
  map_mul' := λ x y, units.ext rfl }

namespace units

variables [monoid M] [monoid N] [monoid P]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def map_equiv (h : M ≃* N) : units M ≃* units N :=
{ inv_fun := map h.symm.to_monoid_hom,
  left_inv := λ u, ext $ h.left_inv u,
  right_inv := λ u, ext $ h.right_inv u,
  .. map h.to_monoid_hom }

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Left addition of an additive unit is a permutation of the underlying type."]
def mul_left (u : units M) : equiv.perm M :=
{ to_fun    := λx, u * x,
  inv_fun   := λx, ↑u⁻¹ * x,
  left_inv  := u.inv_mul_cancel_left,
  right_inv := u.mul_inv_cancel_left }

@[simp, to_additive]
lemma coe_mul_left (u : units M) : ⇑u.mul_left = (*) u := rfl

@[simp, to_additive]
lemma mul_left_symm (u : units M) : u.mul_left.symm = u⁻¹.mul_left :=
equiv.ext $ λ x, rfl

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Right addition of an additive unit is a permutation of the underlying type."]
def mul_right (u : units M) : equiv.perm M :=
{ to_fun    := λx, x * u,
  inv_fun   := λx, x * ↑u⁻¹,
  left_inv  := λ x, mul_inv_cancel_right x u,
  right_inv := λ x, inv_mul_cancel_right x u }

@[simp, to_additive]
lemma coe_mul_right (u : units M) : ⇑u.mul_right = λ x : M, x * u := rfl

@[simp, to_additive]
lemma mul_right_symm (u : units M) : u.mul_right.symm = u⁻¹.mul_right :=
equiv.ext $ λ x, rfl

end units

namespace equiv

section group
variables [group G]

/-- Left multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `add_group` is a permutation of the underlying type."]
protected def mul_left (a : G) : perm G := (to_units a).mul_left

@[simp, to_additive]
lemma coe_mul_left (a : G) : ⇑(equiv.mul_left a) = (*) a := rfl

/-- extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf, to_additive]
lemma mul_left_symm_apply (a : G) : ((equiv.mul_left a).symm : G → G) = (*) a⁻¹ := rfl

@[simp, to_additive]
lemma mul_left_symm (a : G) : (equiv.mul_left a).symm = equiv.mul_left a⁻¹ :=
ext $ λ x, rfl

/-- Right multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `add_group` is a permutation of the underlying type."]
protected def mul_right (a : G) : perm G := (to_units a).mul_right

@[simp, to_additive]
lemma coe_mul_right (a : G) : ⇑(equiv.mul_right a) = λ x, x * a := rfl

@[simp, to_additive]
lemma mul_right_symm (a : G) : (equiv.mul_right a).symm = equiv.mul_right a⁻¹ :=
ext $ λ x, rfl

/-- extra simp lemma that `dsimp` can use. `simp` will never use this.  -/
@[simp, nolint simp_nf, to_additive]
lemma mul_right_symm_apply (a : G) : ((equiv.mul_right a).symm : G → G) = λ x, x * a⁻¹ := rfl

attribute [nolint simp_nf] add_left_symm_apply add_right_symm_apply

variable (G)

/-- Inversion on a `group` is a permutation of the underlying type. -/
@[to_additive "Negation on an `add_group` is a permutation of the underlying type."]
protected def inv : perm G :=
{ to_fun    := λa, a⁻¹,
  inv_fun   := λa, a⁻¹,
  left_inv  := assume a, inv_inv a,
  right_inv := assume a, inv_inv a }

variable {G}

@[simp, to_additive]
lemma coe_inv : ⇑(equiv.inv G) = has_inv.inv := rfl

@[simp, to_additive]
lemma inv_symm : (equiv.inv G).symm = equiv.inv G := rfl

end group

end equiv

section type_tags
open multiplicative additive

/-- Add-isomorphism between `additive (multiplicative A)` and `A`. -/
@[simps] def additive.to_mul_to_add [add_monoid A] : additive (multiplicative A) ≃+ A :=
{ to_fun := to_add ∘ to_mul, inv_fun := of_mul ∘ of_add,
  left_inv := λ _, by simp, right_inv := λ _, by simp, map_add' := by simp }

/-- Mul-isomorphism between `multiplicative (additive G)` and `G`. -/
@[simps] def multiplicative.to_add_to_mul [monoid G] : multiplicative (additive G) ≃* G :=
{ to_fun := to_mul ∘ to_add, inv_fun := of_add ∘ of_mul,
  left_inv := λ _, by simp, right_inv := λ _, by simp, map_mul' := by simp }

/-- Reinterpret `G ≃+ H` as `multiplicative G ≃* multiplicative H`. -/
@[simps {simp_rhs := tt}]
def add_equiv.to_multiplicative [add_monoid G] [add_monoid H] :
  (G ≃+ H) ≃ (multiplicative G ≃* multiplicative H) :=
{ to_fun := λ f, ⟨f.to_add_monoid_hom.to_multiplicative,
                  f.symm.to_add_monoid_hom.to_multiplicative,
                  λ _, by simp, λ _, by simp, λ _, by simp⟩,
  inv_fun := λ f, ⟨add_monoid_hom.to_multiplicative.symm f.to_monoid_hom,
                   add_monoid_hom.to_multiplicative.symm f.symm.to_monoid_hom,
                   λ _, by simp, λ _, by simp, λ _, by simp⟩,
  left_inv := λ x, by { ext, simp },
  right_inv := λ x, by { ext, simp }, }

/-- Reinterpret `G ≃* H` as `additive G ≃+ additive H`. -/
@[simps {simp_rhs := tt}]
def mul_equiv.to_additive [monoid G] [monoid H] :
  (G ≃* H) ≃ (additive G ≃+ additive H) :=
{ to_fun := λ f, ⟨f.to_monoid_hom.to_additive,
                  f.symm.to_monoid_hom.to_additive,
                  λ _, by simp, λ _, by simp, λ _, by simp⟩,
  inv_fun := λ f, ⟨monoid_hom.to_additive.symm f.to_add_monoid_hom,
                   monoid_hom.to_additive.symm f.symm.to_add_monoid_hom,
                   λ _, by simp, λ _, by simp, λ _, by simp⟩,
  left_inv := λ x, by { ext, simp },
  right_inv := λ x, by { ext, simp }, }

/-- Reinterpret `additive G ≃+ H` as `G ≃* multiplicative H`. -/
@[simps {simp_rhs := tt}]
def add_equiv.to_multiplicative' [monoid G] [add_monoid H] :
  (additive G ≃+ H) ≃ (G ≃* multiplicative H) :=
{ to_fun := λ f, ⟨f.to_add_monoid_hom.to_multiplicative',
                  f.symm.to_add_monoid_hom.to_multiplicative'',
                  λ _, by simp, λ _, by simp, λ _, by simp⟩,
  inv_fun := λ f, ⟨f.to_monoid_hom.to_additive',
                   f.symm.to_monoid_hom.to_additive'',
                   λ _, by simp, λ _, by simp, λ _, by simp⟩,
  left_inv := λ x, by { ext, simp },
  right_inv := λ x, by { ext, simp }, }

/-- Reinterpret `G ≃* multiplicative H` as `additive G ≃+ H` as. -/
@[simps {value_md := semireducible, simp_rhs := tt}]
def mul_equiv.to_additive' [monoid G] [add_monoid H] :
  (G ≃* multiplicative H) ≃ (additive G ≃+ H) :=
add_equiv.to_multiplicative'.symm

/-- Reinterpret `G ≃+ additive H` as `multiplicative G ≃* H`. -/
@[simps {simp_rhs := tt}]
def add_equiv.to_multiplicative'' [add_monoid G] [monoid H] :
  (G ≃+ additive H) ≃ (multiplicative G ≃* H) :=
{ to_fun := λ f, ⟨f.to_add_monoid_hom.to_multiplicative'',
                  f.symm.to_add_monoid_hom.to_multiplicative',
                  λ _, by simp, λ _, by simp, λ _, by simp⟩,
  inv_fun := λ f, ⟨f.to_monoid_hom.to_additive'', f.symm.to_monoid_hom.to_additive',
                   λ _, by simp, λ _, by simp, λ _, by simp⟩,
  left_inv := λ x, by { ext, simp, },
  right_inv := λ x, by { ext, simp, }, }

/-- Reinterpret `multiplicative G ≃* H` as `G ≃+ additive H` as. -/
@[simps {value_md := semireducible, simp_rhs := tt}]
def mul_equiv.to_additive'' [add_monoid G] [monoid H] :
  (multiplicative G ≃* H) ≃ (G ≃+ additive H) :=
add_equiv.to_multiplicative''.symm

end type_tags
