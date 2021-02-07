/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.group.pi
import group_theory.free_group
import group_theory.abelianization
import algebra.punit_instances -- just for ℤ[pempty] ≃+ punit
import algebra.module.basic -- just for ℤ[punit] ≃+ ℤ
/-!
# Free abelian groups

The free abelian group on a type `α`, defined as the abelianisation of
the free group on `α`. The free abelian group on `α` is the left adjoint of the
forgetful functor from abelian groups to types. A model for it is the functions
`α → ℤ` which send all but finitely many `(a : α)` to `0`, under pointwise addition.

## Main definitions

Here we use the following variables: `(α β : Type*) (A : Type*) [add_comm_group A]`

* `free_abelian_group α` : the free abelian group on a type `α`. As an abelian
group it is `α →₀ ℤ`, the functions from `α` to `ℤ` such that all but finitely
many elements get mapped to zero, however this is not how it is implemented.

* `lift (f : α → A) : free_abelian_group α →+ A` : the group homomorphism induced
by the map `f`.

* `hom_equiv : (free_abelian_group α →+ A) ≃ (α → A)` : the bijection witnessing adjointness.

* `map (f : α → β) : free_abelian_group α →+ free_abelian_group β` : functoriality
    of `free_abelian_group`

* `instance [monoid α] : semigroup (free_abelian_group α)`

* `instance [comm_monoid α] : comm_ring (free_abelian_group α)`

It has been suggested that we would be better off refactoring this file
and using `finsupp` instead.

## Implementation issues

The definition is `def free_abelian_group : Type u :=
additive $ abelianization $ free_group α`

Chris Hughes has suggested that this all be rewritten in terms of `finsupp`.
Johan Commelin has written all the API relating the definition to `finsupp`
in the lean-liquid repo.

-/


universes u v

variables (α : Type u)

/-- The free abelian group on a type. -/
def free_abelian_group : Type u :=
additive $ abelianization $ free_group α

instance : add_comm_group (free_abelian_group α) :=
@additive.add_comm_group _ $ abelianization.comm_group _

instance : inhabited (free_abelian_group α) := ⟨0⟩

variable {α}

namespace free_abelian_group

/-- The canonical map from α to `free_abelian_group α` -/
def of (x : α) : free_abelian_group α :=
abelianization.of $ free_group.of x

/-- The map `free_abelian_group α →+ A` induced by a map of types `α → A`. -/
def lift {β : Type v} [add_comm_group β] (f : α → β) : free_abelian_group α →+ β :=
(@abelianization.lift _ _ (multiplicative β) _
  (monoid_hom.of (@free_group.to_group _ (multiplicative β) _ f))).to_additive

namespace lift
variables {β : Type v} [add_comm_group β] (f : α → β)
open free_abelian_group

@[simp] protected lemma add (x y : free_abelian_group α) :
  lift f (x + y) = lift f x + lift f y :=
is_add_hom.map_add _ _ _

@[simp] protected lemma neg (x : free_abelian_group α) : lift f (-x) = -lift f x :=
is_add_group_hom.map_neg _ _

@[simp] protected lemma sub (x y : free_abelian_group α) :
  lift f (x - y) = lift f x - lift f y :=
by simp [sub_eq_add_neg]

@[simp] protected lemma zero : lift f 0 = 0 :=
is_add_group_hom.map_zero _

@[simp] protected lemma of (x : α) : lift f (of x) = f x :=
begin
  convert @abelianization.lift.of (free_group α) _ (multiplicative β) _ _ _,
  convert free_group.to_group.of.symm
end

protected theorem unique (g : free_abelian_group α →+ β)
  (hg : ∀ x, g (of x) = f x) {x} :
  g x = lift f x :=
@abelianization.lift.unique (free_group α) _ (multiplicative β) _
  (monoid_hom.of (@free_group.to_group _ (multiplicative β) _ f)) g.to_multiplicative
  (λ x, @free_group.to_group.unique α (multiplicative β) _ _
    ((add_monoid_hom.to_multiplicative' g).comp abelianization.of)
    hg x) _

/-- See note [partially-applied ext lemmas]. -/
@[ext]
protected theorem ext (g h : free_abelian_group α →+ β)
  (H : ∀ x, g (of x) = h (of x)) :
  g = h :=
add_monoid_hom.ext $ λ x, (lift.unique (g ∘ of) g (λ _, rfl)).trans $
eq.symm $ lift.unique _ _ $ λ x, eq.symm $ H x

lemma map_hom {α β γ} [add_comm_group β] [add_comm_group γ]
  (a : free_abelian_group α) (f : α → β) (g : β →+ γ) :
  g (lift f a) = lift (g ∘ f) a :=
begin
  suffices : (g.comp (lift f)) a = lift (g ∘ f) a,
    exact this,
  apply @lift.unique,
  assume a,
  show g ((lift f) (of a)) = g (f a),
  simp only [(∘), lift.of],
end

end lift

section
open_locale classical

lemma of_injective : function.injective (of : α → free_abelian_group α) :=
λ x y hoxy, classical.by_contradiction $ assume hxy : x ≠ y,
  let f : free_abelian_group α →+ ℤ := lift (λ z, if x = z then 1 else 0) in
  have hfx1 : f (of x) = 1, from (lift.of _ _).trans $ if_pos rfl,
  have hfy1 : f (of y) = 1, from hoxy ▸ hfx1,
  have hfy0 : f (of y) = 0, from (lift.of _ _).trans $ if_neg hxy,
  one_ne_zero $ hfy1.symm.trans hfy0

end

section
variables (X : Type*) (G : Type*) [add_comm_group G]

/-- The bijection underlying the free-forgetful adjunction for abelian groups.-/
def hom_equiv : (free_abelian_group X →+ G) ≃ (X → G) :=
{ to_fun := λ f, f.1 ∘ of,
  inv_fun := λ f, add_monoid_hom.of (lift f),
  left_inv := λ f, begin ext, simp end,
  right_inv := λ f, funext $ λ x, lift.of f x }

@[simp]
lemma hom_equiv_apply (f) (x) : ((hom_equiv X G) f) x = f (of x) := rfl
@[simp]
lemma hom_equiv_symm_apply (f) (x) : ((hom_equiv X G).symm f) x = (lift f) x := rfl

end

local attribute [instance] quotient_group.left_rel

@[elab_as_eliminator]
protected theorem induction_on
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ of x)
  (Cn : ∀ x, C (of x) → C (-of x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
quotient.induction_on' z $ λ x, quot.induction_on x $ λ L,
list.rec_on L C0 $ λ ⟨x, b⟩ tl ih,
bool.rec_on b (Cp _ _ (Cn _ (C1 x)) ih) (Cp _ _ (C1 x) ih)

theorem lift.add' {α β} [add_comm_group β] (a : free_abelian_group α) (f g : α → β) :
  lift (f + g) a = lift f a + lift g a :=
begin
  refine free_abelian_group.induction_on a _ _ _ _,
  { simp only [lift.zero, zero_add] },
  { assume x,
    simp only [lift.of, pi.add_apply] },
  { assume x h,
    simp only [lift.neg, lift.of, pi.add_apply, neg_add] },
  { assume x y hx hy,
    simp only [lift.add, hx, hy],
    ac_refl }
end

instance is_add_group_hom_lift' {α} (β) [add_comm_group β] (a : free_abelian_group α) :
  is_add_group_hom (λf, (lift f a : β)) :=
{ map_add := λ f g, lift.add' a f g }

section monad

variables {β : Type u}

instance : monad free_abelian_group.{u} :=
{ pure := λ α, of,
  bind := λ α β x f, lift f x }

@[elab_as_eliminator]
protected theorem induction_on'
  {C : free_abelian_group α → Prop}
  (z : free_abelian_group α)
  (C0 : C 0)
  (C1 : ∀ x, C $ pure x)
  (Cn : ∀ x, C (pure x) → C (-pure x))
  (Cp : ∀ x y, C x → C y → C (x + y)) : C z :=
free_abelian_group.induction_on z C0 C1 Cn Cp

@[simp] lemma map_pure (f : α → β) (x : α) : f <$> (pure x : free_abelian_group α) = pure (f x) :=
lift.of _ _

@[simp] lemma map_zero (f : α → β) : f <$> (0 : free_abelian_group α) = 0 :=
lift.zero (of ∘ f)

@[simp] lemma map_add (f : α → β) (x y : free_abelian_group α) :
  f <$> (x + y) = f <$> x + f <$> y :=
lift.add _ _ _

@[simp] lemma map_neg (f : α → β) (x : free_abelian_group α) : f <$> (-x) = -(f <$> x) :=
lift.neg _ _

@[simp] lemma map_sub (f : α → β) (x y : free_abelian_group α) :
  f <$> (x - y) = f <$> x - f <$> y :=
lift.sub _ _ _

@[simp] lemma map_of (f : α → β) (y : α) : f <$> of y = of (f y) := rfl

@[simp] lemma pure_bind (f : α → free_abelian_group β) (x) : pure x >>= f = f x :=
lift.of _ _

@[simp] lemma zero_bind (f : α → free_abelian_group β) : 0 >>= f = 0 :=
lift.zero f

@[simp] lemma add_bind (f : α → free_abelian_group β) (x y : free_abelian_group α) :
  x + y >>= f = (x >>= f) + (y >>= f) :=
lift.add _ _ _

@[simp] lemma neg_bind (f : α → free_abelian_group β) (x : free_abelian_group α) :
  -x >>= f = -(x >>= f) :=
lift.neg _ _

@[simp] lemma sub_bind (f : α → free_abelian_group β) (x y : free_abelian_group α) :
  x - y >>= f = (x >>= f) - (y >>= f) :=
lift.sub _ _ _

@[simp] lemma pure_seq (f : α → β) (x : free_abelian_group α) : pure f <*> x = f <$> x :=
pure_bind _ _

@[simp] lemma zero_seq (x : free_abelian_group α) : (0 : free_abelian_group (α → β)) <*> x = 0 :=
zero_bind _

@[simp] lemma add_seq (f g : free_abelian_group (α → β)) (x : free_abelian_group α) :
  f + g <*> x = (f <*> x) + (g <*> x) :=
add_bind _ _ _

@[simp] lemma neg_seq (f : free_abelian_group (α → β)) (x : free_abelian_group α) :
  -f <*> x = -(f <*> x) :=
neg_bind _ _

@[simp] lemma sub_seq (f g : free_abelian_group (α → β)) (x : free_abelian_group α) :
  f - g <*> x = (f <*> x) - (g <*> x) :=
sub_bind _ _ _

instance is_add_group_hom_seq (f : free_abelian_group (α → β)) : is_add_group_hom ((<*>) f) :=
{ map_add := λ x y, show lift (<$> (x+y)) _ = _, by simp only [map_add]; exact
@@is_add_hom.map_add _ _ _
  (@@free_abelian_group.is_add_group_hom_lift' (free_abelian_group β) _ _).to_is_add_hom _ _ }

@[simp] lemma seq_zero (f : free_abelian_group (α → β)) : f <*> 0 = 0 :=
is_add_group_hom.map_zero _

@[simp] lemma seq_add (f : free_abelian_group (α → β)) (x y : free_abelian_group α) :
  f <*> (x + y) = (f <*> x) + (f <*> y) :=
is_add_hom.map_add _ _ _

@[simp] lemma seq_neg (f : free_abelian_group (α → β)) (x : free_abelian_group α) :
  f <*> (-x) = -(f <*> x) :=
is_add_group_hom.map_neg _ _

@[simp] lemma seq_sub (f : free_abelian_group (α → β)) (x y : free_abelian_group α) :
  f <*> (x - y) = (f <*> x) - (f <*> y) :=
is_add_group_hom.map_sub _ _ _

instance : is_lawful_monad free_abelian_group.{u} :=
{ id_map := λ α x, free_abelian_group.induction_on' x (map_zero id) (λ x, map_pure id x)
    (λ x ih, by rw [map_neg, ih]) (λ x y ihx ihy, by rw [map_add, ihx, ihy]),
  pure_bind := λ α β x f, pure_bind f x,
  bind_assoc := λ α β γ x f g, free_abelian_group.induction_on' x
    (by iterate 3 { rw zero_bind }) (λ x, by iterate 2 { rw pure_bind })
    (λ x ih, by iterate 3 { rw neg_bind }; rw ih)
    (λ x y ihx ihy, by iterate 3 { rw add_bind }; rw [ihx, ihy]) }

instance : is_comm_applicative free_abelian_group.{u} :=
{ commutative_prod := λ α β x y, free_abelian_group.induction_on' x
    (by rw [map_zero, zero_seq, seq_zero])
    (λ p, by rw [map_pure, pure_seq]; exact free_abelian_group.induction_on' y
      (by rw [map_zero, map_zero, zero_seq])
      (λ q, by rw [map_pure, map_pure, pure_seq, map_pure])
      (λ q ih, by rw [map_neg, map_neg, neg_seq, ih])
      (λ y₁ y₂ ih1 ih2, by rw [map_add, map_add, add_seq, ih1, ih2]))
    (λ p ih, by rw [map_neg, neg_seq, seq_neg, ih])
    (λ x₁ x₂ ih1 ih2, by rw [map_add, add_seq, seq_add, ih1, ih2]) }


end monad

universe w

variables {β : Type v} {γ : Type w}

/-- The additive group homomorphism `free_abelian_group α →+ free_abelian_group β` induced from a
  map `α → β` -/
def map (f : α → β) : free_abelian_group α →+ free_abelian_group β :=
lift (of ∘ f)

lemma lift_comp {α} {β} {γ} [add_comm_group γ]
  (f : α → β) (g : β → γ) (x : free_abelian_group α) :
  lift (g ∘ f) x = lift g (map f x) :=
begin
  apply free_abelian_group.induction_on x,
  { exact add_monoid_hom.map_zero _ },
  { intro y, refl },
  { intros x h, simp only [h, add_monoid_hom.map_neg] },
  { intros x y h₁ h₂, simp only [h₁, h₂, add_monoid_hom.map_add] }
end

lemma map_comp {f : α → β} {g : β → γ} : map (g ∘ f) = (map g).comp (map f) :=
eq.symm $ lift.ext _ _ $ λ x, eq.symm $ lift_comp _ _ _

lemma map_id : map id = add_monoid_hom.id (free_abelian_group α) :=
eq.symm $ lift.ext _ _ $ λ x, lift.unique of (add_monoid_hom.id _) $ λ y, add_monoid_hom.id_apply _

-- version of map_of which uses `map`
lemma map_of' {f : α → β} (a : α) : map f (of a) = of (f a) := rfl

variable (α)

instance [monoid α] : semigroup (free_abelian_group α) :=
{ mul := λ x, lift $ λ x₂, lift (λ x₁, of $ x₁ * x₂) x,
  mul_assoc := λ x y z, begin
    unfold has_mul.mul,
    refine free_abelian_group.induction_on z (by simp) _ _ _,
    { intros L3, rw [lift.of, lift.of],
      refine free_abelian_group.induction_on y (by simp) _ _ _,
      { intros L2, iterate 3 { rw lift.of },
        refine free_abelian_group.induction_on x (by simp) _ _ _,
        { intros L1, iterate 3 { rw lift.of }, congr' 1, exact mul_assoc _ _ _ },
        { intros L1 ih, iterate 3 { rw lift.neg }, rw ih },
        { intros x1 x2 ih1 ih2, iterate 3 { rw lift.add }, rw [ih1, ih2] } },
      { intros L2 ih, iterate 4 { rw lift.neg }, rw ih },
      { intros y1 y2 ih1 ih2, iterate 4 { rw lift.add }, rw [ih1, ih2] } },
    { intros L3 ih, iterate 3 { rw lift.neg }, rw ih },
    { intros z1 z2 ih1 ih2, iterate 2 { rw lift.add }, rw [ih1, ih2], exact (lift.add _ _ _).symm }
  end }

lemma mul_def [monoid α] (x y : free_abelian_group α) :
  x * y = lift (λ x₂, lift (λ x₁, of (x₁ * x₂)) x) y := rfl

lemma of_mul_of [monoid α] (x y : α) : of x * of y = of (x * y) := rfl
lemma of_mul [monoid α] (x y : α) : of (x * y) = of x * of y := rfl

instance [monoid α] : ring (free_abelian_group α) :=
{ one := free_abelian_group.of 1,
  mul_one := λ x, begin
    unfold has_mul.mul semigroup.mul has_one.one,
    rw lift.of,
    refine free_abelian_group.induction_on x rfl _ _ _,
    { intros L, erw [lift.of], congr' 1, exact mul_one L },
    { intros L ih, rw [lift.neg, ih] },
    { intros x1 x2 ih1 ih2, rw [lift.add, ih1, ih2] }
  end,
  one_mul := λ x, begin
    unfold has_mul.mul semigroup.mul has_one.one,
    refine free_abelian_group.induction_on x rfl _ _ _,
    { intros L, rw [lift.of, lift.of], congr' 1, exact one_mul L },
    { intros L ih, rw [lift.neg, ih] },
    { intros x1 x2 ih1 ih2, rw [lift.add, ih1, ih2] }
  end,
  left_distrib := λ x y z, lift.add _ _ _,
  right_distrib := λ x y z, begin
    unfold has_mul.mul semigroup.mul,
    refine free_abelian_group.induction_on z rfl _ _ _,
    { intros L, iterate 3 { rw lift.of }, rw lift.add, refl },
    { intros L ih, iterate 3 { rw lift.neg }, rw [ih, neg_add], refl },
    { intros z1 z2 ih1 ih2, iterate 3 { rw lift.add }, rw [ih1, ih2],
      rw [add_assoc, add_assoc], congr' 1, apply add_left_comm }
  end,
  .. free_abelian_group.add_comm_group α,
  .. free_abelian_group.semigroup α }

lemma one_def [monoid α] : (1 : free_abelian_group α) = of 1 := rfl
lemma of_one [monoid α] : (of 1 : free_abelian_group α) = 1 := rfl

instance [comm_monoid α] : comm_ring (free_abelian_group α) :=
{ mul_comm := λ x y, begin
    refine free_abelian_group.induction_on x (zero_mul y) _ _ _,
    { intros s, refine free_abelian_group.induction_on y (zero_mul _).symm _ _ _,
      { intros t, unfold has_mul.mul semigroup.mul ring.mul,
        iterate 4 { rw lift.of }, congr' 1, exact mul_comm _ _ },
      { intros t ih, rw [mul_neg_eq_neg_mul_symm, ih, neg_mul_eq_neg_mul] },
      { intros y1 y2 ih1 ih2, rw [mul_add, add_mul, ih1, ih2] } },
    { intros s ih, rw [neg_mul_eq_neg_mul_symm, ih, neg_mul_eq_mul_neg] },
    { intros x1 x2 ih1 ih2, rw [add_mul, mul_add, ih1, ih2] }
  end,
  .. free_abelian_group.ring α }

instance pempty_unique : unique (free_abelian_group pempty) :=
{ default := 0,
  uniq := λ x, free_abelian_group.induction_on x rfl
    (λ x, pempty.elim x)
    (λ x, pempty.elim x)
    (by { rintros - - rfl rfl, simp })  }


/-- The free abelian group on the empty type is the trivial group. -/
def pempty_equiv : free_abelian_group pempty ≃+ unit :=
{ map_add' := λ _ _, unit.ext,
  ..equiv_punit_of_unique }

example (T : Type*) [unique T] (C : T → Prop) (h : C (inhabited.default T))
  (x : T) : C x := by refine unique.forall_iff.mpr h x

/-- The free abelian group on a type with one term is isomorphic to `ℤ`. -/
def punit_equiv (T : Type*) [unique T] : free_abelian_group T ≃+ ℤ :=
{ to_fun := free_abelian_group.lift (λ _, (1 : ℤ)),
  inv_fun := λ n, n • of (inhabited.default T),
  left_inv := λ z, free_abelian_group.induction_on z
    (by simp only [zero_smul, lift.zero])
    (unique.forall_iff.2 $ by simp only [one_smul, lift.of])
    (unique.forall_iff.2 $ by simp)
    (λ x y hx hy, by { simp only [lift.add, add_smul] at *, rw [hx, hy]}),
  right_inv := λ n,
  begin
    rw [add_monoid_hom.map_int_module_smul, lift.of],
    exact gsmul_int_one n
  end,
  map_add' := add_monoid_hom.map_add _ }

/-- Isomorphic types have isomorphic free abelian groups. -/
def equiv_of_equiv {α β : Type*} (f : α ≃ β) : free_abelian_group α ≃+ free_abelian_group β :=
{ to_fun := map f,
  inv_fun := map f.symm,
  left_inv := begin
    intros x,
    change (map f.symm).comp (map f) x = x,
    rw [← map_comp, equiv.symm_comp_self, map_id],
    refl,
  end,
  right_inv := begin
    intros x,
    change (map f).comp (map f.symm) x = x,
    rw [← map_comp, equiv.self_comp_symm, map_id],
    refl,
  end,
  map_add' := lift.add _ }

end free_abelian_group
