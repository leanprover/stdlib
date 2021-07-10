/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Bryan Gin-ge Chen
-/
import order.galois_connection

/-!
# Equivalence relations

This file defines the complete lattice of equivalence relations on a type, results about the
inductively defined equivalence closure of a binary relation, and the analogues of some isomorphism
theorems for quotients of arbitrary types.

## Implementation notes

The function `rel` and lemmas ending in ' make it easier to talk about different
equivalence relations on the same type.

The complete lattice instance for equivalence relations could have been defined by lifting
the Galois insertion of equivalence relations on α into binary relations on α, and then using
`complete_lattice.copy` to define a complete lattice instance with more appropriate
definitional equalities (a similar example is `filter.complete_lattice` in
`order/filter/basic.lean`). This does not save space, however, and is less clear.

Partitions are not defined as a separate structure here; users are encouraged to
reason about them using the existing `setoid` and its infrastructure.

## Tags

setoid, equivalence, iseqv, relation, equivalence relation
-/
variables {α : Type*} {β : Type*}


/-- A version of `setoid.r` that takes the equivalence relation as an explicit argument. -/
def setoid.rel (r : setoid α) : α → α → Prop := @setoid.r _ r

/-- A version of `quotient.eq'` compatible with `setoid.rel`, to make rewriting possible. -/
lemma quotient.eq_rel {r : setoid α} {x y} :
  (quotient.mk' x : quotient r) = quotient.mk' y ↔ r.rel x y := quotient.eq

namespace setoid

@[ext] lemma ext' {r s : setoid α} (H : ∀ a b, r.rel a b ↔ s.rel a b) :
  r = s := ext H

lemma ext_iff {r s : setoid α} : r = s ↔ ∀ a b, r.rel a b ↔ s.rel a b :=
⟨λ h a b, h ▸ iff.rfl, ext'⟩

/-- Two equivalence relations are equal iff their underlying binary operations are equal. -/
theorem eq_iff_rel_eq {r₁ r₂ : setoid α} : r₁ = r₂ ↔ r₁.rel = r₂.rel :=
⟨λ h, h ▸ rfl, λ h, setoid.ext' $ λ x y, h ▸ iff.rfl⟩

/-- Defining `≤` for equivalence relations. -/
instance : has_le (setoid α) := ⟨λ r s, ∀ ⦃x y⦄, r.rel x y → s.rel x y⟩

theorem le_def {r s : setoid α} : r ≤ s ↔ ∀ {x y}, r.rel x y → s.rel x y := iff.rfl

@[refl] lemma refl' (r : setoid α) (x) : r.rel x x := r.2.1 x
@[symm] lemma symm' (r : setoid α) : ∀ {x y}, r.rel x y → r.rel y x := λ _ _ h, r.2.2.1 h
@[trans] lemma trans' (r : setoid α) : ∀ {x y z}, r.rel x y → r.rel y z → r.rel x z :=
λ _ _ _ hx, r.2.2.2 hx

lemma comm' (s : setoid α) {x y} : s.rel x y ↔ s.rel y x :=
⟨s.symm', s.symm'⟩

/-- The kernel of a function is an equivalence relation. -/
def ker (f : α → β) : setoid α :=
⟨λ x y, f x = f y, ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ h, h.trans⟩⟩

/-- The kernel of the quotient map induced by an equivalence relation r equals r. -/
@[simp] lemma ker_mk_eq (r : setoid α) : ker (@quotient.mk _ r) = r :=
ext' $ λ x y, quotient.eq

lemma ker_apply_mk_out {f : α → β} (a : α) :
  f (by haveI := setoid.ker f; exact ⟦a⟧.out) = f a :=
@quotient.mk_out _ (setoid.ker f) a

lemma ker_apply_mk_out' {f : α → β} (a : α) :
  f ((quotient.mk' a : quotient $ setoid.ker f).out') = f a :=
@quotient.mk_out' _ (setoid.ker f) a

lemma ker_def {f : α → β} {x y : α} : (ker f).rel x y ↔ f x = f y := iff.rfl

/-- Given types `α`, `β`, the product of two equivalence relations `r` on `α` and `s` on `β`:
    `(x₁, x₂), (y₁, y₂) ∈ α × β` are related by `r.prod s` iff `x₁` is related to `y₁`
    by `r` and `x₂` is related to `y₂` by `s`. -/
protected def prod (r : setoid α) (s : setoid β) : setoid (α × β) :=
{ r := λ x y, r.rel x.1 y.1 ∧ s.rel x.2 y.2,
  iseqv := ⟨λ x, ⟨r.refl' x.1, s.refl' x.2⟩, λ _ _ h, ⟨r.symm' h.1, s.symm' h.2⟩,
            λ _ _ _ h1 h2, ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩ }

/-- The infimum of two equivalence relations. -/
instance : has_inf (setoid α) :=
⟨λ r s, ⟨λ x y, r.rel x y ∧ s.rel x y, ⟨λ x, ⟨r.refl' x, s.refl' x⟩,
 λ _ _ h, ⟨r.symm' h.1, s.symm' h.2⟩,
 λ _ _ _ h1 h2, ⟨r.trans' h1.1 h2.1, s.trans' h1.2 h2.2⟩⟩⟩⟩

/-- The infimum of 2 equivalence relations r and s is the same relation as the infimum
    of the underlying binary operations. -/
lemma inf_def {r s : setoid α} : (r ⊓ s).rel = r.rel ⊓ s.rel := rfl

theorem inf_iff_and {r s : setoid α} {x y} :
  (r ⊓ s).rel x y ↔ r.rel x y ∧ s.rel x y := iff.rfl

/-- The infimum of a set of equivalence relations. -/
instance : has_Inf (setoid α) :=
⟨λ S, ⟨λ x y, ∀ r ∈ S, rel r x y,
⟨λ x r hr, r.refl' x, λ _ _ h r hr, r.symm' $ h r hr,
 λ _ _ _ h1 h2 r hr, r.trans' (h1 r hr) $ h2 r hr⟩⟩⟩

/-- The underlying binary operation of the infimum of a set of equivalence relations
    is the infimum of the set's image under the map to the underlying binary operation. -/
theorem Inf_def {s : set (setoid α)} : (Inf s).rel = Inf (rel '' s) :=
by { ext, simp only [Inf_image, infi_apply, infi_Prop_eq], refl }

instance : partial_order (setoid α) :=
{ le := (≤),
  lt := λ r s, r ≤ s ∧ ¬s ≤ r,
  le_refl := λ _ _ _, id,
  le_trans := λ _ _ _ hr hs _ _ h, hs $ hr h,
  lt_iff_le_not_le := λ _ _, iff.rfl,
  le_antisymm := λ r s h1 h2, setoid.ext' $ λ x y, ⟨λ h, h1 h, λ h, h2 h⟩ }

/-- The complete lattice of equivalence relations on a type, with bottom element `=`
    and top element the trivial equivalence relation. -/
instance complete_lattice : complete_lattice (setoid α) :=
{ inf := has_inf.inf,
  inf_le_left := λ _ _ _ _ h, h.1,
  inf_le_right := λ _ _ _ _ h, h.2,
  le_inf := λ _ _ _ h1 h2 _ _ h, ⟨h1 h, h2 h⟩,
  top := ⟨λ _ _, true, ⟨λ _, trivial, λ _ _ h, h, λ _ _ _ h1 h2, h1⟩⟩,
  le_top := λ _ _ _ _, trivial,
  bot := ⟨(=), ⟨λ _, rfl, λ _ _ h, h.symm, λ _ _ _ h1 h2, h1.trans h2⟩⟩,
  bot_le := λ r x y h, h ▸ r.2.1 x,
  .. complete_lattice_of_Inf (setoid α) $ assume s,
    ⟨λ r hr x y h, h _ hr, λ r hr x y h r' hr', hr hr' h⟩ }

/-- The inductively defined equivalence closure of a binary relation r is the infimum
    of the set of all equivalence relations containing r. -/
theorem eqv_gen_eq (r : α → α → Prop) :
  eqv_gen.setoid r = Inf {s : setoid α | ∀ ⦃x y⦄, r x y → s.rel x y} :=
le_antisymm
  (λ _ _ H, eqv_gen.rec (λ _ _ h _ hs, hs h) (refl' _)
    (λ _ _ _, symm' _) (λ _ _ _ _ _, trans' _) H)
  (Inf_le $ λ _ _ h, eqv_gen.rel _ _ h)

/-- The supremum of two equivalence relations r and s is the equivalence closure of the binary
    relation `x is related to y by r or s`. -/
lemma sup_eq_eqv_gen (r s : setoid α) :
  r ⊔ s = eqv_gen.setoid (λ x y, r.rel x y ∨ s.rel x y) :=
begin
  rw eqv_gen_eq,
  apply congr_arg Inf,
  simp only [le_def, or_imp_distrib, ← forall_and_distrib]
end

/-- The supremum of 2 equivalence relations r and s is the equivalence closure of the
    supremum of the underlying binary operations. -/
lemma sup_def {r s : setoid α} : r ⊔ s = eqv_gen.setoid (r.rel ⊔ s.rel) :=
by rw sup_eq_eqv_gen; refl

/-- The supremum of a set S of equivalence relations is the equivalence closure of the binary
    relation `there exists r ∈ S relating x and y`. -/
lemma Sup_eq_eqv_gen (S : set (setoid α)) :
  Sup S = eqv_gen.setoid (λ x y, ∃ r : setoid α, r ∈ S ∧ r.rel x y) :=
begin
  rw eqv_gen_eq,
  apply congr_arg Inf,
  simp only [upper_bounds, le_def, and_imp, exists_imp_distrib],
  ext,
  exact ⟨λ H x y r hr, H hr, λ H r hr x y, H r hr⟩
end

/-- The supremum of a set of equivalence relations is the equivalence closure of the
    supremum of the set's image under the map to the underlying binary operation. -/
lemma Sup_def {s : set (setoid α)} : Sup s = eqv_gen.setoid (Sup (rel '' s)) :=
begin
  rw [Sup_eq_eqv_gen, Sup_image],
  congr' with x y,
  simp only [supr_apply, supr_Prop_eq, exists_prop]
end

/-- The equivalence closure of an equivalence relation r is r. -/
@[simp] lemma eqv_gen_of_setoid (r : setoid α) : eqv_gen.setoid r.r = r :=
le_antisymm (by rw eqv_gen_eq; exact Inf_le (λ _ _, id)) eqv_gen.rel

/-- Equivalence closure is idempotent. -/
@[simp] lemma eqv_gen_idem (r : α → α → Prop) :
  eqv_gen.setoid (eqv_gen.setoid r).rel = eqv_gen.setoid r :=
eqv_gen_of_setoid _

/-- The equivalence closure of a binary relation r is contained in any equivalence
    relation containing r. -/
theorem eqv_gen_le {r : α → α → Prop} {s : setoid α} (h : ∀ x y, r x y → s.rel x y) :
  eqv_gen.setoid r ≤ s :=
by rw eqv_gen_eq; exact Inf_le h

/-- Equivalence closure of binary relations is monotonic. -/
theorem eqv_gen_mono {r s : α → α → Prop} (h : ∀ x y, r x y → s x y) :
  eqv_gen.setoid r ≤ eqv_gen.setoid s :=
eqv_gen_le $ λ _ _ hr, eqv_gen.rel _ _ $ h _ _ hr

/-- There is a Galois insertion of equivalence relations on α into binary relations
    on α, with equivalence closure the lower adjoint. -/
def gi : @galois_insertion (α → α → Prop) (setoid α) _ _ eqv_gen.setoid rel :=
{ choice := λ r h, eqv_gen.setoid r,
  gc := λ r s, ⟨λ H _ _ h, H $ eqv_gen.rel _ _ h, λ H, eqv_gen_of_setoid s ▸ eqv_gen_mono H⟩,
  le_l_u := λ x, (eqv_gen_of_setoid x).symm ▸ le_refl x,
  choice_eq := λ _ _, rfl }

open function

/-- A function from α to β is injective iff its kernel is the bottom element of the complete lattice
    of equivalence relations on α. -/
theorem injective_iff_ker_bot (f : α → β) :
  injective f ↔ ker f = ⊥ :=
(@eq_bot_iff (setoid α) _ (ker f)).symm

/-- The elements related to x ∈ α by the kernel of f are those in the preimage of f(x) under f. -/
lemma ker_iff_mem_preimage {f : α → β} {x y} : (ker f).rel x y ↔ x ∈ f ⁻¹' {f y} :=
iff.rfl

/-- Equivalence between functions `α → β` such that `r x y → f x = f y` and functions
`quotient r → β`. -/
def lift_equiv (r : setoid α) : {f : α → β // r ≤ ker f} ≃ (quotient r → β) :=
{ to_fun := λ f, quotient.lift (f : α → β) f.2,
  inv_fun := λ f, ⟨f ∘ quotient.mk, λ x y h, by simp [ker_def, quotient.sound h]⟩,
  left_inv := λ ⟨f, hf⟩, subtype.eq $ funext $ λ x, rfl,
  right_inv := λ f, funext $ λ x, quotient.induction_on' x $ λ x, rfl }

/-- The uniqueness part of the universal property for quotients of an arbitrary type. -/
theorem lift_unique {r : setoid α} {f : α → β} (H : r ≤ ker f) (g : quotient r → β)
  (Hg : f = g ∘ quotient.mk) : quotient.lift f H = g :=
begin
  ext ⟨x⟩,
  erw [quotient.lift_mk f H, Hg],
  refl
end

/-- Given a map f from α to β, the natural map from the quotient of α by the kernel of f is
    injective. -/
lemma ker_lift_injective (f : α → β) : injective (@quotient.lift _ _ (ker f) f (λ _ _ h, h)) :=
λ x y, quotient.induction_on₂' x y $ λ a b h, quotient.sound' h

/-- Given a map f from α to β, the kernel of f is the unique equivalence relation on α whose
    induced map from the quotient of α to β is injective. -/
lemma ker_eq_lift_of_injective {r : setoid α} (f : α → β) (H : ∀ x y, r.rel x y → f x = f y)
  (h : injective (quotient.lift f H)) : ker f = r :=
le_antisymm
  (λ x y hk, quotient.exact $ h $ show quotient.lift f H ⟦x⟧ = quotient.lift f H ⟦y⟧, from hk)
  H

variables (r : setoid α) (f : α → β)

/-- The first isomorphism theorem for sets: the quotient of α by the kernel of a function f
    bijects with f's image. -/
noncomputable def quotient_ker_equiv_range :
  quotient (ker f) ≃ set.range f :=
equiv.of_bijective (@quotient.lift _ (set.range f) (ker f)
  (λ x, ⟨f x, set.mem_range_self x⟩) $ λ _ _ h, subtype.ext_val h)
  ⟨λ x y h, ker_lift_injective f $ by rcases x; rcases y; injections,
   λ ⟨w, z, hz⟩, ⟨@quotient.mk _ (ker f) z, by rw quotient.lift_mk; exact subtype.ext_iff_val.2 hz⟩⟩

/-- If `f` has a computable right-inverse, then the quotient by its kernel is equivalent to its
domain. -/
@[simps]
def quotient_ker_equiv_of_right_inverse (g : β → α) (hf : function.right_inverse g f) :
  quotient (ker f) ≃ β :=
{ to_fun := λ a, quotient.lift_on' a f $ λ _ _, id,
  inv_fun := λ b, quotient.mk' (g b),
  left_inv := λ a, quotient.induction_on' a $ λ a, quotient.sound' $ by exact hf (f a),
  right_inv := hf }

/-- The quotient of α by the kernel of a surjective function f bijects with f's codomain.

If a specific right-inverse of `f` is known, `setoid.quotient_ker_equiv_of_right_inverse` can be
definitionally more useful. -/
noncomputable def quotient_ker_equiv_of_surjective (hf : surjective f) :
  quotient (ker f) ≃ β :=
quotient_ker_equiv_of_right_inverse _ (function.surj_inv hf) (right_inverse_surj_inv hf)

variables {r f}

/-- Given a function `f : α → β` and equivalence relation `r` on `α`, the equivalence
    closure of the relation on `f`'s image defined by '`x ≈ y` iff the elements of `f⁻¹(x)` are
    related to the elements of `f⁻¹(y)` by `r`.' -/
def map (r : setoid α) (f : α → β) : setoid β :=
eqv_gen.setoid $ λ x y, ∃ a b, f a = x ∧ f b = y ∧ r.rel a b

/-- Given a surjective function f whose kernel is contained in an equivalence relation r, the
    equivalence relation on f's codomain defined by x ≈ y ↔ the elements of f⁻¹(x) are related to
    the elements of f⁻¹(y) by r. -/
def map_of_surjective (r) (f : α → β) (h : ker f ≤ r) (hf : surjective f) :
  setoid β :=
⟨λ x y, ∃ a b, f a = x ∧ f b = y ∧ r.rel a b,
  ⟨λ x, let ⟨y, hy⟩ := hf x in ⟨y, y, hy, hy, r.refl' y⟩,
   λ _ _ ⟨x, y, hx, hy, h⟩, ⟨y, x, hy, hx, r.symm' h⟩,
   λ _ _ _ ⟨x, y, hx, hy, h₁⟩ ⟨y', z, hy', hz, h₂⟩,
     ⟨x, z, hx, hz, r.trans' h₁ $ r.trans' (h $ by rwa ←hy' at hy) h₂⟩⟩⟩

/-- A special case of the equivalence closure of an equivalence relation r equalling r. -/
lemma map_of_surjective_eq_map (h : ker f ≤ r) (hf : surjective f) :
  map r f = map_of_surjective r f h hf :=
by rw ←eqv_gen_of_setoid (map_of_surjective r f h hf); refl

/-- Given a function `f : α → β`, an equivalence relation `r` on `β` induces an equivalence
    relation on `α` defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `r`'. -/
def comap (f : α → β) (r : setoid β) : setoid α :=
⟨λ x y, r.rel (f x) (f y), ⟨λ _, r.refl' _, λ _ _ h, r.symm' h, λ _ _ _ h1, r.trans' h1⟩⟩

lemma comap_rel (f : α → β) (r : setoid β) (x y : α) : (comap f r).rel x y ↔ r.rel (f x) (f y) :=
iff.rfl

/-- Given a map `f : N → M` and an equivalence relation `r` on `β`, the equivalence relation
    induced on `α` by `f` equals the kernel of `r`'s quotient map composed with `f`. -/
lemma comap_eq {f : α → β} {r : setoid β} : comap f r = ker (@quotient.mk _ r ∘ f) :=
ext $ λ x y, show _ ↔ ⟦_⟧ = ⟦_⟧, by rw quotient.eq; refl

/-- The second isomorphism theorem for sets. -/
noncomputable def comap_quotient_equiv (f : α → β) (r : setoid β) :
  quotient (comap f r) ≃ set.range (@quotient.mk _ r ∘ f) :=
(quotient.congr_right $ ext_iff.1 comap_eq).trans $ quotient_ker_equiv_range $ quotient.mk ∘ f

variables (r f)

/-- The third isomorphism theorem for sets. -/
def quotient_quotient_equiv_quotient (s : setoid α) (h : r ≤ s) :
  quotient (ker (quot.map_right h)) ≃ quotient s :=
{ to_fun := λ x, quotient.lift_on' x (λ w, quotient.lift_on' w (@quotient.mk _ s) $
    λ x y H, quotient.sound $ h H) $ λ x y, quotient.induction_on₂' x y $ λ w z H,
      show @quot.mk _ _ _ = @quot.mk _ _ _, from H,
  inv_fun := λ x, quotient.lift_on' x
    (λ w, @quotient.mk _ (ker $ quot.map_right h) $ @quotient.mk _ r w) $
      λ x y H, quotient.sound' $ show @quot.mk _ _ _ = @quot.mk _ _ _, from quotient.sound H,
  left_inv := λ x, quotient.induction_on' x $ λ y, quotient.induction_on' y $
    λ w, by show ⟦_⟧ = _; refl,
  right_inv := λ x, quotient.induction_on' x $ λ y, by show ⟦_⟧ = _; refl }

variables {r f}

open quotient

/-- Given an equivalence relation `r` on `α`, the order-preserving bijection between the set of
equivalence relations containing `r` and the equivalence relations on the quotient of `α` by `r`. -/
def correspondence (r : setoid α) : {s // r ≤ s} ≃o setoid (quotient r) :=
{ to_fun := λ s, map_of_surjective s.1 quotient.mk ((ker_mk_eq r).symm ▸ s.2) exists_rep,
  inv_fun := λ s, ⟨comap quotient.mk' s, λ x y h, by rw [comap_rel, eq_rel.2 h]⟩,
  left_inv := λ s, subtype.ext_iff_val.2 $ ext' $ λ _ _,
    ⟨λ h, let ⟨a, b, hx, hy, H⟩ := h in
      s.1.trans' (s.1.symm' $ s.2 $ eq_rel.1 hx) $ s.1.trans' H $ s.2 $ eq_rel.1 hy,
     λ h, ⟨_, _, rfl, rfl, h⟩⟩,
  right_inv := λ s, let Hm : ker quotient.mk' ≤ comap quotient.mk' s :=
      λ x y h, by rw [comap_rel, (@eq_rel _ r x y).2 ((ker_mk_eq r) ▸ h)] in
    ext' $ λ x y, ⟨λ h, let ⟨a, b, hx, hy, H⟩ := h in hx ▸ hy ▸ H,
      quotient.induction_on₂ x y $ λ w z h, ⟨w, z, rfl, rfl, h⟩⟩,
  map_rel_iff' := λ s t, ⟨λ h x y hs, let ⟨a, b, hx, hy, ht⟩ := h ⟨x, y, rfl, rfl, hs⟩ in
      t.1.trans' (t.1.symm' $ t.2 $ eq_rel.1 hx) $ t.1.trans' ht $ t.2 $ eq_rel.1 hy,
      λ h x y hs, let ⟨a, b, hx, hy, Hs⟩ := hs in ⟨a, b, hx, hy, h Hs⟩⟩ }

end setoid
