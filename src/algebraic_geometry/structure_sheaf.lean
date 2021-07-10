/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebraic_geometry.prime_spectrum
import algebra.category.CommRing.colimits
import algebra.category.CommRing.limits
import topology.sheaves.local_predicate
import topology.sheaves.forget
import ring_theory.localization
import ring_theory.subring

/-!
# The structure sheaf on `prime_spectrum R`.

We define the structure sheaf on `Top.of (prime_spectrum R)`, for a commutative ring `R` and prove
basic properties about it. We define this as a subsheaf of the sheaf of dependent functions into the
localizations, cut out by the condition that the function must be locally equal to a ratio of
elements of `R`.

Because the condition "is equal to a fraction" passes to smaller open subsets,
the subset of functions satisfying this condition is automatically a subpresheaf.
Because the condition "is locally equal to a fraction" is local,
it is also a subsheaf.

(It may be helpful to refer back to `topology.sheaves.sheaf_of_functions`,
where we show that dependent functions into any type family form a sheaf,
and also `topology.sheaves.local_predicate`, where we characterise the predicates
which pick out sub-presheaves and sub-sheaves of these sheaves.)

We also set up the ring structure, obtaining
`structure_sheaf R : sheaf CommRing (Top.of (prime_spectrum R))`.

We then construct two basic isomorphisms, relating the structure sheaf to the underlying ring `R`.
First, `structure_sheaf.stalk_iso` gives an isomorphism between the stalk of the structure sheaf
at a point `p` and the localization of `R` at the prime ideal `p`. Second,
`structure_sheaf.basic_open_iso` gives an isomorphism between the structure sheaf on `basic_open f`
and the localization of `R` at the submonoid of powers of `f`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

universe u

noncomputable theory

variables (R : Type u) [comm_ring R]

open Top
open topological_space
open category_theory
open opposite

namespace algebraic_geometry

/--
The prime spectrum, just as a topological space.
-/
def prime_spectrum.Top : Top := Top.of (prime_spectrum R)

namespace structure_sheaf

/--
The type family over `prime_spectrum R` consisting of the localization over each point.
-/
@[derive [comm_ring, local_ring]]
def localizations (P : prime_spectrum.Top R) : Type u := localization.at_prime P.as_ideal

instance (P : prime_spectrum.Top R) : inhabited (localizations R P) :=
⟨1⟩

instance (U : opens (prime_spectrum.Top R)) (x : U) :
  algebra R (localizations R x) :=
localization.algebra

instance (U : opens (prime_spectrum.Top R)) (x : U) :
  is_localization.at_prime (localizations R x) (x : prime_spectrum.Top R).as_ideal :=
localization.is_localization

variables {R}

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (prime_spectrum.Top R)} (f : Π x : U, localizations R x) : Prop :=
∃ (r s : R), ∀ x : U,
  ¬ (s ∈ x.1.as_ideal) ∧ f x * algebra_map _ _ s = algebra_map _ _ r

lemma is_fraction.eq_mk' {U : opens (prime_spectrum.Top R)} {f : Π x : U, localizations R x}
  (hf : is_fraction f) :
  ∃ (r s : R) , ∀ x : U, ∃ (hs : s ∉ x.1.as_ideal), f x =
    is_localization.mk' (localization.at_prime _) r
      (⟨s, hs⟩ : (x : prime_spectrum.Top R).as_ideal.prime_compl) :=
begin
  rcases hf with ⟨r, s, h⟩,
  refine ⟨r, s, λ x, ⟨(h x).1, (is_localization.mk'_eq_iff_eq_mul.mpr _).symm⟩⟩,
  exact (h x).2.symm,
end

variables (R)

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (localizations R) :=
{ pred := λ U f, is_fraction f,
  res := by { rintro V U i f ⟨r, s, w⟩, exact ⟨r, s, λ x, w (i x)⟩ } }

/--
We will define the structure sheaf as
the subsheaf of all dependent functions in `Π x : U, localizations R x`
consisting of those functions which can locally be expressed as a ratio of
(the images in the localization of) elements of `R`.

Quoting Hartshorne:

For an open set $U ⊆ Spec A$, we define $𝒪(U)$ to be the set of functions
$s : U → ⨆_{𝔭 ∈ U} A_𝔭$, such that $s(𝔭) ∈ A_𝔭$ for each $𝔭$,
and such that $s$ is locally a quotient of elements of $A$:
to be precise, we require that for each $𝔭 ∈ U$, there is a neighborhood $V$ of $𝔭$,
contained in $U$, and elements $a, f ∈ A$, such that for each $𝔮 ∈ V, f ∉ 𝔮$,
and $s(𝔮) = a/f$ in $A_𝔮$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, localizations x`.
-/
def is_locally_fraction : local_predicate (localizations R) :=
(is_fraction_prelocal R).sheafify

@[simp]
lemma is_locally_fraction_pred
  {U : opens (prime_spectrum.Top R)} (f : Π x : U, localizations R x) :
  (is_locally_fraction R).pred f =
  ∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
  ∃ (r s : R), ∀ y : V,
  ¬ (s ∈ y.1.as_ideal) ∧
    f (i y : U) * algebra_map _ _ s = algebra_map _ _ r :=
rfl

/--
The functions satisfying `is_locally_fraction` form a subring.
-/
def sections_subring (U : (opens (prime_spectrum.Top R))ᵒᵖ) :
  subring (Π x : unop U, localizations R x) :=
{ carrier := { f | (is_locally_fraction R).pred f },
  zero_mem' :=
  begin
    refine λ x, ⟨unop U, x.2, 𝟙 _, 0, 1, λ y, ⟨_, _⟩⟩,
    { rw ←ideal.ne_top_iff_one, exact y.1.is_prime.1, },
    { simp, },
  end,
  one_mem' :=
  begin
    refine λ x, ⟨unop U, x.2, 𝟙 _, 1, 1, λ y, ⟨_, _⟩⟩,
    { rw ←ideal.ne_top_iff_one, exact y.1.is_prime.1, },
    { simp, },
  end,
  add_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩,
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * sb + rb * sa, sa * sb, _⟩,
    intro y,
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa⟩,
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb⟩,
    fsplit,
    { intro H, cases y.1.is_prime.mem_or_mem H; contradiction, },
    { simp only [add_mul, ring_hom.map_add, pi.add_apply, ring_hom.map_mul],
      erw [←wa, ←wb],
      simp only [mul_assoc],
      congr' 2,
      rw [mul_comm], refl, }
  end,
  neg_mem' :=
  begin
    intros a ha x,
    rcases ha x with ⟨V, m, i, r, s, w⟩,
    refine ⟨V, m, i, -r, s, _⟩,
    intro y,
    rcases w y with ⟨nm, w⟩,
    fsplit,
    { exact nm, },
    { simp only [ring_hom.map_neg, pi.neg_apply],
      erw [←w],
      simp only [neg_mul_eq_neg_mul_symm], }
  end,
  mul_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩,
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, ra * rb, sa * sb, _⟩,
    intro y,
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa⟩,
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb⟩,
    fsplit,
    { intro H, cases y.1.is_prime.mem_or_mem H; contradiction, },
    { simp only [pi.mul_apply, ring_hom.map_mul],
      erw [←wa, ←wb],
      simp only [mul_left_comm, mul_assoc, mul_comm],
      refl, }
  end, }

end structure_sheaf

open structure_sheaf

/--
The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.
-/
def structure_sheaf_in_Type : sheaf (Type u) (prime_spectrum.Top R):=
subsheaf_to_Types (is_locally_fraction R)

instance comm_ring_structure_sheaf_in_Type_obj (U : (opens (prime_spectrum.Top R))ᵒᵖ) :
  comm_ring ((structure_sheaf_in_Type R).presheaf.obj U) :=
(sections_subring R U).to_comm_ring

open prime_spectrum

/--
The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structure_presheaf_in_CommRing : presheaf CommRing (prime_spectrum.Top R) :=
{ obj := λ U, CommRing.of ((structure_sheaf_in_Type R).presheaf.obj U),
  map := λ U V i,
  { to_fun := ((structure_sheaf_in_Type R).presheaf.map i),
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    map_one' := rfl,
    map_mul' := λ x y, rfl, }, }

/--
Some glue, verifying that that structure presheaf valued in `CommRing` agrees
with the `Type` valued structure presheaf.
-/
def structure_presheaf_comp_forget :
  structure_presheaf_in_CommRing R ⋙ (forget CommRing) ≅ (structure_sheaf_in_Type R).presheaf :=
nat_iso.of_components
  (λ U, iso.refl _)
  (by tidy)

open Top.presheaf

/--
The structure sheaf on $Spec R$, valued in `CommRing`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def structure_sheaf : sheaf CommRing (prime_spectrum.Top R) :=
{ presheaf := structure_presheaf_in_CommRing R,
  sheaf_condition :=
    -- We check the sheaf condition under `forget CommRing`.
    (sheaf_condition_equiv_sheaf_condition_comp _ _).symm
      (sheaf_condition_equiv_of_iso (structure_presheaf_comp_forget R).symm
        (structure_sheaf_in_Type R).sheaf_condition), }


namespace structure_sheaf

@[simp] lemma res_apply (U V : opens (prime_spectrum.Top R)) (i : V ⟶ U)
  (s : (structure_sheaf R).presheaf.obj (op U)) (x : V) :
  ((structure_sheaf R).presheaf.map i.op s).1 x = (s.1 (i x) : _) :=
rfl

/-

Notation in this comment

X = Spec R
OX = structure sheaf

In the following we construct an isomorphism between OX_p and R_p given any point p corresponding
to a prime ideal in R.

We do this via 8 steps:

1. def const (f g : R) (V) (hv : V ≤ D_g) : OX(V) [for api]
2. def to_open (U) : R ⟶ OX(U)
3. [2] def to_stalk (p : Spec R) : R ⟶ OX_p
4. [2] def to_basic_open (f : R) : R_f ⟶ OX(D_f)
5. [3] def localization_to_stalk (p : Spec R) : R_p ⟶ OX_p
6. def open_to_localization (U) (p) (hp : p ∈ U) : OX(U) ⟶ R_p
7. [6] def stalk_to_fiber_ring_hom (p : Spec R) : OX_p ⟶ R_p
8. [5,7] def stalk_iso (p : Spec R) : OX_p ≅ R_p

In the square brackets we list the dependencies of a construction on the previous steps.

-/

/-- The section of `structure_sheaf R` on an open `U` sending each `x ∈ U` to the element
`f/g` in the localization of `R` at `x`. -/
def const (f g : R) (U : opens (prime_spectrum.Top R))
  (hu : ∀ x ∈ U, g ∈ (x : prime_spectrum.Top R).as_ideal.prime_compl) :
  (structure_sheaf R).presheaf.obj (op U) :=
⟨λ x, is_localization.mk' _ f ⟨g, hu x x.2⟩,
 λ x, ⟨U, x.2, 𝟙 _, f, g, λ y, ⟨hu y y.2, is_localization.mk'_spec _ _ _⟩⟩⟩

@[simp] lemma const_apply (f g : R) (U : opens (prime_spectrum.Top R))
  (hu : ∀ x ∈ U, g ∈ (x : prime_spectrum.Top R).as_ideal.prime_compl) (x : U) :
  (const R f g U hu).1 x = is_localization.mk' _ f ⟨g, hu x x.2⟩ :=
rfl

lemma const_apply' (f g : R) (U : opens (prime_spectrum.Top R))
  (hu : ∀ x ∈ U, g ∈ (x : prime_spectrum.Top R).as_ideal.prime_compl) (x : U)
  (hx : g ∈ (as_ideal (x : prime_spectrum.Top R)).prime_compl) :
  (const R f g U hu).1 x = is_localization.mk' _ f ⟨g, hx⟩ :=
rfl

lemma exists_const (U) (s : (structure_sheaf R).presheaf.obj (op U)) (x : prime_spectrum.Top R)
  (hx : x ∈ U) :
  ∃ (V : opens (prime_spectrum.Top R)) (hxV : x ∈ V) (i : V ⟶ U) (f g : R) hg,
  const R f g V hg = (structure_sheaf R).presheaf.map i.op s :=
let ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩ in
⟨V, hxV, iVU, f, g, λ y hyV, (hfg ⟨y, hyV⟩).1, subtype.eq $ funext $ λ y,
is_localization.mk'_eq_iff_eq_mul.2 $ eq.symm $ (hfg y).2⟩

@[simp] lemma res_const (f g : R) (U hu V hv i) :
  (structure_sheaf R).presheaf.map i (const R f g U hu) = const R f g V hv :=
rfl

lemma res_const' (f g : R) (V hv) :
  (structure_sheaf R).presheaf.map (hom_of_le hv).op (const R f g (basic_open g) (λ _, id)) =
    const R f g V hv :=
rfl

lemma const_zero (f : R) (U hu) : const R 0 f U hu = 0 :=
subtype.eq $ funext $ λ x, is_localization.mk'_eq_iff_eq_mul.2 $
by erw [ring_hom.map_zero, subtype.val_eq_coe, subring.coe_zero, pi.zero_apply, zero_mul]

lemma const_self (f : R) (U hu) : const R f f U hu = 1 :=
subtype.eq $ funext $ λ x, is_localization.mk'_self _ _

lemma const_one (U) : const R 1 1 U (λ p _, submonoid.one_mem _) = 1 :=
const_self R 1 U _

lemma const_add (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
  const R f₁ g₁ U hu₁ + const R f₂ g₂ U hu₂ =
  const R (f₁ * g₂ + f₂ * g₁) (g₁ * g₂) U (λ x hx, submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx)) :=
subtype.eq $ funext $ λ x, eq.symm $
by convert is_localization.mk'_add f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

lemma const_mul (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
  const R f₁ g₁ U hu₁ * const R f₂ g₂ U hu₂ =
  const R (f₁ * f₂) (g₁ * g₂) U (λ x hx, submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx)) :=
subtype.eq $ funext $ λ x, eq.symm $
by convert is_localization.mk'_mul _ f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

lemma const_ext {f₁ f₂ g₁ g₂ : R} {U hu₁ hu₂} (h : f₁ * g₂ = f₂ * g₁) :
  const R f₁ g₁ U hu₁ = const R f₂ g₂ U hu₂ :=
subtype.eq $ funext $ λ x, is_localization.mk'_eq_of_eq h.symm

lemma const_congr {f₁ f₂ g₁ g₂ : R} {U hu} (hf : f₁ = f₂) (hg : g₁ = g₂) :
  const R f₁ g₁ U hu = const R f₂ g₂ U (hg ▸ hu) :=
by substs hf hg

lemma const_mul_rev (f g : R) (U hu₁ hu₂) :
  const R f g U hu₁ * const R g f U hu₂ = 1 :=
by rw [const_mul, const_congr R rfl (mul_comm g f), const_self]

lemma const_mul_cancel (f g₁ g₂ : R) (U hu₁ hu₂) :
  const R f g₁ U hu₁ * const R g₁ g₂ U hu₂ = const R f g₂ U hu₂ :=
by { rw [const_mul, const_ext], rw mul_assoc }

lemma const_mul_cancel' (f g₁ g₂ : R) (U hu₁ hu₂) :
  const R g₁ g₂ U hu₂ * const R f g₁ U hu₁ = const R f g₂ U hu₂ :=
by rw [mul_comm, const_mul_cancel]

/-- The canonical ring homomorphism interpreting an element of `R` as
a section of the structure sheaf. -/
def to_open (U : opens (prime_spectrum.Top R)) :
  CommRing.of R ⟶ (structure_sheaf R).presheaf.obj (op U) :=
{ to_fun := λ f, ⟨λ x, algebra_map R _ f,
    λ x, ⟨U, x.2, 𝟙 _, f, 1, λ y, ⟨(ideal.ne_top_iff_one _).1 y.1.2.1,
      by { rw [ring_hom.map_one, mul_one], refl } ⟩⟩⟩,
  map_one' := subtype.eq $ funext $ λ x, ring_hom.map_one _,
  map_mul' := λ f g, subtype.eq $ funext $ λ x, ring_hom.map_mul _ _ _,
  map_zero' := subtype.eq $ funext $ λ x, ring_hom.map_zero _,
  map_add' := λ f g, subtype.eq $ funext $ λ x, ring_hom.map_add _ _ _ }

@[simp] lemma to_open_res (U V : opens (prime_spectrum.Top R)) (i : V ⟶ U) :
  to_open R U ≫ (structure_sheaf R).presheaf.map i.op = to_open R V :=
rfl

@[simp] lemma to_open_apply (U : opens (prime_spectrum.Top R)) (f : R) (x : U) :
  (to_open R U f).1 x = algebra_map _ _ f :=
rfl

lemma to_open_eq_const (U : opens (prime_spectrum.Top R)) (f : R) : to_open R U f =
  const R f 1 U (λ x _, (ideal.ne_top_iff_one _).1 x.2.1) :=
subtype.eq $ funext $ λ x, eq.symm $ is_localization.mk'_one _ f

/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structure_sheaf R` at `x`. -/
def to_stalk (x : prime_spectrum.Top R) : CommRing.of R ⟶ (structure_sheaf R).presheaf.stalk x :=
(to_open R ⊤ ≫ (structure_sheaf R).presheaf.germ ⟨x, ⟨⟩⟩ : _)

@[simp] lemma to_open_germ (U : opens (prime_spectrum.Top R)) (x : U) :
  to_open R U ≫ (structure_sheaf R).presheaf.germ x =
  to_stalk R x :=
by { rw [← to_open_res R ⊤ U (hom_of_le le_top : U ⟶ ⊤), category.assoc, presheaf.germ_res], refl }

@[simp] lemma germ_to_open (U : opens (prime_spectrum.Top R)) (x : U) (f : R) :
  (structure_sheaf R).presheaf.germ x (to_open R U f) = to_stalk R x f :=
by { rw ← to_open_germ, refl }

lemma germ_to_top (x : prime_spectrum.Top R) (f : R) :
  (structure_sheaf R).presheaf.germ (⟨x, trivial⟩ : (⊤ : opens (prime_spectrum.Top R)))
    (to_open R ⊤ f) =
    to_stalk R x f :=
rfl

lemma is_unit_to_basic_open_self (f : R) : is_unit (to_open R (basic_open f) f) :=
is_unit_of_mul_eq_one _ (const R 1 f (basic_open f) (λ _, id)) $
by rw [to_open_eq_const, const_mul_rev]

lemma is_unit_to_stalk (x : prime_spectrum.Top R) (f : x.as_ideal.prime_compl) :
  is_unit (to_stalk R x (f : R)) :=
by { erw ← germ_to_open R (basic_open (f : R)) ⟨x, f.2⟩ (f : R),
    exact ring_hom.is_unit_map _ (is_unit_to_basic_open_self R f) }

/-- The canonical ring homomorphism from the localization of `R` at `p` to the stalk
of the structure sheaf at the point `p`. -/
def localization_to_stalk (x : prime_spectrum.Top R) :
  CommRing.of (localization.at_prime x.as_ideal) ⟶ (structure_sheaf R).presheaf.stalk x :=
show localization.at_prime x.as_ideal →+* _, from
is_localization.lift (is_unit_to_stalk R x)

@[simp] lemma localization_to_stalk_of (x : prime_spectrum.Top R) (f : R) :
  localization_to_stalk R x (algebra_map _ (localization _) f) = to_stalk R x f :=
is_localization.lift_eq _ f

@[simp] lemma localization_to_stalk_mk' (x : prime_spectrum.Top R) (f : R)
  (s : (as_ideal x).prime_compl) :
  localization_to_stalk R x (is_localization.mk' _ f s : localization _) =
  (structure_sheaf R).presheaf.germ (⟨x, s.2⟩ : basic_open (s : R))
    (const R f s (basic_open s) (λ _, id)) :=
(is_localization.lift_mk'_spec _ _ _ _).2 $
by erw [← germ_to_open R (basic_open s) ⟨x, s.2⟩, ← germ_to_open R (basic_open s) ⟨x, s.2⟩,
    ← ring_hom.map_mul, to_open_eq_const, to_open_eq_const, const_mul_cancel']

/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
def open_to_localization (U : opens (prime_spectrum.Top R)) (x : prime_spectrum.Top R)
  (hx : x ∈ U) :
  (structure_sheaf R).presheaf.obj (op U) ⟶ CommRing.of (localization.at_prime x.as_ideal) :=
{ to_fun := λ s, (s.1 ⟨x, hx⟩ : _),
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

@[simp] lemma coe_open_to_localization (U : opens (prime_spectrum.Top R)) (x : prime_spectrum.Top R)
  (hx : x ∈ U) :
  (open_to_localization R U x hx :
    (structure_sheaf R).presheaf.obj (op U) → localization.at_prime x.as_ideal) =
  (λ s, (s.1 ⟨x, hx⟩ : _)) :=
rfl

lemma open_to_localization_apply (U : opens (prime_spectrum.Top R)) (x : prime_spectrum.Top R)
  (hx : x ∈ U)
  (s : (structure_sheaf R).presheaf.obj (op U)) :
  open_to_localization R U x hx s = (s.1 ⟨x, hx⟩ : _) :=
rfl

/-- The ring homomorphism from the stalk of the structure sheaf of `R` at a point corresponding to
a prime ideal `p` to the localization of `R` at `p`,
formed by gluing the `open_to_localization` maps. -/
def stalk_to_fiber_ring_hom (x : prime_spectrum.Top R) :
  (structure_sheaf R).presheaf.stalk x ⟶ CommRing.of (localization.at_prime x.as_ideal) :=
limits.colimit.desc (((open_nhds.inclusion x).op) ⋙ (structure_sheaf R).presheaf)
  { X := _,
    ι :=
    { app := λ U, open_to_localization R ((open_nhds.inclusion _).obj (unop U)) x (unop U).2, } }

@[simp] lemma germ_comp_stalk_to_fiber_ring_hom (U : opens (prime_spectrum.Top R)) (x : U) :
  (structure_sheaf R).presheaf.germ x ≫ stalk_to_fiber_ring_hom R x =
  open_to_localization R U x x.2 :=
limits.colimit.ι_desc _ _

@[simp] lemma stalk_to_fiber_ring_hom_germ' (U : opens (prime_spectrum.Top R))
  (x : prime_spectrum.Top R) (hx : x ∈ U) (s : (structure_sheaf R).presheaf.obj (op U)) :
  stalk_to_fiber_ring_hom R x ((structure_sheaf R).presheaf.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
ring_hom.ext_iff.1 (germ_comp_stalk_to_fiber_ring_hom R U ⟨x, hx⟩ : _) s

@[simp] lemma stalk_to_fiber_ring_hom_germ (U : opens (prime_spectrum.Top R)) (x : U)
  (s : (structure_sheaf R).presheaf.obj (op U)) :
  stalk_to_fiber_ring_hom R x ((structure_sheaf R).presheaf.germ x s) = s.1 x :=
by { cases x, exact stalk_to_fiber_ring_hom_germ' R U _ _ _ }

@[simp] lemma to_stalk_comp_stalk_to_fiber_ring_hom (x : prime_spectrum.Top R) :
  to_stalk R x ≫ stalk_to_fiber_ring_hom R x = (algebra_map _ _ : R →+* localization _) :=
by { erw [to_stalk, category.assoc, germ_comp_stalk_to_fiber_ring_hom], refl }

@[simp] lemma stalk_to_fiber_ring_hom_to_stalk (x : prime_spectrum.Top R) (f : R) :
  stalk_to_fiber_ring_hom R x (to_stalk R x f) = algebra_map _ (localization _) f :=
ring_hom.ext_iff.1 (to_stalk_comp_stalk_to_fiber_ring_hom R x) _

/-- The ring isomorphism between the stalk of the structure sheaf of `R` at a point `p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`. -/
@[simps] def stalk_iso (x : prime_spectrum.Top R) :
  (structure_sheaf R).presheaf.stalk x ≅ CommRing.of (localization.at_prime x.as_ideal) :=
{ hom := stalk_to_fiber_ring_hom R x,
  inv := localization_to_stalk R x,
  hom_inv_id' := (structure_sheaf R).presheaf.stalk_hom_ext $ λ U hxU,
  begin
    ext s, simp only [comp_apply], rw [id_apply, stalk_to_fiber_ring_hom_germ'],
    obtain ⟨V, hxV, iVU, f, g, hg, hs⟩ := exists_const _ _ s x hxU,
    erw [← res_apply R U V iVU s ⟨x, hxV⟩, ← hs, const_apply, localization_to_stalk_mk'],
    refine (structure_sheaf R).presheaf.germ_ext V hxV (hom_of_le hg) iVU _,
    erw [← hs, res_const']
  end,
  inv_hom_id' := @is_localization.epic_of_localization_map R _ x.as_ideal.prime_compl
      (localization.at_prime x.as_ideal) _ _ (localization.at_prime x.as_ideal) _ _
      (ring_hom.comp (stalk_to_fiber_ring_hom R x) (localization_to_stalk R x))
      (ring_hom.id (localization.at_prime _)) $
    λ f, by simp only [ring_hom.comp_apply, ring_hom.id_apply, localization_to_stalk_of,
        stalk_to_fiber_ring_hom_to_stalk] }

/-- The canonical ring homomorphism interpreting `s ∈ R_f` as a section of the structure sheaf
on the basic open defined by `f ∈ R`. -/
def to_basic_open (f : R) : localization.away f →+*
  (structure_sheaf R).presheaf.obj (op $ basic_open f) :=
is_localization.away.lift f (is_unit_to_basic_open_self R f)

@[simp] lemma to_basic_open_mk' (s f : R) (g : submonoid.powers s) :
  to_basic_open R s (is_localization.mk' (localization.away s) f g) =
  const R f g (basic_open s) (λ x hx, submonoid.powers_subset hx g.2) :=
(is_localization.lift_mk'_spec _ _ _ _).2 $
by rw [to_open_eq_const, to_open_eq_const, const_mul_cancel']

@[simp] lemma localization_to_basic_open (f : R) :
  ring_hom.comp (to_basic_open R f) (algebra_map R (localization.away f)) =
    to_open R (basic_open f) :=
ring_hom.ext $ λ g,
by rw [to_basic_open, is_localization.away.lift, ring_hom.comp_apply, is_localization.lift_eq]

@[simp] lemma to_basic_open_to_map (s f : R) :
  to_basic_open R s (algebra_map R (localization.away s) f) =
    const R f 1 (basic_open s) (λ _ _, submonoid.one_mem _) :=
(is_localization.lift_eq _ _).trans $ to_open_eq_const _ _ _

-- The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
lemma to_basic_open_injective (f : R) : function.injective (to_basic_open R f) :=
begin
  intros s t h_eq,
  obtain ⟨a, ⟨b, hb⟩, rfl⟩ := is_localization.mk'_surjective (submonoid.powers f) s,
  obtain ⟨c, ⟨d, hd⟩, rfl⟩ := is_localization.mk'_surjective (submonoid.powers f) t,
  simp only [to_basic_open_mk'] at h_eq,
  rw is_localization.eq,
  -- We know that the fractions `a/b` and `c/d` are equal as sections of the structure sheaf on
  -- `basic_open f`. We need to show that they agree as elements in the localization of `R` at `f`.
  -- This amounts showing that `a * d * r = c * b * r`, for some power `r = f ^ n` of `f`.
  -- We define `I` as the ideal of *all* elements `r` satisfying the above equation.
  let I : ideal R :=
  { carrier := {r : R | a * d * r = c * b * r},
    zero_mem' := by simp only [set.mem_set_of_eq, mul_zero],
    add_mem' := λ r₁ r₂ hr₁ hr₂, by { dsimp at hr₁ hr₂ ⊢, simp only [mul_add, hr₁, hr₂] },
    smul_mem' := λ r₁ r₂ hr₂, by { dsimp at hr₂ ⊢, simp only [mul_comm r₁ r₂, ← mul_assoc, hr₂] }},
  -- Our claim now reduces to showing that `f` is contained in the radical of `I`
  suffices : f ∈ I.radical,
  { cases this with n hn,
    exact ⟨⟨f ^ n, n, rfl⟩, hn⟩ },
  rw [← vanishing_ideal_zero_locus_eq_radical, mem_vanishing_ideal],
  intros p hfp,
  contrapose hfp,
  rw [mem_zero_locus, set.not_subset],
  have := congr_fun (congr_arg subtype.val h_eq) ⟨p,hfp⟩,
  rw [const_apply, const_apply, is_localization.eq] at this,
  cases this with r hr,
  exact ⟨r.1, hr, r.2⟩
end

/-
Auxiliary lemma for surjectivity of `to_basic_open`.
Every section can locally be represented on basic opens `basic_opens g` as a fraction `f/g`
-/
lemma locally_const_basic_open (U : opens (prime_spectrum.Top R))
  (s : (structure_sheaf R).presheaf.obj (op U)) (x : U) :
  ∃ (f g : R) (i : basic_open g ⟶ U), x.1 ∈ basic_open g ∧
    const R f g (basic_open g) (λ y hy, hy) = (structure_sheaf R).presheaf.map i.op s :=
begin
  -- First, any section `s` can be represented as a fraction `f/g` on some open neighborhood of `x`
  -- and we may pass to a `basic_open h`, since these form a basis
  obtain ⟨V, (hxV : x.1 ∈ V.1), iVU, f, g, (hVDg : V ⊆ basic_open g), s_eq⟩ :=
    exists_const R U s x.1 x.2,
  obtain ⟨_, ⟨h, rfl⟩, hxDh, (hDhV : basic_open h ⊆ V)⟩ :=
    is_topological_basis_basic_opens.exists_subset_of_mem_open hxV V.2,
  -- The problem is of course, that `g` and `h` don't need to coincide.
  -- But, since `basic_open h ≤ basic_open g`, some power of `h` must be a multiple of `g`
  cases (basic_open_le_basic_open_iff h g).mp (set.subset.trans hDhV hVDg) with n hn,
  -- Actually, we will need a *nonzero* power of `h`.
  -- This is because we will need the equality `basic_open (h ^ n) = basic_open h`, which only
  -- holds for a nonzero power `n`. We therefore artificially increase `n` by one.
  replace hn := ideal.mul_mem_left (ideal.span {g}) h hn,
  rw [← pow_succ, ideal.mem_span_singleton'] at hn,
  cases hn with c hc,
  have basic_opens_eq := basic_open_pow h (n+1) (by linarith),
  have i_basic_open := eq_to_hom basic_opens_eq ≫ hom_of_le hDhV,
  -- We claim that `(f * c) / h ^ (n+1)` is our desired representation
  use [f * c, h ^ (n+1), i_basic_open ≫ iVU, (basic_opens_eq.symm.le : _) hxDh],
  rw [op_comp, functor.map_comp, comp_apply, ← s_eq, res_const],
  -- Note that the last rewrite here generated an additional goal, which was a parameter
  -- of `res_const`. We prove this goal first
  swap,
  { intros y hy,
    rw basic_opens_eq at hy,
    exact (set.subset.trans hDhV hVDg : _) hy },
  -- All that is left is a simple calculation
  apply const_ext,
  rw [mul_assoc f c g, hc],
end

/-
Auxiliary lemma for surjectivity of `to_basic_open`.
A local representation of a section `s` as fractions `a i / h i` on finitely many basic opens
`basic_open (h i)` can be "normalized" in such a way that `a i * h j = h i * a j` for all `i, j`
-/
lemma normalize_finite_fraction_representation (U : opens (prime_spectrum.Top R))
  (s : (structure_sheaf R).presheaf.obj (op U)) {ι : Type*} (t : finset ι) (a h : ι → R)
  (iDh : Π i : ι, basic_open (h i) ⟶ U)  (h_cover : U.1 ⊆ ⋃ i ∈ t, (basic_open (h i)).1)
  (hs : ∀ i : ι, const R (a i) (h i) (basic_open (h i)) (λ y hy, hy) =
    (structure_sheaf R).presheaf.map (iDh i).op s) :
  ∃ (a' h' : ι → R) (iDh' : Π i : ι, (basic_open (h' i)) ⟶ U),
    (U.1 ⊆ ⋃ i ∈ t, (basic_open (h' i)).1) ∧
    (∀ i j ∈ t, a' i * h' j = h' i * a' j) ∧
    (∀ i ∈ t, (structure_sheaf R).presheaf.map (iDh' i).op s =
      const R (a' i) (h' i) (basic_open (h' i)) (λ y hy, hy)) :=
begin
  -- First we show that the fractions `(a i * h j) / (h i * h j)` and `(h i * a j) / (h i * h j)`
  -- coincide in the localization of `R` at `h i * h j`
  have fractions_eq : ∀ (i j : ι),
    is_localization.mk' (localization.away _) (a i * h j) ⟨h i * h j, submonoid.mem_powers _⟩ =
    is_localization.mk' _ (h i * a j) ⟨h i * h j, submonoid.mem_powers _⟩,
  { intros i j,
    let D := basic_open (h i * h j),
    let iDi : D ⟶ basic_open (h i) := hom_of_le (basic_open_mul_le_left _ _),
    let iDj : D ⟶ basic_open (h j) := hom_of_le (basic_open_mul_le_right _ _),
    -- Crucially, we need injectivity of `to_basic_open`
    apply to_basic_open_injective R (h i * h j),
    rw [to_basic_open_mk', to_basic_open_mk'],
    simp only [set_like.coe_mk],
    -- Here, both sides of the equation are equal to a restriction of `s`
    transitivity,
    convert congr_arg ((structure_sheaf R).presheaf.map iDj.op) (hs j).symm using 1,
    convert congr_arg ((structure_sheaf R).presheaf.map iDi.op) (hs i) using 1, swap,
    all_goals { rw res_const, apply const_ext, ring },
    -- The remaining two goals were generated during the rewrite of `res_const`
    -- These can be solved immediately
    exacts [basic_open_mul_le_right _ _, basic_open_mul_le_left _ _] },

  -- From the equality in the localization, we obtain for each `(i,j)` some power `(h i * h j) ^ n`
  -- which equalizes `a i * h j` and `h i * a j`
  have exists_power : ∀ (i j : ι), ∃ n : ℕ,
    a i * h j * (h i * h j) ^ n = h i * a j * (h i * h j) ^ n,
  { intros i j,
    obtain ⟨⟨c, n, rfl⟩, hc⟩ := is_localization.eq.mp (fractions_eq i j),
    use (n+1),
    rw pow_succ,
    dsimp at hc,
    convert hc using 1 ; ring },
  let n := λ (p : ι × ι), (exists_power p.1 p.2).some,
  have n_spec := λ (p : ι × ι), (exists_power p.fst p.snd).some_spec,
  -- We need one power `(h i * h j) ^ N` that works for *all* pairs `(i,j)`
  -- Since there are only finitely many indices involved, we can pick the supremum.
  let N := (t.product t).sup n,
  have basic_opens_eq : ∀ i : ι, basic_open ((h i) ^ (N+1)) = basic_open (h i) :=
    λ i, basic_open_pow _ _ (by linarith),
  -- Expanding the fraction `a i / h i` by the power `(h i) ^ N` gives the desired normalization
  refine ⟨(λ i, a i * (h i) ^ N), (λ i, (h i) ^ (N + 1)),
    (λ i, eq_to_hom (basic_opens_eq i) ≫ iDh i), _, _, _⟩,
  { simpa only [basic_opens_eq] using h_cover },
  { intros i j hi hj,
    -- Here we need to show that our new fractions `a i / h i` satisfy the normalization condition
    -- Of course, the power `N` we used to expand the fractions might be bigger than the power
    -- `n (i, j)` which was originally chosen. We denote their difference by `k`
    have n_le_N : n (i, j) ≤ N := finset.le_sup (finset.mem_product.mpr ⟨hi, hj⟩),
    cases nat.le.dest n_le_N with k hk,
    simp only [← hk, pow_add, pow_one],
    -- To accommodate for the difference `k`, we multiply both sides of the equation `n_spec (i, j)`
    -- by `(h i * h j) ^ k`
    convert congr_arg (λ z, z * (h i * h j) ^ k) (n_spec (i, j)) using 1 ;
    { simp only [n, mul_pow], ring } },

  -- Lastly, we need to show that the new fractions still represent our original `s`
  intros i hi,
  rw [op_comp, functor.map_comp, comp_apply, ← hs, res_const],
  -- additional goal spit out by `res_const`
  swap, exact (basic_opens_eq i).le,
  apply const_ext,
  rw pow_succ,
  ring
end

open_locale classical
open_locale big_operators

-- The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
lemma to_basic_open_surjective (f : R) : function.surjective (to_basic_open R f) :=
begin
  intro s,
  -- In this proof, `basic_open f` will play two distinct roles: Firstly, it is an open set in the
  -- prime spectrum. Secondly, it is used as an indexing type for various families of objects
  -- (open sets, ring elements, ...). In order to make the distinction clear, we introduce a type
  -- alias `ι` that is used whenever we want think of it as an indexing type.
  let ι : Type u := basic_open f,

  -- First, we pick some cover of basic opens, on which we can represent `s` as a fraction
  choose a' h' iDh' hxDh' s_eq' using locally_const_basic_open R (basic_open f) s,
  -- Since basic opens are compact, we can pass to a finite subcover
  obtain ⟨t, ht_cover'⟩ := (is_compact_basic_open f).elim_finite_subcover
   (λ (i : ι), (basic_open (h' i)).1) (λ i, is_open_basic_open) (λ x hx, _),
  swap,
  { -- Here, we need to show that our basic opens actually form a cover of `basic_open f`
    rw set.mem_Union,
    exact ⟨⟨x,hx⟩, hxDh' ⟨x, hx⟩⟩ },
  -- We use the normalization lemma from above to obtain the relation `a i * h j = h i * a j`
  obtain ⟨a, h, iDh, ht_cover, ah_ha, s_eq⟩ := normalize_finite_fraction_representation R
    (basic_open f) s t a' h' iDh' ht_cover' s_eq',
  clear s_eq' iDh' hxDh' ht_cover' a' h',
  -- Next we show that some power of `f` is a linear combination of the `h i`
  obtain ⟨n, hn⟩ : f ∈ (ideal.span (h '' ↑t)).radical,
  { rw [← vanishing_ideal_zero_locus_eq_radical, zero_locus_span],
    simp_rw [subtype.val_eq_coe, basic_open_eq_zero_locus_compl] at ht_cover,
    rw set.compl_subset_comm at ht_cover, -- Why doesn't `simp_rw` do this?
    simp_rw [set.compl_Union, compl_compl, ← zero_locus_Union, ← finset.set_bUnion_coe,
             ← set.image_eq_Union ] at ht_cover,
    apply vanishing_ideal_anti_mono ht_cover,
    exact subset_vanishing_ideal_zero_locus {f} (set.mem_singleton f) },

  replace hn := ideal.mul_mem_left _ f hn,
  erw [←pow_succ, finsupp.mem_span_image_iff_total] at hn,
  rcases hn with ⟨b, b_supp, hb⟩,
  rw finsupp.total_apply_of_mem_supported R b_supp at hb,
  dsimp at hb,

  -- Finally, we have all the ingredients.
  -- We claim that our preimage is given by `(∑ (i : ι) in t, b i * a i) / f ^ (n+1)`
  use is_localization.mk' (localization.away f) (∑ (i : ι) in t, b i * a i)
    (⟨f ^ (n+1), n+1, rfl⟩ : submonoid.powers _),
  rw to_basic_open_mk',

  -- Since the structure sheaf is a sheaf, we can show the desired equality locally.
  -- Annoyingly, `sheaf.eq_of_locally_eq` requires an open cover indexed by a *type*, so we need to
  -- coerce our finset `t` to a type first.
  let tt := ((t : set (basic_open f)) : Type u),

  -- TODO: Add a version of `eq_of_locally_eq` for sheaves valued in representably concrete
  -- categories. This will allow us to write `(structure_sheaf R).eq_of_locally_eq` here.
  apply (structure_sheaf_in_Type R).eq_of_locally_eq'
    (λ i : tt, basic_open (h i)) (basic_open f) (λ i : tt, iDh i),
  { -- This feels a little redundant, since already have `ht_cover` as a hypothesis
    -- Unfortunately, `ht_cover` uses a bounded union over the set `t`, while here we have the
    -- Union indexed by the type `tt`, so we need some boilerplate to translate one to the other
    intros x hx,
    erw topological_space.opens.mem_supr,
    have := ht_cover hx,
    rw [← finset.set_bUnion_coe, set.mem_bUnion_iff] at this,
    rcases this with ⟨i, i_mem, x_mem⟩,
    use [i, i_mem] },

  rintro ⟨i, hi⟩,
  dsimp,
  change (structure_sheaf R).presheaf.map _ _ = (structure_sheaf R).presheaf.map _ _,
  rw [s_eq i hi, res_const],
  -- Again, `res_const` spits out an additional goal
  swap,
  { intros y hy,
    change y ∈ basic_open (f ^ (n+1)),
    rw basic_open_pow f (n+1) (by linarith),
    exact (le_of_hom (iDh i) : _) hy },
  -- The rest of the proof is just computation
  apply const_ext,
  rw [← hb, finset.sum_mul, finset.mul_sum],
  apply finset.sum_congr rfl,
  intros j hj,
  rw [mul_assoc, ah_ha j i hj hi],
  ring
end

instance is_iso_to_basic_open (f : R) : is_iso (show CommRing.of _ ⟶ _, from to_basic_open R f) :=
begin
  haveI : is_iso ((forget CommRing).map (show CommRing.of _ ⟶ _, from to_basic_open R f)) :=
    (is_iso_iff_bijective _).mpr ⟨to_basic_open_injective R f, to_basic_open_surjective R f⟩,
  exact is_iso_of_reflects_iso _ (forget CommRing),
end

/-- The ring isomorphism between the structure sheaf on `basic_open f` and the localization of `R`
at the submonoid of powers of `f`. -/
def basic_open_iso (f : R) : (structure_sheaf R).presheaf.obj (op (basic_open f)) ≅
  CommRing.of (localization.away f) :=
(as_iso (show CommRing.of _ ⟶ _, from to_basic_open R f)).symm

section comap

variables {R} {S : Type u} [comm_ring S] {P : Type u} [comm_ring P]

/--
Given a ring homomorphism `f : R →+* S`, an open set `U` of the prime spectrum of `R` and an open
set `V` of the prime spectrum of `S`, such that `V ⊆ (comap f) ⁻¹' U`, we can push a section `s`
on `U` to a section on `V`, by composing with `localization.local_ring_hom _ _ f` from the left and
`comap f` from the right. Explicitly, if `s` evaluates on `comap f p` to `a / b`, its image on `V`
evaluates on `p` to `f(a) / f(b)`.

At the moment, we work with arbitrary dependent functions `s : Π x : U, localizations R x`. Below,
we prove the predicate `is_locally_fraction` is preserved by this map, hence it can be extended to
a morphism between the structure sheaves of `R` and `S`.
-/
def comap_fun (f : R →+* S) (U : opens (prime_spectrum.Top R))
  (V : opens (prime_spectrum.Top S)) (hUV : V.1 ⊆ (prime_spectrum.comap f) ⁻¹' U.1)
  (s : Π x : U, localizations R x) (y : V) : localizations S y :=
localization.local_ring_hom (prime_spectrum.comap f y.1).as_ideal _ f rfl
  (s ⟨(prime_spectrum.comap f y.1), hUV y.2⟩ : _)

lemma comap_fun_is_locally_fraction (f : R →+* S)
  (U : opens (prime_spectrum.Top R)) (V : opens (prime_spectrum.Top S))
  (hUV : V.1 ⊆ (prime_spectrum.comap f) ⁻¹' U.1) (s : Π x : U, localizations R x)
  (hs : (is_locally_fraction R).to_prelocal_predicate.pred s) :
  (is_locally_fraction S).to_prelocal_predicate.pred (comap_fun f U V hUV s) :=
begin
  rintro ⟨p, hpV⟩,
  -- Since `s` is locally fraction, we can find a neighborhood `W` of `prime_spectrum.comap f p`
  -- in `U`, such that `s = a / b` on `W`, for some ring elements `a, b : R`.
  rcases hs ⟨prime_spectrum.comap f p, hUV hpV⟩ with ⟨W, m, iWU, a, b, h_frac⟩,
  -- We claim that we can write our new section as the fraction `f a / f b` on the neighborhood
  -- `(comap f) ⁻¹ W ⊓ V` of `p`.
  refine ⟨opens.comap (comap_continuous f) W ⊓ V, ⟨m, hpV⟩, opens.inf_le_right _ _, f a, f b, _⟩,
  rintro ⟨q, ⟨hqW, hqV⟩⟩,
  specialize h_frac ⟨prime_spectrum.comap f q, hqW⟩,
  refine ⟨h_frac.1, _⟩,
  dsimp only [comap_fun],
  erw [← localization.local_ring_hom_to_map ((prime_spectrum.comap f q).as_ideal),
    ← ring_hom.map_mul, h_frac.2, localization.local_ring_hom_to_map],
  refl,
end

/--
For a ring homomorphism `f : R →+* S` and open sets `U` and `V` of the prime spectra of `R` and
`S` such that `V ⊆ (comap f) ⁻¹ U`, the induced ring homomorphism from the structure sheaf of `R`
at `U` to the structure sheaf of `S` at `V`.

Explicitly, this map is given as follows: For a point `p : V`, if the section `s` evaluates on `p`
to the fraction `a / b`, its image on `V` evaluates on `p` to the fraction `f(a) / f(b)`.
-/
def comap (f : R →+* S) (U : opens (prime_spectrum.Top R))
  (V : opens (prime_spectrum.Top S)) (hUV : V.1 ⊆ (prime_spectrum.comap f) ⁻¹' U.1) :
  (structure_sheaf R).presheaf.obj (op U) →+* (structure_sheaf S).presheaf.obj (op V) :=
{ to_fun := λ s, ⟨comap_fun f U V hUV s.1, comap_fun_is_locally_fraction f U V hUV s.1 s.2⟩,
  map_one' := subtype.ext $ funext $ λ p, by
    { rw [subtype.coe_mk, subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_one,
      pi.one_apply, ring_hom.map_one], refl },
  map_zero' := subtype.ext $ funext $ λ p, by
    { rw [subtype.coe_mk, subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_zero,
      pi.zero_apply, ring_hom.map_zero], refl },
  map_add' := λ s t, subtype.ext $ funext $ λ p, by
    { rw [subtype.coe_mk, subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_add,
      pi.add_apply, ring_hom.map_add], refl },
  map_mul' := λ s t, subtype.ext $ funext $ λ p, by
    { rw [subtype.coe_mk, subtype.val_eq_coe, comap_fun, (sections_subring R (op U)).coe_mul,
      pi.mul_apply, ring_hom.map_mul], refl }
}

@[simp]
lemma comap_apply (f : R →+* S) (U : opens (prime_spectrum.Top R))
  (V : opens (prime_spectrum.Top S)) (hUV : V.1 ⊆ (prime_spectrum.comap f) ⁻¹' U.1)
  (s : (structure_sheaf R).presheaf.obj (op U)) (p : V) :
  (comap f U V hUV s).1 p =
  localization.local_ring_hom (prime_spectrum.comap f p.1).as_ideal _ f rfl
    (s.1 ⟨(prime_spectrum.comap f p.1), hUV p.2⟩ : _) :=
rfl

lemma comap_const (f : R →+* S) (U : opens (prime_spectrum.Top R))
  (V : opens (prime_spectrum.Top S)) (hUV : V.1 ⊆ (prime_spectrum.comap f) ⁻¹' U.1)
  (a b : R) (hb : ∀ x : prime_spectrum R, x ∈ U → b ∈ x.as_ideal.prime_compl) :
  comap f U V hUV (const R a b U hb) =
  const S (f a) (f b) V (λ p hpV, hb (prime_spectrum.comap f p) (hUV hpV)) :=
subtype.eq $ funext $ λ p,
begin
  rw [comap_apply, const_apply, const_apply],
  erw localization.local_ring_hom_mk',
  refl,
end

/--
For an inclusion `i : V ⟶ U` between open sets of the prime spectrum of `R`, the comap of the
identity from OO_X(U) to OO_X(V) equals as the restriction map of the structure sheaf.

This is a generalization of the fact that, for fixed `U`, the comap of the identity from OO_X(U)
to OO_X(U) is the identity.
-/
lemma comap_id_eq_map (U V : opens (prime_spectrum.Top R)) (iVU : V ⟶ U) :
  comap (ring_hom.id R) U V
    (λ p hpV, le_of_hom iVU $ by rwa prime_spectrum.comap_id) =
  (structure_sheaf R).presheaf.map iVU.op :=
ring_hom.ext $ λ s, subtype.eq $ funext $ λ p,
begin
  rw comap_apply,
  -- Unfortunately, we cannot use `localization.local_ring_hom_id` here, because
  -- `prime_spectrum.comap (ring_hom.id R) p` is not *definitionally* equal to `p`. Instead, we use
  -- that we can write `s` as a fraction `a/b` in a small neighborhood around `p`. Since
  -- `prime_spectrum.comap (ring_hom.id R) p` equals `p`, it is also contained in the same
  -- neighborhood, hence `s` equals `a/b` there too.
  obtain ⟨W, hpW, iWU, h⟩ := s.2 (iVU p),
  obtain ⟨a, b, h'⟩ := h.eq_mk',
  obtain ⟨hb₁, s_eq₁⟩ := h' ⟨p, hpW⟩,
  obtain ⟨hb₂, s_eq₂⟩ := h' ⟨prime_spectrum.comap (ring_hom.id _) p.1,
    by rwa prime_spectrum.comap_id⟩,
  dsimp only at s_eq₁ s_eq₂,
  erw [s_eq₂, localization.local_ring_hom_mk', ← s_eq₁, ← res_apply],
end

/--
The comap of the identity is the identity. In this variant of the lemma, two open subsets `U` and
`V` are given as arguments, together with a proof that `U = V`. This is be useful when `U` and `V`
are not definitionally equal.
-/
lemma comap_id (U V : opens (prime_spectrum.Top R)) (hUV : U = V) :
  comap (ring_hom.id R) U V (λ p hpV, by rwa [hUV, prime_spectrum.comap_id]) =
  eq_to_hom (show (structure_sheaf R).presheaf.obj (op U) = _, by rw hUV) :=
by erw [comap_id_eq_map U V (eq_to_hom hUV.symm), eq_to_hom_op, eq_to_hom_map]

@[simp] lemma comap_id' (U : opens (prime_spectrum.Top R)) :
  comap (ring_hom.id R) U U (λ p hpU, by rwa prime_spectrum.comap_id) =
  ring_hom.id _ :=
by { rw comap_id U U rfl, refl }

lemma comap_comp (f : R →+* S) (g : S →+* P) (U : opens (prime_spectrum.Top R))
  (V : opens (prime_spectrum.Top S)) (W : opens (prime_spectrum.Top P))
  (hUV : ∀ p ∈ V, prime_spectrum.comap f p ∈ U) (hVW : ∀ p ∈ W, prime_spectrum.comap g p ∈ V) :
  comap (g.comp f) U W (λ p hpW, hUV (prime_spectrum.comap g p) (hVW p hpW)) =
    (comap g V W hVW).comp (comap f U V hUV) :=
ring_hom.ext $ λ s, subtype.eq $ funext $ λ p,
begin
  rw comap_apply,
  erw localization.local_ring_hom_comp _ (prime_spectrum.comap g p.1).as_ideal,
  -- refl works here, because `prime_spectrum.comap (g.comp f) p` is defeq to
  -- `prime_spectrum.comap f (prime_spectrum.comap g p)`
  refl,
end

@[elementwise, reassoc] lemma to_open_comp_comap (f : R →+* S) :
  to_open R ⊤ ≫ comap f ⊤ ⊤ (λ p hpV, trivial) =
  @category_theory.category_struct.comp _ _ (CommRing.of R) (CommRing.of S) _ f (to_open S ⊤) :=
ring_hom.ext $ λ s, subtype.eq $ funext $ λ p,
begin
  simp_rw [comp_apply, comap_apply, subtype.val_eq_coe],
  erw localization.local_ring_hom_to_map,
  refl,
end

end comap

end structure_sheaf

end algebraic_geometry
