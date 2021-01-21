/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison
-/
import algebra.category.CommRing.colimits
import algebra.category.CommRing.limits
import topology.sheaves.local_predicate
import topology.sheaves.forget
import ring_theory.localization

/-!
# The structure sheaf on `prime_spectrum R`.

We define the structure sheaf on `Top.of (prime_spectrum R)`, for a commutative ring `R`.
We define this as a subsheaf of the sheaf of dependent functions into the localizations,
cut out by the condition that the function must be locally equal to a ratio of elements of `R`.

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
$Spec R$, just as a topological space.
-/
def Spec.Top : Top := Top.of (prime_spectrum R)

namespace structure_sheaf

/--
The type family over `prime_spectrum R` consisting of the localization over each point.
-/
@[derive [comm_ring, local_ring]]
def localizations (P : Spec.Top R) : Type u := localization.at_prime P.as_ideal

instance (P : Spec.Top R) : inhabited (localizations R P) :=
⟨(localization.of _).to_map 1⟩

variables {R}

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (Spec.Top R)} (f : Π x : U, localizations R x) : Prop :=
∃ (r s : R), ∀ x : U,
  ¬ (s ∈ x.1.as_ideal) ∧ f x * (localization.of _).to_map s = (localization.of _).to_map r

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

For an open set $$U ⊆ Spec A$$, we define $$𝒪(U)$$ to be the set of functions
$$s : U → ⨆_{𝔭 ∈ U} A_𝔭$$, such that $s(𝔭) ∈ A_𝔭$$ for each $$𝔭$$,
and such that $$s$$ is locally a quotient of elements of $$A$$:
to be precise, we require that for each $$𝔭 ∈ U$$, there is a neighborhood $$V$$ of $$𝔭$$,
contained in $$U$$, and elements $$a, f ∈ A$$, such that for each $$𝔮 ∈ V, f ∉ 𝔮$$,
and $$s(𝔮) = a/f$$ in $$A_𝔮$$.

Now Hartshorne had the disadvantage of not knowing about dependent functions,
so we replace his circumlocution about functions into a disjoint union with
`Π x : U, localizations x`.
-/
def is_locally_fraction : local_predicate (localizations R) :=
(is_fraction_prelocal R).sheafify

@[simp]
lemma is_locally_fraction_pred
  {U : opens (Spec.Top R)} (f : Π x : U, localizations R x) :
  (is_locally_fraction R).pred f =
  ∀ x : U, ∃ (V) (m : x.1 ∈ V) (i : V ⟶ U),
  ∃ (r s : R), ∀ y : V,
  ¬ (s ∈ y.1.as_ideal) ∧
    f (i y : U) * (localization.of _).to_map s = (localization.of _).to_map r :=
rfl

/--
The functions satisfying `is_locally_fraction` form a subring.
-/
def sections_subring (U : (opens (Spec.Top R))ᵒᵖ) :
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
def structure_sheaf_in_Type : sheaf (Type u) (Spec.Top R):=
subsheaf_to_Types (is_locally_fraction R)

instance comm_ring_structure_sheaf_in_Type_obj (U : (opens (Spec.Top R))ᵒᵖ) :
  comm_ring ((structure_sheaf_in_Type R).presheaf.obj U) :=
(sections_subring R U).to_comm_ring

open prime_spectrum

/--
The `stalk_to_fiber` map for the structure sheaf is surjective.
(In fact, an isomorphism, as constructed below in `stalk_iso_Type`.)
-/
lemma structure_sheaf_stalk_to_fiber_surjective (x : Top.of (prime_spectrum R)) :
  function.surjective (stalk_to_fiber (is_locally_fraction R) x) :=
begin
  apply stalk_to_fiber_surjective,
  intro t,
  obtain ⟨r, ⟨s, hs⟩, rfl⟩ := (localization.of _).mk'_surjective t,
  exact ⟨⟨basic_open s, hs⟩, λ y, (localization.of _).mk' r ⟨s, y.2⟩,
    ⟨prelocal_predicate.sheafify_of ⟨r, s, λ y, ⟨y.2, localization_map.mk'_spec _ _ _⟩⟩, rfl⟩⟩,
end

/--
The `stalk_to_fiber` map for the structure sheaf is injective.
(In fact, an isomorphism, as constructed below in `stalk_iso_Type`.)

The proof here follows the argument in Hartshorne's Algebraic Geometry, Proposition II.2.2.
-/
lemma structure_sheaf_stalk_to_fiber_injective (x : Top.of (prime_spectrum R)) :
  function.injective (stalk_to_fiber (is_locally_fraction R) x) :=
begin
  apply stalk_to_fiber_injective,
  intros U V fU hU fV hV e,
  rcases hU ⟨x, U.2⟩ with ⟨U', mU, iU, ⟨a, b, wU⟩⟩,
  rcases hV ⟨x, V.2⟩ with ⟨V', mV, iV, ⟨c, d, wV⟩⟩,

  have wUx := (wU ⟨x, mU⟩).2,
  dsimp at wUx,
  have wVx := (wV ⟨x, mV⟩).2,
  dsimp at wVx,
  have e' := congr_arg (λ z, z * ((localization.of _).to_map (b * d))) e,
  dsimp at e',
  simp only [←mul_assoc, ring_hom.map_mul] at e',
  rw [mul_right_comm (fV _)] at e',
  erw [wUx, wVx] at e',
  simp only [←ring_hom.map_mul] at e',
  have := @localization_map.mk'_eq_iff_eq _ _ _ _ _
    (localization.of (as_ideal x).prime_compl) a c ⟨b, (wU ⟨x, mU⟩).1⟩ ⟨d, (wV ⟨x, mV⟩).1⟩,
  dsimp at this,
  rw ←this at e',
  rw localization_map.eq at e',
  rcases e' with ⟨⟨h, hh⟩, e''⟩,
  dsimp at e'',

  let Wb : opens _ := basic_open b,
  let Wd : opens _ := basic_open d,
  let Wh : opens _ := basic_open h,
  use ((Wb ⊓ Wd) ⊓ Wh) ⊓ (U' ⊓ V'),
  refine ⟨⟨⟨(wU ⟨x, mU⟩).1, (wV ⟨x, mV⟩).1⟩, hh⟩, ⟨mU, mV⟩⟩,

  refine ⟨_, _, _⟩,
  change _ ⟶ U.val,
  exact (opens.inf_le_right _ _) ≫ (opens.inf_le_left _ _) ≫ iU,
  change _ ⟶ V.val,
  exact (opens.inf_le_right _ _) ≫ (opens.inf_le_right _ _) ≫ iV,

  intro w,

  dsimp,
  have wU' := (wU ⟨w.1, w.2.2.1⟩).2,
  dsimp at wU',
  have wV' := (wV ⟨w.1, w.2.2.2⟩).2,
  dsimp at wV',
  -- We need to prove `fU w = fV w`.
  -- First we show that is suffices to prove `fU w * b * d * h = fV w * b * d * h`.
  -- Then we calculate (at w) as follows:
  --   fU w * b * d * h
  --       = a * d * h        : wU'
  --   ... = c * b * h        : e''
  --   ... = fV w * d * b * h : wV'
  have u : is_unit ((localization.of (as_ideal w.1).prime_compl).to_map (b * d * h)),
  { simp only [ring_hom.map_mul],
    apply is_unit.mul, apply is_unit.mul,
    exact (localization.of (as_ideal w.1).prime_compl).map_units ⟨b, (wU ⟨w, w.2.2.1⟩).1⟩,
    exact (localization.of (as_ideal w.1).prime_compl).map_units ⟨d, (wV ⟨w, w.2.2.2⟩).1⟩,
    exact (localization.of (as_ideal w.1).prime_compl).map_units ⟨h, w.2.1.2⟩, },
  apply (is_unit.mul_left_inj u).1,
  conv_rhs { rw [mul_comm b d] },
  simp only [ring_hom.map_mul, ←mul_assoc],
  erw [wU', wV'],
  dsimp,
  simp only [←ring_hom.map_mul, ←mul_assoc],
  rw e'',
end


/--
The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structure_presheaf_in_CommRing : presheaf CommRing (Spec.Top R) :=
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
def structure_sheaf : sheaf CommRing (Spec.Top R) :=
{ presheaf := structure_presheaf_in_CommRing R,
  sheaf_condition :=
    -- We check the sheaf condition under `forget CommRing`.
    (sheaf_condition_equiv_sheaf_condition_comp _ _).symm
      (sheaf_condition_equiv_of_iso (structure_presheaf_comp_forget R).symm
        (structure_sheaf_in_Type R).sheaf_condition), }

@[simp] lemma res_apply (U V : opens (Spec.Top R)) (i : V ⟶ U)
  (s : (structure_sheaf R).presheaf.obj (op U)) (x : V) :
  ((structure_sheaf R).presheaf.map i.op s).1 x = (s.1 (i x) : _) :=
rfl

/--
The stalk at `x` is equivalent (just as a type) to the localization at `x`.
-/
def stalk_iso_Type (x : prime_spectrum R) :
  (structure_sheaf_in_Type R).presheaf.stalk x ≅ localization.at_prime x.as_ideal :=
(equiv.of_bijective _
  ⟨structure_sheaf_stalk_to_fiber_injective R x,
   structure_sheaf_stalk_to_fiber_surjective R x⟩).to_iso


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
def const (f g : R) (U : opens (Spec.Top R))
  (hu : ∀ x ∈ U, g ∈ (x : Spec.Top R).as_ideal.prime_compl) :
  (structure_sheaf R).presheaf.obj (op U) :=
⟨λ x, (localization.of _).mk' f ⟨g, hu x x.2⟩,
 λ x, ⟨U, x.2, 𝟙 _, f, g, λ y, ⟨hu y y.2, localization_map.mk'_spec _ _ _⟩⟩⟩

@[simp] lemma const_apply (f g : R) (U : opens (Spec.Top R))
  (hu : ∀ x ∈ U, g ∈ (x : Spec.Top R).as_ideal.prime_compl) (x : U) :
  (const R f g U hu).1 x = (localization.of _).mk' f ⟨g, hu x x.2⟩ :=
rfl

lemma const_apply' (f g : R) (U : opens (Spec.Top R))
  (hu : ∀ x ∈ U, g ∈ (x : Spec.Top R).as_ideal.prime_compl) (x : U)
  (hx : g ∈ (as_ideal x.1).prime_compl) :
  (const R f g U hu).1 x = (localization.of _).mk' f ⟨g, hx⟩ :=
rfl

lemma exists_const (U) (s : (structure_sheaf R).presheaf.obj (op U)) (x : Spec.Top R) (hx : x ∈ U) :
  ∃ (V : opens (Spec.Top R)) (hxV : x ∈ V) (i : V ⟶ U) (f g : R) hg,
  const R f g V hg = (structure_sheaf R).presheaf.map i.op s :=
let ⟨V, hxV, iVU, f, g, hfg⟩ := s.2 ⟨x, hx⟩ in
⟨V, hxV, iVU, f, g, λ y hyV, (hfg ⟨y, hyV⟩).1, subtype.eq $ funext $ λ y,
(localization.of _).mk'_eq_iff_eq_mul.2 $ eq.symm $ (hfg y).2⟩

@[simp] lemma res_const (f g : R) (U hu V hv i) :
  (structure_sheaf R).presheaf.map i (const R f g U hu) = const R f g V hv :=
rfl

lemma res_const' (f g : R) (V hv) :
  (structure_sheaf R).presheaf.map (hom_of_le hv).op (const R f g (basic_open g) (λ _, id)) =
    const R f g V hv :=
rfl

lemma const_zero (f : R) (U hu) : const R 0 f U hu = 0 :=
subtype.eq $ funext $ λ x, (localization.of _).mk'_eq_iff_eq_mul.2 $
by erw [ring_hom.map_zero, subtype.val_eq_coe, subring.coe_zero, pi.zero_apply, zero_mul]

lemma const_self (f : R) (U hu) : const R f f U hu = 1 :=
subtype.eq $ funext $ λ x, localization_map.mk'_self _ _

lemma const_one (U) : const R 1 1 U (λ p _, submonoid.one_mem _) = 1 :=
const_self R 1 U _

lemma const_add (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
  const R f₁ g₁ U hu₁ + const R f₂ g₂ U hu₂ =
  const R (f₁ * g₂ + f₂ * g₁) (g₁ * g₂) U (λ x hx, submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx)) :=
subtype.eq $ funext $ λ x, eq.symm $
by convert (localization.of _).mk'_add f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

lemma const_mul (f₁ f₂ g₁ g₂ : R) (U hu₁ hu₂) :
  const R f₁ g₁ U hu₁ * const R f₂ g₂ U hu₂ =
  const R (f₁ * f₂) (g₁ * g₂) U (λ x hx, submonoid.mul_mem _ (hu₁ x hx) (hu₂ x hx)) :=
subtype.eq $ funext $ λ x, eq.symm $
by convert (localization.of _).mk'_mul f₁ f₂ ⟨g₁, hu₁ x x.2⟩ ⟨g₂, hu₂ x x.2⟩

lemma const_ext {f₁ f₂ g₁ g₂ : R} {U hu₁ hu₂} (h : f₁ * g₂ = f₂ * g₁) :
  const R f₁ g₁ U hu₁ = const R f₂ g₂ U hu₂ :=
subtype.eq $ funext $ λ x, (localization.of _).mk'_eq_of_eq h.symm

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
def to_open (U : opens (Spec.Top R)) : CommRing.of R ⟶ (structure_sheaf R).presheaf.obj (op U) :=
{ to_fun := λ f, ⟨λ x, (localization.of _).to_map f,
    λ x, ⟨U, x.2, 𝟙 _, f, 1, λ y, ⟨(ideal.ne_top_iff_one _).1 y.1.2.1,
      by { rw [ring_hom.map_one, mul_one], refl } ⟩⟩⟩,
  map_one' := subtype.eq $ funext $ λ x, ring_hom.map_one _,
  map_mul' := λ f g, subtype.eq $ funext $ λ x, ring_hom.map_mul _ _ _,
  map_zero' := subtype.eq $ funext $ λ x, ring_hom.map_zero _,
  map_add' := λ f g, subtype.eq $ funext $ λ x, ring_hom.map_add _ _ _ }

@[simp] lemma to_open_res (U V : opens (Spec.Top R)) (i : V ⟶ U) :
  to_open R U ≫ (structure_sheaf R).presheaf.map i.op = to_open R V :=
rfl

@[simp] lemma to_open_apply (U : opens (Spec.Top R)) (f : R) (x : U) :
  (to_open R U f).1 x = (localization.of _).to_map f :=
rfl

lemma to_open_eq_const (U : opens (Spec.Top R)) (f : R) : to_open R U f =
  const R f 1 U (λ x _, (ideal.ne_top_iff_one _).1 x.2.1) :=
subtype.eq $ funext $ λ x, eq.symm $ (localization.of _).mk'_one f

/-- The canonical ring homomorphism interpreting an element of `R` as an element of
the stalk of `structure_sheaf R` at `x`. -/
def to_stalk (x : Spec.Top R) : CommRing.of R ⟶ (structure_sheaf R).presheaf.stalk x :=
(to_open R ⊤ ≫ (structure_sheaf R).presheaf.germ ⟨x, ⟨⟩⟩ : _)

@[simp] lemma to_open_germ (U : opens (Spec.Top R)) (x : U) :
  to_open R U ≫ (structure_sheaf R).presheaf.germ x =
  to_stalk R x :=
by { rw [← to_open_res R ⊤ U (hom_of_le le_top : U ⟶ ⊤), category.assoc, presheaf.germ_res], refl }

@[simp] lemma germ_to_open (U : opens (Spec.Top R)) (x : U) (f : R) :
  (structure_sheaf R).presheaf.germ x (to_open R U f) = to_stalk R x f :=
by { rw ← to_open_germ, refl }

lemma germ_to_top (x : Spec.Top R) (f : R) :
  (structure_sheaf R).presheaf.germ (⟨x, trivial⟩ : (⊤ : opens (Spec.Top R))) (to_open R ⊤ f) =
    to_stalk R x f :=
rfl

lemma is_unit_to_basic_open_self (f : R) : is_unit (to_open R (basic_open f) f) :=
is_unit_of_mul_eq_one _ (const R 1 f (basic_open f) (λ _, id)) $
by rw [to_open_eq_const, const_mul_rev]

/-- The canonical ring homomorphism interpreting `s ∈ R_f` as a section of the structure sheaf
on the basic open defined by `f ∈ R`. -/
def to_basic_open (f : R) : CommRing.of (localization (submonoid.powers f)) ⟶
  (structure_sheaf R).presheaf.obj (op $ basic_open f) :=
localization_map.away_map.lift f (localization.away.of f) (is_unit_to_basic_open_self R f)

@[simp] lemma to_basic_open_mk' (s f : R) (g : submonoid.powers s) :
  to_basic_open R s ((localization.of _).mk' f g) =
  const R f g (basic_open s) (λ x hx, submonoid.powers_subset hx g.2) :=
((localization.of _).lift_mk'_spec _ _ _ _).2 $
by rw [to_open_eq_const, to_open_eq_const, const_mul_cancel']

@[simp] lemma localization_to_basic_open (f : R) :
  @category_theory.category_struct.comp _ _ (CommRing.of R)
      (CommRing.of (localization (submonoid.powers f))) _
    (localization.of $ submonoid.powers f).to_map
    (to_basic_open R f) =
  to_open R (basic_open f) :=
ring_hom.ext $ λ g, (localization.of _).lift_eq _ _

@[simp] lemma to_basic_open_to_map (s f : R) : to_basic_open R s ((localization.of _).to_map f) =
  const R f 1 (basic_open s) (λ _ _, submonoid.one_mem _) :=
((localization.of _).lift_eq _ _).trans $ to_open_eq_const _ _ _

lemma is_unit_to_stalk (x : Spec.Top R) (f : x.as_ideal.prime_compl) :
  is_unit (to_stalk R x (f : R)) :=
by { erw ← germ_to_open R (basic_open (f : R)) ⟨x, f.2⟩ (f : R),
    exact ring_hom.is_unit_map _ (is_unit_to_basic_open_self R f) }

/-- The canonical ring homomorphism from the localization of `R` at `p` to the stalk
of the structure sheaf at the point `p`. -/
def localization_to_stalk (x : Spec.Top R) :
  CommRing.of (localization.at_prime x.as_ideal) ⟶ (structure_sheaf R).presheaf.stalk x :=
(localization.of _).lift (is_unit_to_stalk R x)

@[simp] lemma localization_to_stalk_of (x : Spec.Top R) (f : R) :
  localization_to_stalk R x ((localization.of _).to_map f) = to_stalk R x f :=
(localization.of _).lift_eq _ f

@[simp] lemma localization_to_stalk_mk' (x : Spec.Top R) (f : R) (s : (as_ideal x).prime_compl) :
  localization_to_stalk R x ((localization.of _).mk' f s) =
  (structure_sheaf R).presheaf.germ (⟨x, s.2⟩ : basic_open (s : R))
    (const R f s (basic_open s) (λ _, id)) :=
((localization.of _).lift_mk'_spec _ _ _ _).2 $
by erw [← germ_to_open R (basic_open s) ⟨x, s.2⟩, ← germ_to_open R (basic_open s) ⟨x, s.2⟩,
    ← ring_hom.map_mul, to_open_eq_const, to_open_eq_const, const_mul_cancel']

/-- The ring homomorphism that takes a section of the structure sheaf of `R` on the open set `U`,
implemented as a subtype of dependent functions to localizations at prime ideals, and evaluates
the section on the point corresponding to a given prime ideal. -/
def open_to_localization (U : opens (Spec.Top R)) (x : Spec.Top R) (hx : x ∈ U) :
  (structure_sheaf R).presheaf.obj (op U) ⟶ CommRing.of (localization.at_prime x.as_ideal) :=
{ to_fun := λ s, (s.1 ⟨x, hx⟩ : _),
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl }

@[simp] lemma coe_open_to_localization (U : opens (Spec.Top R)) (x : Spec.Top R) (hx : x ∈ U) :
  (open_to_localization R U x hx :
    (structure_sheaf R).presheaf.obj (op U) → localization.at_prime x.as_ideal) =
  (λ s, (s.1 ⟨x, hx⟩ : _)) :=
rfl

lemma open_to_localization_apply (U : opens (Spec.Top R)) (x : Spec.Top R) (hx : x ∈ U)
  (s : (structure_sheaf R).presheaf.obj (op U)) :
  open_to_localization R U x hx s = (s.1 ⟨x, hx⟩ : _) :=
rfl

/-- The ring homomorphism from the stalk of the structure sheaf of `R` at a point corresponding to
a prime ideal `p` to the localization of `R` at `p`,
formed by gluing the `open_to_localization` maps. -/
def stalk_to_fiber_ring_hom (x : Spec.Top R) :
  (structure_sheaf R).presheaf.stalk x ⟶ CommRing.of (localization.at_prime x.as_ideal) :=
limits.colimit.desc (((open_nhds.inclusion x).op) ⋙ (structure_sheaf R).presheaf)
  { X := _,
    ι :=
    { app := λ U, open_to_localization R ((open_nhds.inclusion _).obj (unop U)) x (unop U).2, } }

@[simp] lemma germ_comp_stalk_to_fiber_ring_hom (U : opens (Spec.Top R)) (x : U) :
  (structure_sheaf R).presheaf.germ x ≫ stalk_to_fiber_ring_hom R x =
  open_to_localization R U x x.2 :=
limits.colimit.ι_desc _ _

@[simp] lemma stalk_to_fiber_ring_hom_germ' (U : opens (Spec.Top R)) (x : Spec.Top R) (hx : x ∈ U)
  (s : (structure_sheaf R).presheaf.obj (op U)) :
  stalk_to_fiber_ring_hom R x ((structure_sheaf R).presheaf.germ ⟨x, hx⟩ s) = (s.1 ⟨x, hx⟩ : _) :=
ring_hom.ext_iff.1 (germ_comp_stalk_to_fiber_ring_hom R U ⟨x, hx⟩ : _) s

@[simp] lemma stalk_to_fiber_ring_hom_germ (U : opens (Spec.Top R)) (x : U)
  (s : (structure_sheaf R).presheaf.obj (op U)) :
  stalk_to_fiber_ring_hom R x ((structure_sheaf R).presheaf.germ x s) = s.1 x :=
by { cases x, exact stalk_to_fiber_ring_hom_germ' R U _ _ _ }

@[simp] lemma to_stalk_comp_stalk_to_fiber_ring_hom (x : Spec.Top R) :
  to_stalk R x ≫ stalk_to_fiber_ring_hom R x = (localization.of _).to_map :=
by { erw [to_stalk, category.assoc, germ_comp_stalk_to_fiber_ring_hom], refl }

@[simp] lemma stalk_to_fiber_ring_hom_to_stalk (x : Spec.Top R) (f : R) :
  stalk_to_fiber_ring_hom R x (to_stalk R x f) = (localization.of _).to_map f :=
ring_hom.ext_iff.1 (to_stalk_comp_stalk_to_fiber_ring_hom R x) _

/-- The ring isomorphism between the stalk of the structure sheaf of `R` at a point `p`
corresponding to a prime ideal in `R` and the localization of `R` at `p`. -/
def stalk_iso (x : Spec.Top R) :
  (structure_sheaf R).presheaf.stalk x ≅ CommRing.of (localization.at_prime x.as_ideal) :=
{ hom := stalk_to_fiber_ring_hom R x,
  inv := localization_to_stalk R x,
  hom_inv_id' := (structure_sheaf R).presheaf.stalk_hom_ext $ λ U hxU,
  begin
    ext s, simp only [coe_comp], rw [coe_id, stalk_to_fiber_ring_hom_germ'],
    obtain ⟨V, hxV, iVU, f, g, hg, hs⟩ := exists_const _ _ s x hxU,
    erw [← res_apply R U V iVU s ⟨x, hxV⟩, ← hs, const_apply, localization_to_stalk_mk'],
    refine (structure_sheaf R).presheaf.germ_ext V hxV (hom_of_le hg) iVU _,
    erw [← hs, res_const']
  end,
  inv_hom_id' := (localization.of x.as_ideal.prime_compl).epic_of_localization_map $ λ f,
    by simp only [ring_hom.comp_apply, coe_comp, coe_id, localization_to_stalk_of,
        stalk_to_fiber_ring_hom_to_stalk] }

end algebraic_geometry
