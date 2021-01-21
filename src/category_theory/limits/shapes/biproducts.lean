/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.finite_products
import category_theory.preadditive

/-!
# Biproducts and binary biproducts

We introduce the notion of (finite) biproducts and binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

We treat first the case of a general category with zero morphisms,
and subsequently the case of a preadditive category.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `binary_bicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `binary_bicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit cocone.

In a preadditive category,
* any `binary_biproduct` satisfies `total : fst ≫ inl + snd ≫ inr = 𝟙 X`
* any `binary_product` is a `binary_biproduct`
* any `binary_coproduct` is a `binary_biproduct`

For biproducts indexed by a `fintype J`, a `bicone` again consists of a cone point `X`
and morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.

In a preadditive category,
* any `biproduct` satisfies `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
* any `product` is a `biproduct`
* any `coproduct` is a `biproduct`

## Notation
As `⊕` is already taken for the sum of types, we introduce the notation `X ⊞ Y` for
a binary biproduct. We introduce `⨁ f` for the indexed biproduct.
-/

noncomputable theory

universes v u

open category_theory
open category_theory.functor

namespace category_theory.limits

variables {J : Type v} [decidable_eq J]
variables {C : Type u} [category.{v} C] [has_zero_morphisms C]

/--
A `c : bicone F` is:
* an object `c.X` and
* morphisms `π j : X ⟶ F j` and `ι j : F j ⟶ X` for each `j`,
* such that `ι j ≫ π j'` is the identity when `j = j'` and zero otherwise.
-/
@[nolint has_inhabited_instance]
structure bicone (F : J → C) :=
(X : C)
(π : Π j, X ⟶ F j)
(ι : Π j, F j ⟶ X)
(ι_π : ∀ j j', ι j ≫ π j' = if h : j = j' then eq_to_hom (congr_arg F h) else 0)

@[simp] lemma bicone_ι_π_self {F : J → C} (B : bicone F) (j : J) : B.ι j ≫ B.π j = 𝟙 (F j) :=
by simpa using B.ι_π j j

@[simp] lemma bicone_ι_π_ne {F : J → C} (B : bicone F) {j j' : J} (h : j ≠ j') :
  B.ι j ≫ B.π j' = 0 :=
by simpa [h] using B.ι_π j j'

variables {F : J → C}

namespace bicone
/-- Extract the cone from a bicone. -/
@[simps]
def to_cone (B : bicone F) : cone (discrete.functor F) :=
{ X := B.X,
  π := { app := λ j, B.π j }, }

/-- Extract the cocone from a bicone. -/
@[simps]
def to_cocone (B : bicone F) : cocone (discrete.functor F) :=
{ X := B.X,
  ι := { app := λ j, B.ι j }, }

end bicone

/--
A bicone over `F : J → C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_inhabited_instance]
structure limit_bicone (F : J → C) :=
(bicone : bicone F)
(is_limit : is_limit bicone.to_cone)
(is_colimit : is_colimit bicone.to_cocone)

/--
`has_biproduct F` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `F`.
-/
class has_biproduct (F : J → C) : Prop :=
mk' :: (exists_biproduct : nonempty (limit_bicone F))

lemma has_biproduct.mk {F : J → C} (d : limit_bicone F) : has_biproduct F :=
⟨nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `biproduct_data F` from `has_biproduct F`. -/
def get_biproduct_data (F : J → C) [has_biproduct F] : limit_bicone F :=
classical.choice has_biproduct.exists_biproduct

/-- A bicone for `F` which is both a limit cone and a colimit cocone. -/
def biproduct.bicone (F : J → C) [has_biproduct F] : bicone F :=
(get_biproduct_data F).bicone

/-- `biproduct.bicone F` is a limit cone. -/
def biproduct.is_limit (F : J → C) [has_biproduct F] : is_limit (biproduct.bicone F).to_cone :=
(get_biproduct_data F).is_limit

/-- `biproduct.bicone F` is a colimit cocone. -/
def biproduct.is_colimit (F : J → C) [has_biproduct F] : is_colimit (biproduct.bicone F).to_cocone :=
(get_biproduct_data F).is_colimit

@[priority 100]
instance has_product_of_has_biproduct [has_biproduct F] : has_limit (discrete.functor F) :=
has_limit.mk { cone := (biproduct.bicone F).to_cone,
  is_limit := biproduct.is_limit F, }

@[priority 100]
instance has_coproduct_of_has_biproduct [has_biproduct F] : has_colimit (discrete.functor F) :=
has_colimit.mk { cocone := (biproduct.bicone F).to_cocone,
  is_colimit := biproduct.is_colimit F, }

variables (J C)

/--
`C` has biproducts of shape `J` if we have
a limit and a colimit, with the same cone points,
of every function `F : J → C`.
-/
class has_biproducts_of_shape : Prop :=
(has_biproduct : Π F : J → C, has_biproduct F)

attribute [instance, priority 100] has_biproducts_of_shape.has_biproduct

/-- `has_finite_biproducts C` represents a choice of biproduct for every family of objects in `C`
indexed by a finite type with decidable equality. -/
class has_finite_biproducts : Prop :=
(has_biproducts_of_shape : Π (J : Type v) [decidable_eq J] [fintype J],
  has_biproducts_of_shape J C)

attribute [instance, priority 100] has_finite_biproducts.has_biproducts_of_shape

@[priority 100]
instance has_finite_products_of_has_finite_biproducts [has_finite_biproducts C] :
  has_finite_products C :=
λ J _ _, ⟨λ F, by exactI has_limit_of_iso discrete.nat_iso_functor.symm⟩

@[priority 100]
instance has_finite_coproducts_of_has_finite_biproducts [has_finite_biproducts C] :
  has_finite_coproducts C :=
λ J _ _, ⟨λ F, by exactI has_colimit_of_iso discrete.nat_iso_functor⟩

variables {J C}

/--
The isomorphism between the specified limit and the specified colimit for
a functor with a bilimit.
-/
def biproduct_iso (F : J → C) [has_biproduct F] :
  limits.pi_obj F ≅ limits.sigma_obj F :=
(is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (biproduct.is_limit F)).trans $
  is_colimit.cocone_point_unique_up_to_iso (biproduct.is_colimit F) (colimit.is_colimit _)

end category_theory.limits

namespace category_theory.limits
variables {J : Type v} [decidable_eq J]
variables {C : Type u} [category.{v} C] [has_zero_morphisms C]

/-- `biproduct f` computes the biproduct of a family of elements `f`. (It is defined as an
   abbreviation for `limit (discrete.functor f)`, so for most facts about `biproduct f`, you will
   just use general facts about limits and colimits.) -/
abbreviation biproduct (f : J → C) [has_biproduct f] : C :=
(biproduct.bicone f).X

notation `⨁ ` f:20 := biproduct f

/-- The projection onto a summand of a biproduct. -/
abbreviation biproduct.π (f : J → C) [has_biproduct f] (b : J) : ⨁ f ⟶ f b :=
(biproduct.bicone f).π b

@[simp]
lemma biproduct.bicone_π (f : J → C) [has_biproduct f] (b : J) :
  (biproduct.bicone f).π b = biproduct.π f b := rfl

/-- The inclusion into a summand of a biproduct. -/
abbreviation biproduct.ι (f : J → C) [has_biproduct f] (b : J) : f b ⟶ ⨁ f :=
(biproduct.bicone f).ι b

@[simp]
lemma biproduct.bicone_ι (f : J → C) [has_biproduct f] (b : J) :
  (biproduct.bicone f).ι b = biproduct.ι f b := rfl

@[reassoc]
lemma biproduct.ι_π (f : J → C) [has_biproduct f] (j j' : J) :
  biproduct.ι f j ≫ biproduct.π f j' = if h : j = j' then eq_to_hom (congr_arg f h) else 0 :=
(biproduct.bicone f).ι_π j j'

@[simp,reassoc]
lemma biproduct.ι_π_self (f : J → C) [has_biproduct f] (j : J) :
  biproduct.ι f j ≫ biproduct.π f j = 𝟙 _ :=
by simp [biproduct.ι_π]

@[simp,reassoc]
lemma biproduct.ι_π_ne (f : J → C) [has_biproduct f] {j j' : J} (h : j ≠ j') :
  biproduct.ι f j ≫ biproduct.π f j' = 0 :=
by simp [biproduct.ι_π, h]

/-- Given a collection of maps into the summands, we obtain a map into the biproduct. -/
abbreviation biproduct.lift
  {f : J → C} [has_biproduct f] {P : C} (p : Π b, P ⟶ f b) : P ⟶ ⨁ f :=
(biproduct.is_limit f).lift (fan.mk P p)
/-- Given a collection of maps out of the summands, we obtain a map out of the biproduct. -/
abbreviation biproduct.desc
  {f : J → C} [has_biproduct f] {P : C} (p : Π b, f b ⟶ P) : ⨁ f ⟶ P :=
(biproduct.is_colimit f).desc (cofan.mk P p)

@[simp, reassoc]
lemma biproduct.lift_π {f : J → C} [has_biproduct f] {P : C} (p : Π b, P ⟶ f b) (j : J) :
  biproduct.lift p ≫ biproduct.π f j = p j :=
(biproduct.is_limit f).fac _ _

@[simp, reassoc]
lemma biproduct.ι_desc {f : J → C} [has_biproduct f] {P : C} (p : Π b, f b ⟶ P) (j : J) :
  biproduct.ι f j ≫ biproduct.desc p = p j :=
(biproduct.is_colimit f).fac _ _

/-- Given a collection of maps between corresponding summands of a pair of biproducts
indexed by the same type, we obtain a map between the biproducts. -/
abbreviation biproduct.map [fintype J] {f g : J → C} [has_finite_biproducts C]
  (p : Π b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
is_limit.map (biproduct.bicone f).to_cone (biproduct.is_limit g) (discrete.nat_trans p)

/-- An alternative to `biproduct.map` constructed via colimits.
This construction only exists in order to show it is equal to `biproduct.map`. -/
abbreviation biproduct.map' [fintype J] {f g : J → C} [has_finite_biproducts C]
  (p : Π b, f b ⟶ g b) : ⨁ f ⟶ ⨁ g :=
is_colimit.map (biproduct.is_colimit f) (biproduct.bicone g).to_cocone (discrete.nat_trans p)

@[ext] lemma biproduct.hom_ext {f : J → C} [has_biproduct f]
  {Z : C} (g h : Z ⟶ ⨁ f)
  (w : ∀ j, g ≫ biproduct.π f j = h ≫ biproduct.π f j) : g = h :=
(biproduct.is_limit f).hom_ext w

@[ext] lemma biproduct.hom_ext' {f : J → C} [has_biproduct f]
  {Z : C} (g h : ⨁ f ⟶ Z)
  (w : ∀ j, biproduct.ι f j ≫ g =  biproduct.ι f j ≫ h) : g = h :=
(biproduct.is_colimit f).hom_ext w

lemma biproduct.map_eq_map' [fintype J] {f g : J → C} [has_finite_biproducts C]
  (p : Π b, f b ⟶ g b) : biproduct.map p = biproduct.map' p :=
begin
  ext j j',
  simp only [discrete.nat_trans_app, limits.is_colimit.ι_map, limits.is_limit.map_π, category.assoc,
    ←bicone.to_cone_π_app, ←biproduct.bicone_π, ←bicone.to_cocone_ι_app, ←biproduct.bicone_ι],
  simp only [biproduct.bicone_ι, biproduct.bicone_π, bicone.to_cocone_ι_app, bicone.to_cone_π_app],
  rw [biproduct.ι_π_assoc, biproduct.ι_π],
  split_ifs,
  { subst h, rw [eq_to_hom_refl, category.id_comp], erw category.comp_id, },
  { simp, },
end

instance biproduct.ι_mono (f : J → C) [has_biproduct f]
  (b : J) : split_mono (biproduct.ι f b) :=
{ retraction := biproduct.desc $
    λ b', if h : b' = b then eq_to_hom (congr_arg f h) else biproduct.ι f b' ≫ biproduct.π f b }

instance biproduct.π_epi (f : J → C) [has_biproduct f]
  (b : J) : split_epi (biproduct.π f b) :=
{ section_ := biproduct.lift $
    λ b', if h : b = b' then eq_to_hom (congr_arg f h) else biproduct.ι f b ≫ biproduct.π f b' }

@[simp, reassoc]
lemma biproduct.map_π [fintype J] {f g : J → C} [has_finite_biproducts C]
  (p : Π j, f j ⟶ g j) (j : J) :
  biproduct.map p ≫ biproduct.π g j = biproduct.π f j ≫ p j :=
limits.is_limit.map_π _ _ _ _

@[simp, reassoc]
lemma biproduct.ι_map [fintype J] {f g : J → C} [has_finite_biproducts C]
  (p : Π j, f j ⟶ g j) (j : J) :
  biproduct.ι f j ≫ biproduct.map p = p j ≫ biproduct.ι g j :=
begin
  rw biproduct.map_eq_map',
  convert limits.is_colimit.ι_map _ _ _ _; refl
end

variables {C}

/--
A binary bicone for a pair of objects `P Q : C` consists of the cone point `X`,
maps from `X` to both `P` and `Q`, and maps from both `P` and `Q` to `X`,
so that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`
-/
@[nolint has_inhabited_instance]
structure binary_bicone (P Q : C) :=
(X : C)
(fst : X ⟶ P)
(snd : X ⟶ Q)
(inl : P ⟶ X)
(inr : Q ⟶ X)
(inl_fst' : inl ≫ fst = 𝟙 P . obviously)
(inl_snd' : inl ≫ snd = 0 . obviously)
(inr_fst' : inr ≫ fst = 0 . obviously)
(inr_snd' : inr ≫ snd = 𝟙 Q . obviously)

restate_axiom binary_bicone.inl_fst'
restate_axiom binary_bicone.inl_snd'
restate_axiom binary_bicone.inr_fst'
restate_axiom binary_bicone.inr_snd'
attribute [simp, reassoc] binary_bicone.inl_fst binary_bicone.inl_snd
  binary_bicone.inr_fst binary_bicone.inr_snd

namespace binary_bicone
variables {P Q : C}

/-- Extract the cone from a binary bicone. -/
def to_cone (c : binary_bicone P Q) : cone (pair P Q) :=
binary_fan.mk c.fst c.snd

@[simp]
lemma to_cone_X (c : binary_bicone P Q) :
  c.to_cone.X = c.X := rfl

@[simp]
lemma to_cone_π_app_left (c : binary_bicone P Q) :
  c.to_cone.π.app (walking_pair.left) = c.fst := rfl
@[simp]
lemma to_cone_π_app_right (c : binary_bicone P Q) :
  c.to_cone.π.app (walking_pair.right) = c.snd := rfl

/-- Extract the cocone from a binary bicone. -/
def to_cocone (c : binary_bicone P Q) : cocone (pair P Q) :=
binary_cofan.mk c.inl c.inr

@[simp]
lemma to_cocone_X (c : binary_bicone P Q) :
  c.to_cocone.X = c.X := rfl

@[simp]
lemma to_cocone_ι_app_left (c : binary_bicone P Q) :
  c.to_cocone.ι.app (walking_pair.left) = c.inl := rfl
@[simp]
lemma to_cocone_ι_app_right (c : binary_bicone P Q) :
  c.to_cocone.ι.app (walking_pair.right) = c.inr := rfl

end binary_bicone

namespace bicone

/-- Convert a `bicone` over a function on `walking_pair` to a binary_bicone. -/
@[simps]
def to_binary_bicone {X Y : C} (b : bicone (pair X Y).obj) : binary_bicone X Y :=
{ X := b.X,
  fst := b.π walking_pair.left,
  snd := b.π walking_pair.right,
  inl := b.ι walking_pair.left,
  inr := b.ι walking_pair.right,
  inl_fst' := by { simp [bicone.ι_π], refl, },
  inr_fst' := by simp [bicone.ι_π],
  inl_snd' := by simp [bicone.ι_π],
  inr_snd' := by { simp [bicone.ι_π], refl, }, }

/--
If the cone obtained from a bicone over `pair X Y` is a limit cone,
so is the cone obtained by converting that bicone to a binary_bicone, then to a cone.
-/
def to_binary_bicone_is_limit {X Y : C} {b : bicone (pair X Y).obj}
  (c : is_limit (b.to_cone)) :
  is_limit (b.to_binary_bicone.to_cone) :=
{ lift := λ s, c.lift s,
   fac' := λ s j, by { cases j; erw c.fac, },
   uniq' := λ s m w,
   begin
     apply c.uniq s,
     rintro (⟨⟩|⟨⟩),
     exact w walking_pair.left,
     exact w walking_pair.right,
   end, }

/--
If the cocone obtained from a bicone over `pair X Y` is a colimit cocone,
so is the cocone obtained by converting that bicone to a binary_bicone, then to a cocone.
-/
def to_binary_bicone_is_colimit {X Y : C} {b : bicone (pair X Y).obj}
  (c : is_colimit (b.to_cocone)) :
  is_colimit (b.to_binary_bicone.to_cocone) :=
{ desc := λ s, c.desc s,
   fac' := λ s j, by { cases j; erw c.fac, },
   uniq' := λ s m w,
   begin
     apply c.uniq s,
     rintro (⟨⟩|⟨⟩),
     exact w walking_pair.left,
     exact w walking_pair.right,
   end, }

end bicone

/--
A bicone over `P Q : C`, which is both a limit cone and a colimit cocone.
-/
@[nolint has_inhabited_instance]
structure binary_biproduct_data (P Q : C) :=
(bicone : binary_bicone P Q)
(is_limit : is_limit bicone.to_cone)
(is_colimit : is_colimit bicone.to_cocone)

/--
`has_binary_biproduct P Q` expresses the mere existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`.
-/
class has_binary_biproduct (P Q : C) : Prop :=
mk' :: (exists_binary_biproduct : nonempty (binary_biproduct_data P Q))

lemma has_binary_biproduct.mk {P Q : C} (d : binary_biproduct_data P Q) : has_binary_biproduct P Q :=
⟨nonempty.intro d⟩

/--
Use the axiom of choice to extract explicit `binary_biproduct_data F` from `has_binary_biproduct F`.
-/
def get_binary_biproduct_data (P Q : C) [has_binary_biproduct P Q] : binary_biproduct_data P Q :=
classical.choice has_binary_biproduct.exists_binary_biproduct

/-- A bicone for `P Q ` which is both a limit cone and a colimit cocone. -/
def binary_biproduct.bicone (P Q : C) [has_binary_biproduct P Q] : binary_bicone P Q :=
(get_binary_biproduct_data P Q).bicone

/-- `binary_biproduct.bicone P Q` is a limit cone. -/
def binary_biproduct.is_limit (P Q : C) [has_binary_biproduct P Q] :
  is_limit (binary_biproduct.bicone P Q).to_cone :=
(get_binary_biproduct_data P Q).is_limit

/-- `binary_biproduct.bicone P Q` is a colimit cocone. -/
def binary_biproduct.is_colimit (P Q : C) [has_binary_biproduct P Q] :
  is_colimit (binary_biproduct.bicone P Q).to_cocone :=
(get_binary_biproduct_data P Q).is_colimit

section
variable (C)

/--
`has_binary_biproducts C` represents the existence of a bicone which is
simultaneously a limit and a colimit of the diagram `pair P Q`, for every `P Q : C`.
-/
class has_binary_biproducts : Prop :=
(has_binary_biproduct : Π (P Q : C), has_binary_biproduct P Q)

attribute [instance, priority 100] has_binary_biproducts.has_binary_biproduct

/--
A category with finite biproducts has binary biproducts.

This is not an instance as typically in concrete categories there will be
an alternative construction with nicer definitional properties.
-/
lemma has_binary_biproducts_of_finite_biproducts [has_finite_biproducts C] :
  has_binary_biproducts C :=
{ has_binary_biproduct := λ P Q, has_binary_biproduct.mk
  { bicone := (biproduct.bicone (pair P Q).obj).to_binary_bicone,
    is_limit := bicone.to_binary_bicone_is_limit (biproduct.is_limit _),
    is_colimit := bicone.to_binary_bicone_is_colimit (biproduct.is_colimit _) } }

end

variables {P Q : C}

instance has_binary_biproduct.has_limit_pair [has_binary_biproduct P Q] :
  has_limit (pair P Q) :=
has_limit.mk ⟨_, binary_biproduct.is_limit P Q⟩

instance has_binary_biproduct.has_colimit_pair [has_binary_biproduct P Q] :
  has_colimit (pair P Q) :=
has_colimit.mk ⟨_, binary_biproduct.is_colimit P Q⟩

@[priority 100]
instance has_binary_products_of_has_binary_biproducts [has_binary_biproducts C] :
  has_binary_products C :=
{ has_limit := λ F, has_limit_of_iso (diagram_iso_pair F).symm }
@[priority 100]
instance has_binary_coproducts_of_has_binary_biproducts [has_binary_biproducts C] :
  has_binary_coproducts C :=
{ has_colimit := λ F, has_colimit_of_iso (diagram_iso_pair F) }

/--
The isomorphism between the specified binary product and the specified binary coproduct for
a pair for a binary biproduct.
-/
def biprod_iso (X Y : C) [has_binary_biproduct X Y]  :
  limits.prod X Y ≅ limits.coprod X Y :=
(is_limit.cone_point_unique_up_to_iso (limit.is_limit _) (binary_biproduct.is_limit X Y)).trans $
  is_colimit.cocone_point_unique_up_to_iso (binary_biproduct.is_colimit X Y) (colimit.is_colimit _)

/-- An arbitrary choice of biproduct of a pair of objects. -/
abbreviation biprod (X Y : C) [has_binary_biproduct X Y] := (binary_biproduct.bicone X Y).X

notation X ` ⊞ `:20 Y:20 := biprod X Y

/-- The projection onto the first summand of a binary biproduct. -/
abbreviation biprod.fst {X Y : C} [has_binary_biproduct X Y] : X ⊞ Y ⟶ X :=
(binary_biproduct.bicone X Y).fst
/-- The projection onto the second summand of a binary biproduct. -/
abbreviation biprod.snd {X Y : C} [has_binary_biproduct X Y] : X ⊞ Y ⟶ Y :=
(binary_biproduct.bicone X Y).snd
/-- The inclusion into the first summand of a binary biproduct. -/
abbreviation biprod.inl {X Y : C} [has_binary_biproduct X Y] : X ⟶ X ⊞ Y :=
(binary_biproduct.bicone X Y).inl
/-- The inclusion into the second summand of a binary biproduct. -/
abbreviation biprod.inr {X Y : C} [has_binary_biproduct X Y] : Y ⟶ X ⊞ Y :=
(binary_biproduct.bicone X Y).inr

section
variables {X Y : C} [has_binary_biproduct X Y]

@[simp] lemma binary_biproduct.bicone_fst : (binary_biproduct.bicone X Y).fst = biprod.fst := rfl
@[simp] lemma binary_biproduct.bicone_snd : (binary_biproduct.bicone X Y).snd = biprod.snd := rfl
@[simp] lemma binary_biproduct.bicone_inl : (binary_biproduct.bicone X Y).inl = biprod.inl := rfl
@[simp] lemma binary_biproduct.bicone_inr : (binary_biproduct.bicone X Y).inr = biprod.inr := rfl

end

@[simp,reassoc]
lemma biprod.inl_fst {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
(binary_biproduct.bicone X Y).inl_fst
@[simp,reassoc]
lemma biprod.inl_snd {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
(binary_biproduct.bicone X Y).inl_snd
@[simp,reassoc]
lemma biprod.inr_fst {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
(binary_biproduct.bicone X Y).inr_fst
@[simp,reassoc]
lemma biprod.inr_snd {X Y : C} [has_binary_biproduct X Y] :
  (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
(binary_biproduct.bicone X Y).inr_snd

/-- Given a pair of maps into the summands of a binary biproduct,
we obtain a map into the binary biproduct. -/
abbreviation biprod.lift {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  W ⟶ X ⊞ Y :=
(binary_biproduct.is_limit X Y).lift (binary_fan.mk f g)
/-- Given a pair of maps out of the summands of a binary biproduct,
we obtain a map out of the binary biproduct. -/
abbreviation biprod.desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  X ⊞ Y ⟶ W :=
(binary_biproduct.is_colimit X Y).desc (binary_cofan.mk f g)

@[simp, reassoc]
lemma biprod.lift_fst {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  biprod.lift f g ≫ biprod.fst = f :=
(binary_biproduct.is_limit X Y).fac _ walking_pair.left

@[simp, reassoc]
lemma biprod.lift_snd {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
  biprod.lift f g ≫ biprod.snd = g :=
(binary_biproduct.is_limit X Y).fac _ walking_pair.right

@[simp, reassoc]
lemma biprod.inl_desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  biprod.inl ≫ biprod.desc f g = f :=
(binary_biproduct.is_colimit X Y).fac _ walking_pair.left

@[simp, reassoc]
lemma biprod.inr_desc {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
  biprod.inr ≫ biprod.desc f g = g :=
(binary_biproduct.is_colimit X Y).fac _ walking_pair.right

instance biprod.mono_lift_of_mono_left {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X)
  (g : W ⟶ Y) [mono f] : mono (biprod.lift f g) :=
mono_of_mono_fac $ biprod.lift_fst _ _

instance biprod.mono_lift_of_mono_right {W X Y : C} [has_binary_biproduct X Y] (f : W ⟶ X)
  (g : W ⟶ Y) [mono g] : mono (biprod.lift f g) :=
mono_of_mono_fac $ biprod.lift_snd _ _

instance biprod.epi_desc_of_epi_left {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  [epi f] : epi (biprod.desc f g) :=
epi_of_epi_fac $ biprod.inl_desc _ _

instance biprod.epi_desc_of_epi_right {W X Y : C} [has_binary_biproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  [epi g] : epi (biprod.desc f g) :=
epi_of_epi_fac $ biprod.inr_desc _ _

/-- Given a pair of maps between the summands of a pair of binary biproducts,
we obtain a map between the binary biproducts. -/
abbreviation biprod.map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
is_limit.map (binary_biproduct.bicone W X).to_cone (binary_biproduct.is_limit Y Z)
  (@map_pair _ _ (pair W X) (pair Y Z) f g)

/-- An alternative to `biprod.map` constructed via colimits.
This construction only exists in order to show it is equal to `biprod.map`. -/
abbreviation biprod.map' {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
is_colimit.map (binary_biproduct.is_colimit W X) (binary_biproduct.bicone Y Z).to_cocone
  (@map_pair _ _ (pair W X) (pair Y Z) f g)

@[ext] lemma biprod.hom_ext {X Y Z : C} [has_binary_biproduct X Y] (f g : Z ⟶ X ⊞ Y)
  (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
binary_fan.is_limit.hom_ext (binary_biproduct.is_limit X Y) h₀ h₁


@[ext] lemma biprod.hom_ext' {X Y Z : C} [has_binary_biproduct X Y] (f g : X ⊞ Y ⟶ Z)
  (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
binary_cofan.is_colimit.hom_ext (binary_biproduct.is_colimit X Y) h₀ h₁

lemma biprod.map_eq_map' {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) : biprod.map f g = biprod.map' f g :=
begin
  ext,
  { simp only [map_pair_left, is_colimit.ι_map, is_limit.map_π, biprod.inl_fst_assoc, category.assoc,
    ←binary_bicone.to_cone_π_app_left, ←binary_biproduct.bicone_fst,
    ←binary_bicone.to_cocone_ι_app_left, ←binary_biproduct.bicone_inl],
    simp },
  { simp only [map_pair_left, is_colimit.ι_map, is_limit.map_π, zero_comp,
      biprod.inl_snd_assoc, category.assoc,
      ←binary_bicone.to_cone_π_app_right, ←binary_biproduct.bicone_snd,
      ←binary_bicone.to_cocone_ι_app_left, ←binary_biproduct.bicone_inl],
    simp },
  { simp only [map_pair_right, biprod.inr_fst_assoc, is_colimit.ι_map, is_limit.map_π,
      zero_comp, category.assoc,
      ←binary_bicone.to_cone_π_app_left, ←binary_biproduct.bicone_fst,
      ←binary_bicone.to_cocone_ι_app_right, ←binary_biproduct.bicone_inr],
    simp },
  { simp only [map_pair_right, is_colimit.ι_map, is_limit.map_π, biprod.inr_snd_assoc, category.assoc,
      ←binary_bicone.to_cone_π_app_right, ←binary_biproduct.bicone_snd,
      ←binary_bicone.to_cocone_ι_app_right, ←binary_biproduct.bicone_inr],
    simp }
end

instance biprod.inl_mono {X Y : C} [has_binary_biproduct X Y] :
  split_mono (biprod.inl : X ⟶ X ⊞ Y) :=
{ retraction := biprod.desc (𝟙 X) (biprod.inr ≫ biprod.fst) }

instance biprod.inr_mono {X Y : C} [has_binary_biproduct X Y] :
  split_mono (biprod.inr : Y ⟶ X ⊞ Y) :=
{ retraction := biprod.desc (biprod.inl ≫ biprod.snd) (𝟙 Y)}

instance biprod.fst_epi {X Y : C} [has_binary_biproduct X Y] :
  split_epi (biprod.fst : X ⊞ Y ⟶ X) :=
{ section_ := biprod.lift (𝟙 X) (biprod.inl ≫ biprod.snd) }

instance biprod.snd_epi {X Y : C} [has_binary_biproduct X Y] :
  split_epi (biprod.snd : X ⊞ Y ⟶ Y) :=
{ section_ := biprod.lift (biprod.inr ≫ biprod.fst) (𝟙 Y) }

@[simp,reassoc]
lemma biprod.map_fst {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
is_limit.map_π _ _ _ walking_pair.left

@[simp,reassoc]
lemma biprod.map_snd {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
is_limit.map_π _ _ _ walking_pair.right

-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[simp,reassoc]
lemma biprod.inl_map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.inl ≫ biprod.map f g = f ≫ biprod.inl :=
begin
  rw biprod.map_eq_map',
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ walking_pair.left
end

@[simp,reassoc]
lemma biprod.inr_map {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ⟶ Y) (g : X ⟶ Z) :
  biprod.inr ≫ biprod.map f g = g ≫ biprod.inr :=
begin
  rw biprod.map_eq_map',
  exact is_colimit.ι_map (binary_biproduct.is_colimit W X) _ _ walking_pair.right
end

/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
def biprod.map_iso {W X Y Z : C} [has_binary_biproduct W X] [has_binary_biproduct Y Z]
  (f : W ≅ Y) (g : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z :=
{ hom := biprod.map f.hom g.hom,
  inv := biprod.map f.inv g.inv }

section
variables [has_binary_biproducts C]

/-- The braiding isomorphism which swaps a binary biproduct. -/
@[simps] def biprod.braiding (P Q : C) : P ⊞ Q ≅ Q ⊞ P :=
{ hom := biprod.lift biprod.snd biprod.fst,
  inv := biprod.lift biprod.snd biprod.fst }

/--
An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct.
-/
@[simps]
def biprod.braiding' (P Q : C) : P ⊞ Q ≅ Q ⊞ P :=
{ hom := biprod.desc biprod.inr biprod.inl,
  inv := biprod.desc biprod.inr biprod.inl }

lemma biprod.braiding'_eq_braiding {P Q : C} :
  biprod.braiding' P Q = biprod.braiding P Q :=
by tidy

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc] lemma biprod.braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
  biprod.map f g ≫ (biprod.braiding _ _).hom = (biprod.braiding _ _).hom ≫ biprod.map g f :=
by tidy

@[reassoc] lemma biprod.braiding_map_braiding {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
  (biprod.braiding X W).hom ≫ biprod.map f g ≫ (biprod.braiding Y Z).hom = biprod.map g f :=
by tidy

@[simp, reassoc] lemma biprod.symmetry' (P Q : C) :
  biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst = 𝟙 (P ⊞ Q) :=
by tidy

/-- The braiding isomorphism is symmetric. -/
@[reassoc] lemma biprod.symmetry (P Q : C) :
  (biprod.braiding P Q).hom ≫ (biprod.braiding Q P).hom = 𝟙 _ :=
by simp

end

-- TODO:
-- If someone is interested, they could provide the constructions:
--   has_binary_biproducts ↔ has_finite_biproducts

end category_theory.limits

namespace category_theory.limits

section preadditive
variables {C : Type u} [category.{v} C] [preadditive C]
variables {J : Type v} [decidable_eq J] [fintype J]

open category_theory.preadditive
open_locale big_operators

/--
In a preadditive category, we can construct a biproduct for `f : J → C` from
any bicone `b` for `f` satisfying `total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
lemma has_biproduct_of_total {f : J → C} (b : bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.X) :
  has_biproduct f :=
has_biproduct.mk
{ bicone := b,
  is_limit :=
  { lift := λ s, ∑ j, s.π.app j ≫ b.ι j,
    uniq' := λ s m h,
    begin
      erw [←category.comp_id m, ←total, comp_sum],
      apply finset.sum_congr rfl,
      intros j m,
      erw [reassoc_of (h j)],
    end,
    fac' := λ s j,
    begin
      simp only [sum_comp, category.assoc, bicone.to_cone_π_app, b.ι_π, comp_dite],
      -- See note [dsimp, simp].
      dsimp, simp,
    end },
  is_colimit :=
  { desc := λ s, ∑ j, b.π j ≫ s.ι.app j,
    uniq' := λ s m h,
    begin
      erw [←category.id_comp m, ←total, sum_comp],
            apply finset.sum_congr rfl,
      intros j m,
      erw [category.assoc, h],
    end,
    fac' := λ s j,
    begin
      simp only [comp_sum, ←category.assoc, bicone.to_cocone_ι_app, b.ι_π, dite_comp],
      dsimp, simp,
    end } }

/-- In a preadditive category, if the product over `f : J → C` exists,
    then the biproduct over `f` exists. -/
lemma has_biproduct.of_has_product (f : J → C) [has_product f] :
  has_biproduct f :=
has_biproduct_of_total
{ X := pi_obj f,
  π := limits.pi.π f,
  ι := λ j, pi.lift (λ j', if h : j = j' then eq_to_hom (congr_arg f h) else 0),
  ι_π := λ j j', by simp, }
(by { ext, simp [sum_comp, comp_dite] })

/-- In a preadditive category, if the coproduct over `f : J → C` exists,
    then the biproduct over `f` exists. -/
lemma has_biproduct.of_has_coproduct (f : J → C) [has_coproduct f] :
  has_biproduct f :=
has_biproduct_of_total
{ X := sigma_obj f,
  π := λ j, sigma.desc (λ j', if h : j' = j then eq_to_hom (congr_arg f h) else 0),
  ι := limits.sigma.ι f,
  ι_π := λ j j', by simp, }
begin
  ext,
  simp only [comp_sum, limits.colimit.ι_desc_assoc, eq_self_iff_true,
    limits.colimit.ι_desc, category.comp_id],
  dsimp,
  simp only [dite_comp, finset.sum_dite_eq, finset.mem_univ, if_true, category.id_comp,
    eq_to_hom_refl, zero_comp],
end

/-- A preadditive category with finite products has finite biproducts. -/
lemma has_finite_biproducts.of_has_finite_products [has_finite_products C] :
  has_finite_biproducts C :=
⟨λ J _ _, { has_biproduct := λ F, by exactI has_biproduct.of_has_product _ }⟩

/-- A preadditive category with finite coproducts has finite biproducts. -/
lemma has_finite_biproducts.of_has_finite_coproducts [has_finite_coproducts C] :
  has_finite_biproducts C :=
⟨λ J _ _, { has_biproduct := λ F, by exactI has_biproduct.of_has_coproduct _ }⟩

section
variables {f : J → C} [has_biproduct f]

/--
In any preadditive category, any biproduct satsifies
`∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`
-/
@[simp] lemma biproduct.total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) :=
begin
  ext j j',
  simp [comp_sum, sum_comp, biproduct.ι_π, comp_dite, dite_comp],
end

lemma biproduct.lift_eq {T : C} {g : Π j, T ⟶ f j} :
  biproduct.lift g = ∑ j, g j ≫ biproduct.ι f j :=
begin
  ext j,
  simp [sum_comp, biproduct.ι_π, comp_dite],
end

lemma biproduct.desc_eq {T : C} {g : Π j, f j ⟶ T} :
  biproduct.desc g = ∑ j, biproduct.π f j ≫ g j :=
begin
  ext j,
  simp [comp_sum, biproduct.ι_π_assoc, dite_comp],
end

@[simp, reassoc] lemma biproduct.lift_desc {T U : C} {g : Π j, T ⟶ f j} {h : Π j, f j ⟶ U} :
  biproduct.lift g ≫ biproduct.desc h = ∑ j : J, g j ≫ h j :=
by simp [biproduct.lift_eq, biproduct.desc_eq, comp_sum, sum_comp, biproduct.ι_π_assoc,
  comp_dite, dite_comp]

lemma biproduct.map_eq [has_finite_biproducts C] {f g : J → C} {h : Π j, f j ⟶ g j} :
  biproduct.map h = ∑ j : J, biproduct.π f j ≫ h j ≫ biproduct.ι g j :=
begin
  ext,
  simp [biproduct.ι_π, biproduct.ι_π_assoc, comp_sum, sum_comp, comp_dite, dite_comp],
end

end

/--
In a preadditive category, we can construct a binary biproduct for `X Y : C` from
any binary bicone `b` satisfying `total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X`.

(That is, such a bicone is a limit cone and a colimit cocone.)
-/
lemma has_binary_biproduct_of_total {X Y : C} (b : binary_bicone X Y)
  (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.X) :
  has_binary_biproduct X Y :=
has_binary_biproduct.mk
{ bicone := b,
  is_limit :=
  { lift := λ s, binary_fan.fst s ≫ b.inl +
      binary_fan.snd s ≫ b.inr,
    uniq' := λ s m h, by erw [←category.comp_id m, ←total,
      comp_add, reassoc_of (h walking_pair.left), reassoc_of (h walking_pair.right)],
    fac' := λ s j, by cases j; simp, },
  is_colimit :=
  { desc := λ s, b.fst ≫ binary_cofan.inl s +
      b.snd ≫ binary_cofan.inr s,
    uniq' := λ s m h, by erw [←category.id_comp m, ←total,
      add_comp, category.assoc, category.assoc, h walking_pair.left, h walking_pair.right],
    fac' := λ s j, by cases j; simp, } }

/-- In a preadditive category, if the product of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
lemma has_binary_biproduct.of_has_binary_product (X Y : C) [has_binary_product X Y] :
  has_binary_biproduct X Y :=
has_binary_biproduct_of_total
{ X := X ⨯ Y,
  fst := category_theory.limits.prod.fst,
  snd := category_theory.limits.prod.snd,
  inl := prod.lift (𝟙 X) 0,
  inr := prod.lift 0 (𝟙 Y) }
begin
  ext; simp [add_comp],
end

/-- In a preadditive category, if all binary products exist, then all binary biproducts exist. -/
lemma has_binary_biproducts.of_has_binary_products [has_binary_products C] :
  has_binary_biproducts C :=
{ has_binary_biproduct := λ X Y, has_binary_biproduct.of_has_binary_product X Y, }

/-- In a preadditive category, if the coproduct of `X` and `Y` exists, then the
    binary biproduct of `X` and `Y` exists. -/
lemma has_binary_biproduct.of_has_binary_coproduct (X Y : C) [has_binary_coproduct X Y] :
  has_binary_biproduct X Y :=
has_binary_biproduct_of_total
{ X := X ⨿ Y,
  fst := coprod.desc (𝟙 X) 0,
  snd := coprod.desc 0 (𝟙 Y),
  inl := category_theory.limits.coprod.inl,
  inr := category_theory.limits.coprod.inr }
begin
  ext; simp [add_comp],
end

/-- In a preadditive category, if all binary coproducts exist, then all binary biproducts exist. -/
lemma has_binary_biproducts.of_has_binary_coproducts [has_binary_coproducts C] :
  has_binary_biproducts C :=
{ has_binary_biproduct := λ X Y, has_binary_biproduct.of_has_binary_coproduct X Y, }

section
variables {X Y : C} [has_binary_biproduct X Y]

/--
In any preadditive category, any binary biproduct satsifies
`biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y)`.
-/
@[simp] lemma biprod.total : biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) :=
begin
  ext; simp [add_comp],
end

lemma biprod.lift_eq {T : C} {f : T ⟶ X} {g : T ⟶ Y} :
  biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr :=
begin
  ext; simp [add_comp],
end

lemma biprod.desc_eq {T : C} {f : X ⟶ T} {g : Y ⟶ T} :
  biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g :=
begin
  ext; simp [add_comp],
end

@[simp, reassoc] lemma biprod.lift_desc {T U : C} {f : T ⟶ X} {g : T ⟶ Y} {h : X ⟶ U} {i : Y ⟶ U} :
  biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i :=
by simp [biprod.lift_eq, biprod.desc_eq]


lemma biprod.map_eq [has_binary_biproducts C] {W X Y Z : C} {f : W ⟶ Y} {g : X ⟶ Z} :
  biprod.map f g = biprod.fst ≫ f ≫ biprod.inl + biprod.snd ≫ g ≫ biprod.inr :=
by apply biprod.hom_ext; apply biprod.hom_ext'; simp

end

end preadditive

end category_theory.limits
