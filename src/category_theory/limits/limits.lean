/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Scott Morrison, Floris van Doorn
-/
import category_theory.adjunction.basic
import category_theory.limits.cones

/-!
# Limits and colimits

We set up the general theory of limits and colimits in a category.
In this introduction we only describe the setup for limits;
it is repeated, with slightly different names, for colimits.

The three main structures involved are
* `is_limit c`, for `c : cone F`, `F : J ⥤ C`, expressing that `c` is a limit cone,
* `limit_cone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `has_limit F`, asserting the mere existence of some limit cone for `F`.

`has_limit` is a propositional typeclass
(it's important that it is a proposition merely asserting the existence of a limit,
as otherwise we would have non-defeq problems from incompatible instances).


Typically there are two different ways one can use the limits library:
1. working with particular cones, and terms of type `is_limit`
2. working solely with `has_limit`.

While `has_limit` only asserts the existence of a limit cone,
we happily use the axiom of choice in mathlib,
so there are convenience functions all depending on `has_limit F`:
* `limit F : C`, producing some limit object (of course all such are isomorphic)
* `limit.π F j : limit F ⟶ F.obj j`, the morphisms out of the limit,
* `limit.lift F c : c.X ⟶ limit F`, the universal morphism from any other `c : cone F`, etc.

Key to using the `has_limit` interface is that there is an `@[ext]` lemma stating that
to check `f = g`, for `f g : Z ⟶ limit F`, it suffices to check `f ≫ limit.π F j = g ≫ limit.π F j`
for every `j`.
This, combined with `@[simp]` lemmas, makes it possible to prove many easy facts about limits using
automation (e.g. `tidy`).

There are abbreviations `has_limits_of_shape J C` and `has_limits C`
asserting the existence of classes of limits.
Later more are introduced, for finite limits, special shapes of limits, etc.

Ideally, many results about limits should be stated first in terms of `is_limit`,
and then a result in terms of `has_limit` derived from this.
At this point, however, this is far from uniformly achieved in mathlib ---
often statements are only written in terms of `has_limit`.

## Implementation
At present we simply say everything twice, in order to handle both limits and colimits.
It would be highly desirable to have some automation support,
e.g. a `@[dualize]` attribute that behaves similarly to `@[to_additive]`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/

noncomputable theory

open category_theory category_theory.category category_theory.functor opposite

namespace category_theory.limits

universes v u u' u'' w -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {J K : Type v} [small_category J] [small_category K]
variables {C : Type u} [category.{v} C]

variables {F : J ⥤ C}

/--
A cone `t` on `F` is a limit cone if each cone on `F` admits a unique
cone morphism to `t`.

See https://stacks.math.columbia.edu/tag/002E.
  -/
@[nolint has_inhabited_instance]
structure is_limit (t : cone F) :=
(lift  : Π (s : cone F), s.X ⟶ t.X)
(fac'  : ∀ (s : cone F) (j : J), lift s ≫ t.π.app j = s.π.app j . obviously)
(uniq' : ∀ (s : cone F) (m : s.X ⟶ t.X) (w : ∀ j : J, m ≫ t.π.app j = s.π.app j),
  m = lift s . obviously)

restate_axiom is_limit.fac'
attribute [simp, reassoc] is_limit.fac
restate_axiom is_limit.uniq'

namespace is_limit

instance subsingleton {t : cone F} : subsingleton (is_limit t) :=
⟨by intros P Q; cases P; cases Q; congr; ext; solve_by_elim⟩

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cone point
of any cone over `F` to the cone point of a limit cone over `G`. -/
def map {F G : J ⥤ C} (s : cone F) {t : cone G} (P : is_limit t)
  (α : F ⟶ G) : s.X ⟶ t.X :=
P.lift ((cones.postcompose α).obj s)

@[simp, reassoc] lemma map_π {F G : J ⥤ C} (c : cone F) {d : cone G} (hd : is_limit d)
  (α : F ⟶ G) (j : J) : hd.map c α ≫ d.π.app j = c.π.app j ≫ α.app j :=
fac _ _ _

lemma lift_self {c : cone F} (t : is_limit c) : t.lift c = 𝟙 c.X :=
(t.uniq _ _ (λ j, id_comp _)).symm

/- Repackaging the definition in terms of cone morphisms. -/

/-- The universal morphism from any other cone to a limit cone. -/
@[simps]
def lift_cone_morphism {t : cone F} (h : is_limit t) (s : cone F) : s ⟶ t :=
{ hom := h.lift s }

lemma uniq_cone_morphism {s t : cone F} (h : is_limit t) {f f' : s ⟶ t} :
  f = f' :=
have ∀ {g : s ⟶ t}, g = h.lift_cone_morphism s, by intro g; ext; exact h.uniq _ _ g.w,
this.trans this.symm

/--
Alternative constructor for `is_limit`,
providing a morphism of cones rather than a morphism between the cone points
and separately the factorisation condition.
-/
@[simps]
def mk_cone_morphism {t : cone F}
  (lift : Π (s : cone F), s ⟶ t)
  (uniq' : ∀ (s : cone F) (m : s ⟶ t), m = lift s) : is_limit t :=
{ lift := λ s, (lift s).hom,
  uniq' := λ s m w,
    have cone_morphism.mk m w = lift s, by apply uniq',
    congr_arg cone_morphism.hom this }

/-- Limit cones on `F` are unique up to isomorphism. -/
@[simps]
def unique_up_to_iso {s t : cone F} (P : is_limit s) (Q : is_limit t) : s ≅ t :=
{ hom := Q.lift_cone_morphism s,
  inv := P.lift_cone_morphism t,
  hom_inv_id' := P.uniq_cone_morphism,
  inv_hom_id' := Q.uniq_cone_morphism }

/-- Any cone morphism between limit cones is an isomorphism. -/
def hom_is_iso {s t : cone F} (P : is_limit s) (Q : is_limit t) (f : s ⟶ t) : is_iso f :=
{ inv := P.lift_cone_morphism t,
  hom_inv_id' := P.uniq_cone_morphism,
  inv_hom_id' := Q.uniq_cone_morphism, }

/-- Limits of `F` are unique up to isomorphism. -/
def cone_point_unique_up_to_iso {s t : cone F} (P : is_limit s) (Q : is_limit t) : s.X ≅ t.X :=
(cones.forget F).map_iso (unique_up_to_iso P Q)

@[simp, reassoc] lemma cone_point_unique_up_to_iso_hom_comp {s t : cone F} (P : is_limit s)
  (Q : is_limit t) (j : J) : (cone_point_unique_up_to_iso P Q).hom ≫ t.π.app j = s.π.app j :=
(unique_up_to_iso P Q).hom.w _

@[simp, reassoc] lemma cone_point_unique_up_to_iso_inv_comp {s t : cone F} (P : is_limit s)
  (Q : is_limit t) (j : J) : (cone_point_unique_up_to_iso P Q).inv ≫ s.π.app j = t.π.app j :=
(unique_up_to_iso P Q).inv.w _

@[simp, reassoc] lemma lift_comp_cone_point_unique_up_to_iso_hom {r s t : cone F}
  (P : is_limit s) (Q : is_limit t) :
  P.lift r ≫ (cone_point_unique_up_to_iso P Q).hom = Q.lift r :=
Q.uniq _ _ (by simp)

@[simp, reassoc] lemma lift_comp_cone_point_unique_up_to_iso_inv {r s t : cone F}
  (P : is_limit s) (Q : is_limit t) :
  Q.lift r ≫ (cone_point_unique_up_to_iso P Q).inv = P.lift r :=
P.uniq _ _ (by simp)

/-- Transport evidence that a cone is a limit cone across an isomorphism of cones. -/
def of_iso_limit {r t : cone F} (P : is_limit r) (i : r ≅ t) : is_limit t :=
is_limit.mk_cone_morphism
  (λ s, P.lift_cone_morphism s ≫ i.hom)
  (λ s m, by rw ←i.comp_inv_eq; apply P.uniq_cone_morphism)

@[simp] lemma of_iso_limit_lift {r t : cone F} (P : is_limit r) (i : r ≅ t) (s) :
  (P.of_iso_limit i).lift s = P.lift s ≫ i.hom.hom :=
rfl

/-- Isomorphism of cones preserves whether or not they are limiting cones. -/
def equiv_iso_limit {r t : cone F} (i : r ≅ t) : is_limit r ≃ is_limit t :=
{ to_fun := λ h, h.of_iso_limit i,
  inv_fun := λ h, h.of_iso_limit i.symm,
  left_inv := by tidy,
  right_inv := by tidy }

@[simp] lemma equiv_iso_limit_apply {r t : cone F} (i : r ≅ t) (P : is_limit r) :
  equiv_iso_limit i P = P.of_iso_limit i := rfl

@[simp] lemma equiv_iso_limit_symm_apply {r t : cone F} (i : r ≅ t) (P : is_limit t) :
  (equiv_iso_limit i).symm P = P.of_iso_limit i.symm := rfl

/--
If the canonical morphism from a cone point to a limiting cone point is an iso, then the
first cone was limiting also.
-/
def of_point_iso {r t : cone F} (P : is_limit r) [i : is_iso (P.lift t)] : is_limit t :=
of_iso_limit P
begin
  haveI : is_iso (P.lift_cone_morphism t).hom := i,
  haveI : is_iso (P.lift_cone_morphism t) := cones.cone_iso_of_hom_iso _,
  symmetry,
  apply as_iso (P.lift_cone_morphism t),
end

variables {t : cone F}

lemma hom_lift (h : is_limit t) {W : C} (m : W ⟶ t.X) :
  m = h.lift { X := W, π := { app := λ b, m ≫ t.π.app b } } :=
h.uniq { X := W, π := { app := λ b, m ≫ t.π.app b } } m (λ b, rfl)

/-- Two morphisms into a limit are equal if their compositions with
  each cone morphism are equal. -/
lemma hom_ext (h : is_limit t) {W : C} {f f' : W ⟶ t.X}
  (w : ∀ j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f' :=
by rw [h.hom_lift f, h.hom_lift f']; congr; exact funext w

/--
Given a right adjoint functor between categories of cones,
the image of a limit cone is a limit cone.
-/
def of_right_adjoint {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cone G ⥤ cone F) [is_right_adjoint h] {c : cone G} (t : is_limit c) :
  is_limit (h.obj c) :=
mk_cone_morphism
  (λ s, (adjunction.of_right_adjoint h).hom_equiv s c (t.lift_cone_morphism _))
  (λ s m, (adjunction.eq_hom_equiv_apply _ _ _).2 t.uniq_cone_morphism)

/--
Given two functors which have equivalent categories of cones, we can transport a limiting cone across
the equivalence.
-/
def of_cone_equiv {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cone G ≌ cone F) {c : cone G} :
  is_limit (h.functor.obj c) ≃ is_limit c :=
{ to_fun := λ P, of_iso_limit (of_right_adjoint h.inverse P) (h.unit_iso.symm.app c),
  inv_fun := of_right_adjoint h.functor,
  left_inv := by tidy,
  right_inv := by tidy, }

@[simp] lemma of_cone_equiv_apply_desc {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cone G ≌ cone F) {c : cone G} (P : is_limit (h.functor.obj c)) (s) :
  (of_cone_equiv h P).lift s =
    ((h.unit_iso.hom.app s).hom ≫
      (h.functor.inv.map (P.lift_cone_morphism (h.functor.obj s))).hom) ≫
      (h.unit_iso.inv.app c).hom :=
rfl

@[simp] lemma of_cone_equiv_symm_apply_desc {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cone G ≌ cone F) {c : cone G} (P : is_limit c) (s) :
  ((of_cone_equiv h).symm P).lift s =
    (h.counit_iso.inv.app s).hom ≫ (h.functor.map (P.lift_cone_morphism (h.inverse.obj s))).hom :=
rfl

/--
A cone postcomposed with a natural isomorphism is a limit cone if and only if the original cone is.
-/
def postcompose_hom_equiv {F G : J ⥤ C} (α : F ≅ G) (c : cone F) :
  is_limit ((cones.postcompose α.hom).obj c) ≃ is_limit c :=
of_cone_equiv (cones.postcompose_equivalence α)

/--
A cone postcomposed with the inverse of a natural isomorphism is a limit cone if and only if
the original cone is.
-/
def postcompose_inv_equiv {F G : J ⥤ C} (α : F ≅ G) (c : cone G) :
  is_limit ((cones.postcompose α.inv).obj c) ≃ is_limit c :=
postcompose_hom_equiv α.symm c

/--
The cone points of two limit cones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simps]
def cone_points_iso_of_nat_iso {F G : J ⥤ C} {s : cone F} {t : cone G}
  (P : is_limit s) (Q : is_limit t) (w : F ≅ G) : s.X ≅ t.X :=
{ hom := Q.map s w.hom,
  inv := P.map t w.inv,
  hom_inv_id' := P.hom_ext (by tidy),
  inv_hom_id' := Q.hom_ext (by tidy), }

@[reassoc]
lemma cone_points_iso_of_nat_iso_hom_comp {F G : J ⥤ C} {s : cone F} {t : cone G}
  (P : is_limit s) (Q : is_limit t) (w : F ≅ G) (j : J) :
  (cone_points_iso_of_nat_iso P Q w).hom ≫ t.π.app j = s.π.app j ≫ w.hom.app j :=
by simp

@[reassoc]
lemma cone_points_iso_of_nat_iso_inv_comp {F G : J ⥤ C} {s : cone F} {t : cone G}
  (P : is_limit s) (Q : is_limit t) (w : F ≅ G) (j : J) :
  (cone_points_iso_of_nat_iso P Q w).inv ≫ s.π.app j = t.π.app j ≫ w.inv.app j :=
by simp

@[reassoc]
lemma lift_comp_cone_points_iso_of_nat_iso_hom {F G : J ⥤ C} {r s : cone F} {t : cone G}
  (P : is_limit s) (Q : is_limit t) (w : F ≅ G) :
  P.lift r ≫ (cone_points_iso_of_nat_iso P Q w).hom = Q.map r w.hom :=
Q.hom_ext (by simp)

section equivalence
open category_theory.equivalence

/--
If `s : cone F` is a limit cone, so is `s` whiskered by an equivalence `e`.
-/
def whisker_equivalence {s : cone F} (P : is_limit s) (e : K ≌ J) :
  is_limit (s.whisker e.functor) :=
of_right_adjoint (cones.whiskering_equivalence e).functor P

/--
We can prove two cone points `(s : cone F).X` and `(t.cone F).X` are isomorphic if
* both cones are limit cones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simps]
def cone_points_iso_of_equivalence {F : J ⥤ C} {s : cone F} {G : K ⥤ C} {t : cone G}
  (P : is_limit s) (Q : is_limit t) (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : s.X ≅ t.X :=
let w' : e.inverse ⋙ F ≅ G := (iso_whisker_left e.inverse w).symm ≪≫ inv_fun_id_assoc e G in
{ hom := Q.lift ((cones.equivalence_of_reindexing e.symm w').functor.obj s),
  inv := P.lift ((cones.equivalence_of_reindexing e w).functor.obj t),
  hom_inv_id' :=
  begin
    apply hom_ext P, intros j,
    dsimp,
    simp only [limits.cone.whisker_π, limits.cones.postcompose_obj_π, fac, whisker_left_app,
      assoc, id_comp, inv_fun_id_assoc_hom_app, fac_assoc, nat_trans.comp_app],
    rw [counit_app_functor, ←functor.comp_map, w.hom.naturality],
    simp,
  end,
  inv_hom_id' := by { apply hom_ext Q, tidy, }, }

end equivalence

/-- The universal property of a limit cone: a map `W ⟶ X` is the same as
  a cone on `F` with vertex `W`. -/
def hom_iso (h : is_limit t) (W : C) : (W ⟶ t.X) ≅ ((const J).obj W ⟶ F) :=
{ hom := λ f, (t.extend f).π,
  inv := λ π, h.lift { X := W, π := π },
  hom_inv_id' := by ext f; apply h.hom_ext; intro j; simp; dsimp; refl }

@[simp] lemma hom_iso_hom (h : is_limit t) {W : C} (f : W ⟶ t.X) :
  (is_limit.hom_iso h W).hom f = (t.extend f).π := rfl

/-- The limit of `F` represents the functor taking `W` to
  the set of cones on `F` with vertex `W`. -/
def nat_iso (h : is_limit t) : yoneda.obj t.X ≅ F.cones :=
nat_iso.of_components (λ W, is_limit.hom_iso h (unop W)) (by tidy).

/--
Another, more explicit, formulation of the universal property of a limit cone.
See also `hom_iso`.
-/
def hom_iso' (h : is_limit t) (W : C) :
  ((W ⟶ t.X) : Type v) ≅ { p : Π j, W ⟶ F.obj j // ∀ {j j'} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
h.hom_iso W ≪≫
{ hom := λ π,
  ⟨λ j, π.app j, λ j j' f,
   by convert ←(π.naturality f).symm; apply id_comp⟩,
  inv := λ p,
  { app := λ j, p.1 j,
    naturality' := λ j j' f, begin dsimp, rw [id_comp], exact (p.2 f).symm end } }

/-- If G : C → D is a faithful functor which sends t to a limit cone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def of_faithful {t : cone F} {D : Type u'} [category.{v} D] (G : C ⥤ D) [faithful G]
  (ht : is_limit (G.map_cone t)) (lift : Π (s : cone F), s.X ⟶ t.X)
  (h : ∀ s, G.map (lift s) = ht.lift (G.map_cone s)) : is_limit t :=
{ lift := lift,
  fac' := λ s j, by apply G.map_injective; rw [G.map_comp, h]; apply ht.fac,
  uniq' := λ s m w, begin
    apply G.map_injective, rw h,
    refine ht.uniq (G.map_cone s) _ (λ j, _),
    convert ←congr_arg (λ f, G.map f) (w j),
    apply G.map_comp
  end }

/--
If `F` and `G` are naturally isomorphic, then `F.map_cone c` being a limit implies
`G.map_cone c` is also a limit.
-/
def map_cone_equiv {D : Type u'} [category.{v} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G) {c : cone K}
  (t : is_limit (F.map_cone c)) : is_limit (G.map_cone c) :=
begin
  apply postcompose_inv_equiv (iso_whisker_left K h : _) (G.map_cone c) _,
  apply t.of_iso_limit (postcompose_whisker_left_map_cone h.symm c).symm,
end

/--
A cone is a limit cone exactly if
there is a unique cone morphism from any other cone.
-/
def iso_unique_cone_morphism {t : cone F} :
  is_limit t ≅ Π s, unique (s ⟶ t) :=
{ hom := λ h s,
  { default := h.lift_cone_morphism s,
    uniq := λ _, h.uniq_cone_morphism },
  inv := λ h,
  { lift := λ s, (h s).default.hom,
    uniq' := λ s f w, congr_arg cone_morphism.hom ((h s).uniq ⟨f, w⟩) } }

namespace of_nat_iso
variables {X : C} (h : yoneda.obj X ≅ F.cones)

/-- If `F.cones` is represented by `X`, each morphism `f : Y ⟶ X` gives a cone with cone point `Y`. -/
def cone_of_hom {Y : C} (f : Y ⟶ X) : cone F :=
{ X := Y, π := h.hom.app (op Y) f }

/-- If `F.cones` is represented by `X`, each cone `s` gives a morphism `s.X ⟶ X`. -/
def hom_of_cone (s : cone F) : s.X ⟶ X := h.inv.app (op s.X) s.π

@[simp] lemma cone_of_hom_of_cone (s : cone F) : cone_of_hom h (hom_of_cone h s) = s :=
begin
  dsimp [cone_of_hom, hom_of_cone], cases s, congr, dsimp,
  exact congr_fun (congr_fun (congr_arg nat_trans.app h.inv_hom_id) (op s_X)) s_π,
end

@[simp] lemma hom_of_cone_of_hom {Y : C} (f : Y ⟶ X) : hom_of_cone h (cone_of_hom h f) = f :=
congr_fun (congr_fun (congr_arg nat_trans.app h.hom_inv_id) (op Y)) f

/-- If `F.cones` is represented by `X`, the cone corresponding to the identity morphism on `X`
will be a limit cone. -/
def limit_cone : cone F :=
cone_of_hom h (𝟙 X)

/-- If `F.cones` is represented by `X`, the cone corresponding to a morphism `f : Y ⟶ X` is
the limit cone extended by `f`. -/
lemma cone_of_hom_fac {Y : C} (f : Y ⟶ X) :
cone_of_hom h f = (limit_cone h).extend f :=
begin
  dsimp [cone_of_hom, limit_cone, cone.extend],
  congr' with j,
  have t := congr_fun (h.hom.naturality f.op) (𝟙 X),
  dsimp at t,
  simp only [comp_id] at t,
  rw congr_fun (congr_arg nat_trans.app t) j,
  refl,
end

/-- If `F.cones` is represented by `X`, any cone is the extension of the limit cone by the
corresponding morphism. -/
lemma cone_fac (s : cone F) : (limit_cone h).extend (hom_of_cone h s) = s :=
begin
  rw ←cone_of_hom_of_cone h s,
  conv_lhs { simp only [hom_of_cone_of_hom] },
  apply (cone_of_hom_fac _ _).symm,
end

end of_nat_iso

section
open of_nat_iso

/--
If `F.cones` is representable, then the cone corresponding to the identity morphism on
the representing object is a limit cone.
-/
def of_nat_iso {X : C} (h : yoneda.obj X ≅ F.cones) :
  is_limit (limit_cone h) :=
{ lift := λ s, hom_of_cone h s,
  fac' := λ s j,
  begin
    have h := cone_fac h s,
    cases s,
    injection h with h₁ h₂,
    simp only [heq_iff_eq] at h₂,
    conv_rhs { rw ← h₂ }, refl,
  end,
  uniq' := λ s m w,
  begin
    rw ←hom_of_cone_of_hom h m,
    congr,
    rw cone_of_hom_fac,
    dsimp, cases s, congr' with j, exact w j,
  end }
end

end is_limit

/--
A cocone `t` on `F` is a colimit cocone if each cocone on `F` admits a unique
cocone morphism from `t`.

See https://stacks.math.columbia.edu/tag/002F.
-/
@[nolint has_inhabited_instance]
structure is_colimit (t : cocone F) :=
(desc  : Π (s : cocone F), t.X ⟶ s.X)
(fac'  : ∀ (s : cocone F) (j : J), t.ι.app j ≫ desc s = s.ι.app j . obviously)
(uniq' : ∀ (s : cocone F) (m : t.X ⟶ s.X) (w : ∀ j : J, t.ι.app j ≫ m = s.ι.app j),
  m = desc s . obviously)

restate_axiom is_colimit.fac'
attribute [simp,reassoc] is_colimit.fac
restate_axiom is_colimit.uniq'

namespace is_colimit

instance subsingleton {t : cocone F} : subsingleton (is_colimit t) :=
⟨by intros P Q; cases P; cases Q; congr; ext; solve_by_elim⟩

/-- Given a natural transformation `α : F ⟶ G`, we give a morphism from the cocone point
of a colimit cocone over `F` to the cocone point of any cocone over `G`. -/
def map {F G : J ⥤ C} {s : cocone F} (P : is_colimit s) (t : cocone G)
  (α : F ⟶ G) : s.X ⟶ t.X :=
P.desc ((cocones.precompose α).obj t)

@[simp, reassoc]
lemma ι_map {F G : J ⥤ C} {c : cocone F} (hc : is_colimit c) (d : cocone G) (α : F ⟶ G)
  (j : J) : c.ι.app j ≫ is_colimit.map hc d α = α.app j ≫ d.ι.app j :=
fac _ _ _

@[simp]
lemma desc_self {t : cocone F} (h : is_colimit t) : h.desc t = 𝟙 t.X :=
(h.uniq _ _ (λ j, comp_id _)).symm

/- Repackaging the definition in terms of cocone morphisms. -/

/-- The universal morphism from a colimit cocone to any other cocone. -/
@[simps]
def desc_cocone_morphism {t : cocone F} (h : is_colimit t) (s : cocone F) : t ⟶ s :=
{ hom := h.desc s }

lemma uniq_cocone_morphism {s t : cocone F} (h : is_colimit t) {f f' : t ⟶ s} :
  f = f' :=
have ∀ {g : t ⟶ s}, g = h.desc_cocone_morphism s, by intro g; ext; exact h.uniq _ _ g.w,
this.trans this.symm

/--
Alternative constructor for `is_colimit`,
providing a morphism of cocones rather than a morphism between the cocone points
and separately the factorisation condition.
-/
@[simps]
def mk_cocone_morphism {t : cocone F}
  (desc : Π (s : cocone F), t ⟶ s)
  (uniq' : ∀ (s : cocone F) (m : t ⟶ s), m = desc s) : is_colimit t :=
{ desc := λ s, (desc s).hom,
  uniq' := λ s m w,
    have cocone_morphism.mk m w = desc s, by apply uniq',
    congr_arg cocone_morphism.hom this }

/-- Colimit cocones on `F` are unique up to isomorphism. -/
@[simps]
def unique_up_to_iso {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) : s ≅ t :=
{ hom := P.desc_cocone_morphism t,
  inv := Q.desc_cocone_morphism s,
  hom_inv_id' := P.uniq_cocone_morphism,
  inv_hom_id' := Q.uniq_cocone_morphism }

/-- Any cocone morphism between colimit cocones is an isomorphism. -/
def hom_is_iso {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) (f : s ⟶ t) : is_iso f :=
{ inv := Q.desc_cocone_morphism s,
  hom_inv_id' := P.uniq_cocone_morphism,
  inv_hom_id' := Q.uniq_cocone_morphism, }

/-- Colimits of `F` are unique up to isomorphism. -/
def cocone_point_unique_up_to_iso {s t : cocone F} (P : is_colimit s) (Q : is_colimit t) : s.X ≅ t.X :=
(cocones.forget F).map_iso (unique_up_to_iso P Q)

@[simp, reassoc] lemma comp_cocone_point_unique_up_to_iso_hom {s t : cocone F} (P : is_colimit s)
  (Q : is_colimit t) (j : J) : s.ι.app j ≫ (cocone_point_unique_up_to_iso P Q).hom = t.ι.app j :=
(unique_up_to_iso P Q).hom.w _

@[simp, reassoc] lemma comp_cocone_point_unique_up_to_iso_inv {s t : cocone F} (P : is_colimit s)
  (Q : is_colimit t) (j : J) : t.ι.app j ≫ (cocone_point_unique_up_to_iso P Q).inv = s.ι.app j :=
(unique_up_to_iso P Q).inv.w _

@[simp, reassoc] lemma cocone_point_unique_up_to_iso_hom_desc {r s t : cocone F} (P : is_colimit s)
  (Q : is_colimit t) : (cocone_point_unique_up_to_iso P Q).hom ≫ Q.desc r = P.desc r :=
P.uniq _ _ (by simp)

@[simp, reassoc] lemma cocone_point_unique_up_to_iso_inv_desc {r s t : cocone F} (P : is_colimit s)
  (Q : is_colimit t) : (cocone_point_unique_up_to_iso P Q).inv ≫ P.desc r = Q.desc r :=
Q.uniq _ _ (by simp)

/-- Transport evidence that a cocone is a colimit cocone across an isomorphism of cocones. -/
def of_iso_colimit {r t : cocone F} (P : is_colimit r) (i : r ≅ t) : is_colimit t :=
is_colimit.mk_cocone_morphism
  (λ s, i.inv ≫ P.desc_cocone_morphism s)
  (λ s m, by rw i.eq_inv_comp; apply P.uniq_cocone_morphism)

@[simp] lemma of_iso_colimit_desc {r t : cocone F} (P : is_colimit r) (i : r ≅ t) (s) :
  (P.of_iso_colimit i).desc s = i.inv.hom ≫ P.desc s :=
rfl

/-- Isomorphism of cocones preserves whether or not they are colimiting cocones. -/
def equiv_iso_colimit {r t : cocone F} (i : r ≅ t) : is_colimit r ≃ is_colimit t :=
{ to_fun := λ h, h.of_iso_colimit i,
  inv_fun := λ h, h.of_iso_colimit i.symm,
  left_inv := by tidy,
  right_inv := by tidy }

@[simp] lemma equiv_iso_colimit_apply {r t : cocone F} (i : r ≅ t) (P : is_colimit r) :
  equiv_iso_colimit i P = P.of_iso_colimit i := rfl

@[simp] lemma equiv_iso_colimit_symm_apply {r t : cocone F} (i : r ≅ t) (P : is_colimit t) :
  (equiv_iso_colimit i).symm P = P.of_iso_colimit i.symm := rfl

/--
If the canonical morphism to a cocone point from a colimiting cocone point is an iso, then the
first cocone was colimiting also.
-/
def of_point_iso {r t : cocone F} (P : is_colimit r) [i : is_iso (P.desc t)] : is_colimit t :=
of_iso_colimit P
begin
  haveI : is_iso (P.desc_cocone_morphism t).hom := i,
  haveI : is_iso (P.desc_cocone_morphism t) := cocones.cocone_iso_of_hom_iso _,
  apply as_iso (P.desc_cocone_morphism t),
end

variables {t : cocone F}

lemma hom_desc (h : is_colimit t) {W : C} (m : t.X ⟶ W) :
  m = h.desc { X := W, ι := { app := λ b, t.ι.app b ≫ m,
    naturality' := by intros; erw [←assoc, t.ι.naturality, comp_id, comp_id] } } :=
h.uniq { X := W, ι := { app := λ b, t.ι.app b ≫ m, naturality' := _ } } m (λ b, rfl)

/-- Two morphisms out of a colimit are equal if their compositions with
  each cocone morphism are equal. -/
lemma hom_ext (h : is_colimit t) {W : C} {f f' : t.X ⟶ W}
  (w : ∀ j, t.ι.app j ≫ f = t.ι.app j ≫ f') : f = f' :=
by rw [h.hom_desc f, h.hom_desc f']; congr; exact funext w

/--
Given a left adjoint functor between categories of cocones,
the image of a colimit cocone is a colimit cocone.
-/
def of_left_adjoint {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cocone G ⥤ cocone F) [is_left_adjoint h] {c : cocone G} (t : is_colimit c) :
  is_colimit (h.obj c) :=
mk_cocone_morphism
  (λ s, ((adjunction.of_left_adjoint h).hom_equiv c s).symm (t.desc_cocone_morphism _))
  (λ s m, (adjunction.hom_equiv_apply_eq _ _ _).1 t.uniq_cocone_morphism)

/--
Given two functors which have equivalent categories of cocones,
we can transport a colimiting cocone across the equivalence.
-/
def of_cocone_equiv {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cocone G ≌ cocone F) {c : cocone G} :
  is_colimit (h.functor.obj c) ≃ is_colimit c :=
{ to_fun := λ P, of_iso_colimit (of_left_adjoint h.inverse P) (h.unit_iso.symm.app c),
  inv_fun := of_left_adjoint h.functor,
  left_inv := by tidy,
  right_inv := by tidy, }

@[simp] lemma of_cocone_equiv_apply_desc {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cocone G ≌ cocone F) {c : cocone G} (P : is_colimit (h.functor.obj c)) (s) :
  (of_cocone_equiv h P).desc s =
    (h.unit.app c).hom ≫
    (h.inverse.map (P.desc_cocone_morphism (h.functor.obj s))).hom ≫
    (h.unit_inv.app s).hom :=
rfl

@[simp] lemma of_cocone_equiv_symm_apply_desc {D : Type u'} [category.{v} D] {G : K ⥤ D}
  (h : cocone G ≌ cocone F) {c : cocone G} (P : is_colimit c) (s) :
  ((of_cocone_equiv h).symm P).desc s =
    (h.functor.map (P.desc_cocone_morphism (h.inverse.obj s))).hom ≫ (h.counit.app s).hom :=
rfl

/--
A cocone precomposed with a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/
def precompose_hom_equiv {F G : J ⥤ C} (α : F ≅ G) (c : cocone G) :
  is_colimit ((cocones.precompose α.hom).obj c) ≃ is_colimit c :=
of_cocone_equiv (cocones.precompose_equivalence α)

/--
A cocone precomposed with the inverse of a natural isomorphism is a colimit cocone
if and only if the original cocone is.
-/
def precompose_inv_equiv {F G : J ⥤ C} (α : F ≅ G) (c : cocone F) :
  is_colimit ((cocones.precompose α.inv).obj c) ≃ is_colimit c :=
precompose_hom_equiv α.symm c

/--
The cocone points of two colimit cocones for naturally isomorphic functors
are themselves isomorphic.
-/
@[simps]
def cocone_points_iso_of_nat_iso {F G : J ⥤ C} {s : cocone F} {t : cocone G}
  (P : is_colimit s) (Q : is_colimit t) (w : F ≅ G) : s.X ≅ t.X :=
{ hom := P.map t w.hom,
  inv := Q.map s w.inv,
  hom_inv_id' := P.hom_ext (by tidy),
  inv_hom_id' := Q.hom_ext (by tidy) }

@[reassoc]
lemma comp_cocone_points_iso_of_nat_iso_hom {F G : J ⥤ C} {s : cocone F} {t : cocone G}
  (P : is_colimit s) (Q : is_colimit t) (w : F ≅ G) (j : J) :
  s.ι.app j ≫ (cocone_points_iso_of_nat_iso P Q w).hom = w.hom.app j ≫ t.ι.app j :=
by simp

@[reassoc]
lemma comp_cocone_points_iso_of_nat_iso_inv {F G : J ⥤ C} {s : cocone F} {t : cocone G}
  (P : is_colimit s) (Q : is_colimit t) (w : F ≅ G) (j : J) :
  t.ι.app j ≫ (cocone_points_iso_of_nat_iso P Q w).inv = w.inv.app j ≫ s.ι.app j :=
by simp

@[reassoc]
lemma cocone_points_iso_of_nat_iso_hom_desc {F G : J ⥤ C} {s : cocone F} {r t : cocone G}
  (P : is_colimit s) (Q : is_colimit t) (w : F ≅ G) :
  (cocone_points_iso_of_nat_iso P Q w).hom ≫ Q.desc r = P.map _ w.hom :=
P.hom_ext (by simp)

section equivalence
open category_theory.equivalence

/--
If `s : cone F` is a limit cone, so is `s` whiskered by an equivalence `e`.
-/
def whisker_equivalence {s : cocone F} (P : is_colimit s) (e : K ≌ J) :
  is_colimit (s.whisker e.functor) :=
of_left_adjoint (cocones.whiskering_equivalence e).functor P

/--
We can prove two cocone points `(s : cocone F).X` and `(t.cocone F).X` are isomorphic if
* both cocones are colimit ccoones
* their indexing categories are equivalent via some `e : J ≌ K`,
* the triangle of functors commutes up to a natural isomorphism: `e.functor ⋙ G ≅ F`.

This is the most general form of uniqueness of cocone points,
allowing relabelling of both the indexing category (up to equivalence)
and the functor (up to natural isomorphism).
-/
@[simps]
def cocone_points_iso_of_equivalence {F : J ⥤ C} {s : cocone F} {G : K ⥤ C} {t : cocone G}
  (P : is_colimit s) (Q : is_colimit t) (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : s.X ≅ t.X :=
let w' : e.inverse ⋙ F ≅ G := (iso_whisker_left e.inverse w).symm ≪≫ inv_fun_id_assoc e G in
{ hom := P.desc ((cocones.equivalence_of_reindexing e w).functor.obj t),
  inv := Q.desc ((cocones.equivalence_of_reindexing e.symm w').functor.obj s),
  hom_inv_id' :=
  begin
    apply hom_ext P, intros j,
    dsimp,
    simp only [limits.cocone.whisker_ι, fac, inv_fun_id_assoc_inv_app, whisker_left_app, assoc,
      comp_id, limits.cocones.precompose_obj_ι, fac_assoc, nat_trans.comp_app],
    rw [counit_inv_app_functor, ←functor.comp_map, ←w.inv.naturality_assoc],
    dsimp,
    simp,
  end,
  inv_hom_id' := by { apply hom_ext Q, tidy, }, }

end equivalence

/-- The universal property of a colimit cocone: a map `X ⟶ W` is the same as
  a cocone on `F` with vertex `W`. -/
def hom_iso (h : is_colimit t) (W : C) : (t.X ⟶ W) ≅ (F ⟶ (const J).obj W) :=
{ hom := λ f, (t.extend f).ι,
  inv := λ ι, h.desc { X := W, ι := ι },
  hom_inv_id' := by ext f; apply h.hom_ext; intro j; simp; dsimp; refl }

@[simp] lemma hom_iso_hom (h : is_colimit t) {W : C} (f : t.X ⟶ W) :
  (is_colimit.hom_iso h W).hom f = (t.extend f).ι := rfl

/-- The colimit of `F` represents the functor taking `W` to
  the set of cocones on `F` with vertex `W`. -/
def nat_iso (h : is_colimit t) : coyoneda.obj (op t.X) ≅ F.cocones :=
nat_iso.of_components (is_colimit.hom_iso h) (by intros; ext; dsimp; rw ←assoc; refl)

/--
Another, more explicit, formulation of the universal property of a colimit cocone.
See also `hom_iso`.
-/
def hom_iso' (h : is_colimit t) (W : C) :
  ((t.X ⟶ W) : Type v) ≅ { p : Π j, F.obj j ⟶ W // ∀ {j j' : J} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
h.hom_iso W ≪≫
{ hom := λ ι,
  ⟨λ j, ι.app j, λ j j' f,
   by convert ←(ι.naturality f); apply comp_id⟩,
  inv := λ p,
  { app := λ j, p.1 j,
    naturality' := λ j j' f, begin dsimp, rw [comp_id], exact (p.2 f) end } }

/-- If G : C → D is a faithful functor which sends t to a colimit cocone,
  then it suffices to check that the induced maps for the image of t
  can be lifted to maps of C. -/
def of_faithful {t : cocone F} {D : Type u'} [category.{v} D] (G : C ⥤ D) [faithful G]
  (ht : is_colimit (G.map_cocone t)) (desc : Π (s : cocone F), t.X ⟶ s.X)
  (h : ∀ s, G.map (desc s) = ht.desc (G.map_cocone s)) : is_colimit t :=
{ desc := desc,
  fac' := λ s j, by apply G.map_injective; rw [G.map_comp, h]; apply ht.fac,
  uniq' := λ s m w, begin
    apply G.map_injective, rw h,
    refine ht.uniq (G.map_cocone s) _ (λ j, _),
    convert ←congr_arg (λ f, G.map f) (w j),
    apply G.map_comp
  end }

/--
If `F` and `G` are naturally isomorphic, then `F.map_cone c` being a colimit implies
`G.map_cone c` is also a colimit.
-/
def map_cocone_equiv {D : Type u'} [category.{v} D] {K : J ⥤ C} {F G : C ⥤ D} (h : F ≅ G)
  {c : cocone K} (t : is_colimit (F.map_cocone c)) : is_colimit (G.map_cocone c) :=
begin
  apply is_colimit.of_iso_colimit _ (precompose_whisker_left_map_cocone h c),
  apply (precompose_inv_equiv (iso_whisker_left K h : _) _).symm t,
end

/--
A cocone is a colimit cocone exactly if
there is a unique cocone morphism from any other cocone.
-/
def iso_unique_cocone_morphism {t : cocone F} :
  is_colimit t ≅ Π s, unique (t ⟶ s) :=
{ hom := λ h s,
  { default := h.desc_cocone_morphism s,
    uniq := λ _, h.uniq_cocone_morphism },
  inv := λ h,
  { desc := λ s, (h s).default.hom,
    uniq' := λ s f w, congr_arg cocone_morphism.hom ((h s).uniq ⟨f, w⟩) } }

namespace of_nat_iso
variables {X : C} (h : coyoneda.obj (op X) ≅ F.cocones)

/-- If `F.cocones` is corepresented by `X`, each morphism `f : X ⟶ Y` gives a cocone with cone point `Y`. -/
def cocone_of_hom {Y : C} (f : X ⟶ Y) : cocone F :=
{ X := Y, ι := h.hom.app Y f }

/-- If `F.cocones` is corepresented by `X`, each cocone `s` gives a morphism `X ⟶ s.X`. -/
def hom_of_cocone (s : cocone F) : X ⟶ s.X := h.inv.app s.X s.ι

@[simp] lemma cocone_of_hom_of_cocone (s : cocone F) : cocone_of_hom h (hom_of_cocone h s) = s :=
begin
  dsimp [cocone_of_hom, hom_of_cocone], cases s, congr, dsimp,
  exact congr_fun (congr_fun (congr_arg nat_trans.app h.inv_hom_id) s_X) s_ι,
end

@[simp] lemma hom_of_cocone_of_hom {Y : C} (f : X ⟶ Y) : hom_of_cocone h (cocone_of_hom h f) = f :=
congr_fun (congr_fun (congr_arg nat_trans.app h.hom_inv_id) Y) f

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to the identity morphism on `X`
will be a colimit cocone. -/
def colimit_cocone : cocone F :=
cocone_of_hom h (𝟙 X)

/-- If `F.cocones` is corepresented by `X`, the cocone corresponding to a morphism `f : Y ⟶ X` is
the colimit cocone extended by `f`. -/
lemma cocone_of_hom_fac {Y : C} (f : X ⟶ Y) :
cocone_of_hom h f = (colimit_cocone h).extend f :=
begin
  dsimp [cocone_of_hom, colimit_cocone, cocone.extend],
  congr' with j,
  have t := congr_fun (h.hom.naturality f) (𝟙 X),
  dsimp at t,
  simp only [id_comp] at t,
  rw congr_fun (congr_arg nat_trans.app t) j,
  refl,
end

/-- If `F.cocones` is corepresented by `X`, any cocone is the extension of the colimit cocone by the
corresponding morphism. -/
lemma cocone_fac (s : cocone F) : (colimit_cocone h).extend (hom_of_cocone h s) = s :=
begin
  rw ←cocone_of_hom_of_cocone h s,
  conv_lhs { simp only [hom_of_cocone_of_hom] },
  apply (cocone_of_hom_fac _ _).symm,
end

end of_nat_iso

section
open of_nat_iso

/--
If `F.cocones` is corepresentable, then the cocone corresponding to the identity morphism on
the representing object is a colimit cocone.
-/
def of_nat_iso {X : C} (h : coyoneda.obj (op X) ≅ F.cocones) :
  is_colimit (colimit_cocone h) :=
{ desc := λ s, hom_of_cocone h s,
  fac' := λ s j,
  begin
    have h := cocone_fac h s,
    cases s,
    injection h with h₁ h₂,
    simp only [heq_iff_eq] at h₂,
    conv_rhs { rw ← h₂ }, refl,
  end,
  uniq' := λ s m w,
  begin
    rw ←hom_of_cocone_of_hom h m,
    congr,
    rw cocone_of_hom_fac,
    dsimp, cases s, congr' with j, exact w j,
  end }
end

end is_colimit

section limit

/-- `limit_cone F` contains a cone over `F` together with the information that it is a limit. -/
@[nolint has_inhabited_instance]
structure limit_cone (F : J ⥤ C) :=
(cone : cone F)
(is_limit : is_limit cone)

/-- `has_limit F` represents the mere existence of a limit for `F`. -/
class has_limit (F : J ⥤ C) : Prop :=
mk' :: (exists_limit : nonempty (limit_cone F))

lemma has_limit.mk {F : J ⥤ C} (d : limit_cone F) : has_limit F :=
⟨nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `limit_cone F` from `has_limit F`. -/
def get_limit_cone (F : J ⥤ C) [has_limit F] : limit_cone F :=
classical.choice $ has_limit.exists_limit

variables (J C)

/-- `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`. -/
class has_limits_of_shape : Prop :=
(has_limit : Π F : J ⥤ C, has_limit F)

/-- `C` has all (small) limits if it has limits of every shape. -/
class has_limits : Prop :=
(has_limits_of_shape : Π (J : Type v) [𝒥 : small_category J], has_limits_of_shape J C)

variables {J C}

@[priority 100] -- see Note [lower instance priority]
instance has_limit_of_has_limits_of_shape
  {J : Type v} [small_category J] [H : has_limits_of_shape J C] (F : J ⥤ C) : has_limit F :=
has_limits_of_shape.has_limit F

@[priority 100] -- see Note [lower instance priority]
instance has_limits_of_shape_of_has_limits
  {J : Type v} [small_category J] [H : has_limits C] : has_limits_of_shape J C :=
has_limits.has_limits_of_shape J

/- Interface to the `has_limit` class. -/

/-- An arbitrary choice of limit cone for a functor. -/
def limit.cone (F : J ⥤ C) [has_limit F] : cone F := (get_limit_cone F).cone

/-- An arbitrary choice of limit object of a functor. -/
def limit (F : J ⥤ C) [has_limit F] := (limit.cone F).X

/-- The projection from the limit object to a value of the functor. -/
def limit.π (F : J ⥤ C) [has_limit F] (j : J) : limit F ⟶ F.obj j :=
(limit.cone F).π.app j

@[simp] lemma limit.cone_X {F : J ⥤ C} [has_limit F] :
  (limit.cone F).X = limit F := rfl

@[simp] lemma limit.cone_π {F : J ⥤ C} [has_limit F] :
  (limit.cone F).π.app = limit.π _ := rfl

@[simp, reassoc] lemma limit.w (F : J ⥤ C) [has_limit F] {j j' : J} (f : j ⟶ j') :
  limit.π F j ≫ F.map f = limit.π F j' := (limit.cone F).w f

/-- Evidence that the arbitrary choice of cone provied by `limit.cone F` is a limit cone. -/
def limit.is_limit (F : J ⥤ C) [has_limit F] : is_limit (limit.cone F) :=
(get_limit_cone F).is_limit

/-- The morphism from the cone point of any other cone to the limit object. -/
def limit.lift (F : J ⥤ C) [has_limit F] (c : cone F) : c.X ⟶ limit F :=
(limit.is_limit F).lift c

@[simp] lemma limit.is_limit_lift {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.is_limit F).lift c = limit.lift F c := rfl

@[simp, reassoc] lemma limit.lift_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  limit.lift F c ≫ limit.π F j = c.π.app j :=
is_limit.fac _ c j

/--
Functoriality of limits.

Usually this morphism should be accessed through `lim.map`,
but may be needed separately when you have specified limits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def lim_map {F G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) : limit F ⟶ limit G :=
is_limit.map _ (limit.is_limit G) α

@[simp, reassoc] lemma lim_map_π {F G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) (j : J) :
  lim_map α ≫ limit.π G j = limit.π F j ≫ α.app j :=
limit.lift_π _ j

/-- The cone morphism from any cone to the arbitrary choice of limit cone. -/
def limit.cone_morphism {F : J ⥤ C} [has_limit F] (c : cone F) :
  c ⟶ limit.cone F :=
(limit.is_limit F).lift_cone_morphism c

@[simp] lemma limit.cone_morphism_hom {F : J ⥤ C} [has_limit F] (c : cone F) :
  (limit.cone_morphism c).hom = limit.lift F c := rfl
lemma limit.cone_morphism_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  (limit.cone_morphism c).hom ≫ limit.π F j = c.π.app j :=
by simp

@[simp, reassoc] lemma limit.cone_point_unique_up_to_iso_hom_comp {F : J ⥤ C} [has_limit F]
  {c : cone F} (hc : is_limit c) (j : J) :
  (is_limit.cone_point_unique_up_to_iso hc (limit.is_limit _)).hom ≫ limit.π F j = c.π.app j :=
is_limit.cone_point_unique_up_to_iso_hom_comp _ _ _

@[simp, reassoc] lemma limit.cone_point_unique_up_to_iso_inv_comp {F : J ⥤ C} [has_limit F]
  {c : cone F} (hc : is_limit c) (j : J) :
  (is_limit.cone_point_unique_up_to_iso (limit.is_limit _) hc).inv ≫ limit.π F j = c.π.app j :=
is_limit.cone_point_unique_up_to_iso_inv_comp _ _ _

/--
Given any other limit cone for `F`, the chosen `limit F` is isomorphic to the cone point.
-/
def limit.iso_limit_cone {F : J ⥤ C} [has_limit F] (t : limit_cone F) :
  limit F ≅ t.cone.X :=
is_limit.cone_point_unique_up_to_iso (limit.is_limit F) t.is_limit

@[simp, reassoc] lemma limit.iso_limit_cone_hom_π
  {F : J ⥤ C} [has_limit F] (t : limit_cone F) (j : J) :
  (limit.iso_limit_cone t).hom ≫ t.cone.π.app j = limit.π F j :=
by { dsimp [limit.iso_limit_cone, is_limit.cone_point_unique_up_to_iso], tidy, }

@[simp, reassoc] lemma limit.iso_limit_cone_inv_π
  {F : J ⥤ C} [has_limit F] (t : limit_cone F) (j : J) :
  (limit.iso_limit_cone t).inv ≫ limit.π F j = t.cone.π.app j :=
by { dsimp [limit.iso_limit_cone, is_limit.cone_point_unique_up_to_iso], tidy, }

@[ext] lemma limit.hom_ext {F : J ⥤ C} [has_limit F] {X : C} {f f' : X ⟶ limit F}
  (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
(limit.is_limit F).hom_ext w

@[simp] lemma limit.lift_map {F G : J ⥤ C} [has_limit F] [has_limit G] (c : cone F) (α : F ⟶ G) :
  limit.lift F c ≫ lim_map α = limit.lift G ((cones.postcompose α).obj c) :=
by { ext, rw [assoc, lim_map_π, limit.lift_π_assoc, limit.lift_π], refl }

@[simp] lemma limit.lift_cone {F : J ⥤ C} [has_limit F] :
  limit.lift F (limit.cone F) = 𝟙 (limit F) :=
(limit.is_limit _).lift_self

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.hom_iso (F : J ⥤ C) [has_limit F] (W : C) : (W ⟶ limit F) ≅ (F.cones.obj (op W)) :=
(limit.is_limit F).hom_iso W

@[simp] lemma limit.hom_iso_hom (F : J ⥤ C) [has_limit F] {W : C} (f : W ⟶ limit F) :
  (limit.hom_iso F W).hom f = (const J).map f ≫ (limit.cone F).π :=
(limit.is_limit F).hom_iso_hom f

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
def limit.hom_iso' (F : J ⥤ C) [has_limit F] (W : C) :
  ((W ⟶ limit F) : Type v) ≅ { p : Π j, W ⟶ F.obj j // ∀ {j j' : J} (f : j ⟶ j'), p j ≫ F.map f = p j' } :=
(limit.is_limit F).hom_iso' W

lemma limit.lift_extend {F : J ⥤ C} [has_limit F] (c : cone F) {X : C} (f : X ⟶ c.X) :
  limit.lift F (c.extend f) = f ≫ limit.lift F c :=
by obviously

/--
If a functor `F` has a limit, so does any naturally isomorphic functor.
-/
lemma has_limit_of_iso {F G : J ⥤ C} [has_limit F] (α : F ≅ G) : has_limit G :=
has_limit.mk
{ cone := (cones.postcompose α.hom).obj (limit.cone F),
  is_limit :=
  { lift := λ s, limit.lift F ((cones.postcompose α.inv).obj s),
    fac' := λ s j,
    begin
      rw [cones.postcompose_obj_π, nat_trans.comp_app, limit.cone_π, ←category.assoc, limit.lift_π],
      simp
    end,
    uniq' := λ s m w,
    begin
      apply limit.hom_ext, intro j,
      rw [limit.lift_π, cones.postcompose_obj_π, nat_trans.comp_app, ←nat_iso.app_inv, iso.eq_comp_inv],
      simpa using w j
    end } }

/-- If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit. -/
-- See the construction of limits from products and equalizers
-- for an example usage.
lemma has_limit.of_cones_iso {J K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C)
  (h : F.cones ≅ G.cones) [has_limit F] : has_limit G :=
has_limit.mk ⟨_, is_limit.of_nat_iso ((is_limit.nat_iso (limit.is_limit F)) ≪≫ h)⟩

/--
The limits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_limit.iso_of_nat_iso {F G : J ⥤ C} [has_limit F] [has_limit G] (w : F ≅ G) :
  limit F ≅ limit G :=
is_limit.cone_points_iso_of_nat_iso (limit.is_limit F) (limit.is_limit G) w

@[simp, reassoc]
lemma has_limit.iso_of_nat_iso_hom_π {F G : J ⥤ C} [has_limit F] [has_limit G]
  (w : F ≅ G) (j : J) :
  (has_limit.iso_of_nat_iso w).hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
is_limit.cone_points_iso_of_nat_iso_hom_comp _ _ _ _

@[simp, reassoc]
lemma has_limit.lift_iso_of_nat_iso_hom {F G : J ⥤ C} [has_limit F] [has_limit G] (t : cone F)
  (w : F ≅ G) :
  limit.lift F t ≫ (has_limit.iso_of_nat_iso w).hom = limit.lift G ((cones.postcompose w.hom).obj _) :=
is_limit.lift_comp_cone_points_iso_of_nat_iso_hom _ _ _

/--
The limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_limit.iso_of_equivalence {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
is_limit.cone_points_iso_of_equivalence (limit.is_limit F) (limit.is_limit G) e w

@[simp]
lemma has_limit.iso_of_equivalence_hom_π {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
  (has_limit.iso_of_equivalence e w).hom ≫ limit.π G k =
    limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) :=
begin
  simp only [has_limit.iso_of_equivalence, is_limit.cone_points_iso_of_equivalence_hom],
  dsimp,
  simp,
end

@[simp]
lemma has_limit.iso_of_equivalence_inv_π {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
  (has_limit.iso_of_equivalence e w).inv ≫ limit.π F j =
    limit.π G (e.functor.obj j) ≫ w.hom.app j :=
begin
  simp only [has_limit.iso_of_equivalence, is_limit.cone_points_iso_of_equivalence_hom],
  dsimp,
  simp,
end

section pre
variables (F) [has_limit F] (E : K ⥤ J) [has_limit (E ⋙ F)]

/--
The canonical morphism from the limit of `F` to the limit of `E ⋙ F`.
-/
def limit.pre : limit F ⟶ limit (E ⋙ F) :=
limit.lift (E ⋙ F) ((limit.cone F).whisker E)

@[simp, reassoc] lemma limit.pre_π (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) :=
by { erw is_limit.fac, refl }

@[simp] lemma limit.lift_pre (c : cone F) :
  limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) :=
by ext; simp

variables {L : Type v} [small_category L]
variables (D : L ⥤ K) [has_limit (D ⋙ E ⋙ F)]

@[simp] lemma limit.pre_pre : limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) :=
by ext j; erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π]; refl

variables {E F}

/---
If we have particular limit cones available for `E ⋙ F` and for `F`,
we obtain a formula for `limit.pre F E`.
-/
lemma limit.pre_eq (s : limit_cone (E ⋙ F)) (t : limit_cone F) :
  limit.pre F E =
    (limit.iso_limit_cone t).hom ≫ s.is_limit.lift ((t.cone).whisker E) ≫
      (limit.iso_limit_cone s).inv :=
by tidy

end pre

section post
variables {D : Type u'} [category.{v} D]

variables (F) [has_limit F] (G : C ⥤ D) [has_limit (F ⋙ G)]

/--
The canonical morphism from `G` applied to the limit of `F` to the limit of `F ⋙ G`.
-/
def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
limit.lift (F ⋙ G) (G.map_cone (limit.cone F))

@[simp, reassoc] lemma limit.post_π (j : J) :
  limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) :=
by { erw is_limit.fac, refl }

@[simp] lemma limit.lift_post (c : cone F) :
  G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.map_cone c) :=
by { ext, rw [assoc, limit.post_π, ←G.map_comp, limit.lift_π, limit.lift_π], refl }

@[simp] lemma limit.post_post
  {E : Type u''} [category.{v} E] (H : D ⥤ E) [has_limit ((F ⋙ G) ⋙ H)] :
/- H G (limit F) ⟶ H (limit (F ⋙ G)) ⟶ limit ((F ⋙ G) ⋙ H) equals -/
/- H G (limit F) ⟶ limit (F ⋙ (G ⋙ H)) -/
  H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) :=
by ext; erw [assoc, limit.post_π, ←H.map_comp, limit.post_π, limit.post_π]; refl

end post

lemma limit.pre_post {D : Type u'} [category.{v} D]
  (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  [has_limit F] [has_limit (E ⋙ F)] [has_limit (F ⋙ G)] [has_limit ((E ⋙ F) ⋙ G)] :
/- G (limit F) ⟶ G (limit (E ⋙ F)) ⟶ limit ((E ⋙ F) ⋙ G) vs -/
/- G (limit F) ⟶ limit F ⋙ G ⟶ limit (E ⋙ (F ⋙ G)) or -/
  G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E :=
by ext; erw [assoc, limit.post_π, ←G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π]; refl

open category_theory.equivalence
instance has_limit_equivalence_comp (e : K ≌ J) [has_limit F] : has_limit (e.functor ⋙ F) :=
has_limit.mk { cone := cone.whisker e.functor (limit.cone F),
  is_limit := is_limit.whisker_equivalence (limit.is_limit F) e, }

local attribute [elab_simple] inv_fun_id_assoc -- not entirely sure why this is needed

/--
If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`.
-/
lemma has_limit_of_equivalence_comp (e : K ≌ J) [has_limit (e.functor ⋙ F)] : has_limit F :=
begin
  haveI : has_limit (e.inverse ⋙ e.functor ⋙ F) := limits.has_limit_equivalence_comp e.symm,
  apply has_limit_of_iso (e.inv_fun_id_assoc F),
end

-- `has_limit_comp_equivalence` and `has_limit_of_comp_equivalence`
-- are proved in `category_theory/adjunction/limits.lean`.

section lim_functor


variables [has_limits_of_shape J C]

section

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
@[simps obj]
def lim : (J ⥤ C) ⥤ C :=
{ obj := λ F, limit F,
  map := λ F G α, lim_map α,
  map_id' := λ F, by { ext, erw [lim_map_π, category.id_comp, category.comp_id] },
  map_comp' := λ F G H α β,
    by ext; erw [assoc, is_limit.fac, is_limit.fac, ←assoc, is_limit.fac, assoc]; refl }
end

variables {F} {G : J ⥤ C} (α : F ⟶ G)

-- We generate this manually since `simps` gives it a weird name.
@[simp] lemma lim_map_eq_lim_map : lim.map α = lim_map α := rfl

lemma limit.map_pre [has_limits_of_shape K C] (E : K ⥤ J) :
  lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whisker_left E α) :=
by { ext, simp }

lemma limit.map_pre' [has_limits_of_shape K C]
  (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
  limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whisker_right α F) :=
by ext1; simp [← category.assoc]

lemma limit.id_pre (F : J ⥤ C) :
limit.pre F (𝟭 _) = lim.map (functor.left_unitor F).inv := by tidy

lemma limit.map_post {D : Type u'} [category.{v} D] [has_limits_of_shape J D] (H : C ⥤ D) :
/- H (limit F) ⟶ H (limit G) ⟶ limit (G ⋙ H) vs
   H (limit F) ⟶ limit (F ⋙ H) ⟶ limit (G ⋙ H) -/
  H.map (lim_map α) ≫ limit.post G H = limit.post F H ≫ lim_map (whisker_right α H) :=
begin
  ext,
  simp only [whisker_right_app, lim_map_π, assoc, limit.post_π_assoc, limit.post_π, ← H.map_comp],
end

/--
The isomorphism between
morphisms from `W` to the cone point of the limit cone for `F`
and cones over `F` with cone point `W`
is natural in `F`.
-/
def lim_yoneda : lim ⋙ yoneda ≅ category_theory.cones J C :=
nat_iso.of_components (λ F, nat_iso.of_components (λ W, limit.hom_iso F (unop W)) (by tidy))
  (by tidy)

end lim_functor

/--
We can transport limits of shape `J` along an equivalence `J ≌ J'`.
-/
lemma has_limits_of_shape_of_equivalence {J' : Type v} [small_category J']
  (e : J ≌ J') [has_limits_of_shape J C] : has_limits_of_shape J' C :=
by { constructor, intro F, apply has_limit_of_equivalence_comp e, apply_instance }

end limit


section colimit

/-- `colimit_cocone F` contains a cocone over `F` together with the information that it is a
    colimit. -/
@[nolint has_inhabited_instance]
structure colimit_cocone (F : J ⥤ C) :=
(cocone : cocone F)
(is_colimit : is_colimit cocone)

/-- `has_colimit F` represents the mere existence of a colimit for `F`. -/
class has_colimit (F : J ⥤ C) : Prop :=
mk' :: (exists_colimit : nonempty (colimit_cocone F))

lemma has_colimit.mk {F : J ⥤ C} (d : colimit_cocone F) : has_colimit F :=
⟨nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `colimit_cocone F` from `has_colimit F`. -/
def get_colimit_cocone (F : J ⥤ C) [has_colimit F] : colimit_cocone F :=
classical.choice $ has_colimit.exists_colimit

variables (J C)

/-- `C` has colimits of shape `J` if there exists a colimit for every functor `F : J ⥤ C`. -/
class has_colimits_of_shape : Prop :=
(has_colimit : Π F : J ⥤ C, has_colimit F)

/-- `C` has all (small) colimits if it has colimits of every shape. -/
class has_colimits : Prop :=
(has_colimits_of_shape : Π (J : Type v) [𝒥 : small_category J], has_colimits_of_shape J C)

variables {J C}

@[priority 100] -- see Note [lower instance priority]
instance has_colimit_of_has_colimits_of_shape
  {J : Type v} [small_category J] [H : has_colimits_of_shape J C] (F : J ⥤ C) : has_colimit F :=
has_colimits_of_shape.has_colimit F

@[priority 100] -- see Note [lower instance priority]
instance has_colimits_of_shape_of_has_colimits
  {J : Type v} [small_category J] [H : has_colimits C] : has_colimits_of_shape J C :=
has_colimits.has_colimits_of_shape J

/- Interface to the `has_colimit` class. -/

/-- An arbitrary choice of colimit cocone of a functor. -/
def colimit.cocone (F : J ⥤ C) [has_colimit F] : cocone F := (get_colimit_cocone F).cocone

/-- An arbitrary choice of colimit object of a functor. -/
def colimit (F : J ⥤ C) [has_colimit F] := (colimit.cocone F).X

/-- The coprojection from a value of the functor to the colimit object. -/
def colimit.ι (F : J ⥤ C) [has_colimit F] (j : J) : F.obj j ⟶ colimit F :=
(colimit.cocone F).ι.app j

@[simp] lemma colimit.cocone_ι {F : J ⥤ C} [has_colimit F] (j : J) :
  (colimit.cocone F).ι.app j = colimit.ι _ j := rfl

@[simp] lemma colimit.cocone_X {F : J ⥤ C} [has_colimit F] :
  (colimit.cocone F).X = colimit F := rfl

@[simp, reassoc] lemma colimit.w (F : J ⥤ C) [has_colimit F] {j j' : J} (f : j ⟶ j') :
  F.map f ≫ colimit.ι F j' = colimit.ι F j := (colimit.cocone F).w f

/-- Evidence that the arbitrary choice of cocone is a colimit cocone. -/
def colimit.is_colimit (F : J ⥤ C) [has_colimit F] : is_colimit (colimit.cocone F) :=
(get_colimit_cocone F).is_colimit

/-- The morphism from the colimit object to the cone point of any other cocone. -/
def colimit.desc (F : J ⥤ C) [has_colimit F] (c : cocone F) : colimit F ⟶ c.X :=
(colimit.is_colimit F).desc c

@[simp] lemma colimit.is_colimit_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.is_colimit F).desc c = colimit.desc F c := rfl

/--
We have lots of lemmas describing how to simplify `colimit.ι F j ≫ _`,
and combined with `colimit.ext` we rely on these lemmas for many calculations.

However, since `category.assoc` is a `@[simp]` lemma, often expressions are
right associated, and it's hard to apply these lemmas about `colimit.ι`.

We thus use `reassoc` to define additional `@[simp]` lemmas, with an arbitrary extra morphism.
(see `tactic/reassoc_axiom.lean`)
 -/
@[simp, reassoc] lemma colimit.ι_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
is_colimit.fac _ c j

/--
Functoriality of colimits.

Usually this morphism should be accessed through `colim.map`,
but may be needed separately when you have specified colimits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def colim_map {F G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) : colimit F ⟶ colimit G :=
is_colimit.map (colimit.is_colimit F) _ α

@[simp, reassoc]
lemma ι_colim_map {F G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) (j : J) :
  colimit.ι F j ≫ colim_map α = α.app j ≫ colimit.ι G j :=
colimit.ι_desc _ j

/-- The cocone morphism from the arbitrary choice of colimit cocone to any cocone. -/
def colimit.cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone F) ⟶ c :=
(colimit.is_colimit F).desc_cocone_morphism c

@[simp] lemma colimit.cocone_morphism_hom {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone_morphism c).hom = colimit.desc F c := rfl
lemma colimit.ι_cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ (colimit.cocone_morphism c).hom = c.ι.app j :=
by simp

@[simp, reassoc] lemma colimit.comp_cocone_point_unique_up_to_iso_hom {F : J ⥤ C} [has_colimit F]
  {c : cocone F} (hc : is_colimit c) (j : J) :
  colimit.ι F j ≫ (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hc).hom = c.ι.app j :=
is_colimit.comp_cocone_point_unique_up_to_iso_hom _ _ _

@[simp, reassoc] lemma colimit.comp_cocone_point_unique_up_to_iso_inv {F : J ⥤ C} [has_colimit F]
  {c : cocone F} (hc : is_colimit c) (j : J) :
  colimit.ι F j ≫ (is_colimit.cocone_point_unique_up_to_iso hc (colimit.is_colimit _)).inv = c.ι.app j :=
is_colimit.comp_cocone_point_unique_up_to_iso_inv _ _ _

/--
Given any other colimit cocone for `F`, the chosen `colimit F` is isomorphic to the cocone point.
-/
def colimit.iso_colimit_cocone {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) :
  colimit F ≅ t.cocone.X :=
is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) t.is_colimit

@[simp, reassoc] lemma colimit.iso_colimit_cocone_ι_hom
  {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) (j : J) :
  colimit.ι F j ≫ (colimit.iso_colimit_cocone t).hom = t.cocone.ι.app j :=
by { dsimp [colimit.iso_colimit_cocone, is_colimit.cocone_point_unique_up_to_iso], tidy, }

@[simp, reassoc] lemma colimit.iso_colimit_cocone_ι_inv
  {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) (j : J) :
  t.cocone.ι.app j ≫ (colimit.iso_colimit_cocone t).inv = colimit.ι F j :=
by { dsimp [colimit.iso_colimit_cocone, is_colimit.cocone_point_unique_up_to_iso], tidy, }

@[ext] lemma colimit.hom_ext {F : J ⥤ C} [has_colimit F] {X : C} {f f' : colimit F ⟶ X}
  (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ f') : f = f' :=
(colimit.is_colimit F).hom_ext w

@[simp] lemma colimit.desc_cocone {F : J ⥤ C} [has_colimit F] :
  colimit.desc F (colimit.cocone F) = 𝟙 (colimit F) :=
(colimit.is_colimit _).desc_self

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
def colimit.hom_iso (F : J ⥤ C) [has_colimit F] (W : C) : (colimit F ⟶ W) ≅ (F.cocones.obj W) :=
(colimit.is_colimit F).hom_iso W

@[simp] lemma colimit.hom_iso_hom (F : J ⥤ C) [has_colimit F] {W : C} (f : colimit F ⟶ W) :
  (colimit.hom_iso F W).hom f = (colimit.cocone F).ι ≫ (const J).map f :=
(colimit.is_colimit F).hom_iso_hom f

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
def colimit.hom_iso' (F : J ⥤ C) [has_colimit F] (W : C) :
  ((colimit F ⟶ W) : Type v) ≅ { p : Π j, F.obj j ⟶ W // ∀ {j j'} (f : j ⟶ j'), F.map f ≫ p j' = p j } :=
(colimit.is_colimit F).hom_iso' W

lemma colimit.desc_extend (F : J ⥤ C) [has_colimit F] (c : cocone F) {X : C} (f : c.X ⟶ X) :
  colimit.desc F (c.extend f) = colimit.desc F c ≫ f :=
begin
  ext1, rw [←category.assoc], simp
end

/--
If `F` has a colimit, so does any naturally isomorphic functor.
-/
-- This has the isomorphism pointing in the opposite direction than in `has_limit_of_iso`.
-- This is intentional; it seems to help with elaboration.
lemma has_colimit_of_iso {F G : J ⥤ C} [has_colimit F] (α : G ≅ F) : has_colimit G :=
has_colimit.mk
{ cocone := (cocones.precompose α.hom).obj (colimit.cocone F),
  is_colimit :=
  { desc := λ s, colimit.desc F ((cocones.precompose α.inv).obj s),
    fac' := λ s j,
    begin
      rw [cocones.precompose_obj_ι, nat_trans.comp_app, colimit.cocone_ι],
      rw [category.assoc, colimit.ι_desc, ←nat_iso.app_hom, ←iso.eq_inv_comp], refl
    end,
    uniq' := λ s m w,
    begin
      apply colimit.hom_ext, intro j,
      rw [colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app, ←nat_iso.app_inv,
        iso.eq_inv_comp],
      simpa using w j
    end } }

/-- If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit. -/
lemma has_colimit.of_cocones_iso {J K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C)
  (h : F.cocones ≅ G.cocones) [has_colimit F] : has_colimit G :=
has_colimit.mk ⟨_, is_colimit.of_nat_iso ((is_colimit.nat_iso (colimit.is_colimit F)) ≪≫ h)⟩

/--
The colimits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_colimit.iso_of_nat_iso {F G : J ⥤ C} [has_colimit F] [has_colimit G] (w : F ≅ G) :
  colimit F ≅ colimit G :=
is_colimit.cocone_points_iso_of_nat_iso (colimit.is_colimit F) (colimit.is_colimit G) w

@[simp, reassoc]
lemma has_colimit.iso_of_nat_iso_ι_hom {F G : J ⥤ C} [has_colimit F] [has_colimit G]
  (w : F ≅ G) (j : J) :
  colimit.ι F j ≫ (has_colimit.iso_of_nat_iso w).hom = w.hom.app j ≫ colimit.ι G j :=
is_colimit.comp_cocone_points_iso_of_nat_iso_hom _ _ _ _

@[simp, reassoc]
lemma has_colimit.iso_of_nat_iso_hom_desc {F G : J ⥤ C} [has_colimit F] [has_colimit G] (t : cocone G)
  (w : F ≅ G) :
  (has_colimit.iso_of_nat_iso w).hom ≫ colimit.desc G t = colimit.desc F ((cocones.precompose w.hom).obj _) :=
is_colimit.cocone_points_iso_of_nat_iso_hom_desc _ _ _

/--
The colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_colimit.iso_of_equivalence {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) : colimit F ≅ colimit G :=
is_colimit.cocone_points_iso_of_equivalence (colimit.is_colimit F) (colimit.is_colimit G) e w

@[simp]
lemma has_colimit.iso_of_equivalence_hom_π {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (j : J) :
  colimit.ι F j ≫ (has_colimit.iso_of_equivalence e w).hom =
     F.map (e.unit.app j) ≫ w.inv.app _ ≫ colimit.ι G _ :=
begin
  simp [has_colimit.iso_of_equivalence, is_colimit.cocone_points_iso_of_equivalence_inv],
  dsimp,
  simp,
end

@[simp]
lemma has_colimit.iso_of_equivalence_inv_π {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G]
   (e : J ≌ K) (w : e.functor ⋙ G ≅ F) (k : K) :
  colimit.ι G k ≫ (has_colimit.iso_of_equivalence e w).inv =
     G.map (e.counit_inv.app k) ≫ w.hom.app (e.inverse.obj k) ≫ colimit.ι F (e.inverse.obj k) :=
begin
  simp [has_colimit.iso_of_equivalence, is_colimit.cocone_points_iso_of_equivalence_inv],
  dsimp,
  simp,
end

section pre
variables (F) [has_colimit F] (E : K ⥤ J) [has_colimit (E ⋙ F)]

/--
The canonical morphism from the colimit of `E ⋙ F` to the colimit of `F`.
-/
def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
colimit.desc (E ⋙ F) ((colimit.cocone F).whisker E)

@[simp, reassoc] lemma colimit.ι_pre (k : K) : colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) :=
by { erw is_colimit.fac, refl, }

@[simp] lemma colimit.pre_desc (c : cocone F) :
  colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) :=
by ext; rw [←assoc, colimit.ι_pre]; simp

variables {L : Type v} [small_category L]
variables (D : L ⥤ K) [has_colimit (D ⋙ E ⋙ F)]

@[simp] lemma colimit.pre_pre : colimit.pre (E ⋙ F) D ≫ colimit.pre F E = colimit.pre F (D ⋙ E) :=
begin
  ext j,
  rw [←assoc, colimit.ι_pre, colimit.ι_pre],
  letI : has_colimit ((D ⋙ E) ⋙ F) := show has_colimit (D ⋙ E ⋙ F), by apply_instance,
  exact (colimit.ι_pre F (D ⋙ E) j).symm
end

variables {E F}

/---
If we have particular colimit cocones available for `E ⋙ F` and for `F`,
we obtain a formula for `colimit.pre F E`.
-/
lemma colimit.pre_eq (s : colimit_cocone (E ⋙ F)) (t : colimit_cocone F) :
  colimit.pre F E =
    (colimit.iso_colimit_cocone s).hom ≫ s.is_colimit.desc ((t.cocone).whisker E) ≫
      (colimit.iso_colimit_cocone t).inv :=
by tidy

end pre

section post
variables {D : Type u'} [category.{v} D]

variables (F) [has_colimit F] (G : C ⥤ D) [has_colimit (F ⋙ G)]

/--
The canonical morphism from `G` applied to the colimit of `F ⋙ G`
to `G` applied to the colimit of `F`.
-/
def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
colimit.desc (F ⋙ G) (G.map_cocone (colimit.cocone F))

@[simp, reassoc] lemma colimit.ι_post (j : J) : colimit.ι (F ⋙ G) j ≫ colimit.post F G  = G.map (colimit.ι F j) :=
by { erw is_colimit.fac, refl, }

@[simp] lemma colimit.post_desc (c : cocone F) :
  colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.map_cocone c) :=
by { ext, rw [←assoc, colimit.ι_post, ←G.map_comp, colimit.ι_desc, colimit.ι_desc], refl }

@[simp] lemma colimit.post_post
  {E : Type u''} [category.{v} E] (H : D ⥤ E) [has_colimit ((F ⋙ G) ⋙ H)] :
/- H G (colimit F) ⟶ H (colimit (F ⋙ G)) ⟶ colimit ((F ⋙ G) ⋙ H) equals -/
/- H G (colimit F) ⟶ colimit (F ⋙ (G ⋙ H)) -/
  colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) :=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←H.map_comp, colimit.ι_post],
  exact (colimit.ι_post F (G ⋙ H) j).symm
end

end post

lemma colimit.pre_post {D : Type u'} [category.{v} D]
  (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D)
  [has_colimit F] [has_colimit (E ⋙ F)] [has_colimit (F ⋙ G)] [has_colimit ((E ⋙ F) ⋙ G)] :
/- G (colimit F) ⟶ G (colimit (E ⋙ F)) ⟶ colimit ((E ⋙ F) ⋙ G) vs -/
/- G (colimit F) ⟶ colimit F ⋙ G ⟶ colimit (E ⋙ (F ⋙ G)) or -/
  colimit.post (E ⋙ F) G ≫ G.map (colimit.pre F E) = colimit.pre (F ⋙ G) E ≫ colimit.post F G :=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←G.map_comp, colimit.ι_pre, ←assoc],
  letI : has_colimit (E ⋙ F ⋙ G) := show has_colimit ((E ⋙ F) ⋙ G), by apply_instance,
  erw [colimit.ι_pre (F ⋙ G) E j, colimit.ι_post]
end

open category_theory.equivalence
instance has_colimit_equivalence_comp (e : K ≌ J) [has_colimit F] : has_colimit (e.functor ⋙ F) :=
has_colimit.mk { cocone := cocone.whisker e.functor (colimit.cocone F),
  is_colimit := is_colimit.whisker_equivalence (colimit.is_colimit F) e, }

/--
If a `E ⋙ F` has a colimit, and `E` is an equivalence, we can construct a colimit of `F`.
-/
lemma has_colimit_of_equivalence_comp (e : K ≌ J) [has_colimit (e.functor ⋙ F)] : has_colimit F :=
begin
  haveI : has_colimit (e.inverse ⋙ e.functor ⋙ F) := limits.has_colimit_equivalence_comp e.symm,
  apply has_colimit_of_iso (e.inv_fun_id_assoc F).symm,
end

section colim_functor


variables [has_colimits_of_shape J C]

section
local attribute [simp] colim_map

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
@[simps obj]
def colim : (J ⥤ C) ⥤ C :=
{ obj := λ F, colimit F,
  map := λ F G α, colim_map α,
  map_id' := λ F, by { ext, erw [ι_colim_map, id_comp, comp_id] },
  map_comp' := λ F G H α β,
    by { ext, erw [←assoc, is_colimit.fac, is_colimit.fac, assoc, is_colimit.fac, ←assoc], refl } }

end

variables {F} {G : J ⥤ C} (α : F ⟶ G)

@[simp, reassoc] lemma colimit.ι_map (j : J) : colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j :=
by apply is_colimit.fac

@[simp] lemma colimit.map_desc (c : cocone G) :
  colim.map α ≫ colimit.desc G c = colimit.desc F ((cocones.precompose α).obj c) :=
by ext; rw [←assoc, colimit.ι_map, assoc, colimit.ι_desc, colimit.ι_desc]; refl

lemma colimit.pre_map [has_colimits_of_shape K C] (E : K ⥤ J) :
  colimit.pre F E ≫ colim.map α = colim.map (whisker_left E α) ≫ colimit.pre G E :=
by ext; rw [←assoc, colimit.ι_pre, colimit.ι_map, ←assoc, colimit.ι_map, assoc, colimit.ι_pre]; refl

lemma colimit.pre_map' [has_colimits_of_shape K C]
  (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
  colimit.pre F E₁ = colim.map (whisker_right α F) ≫ colimit.pre F E₂ :=
by ext1; simp [← category.assoc]

lemma colimit.pre_id (F : J ⥤ C) :
colimit.pre F (𝟭 _) = colim.map (functor.left_unitor F).hom := by tidy

lemma colimit.map_post {D : Type u'} [category.{v} D] [has_colimits_of_shape J D] (H : C ⥤ D) :
/- H (colimit F) ⟶ H (colimit G) ⟶ colimit (G ⋙ H) vs
   H (colimit F) ⟶ colimit (F ⋙ H) ⟶ colimit (G ⋙ H) -/
  colimit.post F H ≫ H.map (colim.map α) = colim.map (whisker_right α H) ≫ colimit.post G H:=
begin
  ext,
  rw [←assoc, colimit.ι_post, ←H.map_comp, colimit.ι_map, H.map_comp],
  rw [←assoc, colimit.ι_map, assoc, colimit.ι_post],
  refl
end

/--
The isomorphism between
morphisms from the cone point of the colimit cocone for `F` to `W`
and cocones over `F` with cone point `W`
is natural in `F`.
-/
def colim_coyoneda : colim.op ⋙ coyoneda ≅ category_theory.cocones J C :=
nat_iso.of_components (λ F, nat_iso.of_components (colimit.hom_iso (unop F)) (by tidy))
  (by tidy)

end colim_functor

/--
We can transport colimits of shape `J` along an equivalence `J ≌ J'`.
-/
lemma has_colimits_of_shape_of_equivalence {J' : Type v} [small_category J']
  (e : J ≌ J') [has_colimits_of_shape J C] : has_colimits_of_shape J' C :=
by { constructor, intro F, apply has_colimit_of_equivalence_comp e, apply_instance }

end colimit

section opposite

/--
If `t : cone F` is a limit cone, then `t.op : cocone F.op` is a colimit cocone.
-/
def is_limit.op {t : cone F} (P : is_limit t) : is_colimit t.op :=
{ desc := λ s, (P.lift s.unop).op,
  fac' := λ s j, congr_arg has_hom.hom.op (P.fac s.unop (unop j)),
  uniq' := λ s m w,
  begin
    rw ← P.uniq s.unop m.unop,
    { refl, },
    { dsimp, intro j, rw ← w, refl, }
  end }

/--
If `t : cocone F` is a colimit cocone, then `t.op : cone F.op` is a limit cone.
-/
def is_colimit.op {t : cocone F} (P : is_colimit t) : is_limit t.op :=
{ lift := λ s, (P.desc s.unop).op,
  fac' := λ s j, congr_arg has_hom.hom.op (P.fac s.unop (unop j)),
  uniq' := λ s m w,
  begin
    rw ← P.uniq s.unop m.unop,
    { refl, },
    { dsimp, intro j, rw ← w, refl, }
  end }

/--
If `t : cone F.op` is a limit cone, then `t.unop : cocone F` is a colimit cocone.
-/
def is_limit.unop {t : cone F.op} (P : is_limit t) : is_colimit t.unop :=
{ desc := λ s, (P.lift s.op).unop,
  fac' := λ s j, congr_arg has_hom.hom.unop (P.fac s.op (op j)),
  uniq' := λ s m w,
  begin
    rw ← P.uniq s.op m.op,
    { refl, },
    { dsimp, intro j, rw ← w, refl, }
  end }

/--
If `t : cocone F.op` is a colimit cocone, then `t.unop : cone F.` is a limit cone.
-/
def is_colimit.unop {t : cocone F.op} (P : is_colimit t) : is_limit t.unop :=
{ lift := λ s, (P.desc s.op).unop,
  fac' := λ s j, congr_arg has_hom.hom.unop (P.fac s.op (op j)),
  uniq' := λ s m w,
  begin
    rw ← P.uniq s.op m.op,
    { refl, },
    { dsimp, intro j, rw ← w, refl, }
  end }

/--
`t : cone F` is a limit cone if and only is `t.op : cocone F.op` is a colimit cocone.
-/
def is_limit_equiv_is_colimit_op {t : cone F} : is_limit t ≃ is_colimit t.op :=
equiv_of_subsingleton_of_subsingleton
  is_limit.op (λ P, P.unop.of_iso_limit (cones.ext (iso.refl _) (by tidy)))

/--
`t : cocone F` is a colimit cocone if and only is `t.op : cone F.op` is a limit cone.
-/
def is_colimit_equiv_is_limit_op {t : cocone F} : is_colimit t ≃ is_limit t.op :=
equiv_of_subsingleton_of_subsingleton
  is_colimit.op (λ P, P.unop.of_iso_colimit (cocones.ext (iso.refl _) (by tidy)))

end opposite

end category_theory.limits
