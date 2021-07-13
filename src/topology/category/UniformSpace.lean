/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Scott Morrison
-/
import category_theory.monad.limits
import topology.uniform_space.completion
import topology.category.Top.basic
import category_theory.concrete_category.representable

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/

universes u

open category_theory

/-- A (bundled) uniform space. -/
def UniformSpace : Type (u+1) := bundled uniform_space

namespace UniformSpace

/-- The information required to build morphisms for `UniformSpace`. -/
instance : unbundled_hom @uniform_continuous :=
⟨@uniform_continuous_id, @uniform_continuous.comp⟩

attribute [derive [has_coe_to_sort, large_category, concrete_category]] UniformSpace

instance (x : UniformSpace) : uniform_space x := x.str

/-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
def of (α : Type u) [uniform_space α] : UniformSpace := ⟨α⟩

instance : inhabited UniformSpace := ⟨UniformSpace.of empty⟩

@[simp] lemma coe_of (X : Type u) [uniform_space X] : (of X : Type u) = X := rfl

instance (X Y : UniformSpace) : has_coe_to_fun (X ⟶ Y) :=
{ F := λ _, X → Y, coe := category_theory.functor.map (forget UniformSpace) }

@[simp] lemma coe_comp {X Y Z : UniformSpace} (f : X ⟶ Y) (g : Y ⟶ Z) :
  (f ≫ g : X → Z) = g ∘ f := rfl
@[simp] lemma coe_id (X : UniformSpace) : (𝟙 X : X → X) = id := rfl
@[simp] lemma coe_mk {X Y : UniformSpace} (f : X → Y) (hf : uniform_continuous f) :
  ((⟨f, hf⟩ : X ⟶ Y) : X → Y) = f := rfl

lemma hom_ext {X Y : UniformSpace} {f g : X ⟶ Y} : (f : X → Y) = g → f = g := subtype.eq

/-- The forgetful functor from uniform spaces to topological spaces. -/
instance has_forget_to_Top : has_forget₂ UniformSpace.{u} Top.{u} :=
{ forget₂ :=
  { obj := λ X, Top.of X,
    map := λ X Y f, { to_fun := f,
                      continuous_to_fun := uniform_continuous.continuous f.property }, }, }

instance : representably_concrete UniformSpace.{u} :=
{ out := functor.corepresentable_of_nat_iso _ (opposite.op (of punit))
          (nat_iso.of_components
            (λ X, { hom := λ (f : _ ⟶ _), f ⟨⟩,
                    inv := λ x, ⟨λ _, x, uniform_continuous_const⟩})
            (λ X Y f, rfl)) }

end UniformSpace

/-- A (bundled) complete separated uniform space. -/
structure CpltSepUniformSpace :=
(α : Type u)
[is_uniform_space : uniform_space α]
[is_complete_space : complete_space α]
[is_separated : separated_space α]

namespace CpltSepUniformSpace

instance : has_coe_to_sort CpltSepUniformSpace :=
{ S := Type u, coe := CpltSepUniformSpace.α }

attribute [instance] is_uniform_space is_complete_space is_separated

def to_UniformSpace (X : CpltSepUniformSpace) : UniformSpace :=
UniformSpace.of X

instance complete_space (X : CpltSepUniformSpace) : complete_space ((to_UniformSpace X).α) :=
CpltSepUniformSpace.is_complete_space X

instance separated_space (X : CpltSepUniformSpace) : separated_space ((to_UniformSpace X).α) :=
CpltSepUniformSpace.is_separated X

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [uniform_space X] [complete_space X] [separated_space X] :
CpltSepUniformSpace := ⟨X⟩

@[simp] lemma coe_of (X : Type u) [uniform_space X] [complete_space X] [separated_space X] :
  (of X : Type u) = X := rfl

instance : inhabited CpltSepUniformSpace :=
begin
  haveI : separated_space empty := separated_iff_t2.mpr (by apply_instance),
  exact ⟨CpltSepUniformSpace.of empty⟩
end

/-- The category instance on `CpltSepUniformSpace`. -/
instance category : large_category CpltSepUniformSpace :=
induced_category.category to_UniformSpace

/-- The concrete category instance on `CpltSepUniformSpace`. -/
instance concrete_category : concrete_category CpltSepUniformSpace :=
induced_category.concrete_category to_UniformSpace

instance has_forget_to_UniformSpace : has_forget₂ CpltSepUniformSpace UniformSpace :=
induced_category.has_forget₂ to_UniformSpace

end CpltSepUniformSpace

namespace UniformSpace

open uniform_space
open CpltSepUniformSpace

/-- The functor turning uniform spaces into complete separated uniform spaces. -/
noncomputable def completion_functor : UniformSpace ⥤ CpltSepUniformSpace :=
{ obj := λ X, CpltSepUniformSpace.of (completion X),
  map := λ X Y f, ⟨completion.map f.1, completion.uniform_continuous_map⟩,
  map_id' := λ X, subtype.eq completion.map_id,
  map_comp' := λ X Y Z f g, subtype.eq (completion.map_comp g.property f.property).symm, }.

/-- The inclusion of a uniform space into its completion. -/
def completion_hom (X : UniformSpace) :
  X ⟶ (forget₂ CpltSepUniformSpace UniformSpace).obj (completion_functor.obj X) :=
{ val := (coe : X → completion X),
  property := completion.uniform_continuous_coe X }

@[simp] lemma completion_hom_val (X : UniformSpace) (x) :
  (completion_hom X) x = (x : completion X) := rfl

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
noncomputable def extension_hom {X : UniformSpace} {Y : CpltSepUniformSpace}
  (f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpace).obj Y) :
  completion_functor.obj X ⟶ Y :=
{ val := completion.extension f,
  property := completion.uniform_continuous_extension }

@[simp] lemma extension_hom_val {X : UniformSpace} {Y : CpltSepUniformSpace}
  (f : X ⟶ (forget₂ _ _).obj Y) (x) :
  (extension_hom f) x = completion.extension f x := rfl.

@[simp] lemma extension_comp_coe {X : UniformSpace} {Y : CpltSepUniformSpace}
(f : to_UniformSpace (CpltSepUniformSpace.of (completion X)) ⟶ to_UniformSpace Y) :
extension_hom (completion_hom X ≫ f) = f :=
by { apply subtype.eq, funext x, exact congr_fun (completion.extension_comp_coe f.property) x }

/-- The completion functor is left adjoint to the forgetful functor. -/
noncomputable def adj : completion_functor ⊣ forget₂ CpltSepUniformSpace UniformSpace :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, completion_hom X ≫ f,
    inv_fun := λ f, extension_hom f,
    left_inv := λ f, by { dsimp, erw extension_comp_coe },
    right_inv := λ f,
    begin
      apply subtype.eq, funext x, cases f,
      exact @completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.separated_space _) f_property _
    end },
  hom_equiv_naturality_left_symm' := λ X X' Y f g,
  begin
    apply hom_ext, funext x, dsimp,
    erw [coe_comp, ←completion.extension_map],
    refl, exact g.property, exact f.property,
  end }

noncomputable instance : is_right_adjoint (forget₂ CpltSepUniformSpace UniformSpace) :=
⟨completion_functor, adj⟩
noncomputable instance : reflective (forget₂ CpltSepUniformSpace UniformSpace) := {}

open category_theory.limits

-- TODO Once someone defines `has_limits UniformSpace`, turn this into an instance.
example [has_limits.{u} UniformSpace.{u}] : has_limits.{u} CpltSepUniformSpace.{u} :=
has_limits_of_reflective $ forget₂ CpltSepUniformSpace UniformSpace.{u}

end UniformSpace
