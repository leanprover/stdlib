/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/

import order.omega_complete_partial_order
import order.category.Preorder
import category_theory.limits.constructions.limits_of_products_and_equalizers

/-!
# Category of types with a omega complete partial order

In this file, we bundle the class `omega_complete_partial_order` into a
concrete category and prove that continuous functions also form
a `omega_complete_partial_order`.

## Main definitions

 * `ωCPO`
   * an instance of `category` and `concrete_category`

 -/

open category_theory

universes u v

/-- The category of types with a omega complete partial order. -/
def ωCPO : Type (u+1) := bundled omega_complete_partial_order

namespace ωCPO

open omega_complete_partial_order

instance : bundled_hom @continuous_hom :=
{ to_fun := @continuous_hom.to_fun,
  id := @continuous_hom.id,
  comp := @continuous_hom.comp,
  hom_ext := @continuous_hom.coe_inj }

attribute [derive [has_coe_to_sort, large_category, concrete_category]] ωCPO

/-- Construct a bundled ωCPO from the underlying type and typeclass. -/
def of (α : Type*) [omega_complete_partial_order α] : ωCPO := bundled.of α

instance : inhabited ωCPO := ⟨of punit⟩

instance (α : ωCPO) : omega_complete_partial_order α := α.str

section

open category_theory.limits

namespace has_products

/-- The pi-type gives a cone for a product. -/
def product {J : Type v} (f : J → ωCPO.{v}) : fan f :=
fan.mk (of (Π j, f j)) (λ j, continuous_hom.of_mono (pi.monotone_apply j : _) (λ c, rfl))

/-- The pi-type is a limit cone for the product. -/
def is_product (J : Type v) (f : J → ωCPO) : is_limit (product f) :=
{ lift := λ s,
    ⟨λ t j, s.π.app j t, λ x y h j, (s.π.app j).monotone h,
     λ x, funext (λ j, (s.π.app j).continuous x)⟩,
  uniq' := λ s m w,
  begin
    ext t j,
    change m t j = s.π.app j t,
    rw ← w j,
    refl,
  end }.

instance (J : Type v) (f : J → ωCPO.{v}) : has_product f :=
has_limit.mk ⟨_, is_product _ f⟩

end has_products

instance omega_complete_partial_order_equalizer
  {α β : Type*} [omega_complete_partial_order α] [omega_complete_partial_order β]
  (f g : α →𝒄 β) : omega_complete_partial_order {a : α // f a = g a} :=
omega_complete_partial_order.subtype _ $ λ c hc,
begin
  rw [f.continuous, g.continuous],
  congr' 1,
  ext,
  apply hc _ ⟨_, rfl⟩,
end

namespace has_equalizers

/-- The equalizer inclusion function as a `continuous_hom`. -/
def equalizer_ι {α β : Type*} [omega_complete_partial_order α] [omega_complete_partial_order β]
  (f g : α →𝒄 β) :
  {a : α // f a = g a} →𝒄 α :=
continuous_hom.of_mono (preorder_hom.subtype.val _) (λ c, rfl)

/-- A construction of the equalizer fork. -/
def equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) :
  fork f g :=
@fork.of_ι _ _ _ _ _ _ (ωCPO.of {a // f a = g a}) (equalizer_ι f g)
  (continuous_hom.ext _ _ (λ x, x.2))

/-- The equalizer fork is a limit. -/
def is_equalizer {X Y : ωCPO.{v}} (f g : X ⟶ Y) : is_limit (equalizer f g) :=
fork.is_limit.mk' _ $ λ s,
⟨{ to_fun := λ x, ⟨s.ι x, by apply continuous_hom.congr_fun s.condition⟩,
    monotone' := λ x y h, s.ι.monotone h,
    cont := λ x, subtype.ext (s.ι.continuous x) },
  by { ext, refl },
  λ m hm,
  begin
    ext,
    apply continuous_hom.congr_fun hm,
  end⟩

end has_equalizers

instance : has_products ωCPO.{v} :=
λ J, { has_limit := λ F, has_limit_of_iso discrete.nat_iso_functor.symm }

instance {X Y : ωCPO.{v}} (f g : X ⟶ Y) : has_limit (parallel_pair f g) :=
has_limit.mk ⟨_, has_equalizers.is_equalizer f g⟩

instance : has_equalizers ωCPO.{v} := has_equalizers_of_has_limit_parallel_pair _

instance : has_limits ωCPO.{v} := limits_from_equalizers_and_products

end


end ωCPO
