
import data.pfunctor.indexed.basic
import data.qpf.indexed.basic
import category_theory.products

universes u

namespace iqpf
variables {I J K : Type u}
  (F : fam I ⥤ fam J) [q  : iqpf F]
  (G : fam J ⥤ fam K) [q' : iqpf G]

open category_theory

namespace comp
open ipfunctor
variables {F G} {α β : fam J} (f : α ⟶ β)

include q q'

local attribute [simp] category_theory.functor.map_comp_map category_theory.functor.map_comp_map_assoc
local attribute [-simp] functor.map_comp

section defs

variables F G

/--
Abstraction of the composition of qpfs
-/
@[simp] def abs (α) : (ipfunctor.comp (P G) (P F)).obj α ⟶ (F ⋙ G).obj α :=
ipfunctor.comp.get _ _ α ≫ (P G).map (abs F _) ≫ abs G _ ≫ 𝟙 (G.obj (F.obj α))

/--
Representation of the composition of qpfs
-/
@[simp] def repr (α) : (F ⋙ G).obj α ⟶ (ipfunctor.comp (P G) (P F)).obj α :=
𝟙 (G.obj (F.obj α)) ≫ @repr _ _ G q' _ ≫ (P G).map (repr F α) ≫ ipfunctor.comp.mk _ _ _

end defs

lemma abs_repr ⦃α⦄ : comp.repr F G α ≫ comp.abs F G _ = 𝟙 ((F ⋙ G).obj α) :=
by { intros,
  simp only [repr, abs, category.id_comp, category.comp_id, category.assoc, ipfunctor.comp.mk_get_assoc, functor.map_comp_map_assoc],
  erw [functor.map_comp_map_assoc, abs_repr, category_theory.functor.map_id, category.id_comp, category.id_comp, abs_repr], refl }

lemma abs_map ⦃α β⦄ (f : α ⟶ β) : (ipfunctor.comp (P G) (P F)).map f ≫ comp.abs F G _ = comp.abs F G _ ≫ (F ⋙ G).map f :=
by { intros, simp only [comp.abs, abs_map, functor.comp_map, ipfunctor.comp.map_get_assoc, functor.map_comp_map,
     abs_map_assoc, category.comp_id, category.assoc, category_theory.functor.map_comp_map] }

instance : iqpf (F ⋙ G) :=
{ P         := ipfunctor.comp (P G) (P F),
  abs := abs F G,
  repr := repr F G,
  abs_repr := abs_repr,
  abs_map := abs_map,
 }

end comp

end iqpf
