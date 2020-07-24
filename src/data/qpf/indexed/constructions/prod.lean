
import data.pfunctor.indexed.basic
import data.qpf.indexed.basic

import category_theory.products

import tactic.core

universes u

namespace category_theory.functor.fam

variables {I I' J J' : Type u}
  (F : fam I  ⥤ fam J )
  (G : fam I' ⥤ fam J')

/-- First projection of the product of two families -/
def prod_fst (X : fam (I ⊕ I')) : fam I
| i := X $ sum.inl i

/-- Second projection of the product of two families -/
def prod_snd (X : fam (I ⊕ I')) : fam I'
| i := X $ sum.inr i

/-- Application of the product functors `F` and `G` -/
protected def prod.obj (X : fam (I ⊕ I')) : fam (J ⊕ J')
| (sum.inl j) := F.obj (prod_fst X) j
| (sum.inr j) := G.obj (prod_snd X) j

/-- Projection of a morphism in the product category of two families into its left category -/
protected def prod.map.fst ⦃X Y : fam (I ⊕ I')⦄ : (X ⟶ Y) → (prod_fst X ⟶ prod_fst Y)
| f i x := f x

/-- Projection of a morphism in the product category of two families into its right category -/
protected def prod.map.snd ⦃X Y : fam (I ⊕ I')⦄ : (X ⟶ Y) → (prod_snd X ⟶ prod_snd Y)
| f i x := f x

/-- `map` of the product of `F` and `G` -/
protected def prod.map ⦃X Y : fam (I ⊕ I')⦄ : (X ⟶ Y) → (prod.obj F G X ⟶ prod.obj F G Y)
| f (sum.inl j) := λ x, F.map (map.fst f) x
| f (sum.inr j) := λ x, G.map (map.snd f) x

/--  -/
protected def prod.map' ⦃X Y : fam (I ⊕ I')⦄ :
  (prod_fst X ⟶ prod_fst Y) → (prod_snd X ⟶ prod_snd Y) → (X ⟶ Y)
| f g (sum.inl i) x := f x
| f g (sum.inr i) x := g x

@[simp] lemma prod.map.fst_id ⦃X : fam (I ⊕ I')⦄ : map.fst (𝟙 X) = 𝟙 _ := by ext; refl

@[simp] lemma prod.map.snd_id ⦃X : fam (I ⊕ I')⦄ : map.snd (𝟙 X) = 𝟙 _ := by ext; refl

@[simp] lemma prod.map.fst_comp ⦃X Y Z : fam (I ⊕ I')⦄ (f : X ⟶ Y) (g : Y ⟶ Z) :
  map.fst (f ≫ g) = map.fst f ≫ map.fst g := by ext; refl

@[simp] lemma prod.map.snd_comp ⦃X Y Z : fam (I ⊕ I')⦄ (f : X ⟶ Y) (g : Y ⟶ Z) :
  map.snd (f ≫ g) = map.snd f ≫ map.snd g := by ext; refl

/--
The product of two functors is a functor.
-/
def prod : fam (I ⊕ I') ⥤ fam (J ⊕ J') :=
{ obj := prod.obj F G,
  map := prod.map F G,
  map_id' := by { intros, ext ⟨ ⟩ ⟨ ⟩; simp [prod.map,prod.obj]; refl },
  map_comp' := by { intros, ext ⟨ ⟩ ⟨ ⟩; simp [prod.map,- ipfunctor.then_def]; refl } }

/--
Construct the product of two families
-/
def prod_obj (X : fam I) (Y : fam I') : fam (I ⊕ I')
| (sum.inl i) := X i
| (sum.inr i) := Y i

/--
Form an object `(prod F G).obj X` from components
-/
def prod_mk : Π X : fam (I ⊕ I'),
  prod_obj (F.obj $ prod_fst X) (G.obj $ prod_snd X) ⟶ (prod F G).obj X
| X (sum.inl j) x := x
| X (sum.inr j) x := x

/--
Deconstruct an object `(prod F G).obj X` into components
-/
def prod_get : Π X : fam (I ⊕ I'), (prod F G).obj X ⟶ prod_obj (F.obj $ prod_fst X) (G.obj $ prod_snd X)
| X (sum.inl j) x := x
| X (sum.inr j) x := x

/--
Map on the type family product
-/
def prod_map {X X' : fam I} {Y Y' : fam I'} : Π (f : X ⟶ X') (g : Y ⟶ Y'), prod_obj X Y ⟶ prod_obj X' Y'
| f g (sum.inl j) x := f x
| f g (sum.inr j) x := g x

@[simp,reassoc]
lemma prod_get_mk {X : fam (I ⊕ I')} :
  prod_get F G X ≫ prod_mk F G X = 𝟙 _ :=
by ext1 ⟨ ⟩; refl

@[simp,reassoc]
lemma prod_mk_nat {X Y : fam (I⊕I')}
  (f : X ⟶ Y)  :
  prod_mk F G _ ≫ (prod F G).map f =
  prod_map (F.map $ prod.map.fst f) (G.map $ prod.map.snd f) ≫ prod_mk F G _ :=
by ext1 ⟨ ⟩; refl

end category_theory.functor.fam

namespace ipfunctor

variables {I I' J J' : Type u}
  (F : ipfunctor I  J)
  (G : ipfunctor I' J')

/--
The B component of the product of polynomial functors
-/
def prod_B : Π (i : J ⊕ J'), sum.elim (F.A) (G.A) i → fam (I ⊕ I')
| (sum.inl i) x (sum.inl j) := F.B i x j
| (sum.inr i) x (sum.inr j) := G.B i x j
| _ _ _ := pempty

open category_theory.functor.fam (prod_obj prod_fst prod_snd prod.map')
open category_theory.functor

/--
First projection applied to the B component of product
-/
def fst_prod_B {X : fam I} : Π (i : J') (x : (G.A) i),
  prod_fst (prod_B F G (sum.inr i) x) ⟶ X .

/--
Second projection applied to the B component of product
-/
def snd_prod_B {X : fam I'} : Π (i : J) (x : (F.A) i),
  prod_snd (prod_B F G (sum.inl i) x) ⟶ X .

/--
The product of a polynomial functor is a polynomial functor
-/
def prod : ipfunctor (I ⊕ I') (J ⊕ J') :=
⟨ sum.elim F.A G.A, prod_B F G ⟩

/--
Construct a product
-/
def prod_mk : Π X : fam (I ⊕ I'), prod_obj (F.obj $ prod_fst X) (G.obj $ prod_snd X) ⟶ (prod F G).obj X
| X (sum.inl j) ⟨x,f⟩ := ⟨x,prod.map' f (snd_prod_B F G _ _)⟩
| X (sum.inr j) ⟨x,f⟩ := ⟨x,prod.map' (fst_prod_B F G _ _) f⟩

/--
Deconstruct a product
-/
def prod_get : Π X : fam (I ⊕ I'),
  (prod F G).obj X ⟶ prod_obj (F.obj $ prod_fst X) (G.obj $ prod_snd X)
| X (sum.inl j) x := ⟨x.1,fam.prod.map.fst x.2⟩
| X (sum.inr j) x := ⟨x.1,fam.prod.map.snd x.2⟩

@[simp,reassoc]
lemma prod_mk_get {X : fam (I ⊕ I')} :
  prod_mk F G X ≫ prod_get F G X = 𝟙 _ :=
by { ext1 ⟨ ⟩, ext ⟨_,_ ⟩; intros, refl, cases a, simp, ext _ ⟨ ⟩,
     dsimp [prod_get,prod_mk,fam.prod.map.fst,fam.prod.map'], ext, refl,
     ext ⟨ ⟩, refl, rintros ⟨ ⟩, dsimp [prod_get,prod_mk,fam.prod.map.fst,fam.prod.map'], ext, refl, rintros _ _ ⟨ ⟩,
     simp [prod_get,prod_mk,fam.prod.map.fst,fam.prod.map'], ext, refl }

@[simp]
lemma prod_map_id {X : fam I} {X' : fam I'} :
  fam.prod_map (𝟙 X) (𝟙 X') = 𝟙 _ :=
by ext ⟨ ⟩; refl

@[simp,reassoc]
lemma prod_map_comp_map {X Y Z : fam I} {X' Y' Z' : fam I'} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') :
  fam.prod_map f f' ≫ fam.prod_map g g' = fam.prod_map (f ≫ g) (f' ≫ g') :=
by ext ⟨ ⟩; refl

@[simp,reassoc]
lemma prod_get_nat {X Y : fam (I⊕I')} (f : X ⟶ Y) :
  (prod F G).map f ≫ prod_get F G _ =
  prod_get F G _ ≫ fam.prod_map (F.map $ fam.prod.map.fst f) (G.map $ fam.prod.map.snd f) :=
by { ext1 ⟨ ⟩; ext1 ⟨ ⟩; intros; refl }

end ipfunctor

namespace iqpf
variables {I I' J J' : Type u}
  (F : fam I  ⥤ fam J ) [q  : iqpf F]
  (G : fam I' ⥤ fam J') [q' : iqpf G]

attribute [ext fam] funext

open category_theory


namespace prod
open category_theory.functor.fam ipfunctor
variables {F G} {α β : fam J} (f : α ⟶ β)

include q q'

local attribute [simp] category_theory.functor.map_comp_map category_theory.functor.map_comp_map_assoc
local attribute [-simp] functor.map_comp

open fam.prod (fst snd)

instance : iqpf (prod F G) :=
{ P         := ipfunctor.prod (P F) (P G),
  abs       := λ α, ipfunctor.prod_get _ _ _ ≫ prod_map (abs _ (prod_fst α)) (abs _ (prod_snd α)) ≫ prod_mk F G _,
  repr      := λ α, prod_get _ _ _ ≫ prod_map (repr _ _) (repr _ _) ≫ ipfunctor.prod_mk _ _ _,
  abs_repr  := by { intros, simp, },
  abs_map   := by { intros, simp, },
 }

end prod

end iqpf
