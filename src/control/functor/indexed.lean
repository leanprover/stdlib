/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import control.family

/-!
# Operations on functors between indexed type families
-/

universes u v w

local infixr ` ⊗ `:20 := (⨯)
local infixr ` ⊗' `:20 := category_theory.limits.prod.map

namespace category_theory.functor.fam

variables {I J : Type u} {α β γ : fam I} {F : fam I ⥤ fam J}

open fam

@[simp] theorem drop_fun_split_fun {α α' : fam (I ⊕ J)}
  (f : drop α ⟶ drop α') (g : last α ⟶ last α') :
  drop_fun (split_fun f g) = f := by ext; refl

@[simp] theorem last_fun_split_fun {α α' : fam (I⊕J)}
  (f : drop α ⟶ fam.drop α') (g : last α ⟶ last α') :
  last_fun (split_fun f g) = g := by ext; refl

open fam

theorem split_fun_inj
  {α α' : fam (I ⊕ J)} {f f' : drop α ⟶ drop α'} {g g' : last α ⟶ last α'}
  (H : split_fun f g = split_fun f' g') : f = f' ∧ g = g' :=
by rw [← drop_fun_split_fun f g, H, ← last_fun_split_fun f g, H]; simp

@[reassoc]
theorem append_fun_comp_split_fun
  {α γ : fam I} {β δ : fam J} {ε : fam (I ⊕ J)}
    (f₀ : fam.drop ε ⟶ fam.drop (α.append1 β)) (f₁ : α ⟶ γ)
    (g₀ : fam.last ε ⟶ fam.last (α.append1 β)) (g₁ : β ⟶ δ) :
  fam.split_fun f₀ g₀ ≫ fam.append_fun f₁ g₁ = fam.split_fun (f₀ ≫ f₁) (g₀ ≫ g₁) :=
(fam.split_fun_comp _ _ _ _).symm

/-! for lifting predicates and relations -/

/-- `pred_last α p x` predicates `p` of the last element of `x : α.append1 β`. -/
def pred_last (α : fam I) {β : fam J} (p : Pred β) : Pred (α.append1 β)
| (sum.inl i) x := true
| (sum.inr j) x := p _ x

/-- `rel_last α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and all the other elements are equal. -/
def rel_last (α : fam I) {β γ : fam J} (r : Pred $ β ⊗ γ) :
  Pred (α.append1 β ⊗ α.append1 γ)
| (sum.inl i) := λ x,
  let x₀ := (fam.prod.fst _ x),
      x₁ := (fam.prod.snd _ x) in
  fam.eq α i $ fam.prod.mk x₀ x₁
| (sum.inr i) := λ x,
  let x₀ := (fam.prod.fst _ x),
      x₁ := (fam.prod.snd _ x) in
  r i $ fam.prod.mk x₀ x₁

end category_theory.functor.fam

namespace quot.indexed

/-- map on `quot` that weakens its relation -/
def factor {I} {α : fam I} (r s: fam.Pred (α ⊗ α))
  (h : ∀ i (a : fam.unit i ⟶ α ⊗ α), a ⊨ r → a ⊨ s) :
  fam.quot r ⟶ fam.quot s :=
fam.quot.lift _ (fam.quot.mk _)
(λ X a h', fam.quot.sound _ (h _ _ h') )

lemma factor_mk_eq {I} {α : fam I} (r s: fam.Pred (α ⊗ α))
  (h : ∀ i (a : fam.unit i ⟶ α ⊗ α), a ⊨ r → a ⊨ s) :
  fam.quot.mk _ ≫ factor r s h = fam.quot.mk _ := rfl

end quot.indexed
