/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon
-/
import tactic.interactive
import control.family
import control.functor.indexed
import data.sigma

/-!
# Polynomial functors between indexed type families

Indexed polynomial functors are used for defining M-types and W-types.
They map a type family `α : fam J` to the type family
`λ j, Σ a : A j, B j a ⟶ α`, with `A : fam J` and `B : Π j, A j → fam I`.
They interact well with Lean's inductive definitions because they
guarantee that occurrences of `α` are positive.

## Main definitions

 * `ipfunctor` an indexed polynomial functor
 * `ipfunctor₀` for a specialized case of `ipfunctor`
 * `ipfunctor.apply` the functor structure instance of `ipfunctor`
 * `ipfunctor.Idx` to index the contents of of a `ipfunctor` application
 * `ipfunctor.comp` for functor composition
 * `ipfunctor.drop` and `ipfunctor.last` to decompose a functor
 * `ipfunctor.pf.mk` to turn a value of `ipfunctor.apply` into an arrow

-/

universes v v' u u'

local infixr ` ⊗ `:20 := (⨯)
local infixr ` ⊗' `:20 := category_theory.limits.prod.map

/-- Polynomial functors between indexed type families -/
structure ipfunctor (I J : Type u) :=
(A : fam J) (B : Π j, A j → fam I)

instance {I J} : inhabited (ipfunctor I J) := ⟨ ⟨ λ _, default _, λ _ _ _, default _ ⟩ ⟩

/-- specialized version of `ipfunctor` used for defining simple constructions -/
@[derive inhabited]
def ipfunctor₀ (I : Type u) := ipfunctor I I

namespace ipfunctor

variables {I J : Type u} {α β : Type u}

section pfunc
variables (P : ipfunctor I J)

/-- polynomial functor `P` as a functor -/
def apply : fam I ⥤ fam J :=
{ obj := λ X i, Σ a : P.A i, P.B i a ⟶ X,
  map := λ X Y f i ⟨a,g⟩, ⟨a, g ≫ f⟩ }

/-- Applying `P` to an object of `fam I` -/
def obj : fam I → fam J := P.apply.obj

/-- map function for polynomial functor `P` -/
def map {X Y : fam I} (f : X ⟶ Y) : P.obj X ⟶ P.obj Y := P.apply.map f

lemma map_id {X : fam I} : P.map (𝟙 X) = 𝟙 _ :=
category_theory.functor.map_id _ _

@[reassoc]
lemma map_comp {X Y Z : fam I} (f : X ⟶ Y) (g : Y ⟶ Z) : P.map (f ≫ g) = P.map f ≫ P.map g :=
category_theory.functor.map_comp _ _ _

@[simp, reassoc]
lemma map_comp_map {X Y Z : fam I} (f : X ⟶ Y) (g : Y ⟶ Z) : P.map f ≫ P.map g = P.map (f ≫ g) :=
(category_theory.functor.map_comp _ _ _).symm

@[simp]
lemma apply_map {X Y : fam I} (f : X ⟶ Y) : P.apply.map f = P.map f := rfl

theorem map_eq' {α β : fam I} (f : α ⟶ β) {j : J} (a : P.A j) (g : P.B j a ⟶ α) :
  P.map f _ ⟨a, g⟩ = ⟨a, g ≫ f⟩ :=
rfl

open fam set category_theory.functor

@[simp, reassoc]
theorem map_eq {α β : fam I} (f : α ⟶ β) {j : J} (a : P.A j) (g : P.B j a ⟶ α) :
  value j (P.obj _) ⟨a, g⟩ ≫ P.map f = value j (P.obj _) ⟨a, g ≫ f⟩ :=
by ext _ ⟨ ⟩ : 2; simp [map_eq']

/-- `Idx` identifies a location inside the application of an ipfunctor.
For `P : ipfunctor`, `x : P.obj α` and `i : P.Idx`, `i` can designate
one part of `x` or is invalid, if `i.1 ≠ x.1` -/
def Idx (j : J) := Σ (x : P.A j) i, P.B j x i

instance Idx.inhabited {i} [inhabited (P.A i)] [inhabited I] [inhabited $ P.B i (default (P.A i)) (default I)] :
  inhabited (Idx P i) := ⟨ ⟨default _,default _,default _⟩ ⟩

/-- Type index of the `A` component referenced by index `x` -/
def Idx.idx {P : ipfunctor I J} {j : J} (x : Idx P j) : I := x.2.1

/-- Lookup the part of `x` designed by index `j` or return an arbitrary value -/
def obj.iget {i} [decidable_eq $ P.A i] {α : fam I} (x : P.obj α i) (k : P.Idx i) [inhabited $ α k.idx] : α k.idx :=
if h : k.1 = x.1
  then x.2 _ (cast (by rw [Idx.idx,← h]) $ k.2.2)
  else default _

end pfunc

end ipfunctor

/-!
Composition of polynomial functors.
-/

namespace ipfunctor

variables {I J K : Type u} (P₂ : ipfunctor.{u} J K) (P₁ : ipfunctor.{u} I J)

/-- Composition of polynomial functors. -/
def comp : ipfunctor.{u} I K :=
⟨ λ i, Σ a₂ : P₂.1 i, P₂.2 _ a₂ ⟶ P₁.1,
  λ k a₂a₁ i, Σ j (u : P₂.2 _ a₂a₁.1 j), P₁.2 _ (a₂a₁.2 _ u) i ⟩

/-- Contructor for polynomial functor composition -/
def comp.mk : Π (α : fam I), P₂.obj (P₁.obj α) ⟶ (comp P₂ P₁).obj α :=
λ α k x, ⟨ ⟨x.1,x.2 ≫ λ j, sigma.fst⟩, λ i a₂a₁, (x.2 _ _).2 _ a₂a₁.2.2 ⟩

/-- Destructor for polynomial functor composition -/
def comp.get : Π (α : fam I), (comp P₂ P₁).obj α ⟶ P₂.obj (P₁.obj α) :=
λ α k x, ⟨ x.1.1, λ j a₂, ⟨x.1.2 _ a₂, λ i a₁, x.2 _ ⟨j, a₂, a₁⟩⟩ ⟩

@[simp, reassoc]
lemma comp.mk_get : Π (α : fam I), comp.mk P₂ P₁ α ≫ comp.get P₂ P₁ α = 𝟙 _ :=
λ α, funext $ λ k, funext $ λ ⟨x,y⟩, congr_arg (sigma.mk x) (by ext : 3; intros; refl)

@[simp, reassoc]
lemma comp.get_mk : Π (α : fam I), comp.get P₂ P₁ α ≫ comp.mk P₂ P₁ α = 𝟙 _ :=
λ α, funext $ λ k, funext $ λ ⟨⟨a,c⟩,b⟩, congr_arg (sigma.mk _) $ by ext _ ⟨a,b,c⟩; refl

instance get.category_theory.is_iso {α : fam I} : category_theory.is_iso (comp.get P₂ P₁ α) :=
{ inv := comp.mk P₂ P₁ α }

instance mk.category_theory.is_iso {α : fam I} : category_theory.is_iso (comp.mk P₂ P₁ α) :=
{ inv := comp.get P₂ P₁ α }

@[simp, reassoc]
lemma comp.map_get : Π {α β : fam I} (f : α ⟶ β), (comp P₂ P₁).map f ≫ comp.get P₂ P₁ β = comp.get P₂ P₁ α ≫ map _ (map _ f) :=
by { intros, ext _ ⟨a,b⟩; intros; refl }

@[simp, reassoc]
lemma comp.map_mk : Π {α β : fam I} (f : α ⟶ β), map _ (map _ f) ≫ comp.mk P₂ P₁ β = comp.mk P₂ P₁ α ≫ (comp P₂ P₁).map f :=
λ α β f,
@category_theory.mono.right_cancellation _ _ _ _ (comp.get P₂ P₁ β) _ _ _ _ (by simp)

end ipfunctor

/-
Lifting predicates and relations.
-/

namespace ipfunctor
variables {I J : Type u} {P : ipfunctor.{u} I J}
open category_theory.functor.fam
open fam set category_theory.functor

/-- Eliminator for polynomial functor -/
@[elab_as_eliminator]
def obj_cases
   {α : fam I} {j} {C : (unit j ⟶ P.obj α) → Sort*}
   (h : ∀ a f, C $ value _ _ ⟨a,f⟩)
   (x : unit j ⟶ P.obj α) : C x :=
begin
  rcases h' : x _ unit.rfl with ⟨a,f⟩,
  have : value _ _ (x _ unit.rfl) = x,
  { ext _ ⟨ ⟩ : 2, refl },
  rw h' at this, specialize h a f,
  simpa [this] using h
end

theorem liftp_iff {α : fam I} (p : Π ⦃i⦄ , α i → Prop) {j} (x : unit j ⟶ P.obj α) :
  fam.liftp p x ↔ ∃ a f, x = value _ _ ⟨a, f⟩ ∧ ∀ (i : I) y, p (@f i y) :=
begin
  split,
  { rintros ⟨y, hy⟩, revert y, refine obj_cases _, intros a f hy,
    rw [← ipfunctor.map, map_eq P] at hy,
    use [a, f ≫ fam.subtype.val, hy.symm],
    intros, apply (f _ y).property },
  rintros ⟨a, f, xeq, pf⟩,
  let g : unit j ⟶ P.obj (subtype p),
  { rintros _ ⟨ ⟩, refine ⟨a, λ i b, ⟨f _ b, pf _ _⟩⟩, },
  refine ⟨g, _⟩,
  ext _ ⟨ ⟩ : 2, rw xeq, refl,
end

theorem liftp_iff' {α : fam I} (p : Π ⦃i⦄ , α i → Prop) {i} (a : P.A i) (f : P.B i a ⟶ α) :
  @fam.liftp.{u} _ _ P.apply _ p _ (value _ _ ⟨a,f⟩) ↔ ∀ i x, p (@f i x) :=
begin
  simp only [liftp_iff, sigma.mk.inj_iff]; split; intro,
  { casesm* [Exists _, _ ∧ _],
    replace a_1_h_h_left := congr_fun (congr_fun a_1_h_h_left i) unit.rfl,
    dsimp [value] at a_1_h_h_left, cases a_1_h_h_left, assumption },
  repeat { constructor <|> assumption }
end

theorem liftr_iff {α : fam I} (r : Pred (α ⊗ α)) {j} (x y : unit j ⟶ P.obj α) :
  fam.liftr r x y ↔ ∃ a f₀ f₁, x = value _ _ ⟨a, f₀⟩ ∧ y = value _ _ ⟨a, f₁⟩ ∧ ∀ i j, r _ (fam.prod.mk (@f₀ i j) (@f₁ i j)) :=
begin
  split,
  { rintros ⟨u, xeq, yeq⟩,
    revert u, refine obj_cases _, intros a f xeq yeq,
    rw [← ipfunctor.map, map_eq] at xeq yeq,
    use [a,f ≫ fam.subtype.val ≫ fam.prod.fst,f ≫ fam.subtype.val ≫ fam.prod.snd, xeq.symm, yeq.symm],
    intros, convert (f _ j_1).property, ext ⟨ ⟩; refl },
  rintros ⟨a, f₀, f₁, xeq, yeq, h⟩,
  let g : unit j ⟶ P.obj (subtype r),
  { rintros _ ⟨ ⟩, refine ⟨a, λ i b, ⟨fam.prod.mk (f₀ _ b) (f₁ _ b), h _ _⟩⟩, },
  refine ⟨g, _⟩,
  split; ext _ ⟨ ⟩ : 2,
  { rw xeq, refl },
  { rw yeq, refl },
end

theorem liftp_iff₀ {α : fam I} {X : fam J} (p : fam.Pred α) (x : X ⟶ P.obj α) :
  liftp p x ↔ ∀ j (y : X j), ∃ a f, x _ y = ⟨a, f⟩ ∧ ∀ i a, p i (f _ a) :=
begin
  split,
  { rintros ⟨y, hy⟩ j z, cases h : y _ z with a f,
    refine ⟨a, λ i a, subtype.val (f _ a), _, λ i a, subtype.property (f _ a)⟩, --, λ i, (f i).property⟩,
    fold ipfunctor.map ipfunctor.obj at *,
    -- rw [← ipfunctor.map, ← ipfunctor.obj] at h,
    simp [hy.symm, (≫), h, map_eq'],
    simp [(∘),fam.subtype.val], },
  introv hv, dsimp [liftp],
  choose a f hv using hv,
  let F₀ := λ j k, a j k,
  let F₁ : Π j k, P.B j (F₀ j k) ⟶ α := λ j k, f j k,
  have F₂ : ∀ j k, x _ k = ⟨F₀ j k,F₁ j k⟩ := λ j k, (hv j k).1,
  have F₃ : ∀ j k i a, p i (F₁ j k _ a) := λ j k, (hv j k).2,
  refine ⟨λ j x, ⟨F₀ j x,λ i y, ⟨F₁ j x _ y,F₃ j x i y⟩⟩,_⟩,
  ext : 2, rw F₂, refl
end

open category_theory

theorem liftr_iff₀ {α β : fam I} (r : fam.Pred (α ⊗ β)) {X : fam J} (x : X ⟶ P.obj α) {y} :
  liftr r x y ↔ ∀ j (z : X j), ∃ a f₀ f₁, x _ z = ⟨a, f₀⟩ ∧ y _ z = ⟨a, f₁⟩ ∧ ∀ i a, r i (fam.prod.mk (f₀ _ a) (f₁ _ a)) :=
begin
  split,
  { rintros ⟨u, xeq, yeq⟩ j z, cases h : u _ z with a f,
    -- use a, have := λ i (b : P.B j a i), (f b).val,
    use [a, f ≫ fam.subtype.val ≫ limits.prod.fst, f ≫ fam.subtype.val ≫ limits.prod.snd],
    split, { simp only [← xeq, pi.comp_apply, types_comp_apply, h, map_eq', apply_map], },
    split, { simp only [← yeq, pi.comp_apply, types_comp_apply, h, map_eq', apply_map], },
    intros i a, convert (f _ a).property, simp only [pi.comp_apply, types_comp_apply],
    rw [← fam.prod.fst, ← fam.prod.snd, fam.prod.mk_fst_snd], refl },
  rintros hv, dsimp [liftr],
  choose a f₀ f₁ hv using hv,
  let F₀ := λ j k, a j k,
  let F₁ : Π j k, P.B j (F₀ j k) ⟶ α := λ j k, f₀ j k,
  let F₂ : Π j k, P.B j (F₀ j k) ⟶ β := λ j k, f₁ j k,
  have F₃ : ∀ j k, x _ k = ⟨F₀ j k,F₁ j k⟩ := λ j k, (hv j k).1,
  have F₄ : ∀ j k, y _ k = ⟨F₀ j k,F₂ j k⟩ := λ j k, (hv j k).2.1,
  have F₅ : ∀ j k i a, r i (fam.prod.mk (F₁ j k _ a) (F₂ j k _ a)) := λ j k, (hv j k).2.2,
  refine ⟨λ j x, ⟨F₀ j x,λ i y, _⟩,_⟩,
  { refine ⟨(fam.prod.mk (F₁ j x _ y) (F₂ j x _ y)), F₅ _ _ _ _⟩ },
  split; ext : 2; [rw F₃,rw F₄]; refl,
end

theorem supp_eq {α : fam I} (j i) (a : P.A j) (f : P.B j a ⟶ α) :
  @fam.supp.{u} _ _ P.apply _ _  (value _ _ ⟨a,f⟩) i = @f _ '' univ :=
begin
  ext, simp only [fam.supp, image_univ, mem_range, mem_set_of_eq],
  split; intro h,
  { apply @h (λ i x, ∃ (y : P.B j a i), f _ y = x),
    rw liftp_iff', intros, refine ⟨_,rfl⟩ },
  { simp only [liftp_iff'], cases h, subst x,
    tauto }
end

end ipfunctor

/-!
Decomposing an ipfunctor on product of type families.

The terminology, `drop` and `last` is purposefully asymmetric to
hint at the fact that type families and intended to be built
out of an iteration of products. For instance, `fam (((pempty ⊕ I) ⊕ J) ⊕ K)` is
intended to encode a vector of type families `[fam I, fam J, fam K]` and gives easy
access to the last object.
-/

namespace ipfunctor
variables {I J : Type u} (P : ipfunctor.{u} (J⊕I) I)

/-- Take a functor from the left component of the source type family of `P`
to the target type family of `P` -/
def drop : ipfunctor J I :=
{ A := P.A, B := λ i a, (P.B i a).drop }

/-- Take a functor from the right component of the source type family of `P`
to the target type family of `P` -/
def last : ipfunctor₀ I :=
{ A := P.A, B := λ i a, (P.B i a).last }

/-- Helper definition for reasoning about the construction by parts of
a polynomial functor -/
@[reducible] def append_contents {α : fam J} {β : fam I}
    {i} {a : P.A i} (f' : P.drop.B i a ⟶ α) (f : P.last.B i a ⟶ β) :
  P.B i a ⟶ α.append1 β :=
fam.split_fun f' f

variables {j : I} {a a' : P.A j} {α α' : fam J} {β β' : fam I}
  (f₀ : P.drop.B j a ⟶ α) (f₁ : α ⟶ α')
  (g₀ : P.last.B j a ⟶ β) (g₁ : β ⟶ β')

lemma append_contents_comp :
  append_contents _ (f₀ ≫ f₁) (g₀ ≫ g₁) = append_contents _ f₀ g₀ ≫ fam.split_fun f₁ g₁ :=
by rw [append_contents,append_contents,← fam.split_fun_comp]

end ipfunctor

namespace ipfunctor
variables {I J : Type u} (P : ipfunctor.{u} I J)

/-- Shorthand for creating an arrow from a value. The type is more
specific than necessary but helps with elaboration -/
def pf.mk {α} (i) (x : P.obj α i) : fam.unit i ⟶ P.obj α :=
fam.value _ _ x

@[reassoc]
lemma pf.mk_map_eq {α β} (i) (a : P.A i) (f : P.B i a ⟶ α) (g : α ⟶ β) :
  pf.mk P i ⟨a,f⟩ ≫ P.map g = pf.mk P i ⟨a,f ≫ g⟩ :=
ipfunctor.map_eq _ _ _ _

end ipfunctor
