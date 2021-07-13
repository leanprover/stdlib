/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
import data.pfunctor.multivariate.basic

/-!
# Multivariate quotients of polynomial functors.

Basic definition of multivariate QPF. QPFs form a compositional framework
for defining inductive and coinductive types, their quotients and nesting.

The idea is based on building ever larger functors. For instance, we can define
a list using a shape functor:

```lean
inductive list_shape (a b : Type)
| nil : list_shape
| cons : a -> b -> list_shape
```

This shape can itself be decomposed as a sum of product which are themselves
QPFs. It follows that the shape is a QPF and we can take its fixed point
and create the list itself:

```lean
def list (a : Type) := fix list_shape a -- not the actual notation
```

We can continue and define the quotient on permutation of lists and create
the multiset type:

```lean
def multiset (a : Type) := qpf.quot list.perm list a -- not the actual notion
```

And `multiset` is also a QPF. We can then create a novel data type (for Lean):

```lean
inductive tree (a : Type)
| node : a -> multiset tree -> tree
```

An unordered tree. This is currently not supported by Lean because it nests
an inductive type inside of a quotient. We can go further and define
unordered, possibly infinite trees:

```lean
coinductive tree' (a : Type)
| node : a -> multiset tree' -> tree'
```

by using the `cofix` construct. Those options can all be mixed and
matched because they preserve the properties of QPF. The latter example,
`tree'`, combines fixed point, co-fixed point and quotients.

## Related modules

 * constructions
   * fix
   * cofix
   * quot
   * comp
   * sigma / pi
   * prj
   * const

each proves that some operations on functors preserves the QPF structure

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

universe u

open_locale mvfunctor

/--
Multivariate quotients of polynomial functors.
-/
class mvqpf {n : ℕ} (F : typevec.{u} n → Type*) [mvfunctor F] :=
(P         : mvpfunctor.{u} n)
(abs       : Π {α}, P.obj α → F α)
(repr      : Π {α}, F α → P.obj α)
(abs_repr  : ∀ {α} (x : F α), abs (repr x) = x)
(abs_map   : ∀ {α β} (f : α ⟹ β) (p : P.obj α), abs (f <$$> p) = f <$$> abs p)

namespace mvqpf
variables {n : ℕ} {F : typevec.{u} n → Type*} [mvfunctor F] [q : mvqpf F]
include q
open mvfunctor (liftp liftr)

/-!
### Show that every mvqpf is a lawful mvfunctor.
-/

protected theorem id_map {α : typevec n} (x : F α) : typevec.id <$$> x = x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map], reflexivity }

@[simp] theorem comp_map {α β γ : typevec n} (f : α ⟹ β) (g : β ⟹ γ) (x : F α) :
  (g ⊚ f) <$$> x = g <$$> f <$$> x :=
by { rw ←abs_repr x, cases repr x with a f, rw [←abs_map, ←abs_map, ←abs_map], reflexivity }

@[priority 100]
instance is_lawful_mvfunctor : is_lawful_mvfunctor F :=
{ id_map := @mvqpf.id_map n F _ _,
  comp_map := @comp_map n F _ _ }

/- Lifting predicates and relations -/

theorem liftp_iff {α : typevec n} (p : Π ⦃i⦄, α i → Prop) (x : F α) :
  liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i j, p (f i j) :=
begin
  split,
  { rintros ⟨y, hy⟩, cases h : repr y with a f,
    use [a, λ i j, (f i j).val], split,
    { rw [←hy, ←abs_repr y, h, ←abs_map], reflexivity },
    intros i j, apply (f i j).property },
  rintros ⟨a, f, h₀, h₁⟩, dsimp at *,
  use abs (⟨a, λ i j, ⟨f i j, h₁ i j⟩⟩),
  rw [←abs_map, h₀], reflexivity
end

theorem liftr_iff {α : typevec n} (r : Π ⦃i⦄, α i → α i → Prop) (x y : F α) :
  liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) :=
begin
  split,
  { rintros ⟨u, xeq, yeq⟩, cases h : repr u with a f,
    use [a, λ i j, (f i j).val.fst, λ i j, (f i j).val.snd],
    split, { rw [←xeq, ←abs_repr u, h, ←abs_map], refl },
    split, { rw [←yeq, ←abs_repr u, h, ←abs_map], refl },
    intros i j, exact (f i j).property },
  rintros ⟨a, f₀, f₁, xeq, yeq, h⟩,
  use abs ⟨a, λ i j, ⟨(f₀ i j, f₁ i j), h i j⟩⟩,
  dsimp, split,
  { rw [xeq, ←abs_map], refl },
  rw [yeq, ←abs_map], refl
end

open set
open mvfunctor

theorem mem_supp {α : typevec n} (x : F α) (i) (u : α i) :
  u ∈ supp x i ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ :=
begin
  rw [supp], dsimp, split,
  { intros h a f haf,
    have : liftp (λ i u, u ∈ f i '' univ) x,
    { rw liftp_iff, refine ⟨a, f, haf.symm, _⟩,
      intros i u, exact mem_image_of_mem _ (mem_univ _) },
    exact h this },
  intros h p, rw liftp_iff,
  rintros ⟨a, f, xeq, h'⟩,
  rcases h a f xeq.symm with ⟨i, _, hi⟩,
  rw ←hi, apply h'
end

theorem supp_eq {α : typevec n} {i} (x : F α) :
  supp x i = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f i '' univ } :=
by ext; apply mem_supp

theorem has_good_supp_iff {α : typevec n} (x : F α) :
  (∀ p, liftp p x ↔ ∀ i (u ∈ supp x i), p i u) ↔
    ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ i a' f', abs ⟨a', f'⟩ = x → f i '' univ ⊆ f' i '' univ :=
begin
  split,
  { intros h,
    have : liftp (supp x) x, by { rw h, introv, exact id, },
    rw liftp_iff at this, rcases this with ⟨a, f, xeq, h'⟩,
    refine ⟨a, f, xeq.symm, _⟩,
    intros a' f' h'',
    rintros hu u ⟨j, h₂, hfi⟩,
    have hh : u ∈ supp x a', by rw ←hfi; apply h',
    refine (mem_supp x _ u).mp hh _ _ hu, },
  rintros ⟨a, f, xeq, h⟩ p, rw liftp_iff, split,
  { rintros ⟨a', f', xeq', h'⟩ i u usuppx,
    rcases (mem_supp x _ u).mp @usuppx a' f' xeq'.symm with ⟨i, _, f'ieq⟩,
    rw ←f'ieq, apply h' },
  intro h',
  refine ⟨a, f, xeq.symm, _⟩, intros j y,
  apply h', rw mem_supp,
  intros a' f' xeq',
  apply h _ a' f' xeq',
  apply mem_image_of_mem _ (mem_univ _)
end

variable (q)

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
def is_uniform : Prop := ∀ ⦃α : typevec n⦄ (a a' : q.P.A)
    (f : q.P.B a ⟹ α) (f' : q.P.B a' ⟹ α),
  abs ⟨a, f⟩ = abs ⟨a', f'⟩ → ∀ i, f i '' univ = f' i '' univ

/-- does `abs` preserve `liftp`? -/
def liftp_preservation : Prop :=
∀ ⦃α : typevec n⦄ (p : Π ⦃i⦄, α i → Prop) (x : q.P.obj α), liftp p (abs x) ↔ liftp p x

/-- does `abs` preserve `supp`? -/
def supp_preservation : Prop :=
∀ ⦃α⦄ (x : q.P.obj α), supp (abs x) = supp x

variable [q]

theorem supp_eq_of_is_uniform (h : q.is_uniform) {α : typevec n} (a : q.P.A) (f : q.P.B a ⟹ α) :
  ∀ i, supp (abs ⟨a, f⟩) i = f i '' univ :=
begin
  intro, ext u, rw [mem_supp], split,
  { intro h', apply h' _ _ rfl },
  intros h' a' f' e,
  rw [←h _ _ _ _ e.symm], apply h'
end

theorem liftp_iff_of_is_uniform (h : q.is_uniform) {α : typevec n} (x : F α) (p : Π i, α i → Prop) :
  liftp p x ↔ ∀ i (u ∈ supp x i), p i u :=
begin
  rw [liftp_iff, ←abs_repr x],
  cases repr x with a f,  split,
  { rintros ⟨a', f', abseq, hf⟩ u,
    rw [supp_eq_of_is_uniform h, h _ _ _ _ abseq],
    rintros b ⟨i, _, hi⟩, rw ←hi, apply hf },
  intro h',
  refine ⟨a, f, rfl, λ _ i, h' _ _ _⟩,
  rw supp_eq_of_is_uniform h,
  exact ⟨i, mem_univ i, rfl⟩
end

theorem supp_map (h : q.is_uniform) {α β : typevec n} (g : α ⟹ β) (x : F α) (i) :
  supp (g <$$> x) i = g i '' supp x i :=
begin
  rw ←abs_repr x, cases repr x with a f, rw [←abs_map, mvpfunctor.map_eq],
  rw [supp_eq_of_is_uniform h, supp_eq_of_is_uniform h, ← image_comp],
  refl,
end

theorem supp_preservation_iff_uniform :
  q.supp_preservation ↔ q.is_uniform :=
begin
  split,
  { intros h α a a' f f' h' i,
    rw [← mvpfunctor.supp_eq,← mvpfunctor.supp_eq,← h,h',h] },
  { rintros h α ⟨a,f⟩, ext, rwa [supp_eq_of_is_uniform,mvpfunctor.supp_eq], }
end

theorem supp_preservation_iff_liftp_preservation :
  q.supp_preservation ↔ q.liftp_preservation :=
begin
  split; intro h,
  { rintros α p ⟨a,f⟩,
    have h' := h, rw supp_preservation_iff_uniform at h',
    dsimp only [supp_preservation,supp] at h,
    simp only [liftp_iff_of_is_uniform, supp_eq_of_is_uniform, mvpfunctor.liftp_iff', h',
      image_univ, mem_range, exists_imp_distrib],
    split; intros; subst_vars; solve_by_elim },
  { rintros α ⟨a,f⟩,
    simp only [liftp_preservation] at h,
    ext, simp [supp,h] }
end

theorem liftp_preservation_iff_uniform :
  q.liftp_preservation ↔ q.is_uniform :=
by rw [← supp_preservation_iff_liftp_preservation, supp_preservation_iff_uniform]

end mvqpf
