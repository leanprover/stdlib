/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Simon Hudon
-/
import data.pfunctor.multivariate.W
import data.qpf.multivariate.basic
universes u v

/-!
# The initial algebra of a multivariate qpf is again a qpf.

For a `(n+1)`-ary QPF `F (α₀,..,αₙ)`, we take the least fixed point of `F` with
regards to its last argument `αₙ`. The result is a `n`-ary functor: `fix F (α₀,..,αₙ₋₁)`.
Making `fix F` into a functor allows us to take the fixed point, compose with other functors
and take a fixed point again.

## Main definitions

 * `fix.mk`     - constructor
 * `fix.dest    - destructor
 * `fix.rec`    - recursor: basis for defining functions by structural recursion on `fix F α`
 * `fix.drec`   - dependent recursor: generalization of `fix.rec` where the result type of the function
                  is allowed to dependent on the `fix F α` value
 * `fix.rec_eq` - defining equation for `recursor`
 * `fix.ind`    - induction principle for `fix F α`

## Implementation notes

For `F` a QPF`, we define `fix F α` in terms of the W-type of the polynomial functor `P` of `F`.
We define the relation `Wequiv` and take its quotient as the definition of `fix F α`.

```lean
inductive Wequiv {α : typevec n} : q.P.W α → q.P.W α → Prop
| ind (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f₀ f₁ : q.P.last.B a → q.P.W α) :
    (∀ x, Wequiv (f₀ x) (f₁ x)) → Wequiv (q.P.W_mk a f' f₀) (q.P.W_mk a f' f₁)
| abs (a₀ : q.P.A) (f'₀ : q.P.drop.B a₀ ⟹ α) (f₀ : q.P.last.B a₀ → q.P.W α)
      (a₁ : q.P.A) (f'₁ : q.P.drop.B a₁ ⟹ α) (f₁ : q.P.last.B a₁ → q.P.W α) :
      abs ⟨a₀, q.P.append_contents f'₀ f₀⟩ = abs ⟨a₁, q.P.append_contents f'₁ f₁⟩ →
        Wequiv (q.P.W_mk a₀ f'₀ f₀) (q.P.W_mk a₁ f'₁ f₁)
| trans (u v w : q.P.W α) : Wequiv u v → Wequiv v w → Wequiv u w
```

See [avigad-carneiro-hudon2019] for more details.

## Reference

 * [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial Functors*][avigad-carneiro-hudon2019]
-/

namespace mvqpf
open typevec
open mvfunctor (liftp liftr)
open_locale mvfunctor

variables {n : ℕ} {F : typevec.{u} (n+1) → Type u} [mvfunctor F] [q : mvqpf F]
include q

/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF {α : typevec n} {β : Type*} (g : F (α.append1 β) → β) : q.P.W α → β :=
q.P.W_rec (λ a f' f rec, g (abs ⟨a, split_fun f' rec⟩))

theorem recF_eq {α : typevec n} {β : Type*} (g : F (α.append1 β) → β)
    (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a → q.P.W α) :
  recF g (q.P.W_mk a f' f) =  g (abs ⟨a, split_fun f' (recF g ∘ f)⟩) :=
by rw [recF, mvpfunctor.W_rec_eq]; refl

theorem recF_eq' {α : typevec n} {β : Type*} (g : F (α.append1 β) → β)
    (x : q.P.W α) :
  recF g x = g (abs ((append_fun id (recF g)) <$$> q.P.W_dest' x)) :=
begin
  apply q.P.W_cases _ x,
  intros a f' f,
  rw [recF_eq, q.P.W_dest'_W_mk, mvpfunctor.map_eq, append_fun_comp_split_fun,
    typevec.id_comp]
end

/-- Equivalence relation on W-types that represent the same `fix F`
value -/
inductive Wequiv {α : typevec n} : q.P.W α → q.P.W α → Prop
| ind (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f₀ f₁ : q.P.last.B a → q.P.W α) :
    (∀ x, Wequiv (f₀ x) (f₁ x)) → Wequiv (q.P.W_mk a f' f₀) (q.P.W_mk a f' f₁)
| abs (a₀ : q.P.A) (f'₀ : q.P.drop.B a₀ ⟹ α) (f₀ : q.P.last.B a₀ → q.P.W α)
      (a₁ : q.P.A) (f'₁ : q.P.drop.B a₁ ⟹ α) (f₁ : q.P.last.B a₁ → q.P.W α) :
      abs ⟨a₀, q.P.append_contents f'₀ f₀⟩ = abs ⟨a₁, q.P.append_contents f'₁ f₁⟩ →
        Wequiv (q.P.W_mk a₀ f'₀ f₀) (q.P.W_mk a₁ f'₁ f₁)
| trans (u v w : q.P.W α) : Wequiv u v → Wequiv v w → Wequiv u w

theorem recF_eq_of_Wequiv (α : typevec n) {β : Type*} (u : F (α.append1 β) → β)
    (x y : q.P.W α) :
  Wequiv x y → recF u x = recF u y :=
begin
  apply q.P.W_cases _ x,
  intros a₀ f'₀ f₀,
  apply q.P.W_cases _ y,
  intros a₁ f'₁ f₁,
  intro h, induction h,
  case mvqpf.Wequiv.ind : a f' f₀ f₁ h ih { simp only [recF_eq, function.comp, ih] },
  case mvqpf.Wequiv.abs : a₀ f'₀ f₀ a₁ f'₁ f₁ h
    { simp only [recF_eq', abs_map, mvpfunctor.W_dest'_W_mk, h] },
  case mvqpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact eq.trans ih₁ ih₂ }
end

theorem Wequiv.abs' {α : typevec n} (x y : q.P.W α)
    (h : abs (q.P.W_dest' x) = abs (q.P.W_dest' y)) :
  Wequiv x y :=
begin
  revert h,
  apply q.P.W_cases _ x,
  intros a₀ f'₀ f₀,
  apply q.P.W_cases _ y,
  intros a₁ f'₁ f₁,
  apply Wequiv.abs
end

theorem Wequiv.refl {α : typevec n} (x : q.P.W α) : Wequiv x x :=
by apply q.P.W_cases _ x; intros a f' f; exact Wequiv.abs a f' f a f' f rfl

theorem Wequiv.symm {α : typevec n} (x y : q.P.W α) : Wequiv x y → Wequiv y x :=
begin
  intro h, induction h,
  case mvqpf.Wequiv.ind : a f' f₀ f₁ h ih
    { exact Wequiv.ind _ _ _ _ ih },
  case mvqpf.Wequiv.abs : a₀ f'₀ f₀ a₁ f'₁ f₁ h
    { exact Wequiv.abs _ _ _ _ _ _ h.symm },
  case mvqpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { exact mvqpf.Wequiv.trans _ _ _ ih₂ ih₁}
end

/-- maps every element of the W type to a canonical representative -/
def Wrepr {α : typevec n} : q.P.W α → q.P.W α := recF (q.P.W_mk' ∘ repr)

theorem Wrepr_W_mk  {α : typevec n}
    (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a → q.P.W α) :
  Wrepr (q.P.W_mk a f' f) =
    q.P.W_mk' (repr (abs ((append_fun id Wrepr) <$$> ⟨a, q.P.append_contents f' f⟩))) :=
by rw [Wrepr, recF_eq', q.P.W_dest'_W_mk]; refl

theorem Wrepr_equiv {α : typevec n} (x : q.P.W α) : Wequiv (Wrepr x) x :=
begin
  apply q.P.W_ind _ x, intros a f' f ih,
  apply Wequiv.trans _ (q.P.W_mk' ((append_fun id Wrepr) <$$> ⟨a, q.P.append_contents f' f⟩)),
  { apply Wequiv.abs',
    rw [Wrepr_W_mk, q.P.W_dest'_W_mk', q.P.W_dest'_W_mk', abs_repr] },
  rw [q.P.map_eq, mvpfunctor.W_mk', append_fun_comp_split_fun, id_comp],
  apply Wequiv.ind, exact ih
end

theorem Wequiv_map {α β : typevec n} (g : α ⟹ β) (x y : q.P.W α) :
  Wequiv x y → Wequiv (g <$$> x) (g <$$> y) :=
begin
  intro h, induction h,
  case mvqpf.Wequiv.ind : a f' f₀ f₁ h ih
    { rw [q.P.W_map_W_mk, q.P.W_map_W_mk], apply Wequiv.ind, apply ih },
  case mvqpf.Wequiv.abs : a₀ f'₀ f₀ a₁ f'₁ f₁ h
    { rw [q.P.W_map_W_mk, q.P.W_map_W_mk], apply Wequiv.abs,
      show abs (q.P.obj_append1 a₀ (g ⊚ f'₀) (λ x, q.P.W_map g (f₀ x))) =
           abs (q.P.obj_append1 a₁ (g ⊚ f'₁) (λ x, q.P.W_map g (f₁ x))),
      rw [←q.P.map_obj_append1, ←q.P.map_obj_append1, abs_map, abs_map, h] },
  case mvqpf.Wequiv.trans : x y z e₁ e₂ ih₁ ih₂
    { apply mvqpf.Wequiv.trans, apply ih₁, apply ih₂ }
end

/--
Define the fixed point as the quotient of trees under the equivalence relation.
-/
def W_setoid (α : typevec n) : setoid (q.P.W α) :=
⟨Wequiv, @Wequiv.refl _ _ _ _ _, @Wequiv.symm _ _ _ _ _, @Wequiv.trans _ _ _ _ _⟩

local attribute [instance] W_setoid

/-- Least fixed point of functor F. The result is a functor with one fewer parameters
than the input. For `F a b c` a ternary functor, fix F is a binary functor such that

```lean
fix F a b = F a b (fix F a b)
```
-/
def fix {n : ℕ} (F : typevec (n+1) → Type*) [mvfunctor F] [q : mvqpf F] (α : typevec n) :=
quotient (W_setoid α : setoid (q.P.W α))

attribute [nolint has_inhabited_instance] fix

/-- `fix F` is a functor -/
def fix.map {α β : typevec n} (g : α ⟹ β) : fix F α → fix F β :=
quotient.lift (λ x : q.P.W α, ⟦q.P.W_map g x⟧)
  (λ a b h, quot.sound (Wequiv_map _ _ _ h))

instance fix.mvfunctor : mvfunctor (fix F) :=
{ map := @fix.map _ _ _ _}

variable {α : typevec.{u} n}

/-- Recursor for `fix F` -/
def fix.rec {β : Type u} (g : F (α ::: β) → β) : fix F α → β :=
quot.lift (recF g) (recF_eq_of_Wequiv α g)

/-- Access W-type underlying `fix F`  -/
def fix_to_W : fix F α → q.P.W α :=
quotient.lift Wrepr (recF_eq_of_Wequiv α (λ x, q.P.W_mk' (repr x)))

/-- Constructor for `fix F` -/
def fix.mk (x : F (append1 α (fix F α))) : fix F α :=
  quot.mk _ (q.P.W_mk' (append_fun id fix_to_W <$$> repr x))

/-- Destructor for `fix F` -/
def fix.dest : fix F α → F (append1 α (fix F α)) :=
fix.rec (mvfunctor.map (append_fun id fix.mk))

theorem fix.rec_eq {β : Type u} (g : F (append1 α β) → β) (x : F (append1 α (fix F α))) :
  fix.rec g (fix.mk x) = g (append_fun id (fix.rec g) <$$> x) :=
have recF g ∘ fix_to_W = fix.rec g,
  by { apply funext, apply quotient.ind, intro x, apply recF_eq_of_Wequiv,
       apply Wrepr_equiv },
begin
  conv { to_lhs, rw [fix.rec, fix.mk], dsimp },
  cases h : repr x with a f,
  rw [mvpfunctor.map_eq, recF_eq', ←mvpfunctor.map_eq, mvpfunctor.W_dest'_W_mk'],
  rw [←mvpfunctor.comp_map, abs_map, ←h, abs_repr, ←append_fun_comp, id_comp, this]
end

theorem fix.ind_aux (a : q.P.A) (f' : q.P.drop.B a ⟹ α) (f : q.P.last.B a → q.P.W α) :
  fix.mk (abs ⟨a, q.P.append_contents f' (λ x, ⟦f x⟧)⟩) = ⟦q.P.W_mk a f' f⟧ :=
have fix.mk (abs ⟨a, q.P.append_contents f' (λ x, ⟦f x⟧)⟩) = ⟦Wrepr (q.P.W_mk a f' f)⟧,
  begin
    apply quot.sound, apply Wequiv.abs',
    rw [mvpfunctor.W_dest'_W_mk', abs_map, abs_repr, ←abs_map, mvpfunctor.map_eq],
    conv { to_rhs, rw [Wrepr_W_mk, q.P.W_dest'_W_mk', abs_repr, mvpfunctor.map_eq] },
    congr' 2, rw [mvpfunctor.append_contents, mvpfunctor.append_contents],
    rw [append_fun, append_fun, ←split_fun_comp, ←split_fun_comp],
    reflexivity
  end,
by { rw this, apply quot.sound, apply Wrepr_equiv }

theorem fix.ind_rec {β : Type*} (g₁ g₂ : fix F α → β)
    (h : ∀ x : F (append1 α (fix F α)),
      (append_fun id g₁) <$$> x = (append_fun id g₂) <$$> x → g₁ (fix.mk x) = g₂ (fix.mk x)) :
  ∀ x, g₁ x = g₂ x :=
begin
  apply quot.ind,
  intro x,
  apply q.P.W_ind _ x, intros a f' f ih,
  show g₁ ⟦q.P.W_mk a f' f⟧ = g₂ ⟦q.P.W_mk a f' f⟧,
  rw [←fix.ind_aux a f' f], apply h,
  rw [←abs_map, ←abs_map, mvpfunctor.map_eq, mvpfunctor.map_eq],
  congr' 2,
  rw [mvpfunctor.append_contents, append_fun, append_fun, ←split_fun_comp, ←split_fun_comp],
  have : g₁ ∘ (λ x, ⟦f x⟧) = g₂ ∘ (λ x, ⟦f x⟧),
  { ext x, exact ih x },
  rw this
end

theorem fix.rec_unique {β : Type*} (g : F (append1 α β) → β) (h : fix F α → β)
    (hyp : ∀ x, h (fix.mk x) = g (append_fun id h <$$> x)) :
  fix.rec g = h :=
begin
  ext x,
  apply fix.ind_rec,
  intros x hyp',
  rw [hyp, ←hyp', fix.rec_eq]
end

theorem fix.mk_dest (x : fix F α) : fix.mk (fix.dest x) = x :=
begin
  change (fix.mk ∘ fix.dest) x = x,
  apply fix.ind_rec,
  intro x, dsimp,
  rw [fix.dest, fix.rec_eq, ←comp_map, ←append_fun_comp, id_comp],
  intro h, rw h,
  show fix.mk (append_fun id id <$$> x) = fix.mk x,
  rw [append_fun_id_id, mvfunctor.id_map]
end

theorem fix.dest_mk (x : F (append1 α (fix F α))) : fix.dest (fix.mk x) = x :=
begin
  unfold fix.dest, rw [fix.rec_eq, ←fix.dest, ←comp_map],
  conv { to_rhs, rw ←(mvfunctor.id_map x) },
  rw [←append_fun_comp, id_comp],
  have : fix.mk ∘ fix.dest = id, {ext x, apply fix.mk_dest },
  rw [this, append_fun_id_id]
end

theorem fix.ind {α : typevec n} (p : fix F α → Prop)
    (h : ∀ x : F (α.append1 (fix F α)), liftp (pred_last α p) x → p (fix.mk x)) :
  ∀ x, p x :=
begin
  apply quot.ind,
  intro x,
  apply q.P.W_ind _ x, intros a f' f ih,
  change p ⟦q.P.W_mk a f' f⟧,
  rw [←fix.ind_aux a f' f],
  apply h,
  rw mvqpf.liftp_iff,
  refine ⟨_, _, rfl, _⟩,
  intros i j,
  cases i,
  { apply ih },
  { triv },
end

instance mvqpf_fix : mvqpf (fix F) :=
{ P         := q.P.Wp,
  abs       := λ α, quot.mk Wequiv,
  repr      := λ α, fix_to_W,
  abs_repr  := by { intros α, apply quot.ind, intro a, apply quot.sound, apply Wrepr_equiv },
  abs_map   :=
    begin
      intros α β g x, conv { to_rhs, dsimp [mvfunctor.map]},
      rw fix.map, apply quot.sound,
      apply Wequiv.refl
    end }

/-- Dependent recursor for `fix F` -/
def fix.drec {β : fix F α → Type u} (g : Π x : F (α ::: sigma β), β (fix.mk $ (id ::: sigma.fst) <$$> x)) (x : fix F α) : β x :=
let y := @fix.rec _ F _ _ α (sigma β) (λ i, ⟨_,g i⟩) x in
have x = y.1,
  by { symmetry, dsimp [y], apply fix.ind_rec _ id _ x, intros x' ih,
       rw fix.rec_eq, dsimp, simp [append_fun_id_id] at ih,
       congr, conv { to_rhs, rw [← ih] }, rw [mvfunctor.map_map,← append_fun_comp,id_comp], },
cast (by rw this) y.2

end mvqpf
