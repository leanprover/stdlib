/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The initial algebra of a multivariate qpf is again a qpf.
-/
import data.pfunctor.indexed.W
import data.qpf.indexed.basic
universes u v

open category_theory.functor.fam (liftp liftr) fam category_theory
open category_theory.functor

namespace iqpf

variables {I J : Type u} {F : fam (I ⊕ J) ⥤ fam J} [q : iqpf F] {α : fam I} {β : fam J}
include q

/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
def recF (g : F.obj (α.append1 β) ⟶ β) : q.P.W α ⟶ β :=
q.P.W_ind (λ j a f' f rec,
  g (abs _ _ ⟨a,fam.split_fun f' rec⟩))

theorem recF_eq (g : F.obj (α.append1 β) ⟶ β)
    {i} (a : q.P.A i) (f' : q.P.drop.B i a ⟶ α) (f : q.P.last.B i a ⟶ q.P.W α) :
  recF g (q.P.W_mk a f' f) =  g (abs _ _ ⟨a, fam.split_fun f' (f ≫ recF g)⟩) :=
by simp only [recF]; rw [ipfunctor.W_ind_eq]; refl

open category_theory.functor.fam

theorem recF_eq' (g : F.obj (α.append1 β) ⟶ β) :
  recF g = q.P.W_dest' ≫ q.P.map (fam.append_fun (𝟙 _) (recF g)) ≫ abs _ _ ≫ g :=
begin
  ext i x : 2,
  apply q.P.W_cases _ _ x,
  intros j a f' f, erw [recF_eq], apply congr_arg (@g _),
  erw [ipfunctor.map_eq',append_fun_comp_split_fun], congr,
  ext : 2, dsimp, rw ipfunctor.W_path_dest_right_W_path_cases_on, cases f x_2; refl,
end

/--
The equivalence on W-types based on the equality of the abstraction function
of the QPF
-/
inductive Wequiv : Π {i}, q.P.W α i → q.P.W α i → Prop
| ind {i} (a : q.P.A i) (f' : q.P.drop.B i a ⟶ α) (f₀ f₁ : q.P.last.B i a ⟶ q.P.W α) :
    (∀ j (x : q.P.last.B i a j), Wequiv ((f₀ : Π j, q.P.last.B i a j → q.P.W α j) x) (f₁ x)) → Wequiv (q.P.W_mk a f' f₀) (q.P.W_mk a f' f₁)
| abs {i} (a₀ : q.P.A i) (f'₀ : q.P.drop.B i a₀ ⟶ α) (f₀ : q.P.last.B i a₀ ⟶ q.P.W α)
          (a₁ : q.P.A i) (f'₁ : q.P.drop.B i a₁ ⟶ α) (f₁ : q.P.last.B i a₁ ⟶ q.P.W α) :
      abs _ _ ⟨a₀, q.P.append_contents f'₀ f₀⟩ = abs _ _ ⟨a₁, q.P.append_contents f'₁ f₁⟩ →
        Wequiv (q.P.W_mk a₀ f'₀ f₀) (q.P.W_mk a₁ f'₁ f₁)
| trans {i} (u v w : q.P.W α i) : Wequiv u v → Wequiv v w → Wequiv u w

open fam

theorem recF_eq_of_Wequiv (α : fam I) {β : fam J} (u : F.obj (α.append1 β) ⟶ β)
    ⦃i⦄ (x y : q.P.W α i) :
  Wequiv x y → recF u x = recF u y :=
begin
  revert i x, refine q.P.W_cases _ ,
  intros i a₀ f'₀ f₀ y,
  revert i y, refine q.P.W_cases _,
  intros i a₁ f'₁ f₁, introv,
  intro h, induction h,
  case iqpf.Wequiv.ind : j a f' f₀ f₁ h ih
  { have : f₀ ≫ recF u = f₁ ≫ recF u, { ext : 2, simp only [ih, ipfunctor.then_def] },
    simp only [recF_eq, this, ih, fam.split_fun_comp] },
  case iqpf.Wequiv.abs : j a₀ f'₀ f₀ a₁ f'₁ f₁ h
    { rw [recF_eq'], simp only [abs_map_assoc, ipfunctor.W_dest'_W_mk, h, ipfunctor.then_def] },
  case iqpf.Wequiv.trans : i x y z e₁ e₂ ih₁ ih₂
    { exact eq.trans ih₁ ih₂ }
end

theorem Wequiv.abs' ⦃i⦄ (x y : q.P.W α i)
    (h : abs _ _ (q.P.W_dest' x) = abs _ _ (q.P.W_dest' y)) :
  Wequiv x y :=
begin
  revert i x h, refine q.P.W_cases _,
  intros i a₀ f'₀ f₀ y,
  revert i y, refine q.P.W_cases _,
  intros i a₁ f'₁ f₁, introv,
  apply Wequiv.abs
end

theorem Wequiv.refl ⦃i⦄ (x : q.P.W α i) : Wequiv x x :=
by apply q.P.W_cases _ _ x; intros i a f' f; exact Wequiv.abs a f' f a f' f rfl

theorem Wequiv.symm ⦃i⦄ (x y : q.P.W α i) : Wequiv x y → Wequiv y x :=
begin
  intro h, induction h,
  case iqpf.Wequiv.ind : i a f' f₀ f₁ h ih
    { exact Wequiv.ind _ _ _ _ ih },
  case iqpf.Wequiv.abs : i a₀ f'₀ f₀ a₁ f'₁ f₁ h
    { exact Wequiv.abs _ _ _ _ _ _ h.symm },
  case iqpf.Wequiv.trans : i x y z e₁ e₂ ih₁ ih₂
    { exact iqpf.Wequiv.trans _ _ _ ih₂ ih₁}
end

/-- maps every element of the W type to a canonical representative -/
def Wrepr : q.P.W α ⟶ q.P.W α := recF (repr _ _ ≫ q.P.W_mk')

theorem Wrepr_W_mk  ⦃i⦄
    (a : q.P.A i) (f' : q.P.drop.B i a ⟶ α) (f : q.P.last.B i a ⟶ q.P.W α) :
  Wrepr (q.P.W_mk a f' f) =
    q.P.W_mk' (repr _ _ (abs _ _ (q.P.map (fam.append_fun (𝟙 _) Wrepr) ⟨a, q.P.append_contents f' f⟩))) :=
by simp only [Wrepr, recF_eq, split_fun_comp_right, ipfunctor.then_def]; refl

theorem Wrepr_equiv ⦃i⦄ (x : q.P.W α i) : Wequiv (Wrepr x) x :=
begin
  apply q.P.W_ind _ _ x, intros i a f' f ih,
  apply Wequiv.trans _ (q.P.W_mk a f' (f ≫ Wrepr)),
  { apply Wequiv.abs',
    rw [Wrepr_W_mk, q.P.W_dest'_W_mk, q.P.W_dest'_W_mk'', abs_repr', ipfunctor.map_eq'],
    congr, erw [← split_fun_comp,category.comp_id], },
  apply Wequiv.ind, exact ih
end

theorem Wequiv_map {α β : fam I} (g : α ⟶ β) ⦃i⦄ (x y : q.P.W α i) :
  Wequiv x y → Wequiv (q.P.W_map g x) (q.P.W_map g y) :=
begin
  intro h, induction h,
  case iqpf.Wequiv.ind : i a f' f₀ f₁ h ih
    { erw [q.P.W_map_W_mk, q.P.W_map_W_mk], apply Wequiv.ind, apply ih },
  case iqpf.Wequiv.abs : j a₀ f'₀ f₀ a₁ f'₁ f₁ h
    { rw [q.P.W_map_W_mk, q.P.W_map_W_mk], apply Wequiv.abs,
      rw [ipfunctor.append_contents_comp, ipfunctor.append_contents_comp, ← ipfunctor.map_eq', ← ipfunctor.map_eq', abs_map', abs_map', h]},
  case iqpf.Wequiv.trans : i x y z e₁ e₂ ih₁ ih₂
    { apply iqpf.Wequiv.trans, apply ih₁, apply ih₂ }
end

/-
Define the fixed point as the quotient of trees under the equivalence relation.
-/

/-- setoid based on Wequiv -/
def W_setoid (α : fam I) (i) : setoid (q.P.W α i) :=
⟨Wequiv, @Wequiv.refl _ _ _ _ _ _, @Wequiv.symm _ _ _ _ _ _, @Wequiv.trans _ _ _ _ _ _⟩

local attribute [instance] W_setoid

/-- least fixed point of a QPF -/
def fix (F : fam (I⊕J) ⥤ fam J) [q : iqpf F] (α : fam I) : fam J
| i := quotient (W_setoid α i : setoid (q.P.W α i))

/-- map of the least fixed point of a QPF -/
def fix.map {α β : fam I} : Π (g : α ⟶ β), fix F α ⟶ fix F β
| g i :=
quotient.lift (λ x : q.P.W α i, ⟦q.P.W_map g x⟧)
  (λ a b h, quot.sound (Wequiv_map _ _ _ h))

section

variable (F)

/-- The least fixed point of a QPF is a functor -/
def pFix : fam I ⥤ fam J :=
{ obj := fix F,
  map := λ X Y f, fix.map f }

end

/--  -/
def fix.lift (f : q.P.W α ⟶ β) (h : ∀ {i} a b : q.P.W α i, Wequiv a b → f a = f b) : (fix F α ⟶ β) :=
λ i x, quot.lift (@f i) h x

/-- Recursor for `fix F α` -/
def fix.rec (g : F.obj (α.append1 β) ⟶ β) : fix F α ⟶ β :=
fix.lift (recF g) (recF_eq_of_Wequiv α g)

/-- Destruct a `fix F α` into its underlying W-type -/
def fix.quot.dest : fix F α ⟶ q.P.W α :=
fix.lift Wrepr (recF_eq_of_Wequiv α (λ i x, q.P.W_mk' (repr _ _ x)))

/-- Construct a `fix F α` from its underlying W-type -/
def fix.quot.mk : q.P.W α ⟶ fix F α :=
λ i (x : q.P.W α i), quot.mk _ x

@[simp, reassoc]
lemma fix.quot.mk_lift {γ : fam J} (g : q.P.W α ⟶ γ)
      (h : ∀ ⦃i : J⦄ (a b : ipfunctor.W (P F) α i), Wequiv a b → g a = g b) :
  fix.quot.mk ≫ fix.lift g h = g :=
by ext; simp only [fix.lift, fix.quot.mk, ipfunctor.then_def]

/-- Constructor for `fix F α` -/
def fix.mk : F.obj (α.append1 (fix F α)) ⟶ fix F α :=
repr _ _ ≫ q.P.map (fam.append_fun (𝟙 _) fix.quot.dest) ≫ q.P.W_mk' ≫ fix.quot.mk

/-- Destructor for `fix F α` -/
def fix.dest : fix F α ⟶ F.obj (α.append1 (fix F α)) :=
fix.rec (F.map $ fam.append_fun (𝟙 _) fix.mk)

lemma fix_to_W_recF (g : F.obj (α.append1 β) ⟶ β) : fix.quot.dest ≫ recF g = fix.rec g :=
by { ext i a : 2, apply quotient.induction_on a, intro x,
     apply recF_eq_of_Wequiv, apply Wrepr_equiv }

@[reassoc]
theorem fix.rec_eq (g : F.obj (α.append1 β) ⟶ β) : -- ⦃i⦄ (x : F.obj (α.append1 (fix F α)) i) :
  fix.mk ≫ fix.rec g = F.map (fam.append_fun (𝟙 _) (fix.rec g)) ≫ g :=
begin
  conv { to_lhs, rw [fix.rec,fix.mk] }, simp only [fix.quot.mk_lift, category.assoc],
  rw [recF_eq', abs_map_assoc, ipfunctor.W_dest'_W_mk'_assoc, abs_map_assoc, abs_repr_assoc,
        ← category_theory.functor.map_comp_assoc,← append_fun_comp, category.id_comp, fix_to_W_recF],
end

theorem fix.ind_aux {i} (a : q.P.A i) (f' : q.P.drop.B _ a ⟶ α) (f : q.P.last.B i a ⟶ q.P.W α) :
  fix.mk (abs _ _ ⟨a, q.P.append_contents f' (λ i x, ⟦f x⟧)⟩) = ⟦q.P.W_mk a f' f⟧ :=
have fix.mk (abs _ _ ⟨a, q.P.append_contents f' (λ i x, ⟦f x⟧)⟩) = ⟦Wrepr (q.P.W_mk a f' f)⟧,
  begin
    apply quot.sound, apply Wequiv.abs',
    rw [ipfunctor.W_dest'_W_mk'', abs_map', abs_repr', ←abs_map', ipfunctor.map_eq'],
    conv { to_rhs, rw [Wrepr_W_mk, q.P.W_dest'_W_mk'', abs_repr', ipfunctor.map_eq'] },
    congr' 2, rw [ipfunctor.append_contents, ipfunctor.append_contents],
    rw [append_fun, append_fun, ←split_fun_comp, ←split_fun_comp],
    reflexivity
  end,
by { rw this, apply quot.sound, apply Wrepr_equiv }

theorem fix.ind_rec {β : fam J} (g₁ g₂ : fix F α ⟶ β)
    (h : ∀ ⦃i⦄ x : unit i ⟶ F.obj (append1 α (fix F α)),
      x ≫ F.map (append_fun (𝟙 _) g₁) = x ≫ F.map (append_fun (𝟙 α) g₂) →
      x ≫ fix.mk ≫ g₁ = x ≫ fix.mk ≫ g₂) :
  g₁ = g₂ :=
begin
  ext i x,
  apply quot.induction_on x, intros x,
  apply q.P.W_ind _ _ x, intros j a f' f ih,
  show g₁ ⟦q.P.W_mk a f' f⟧ = g₂ ⟦q.P.W_mk a f' f⟧,
  rw [←fix.ind_aux a f' f],
  specialize h (value _ ((P F).obj (append1 α (fix F α))) ⟨a,ipfunctor.append_contents _ f' (λ i x, ⟦f x⟧)⟩ ≫ abs _ _) _,
  { replace h := congr_fun (congr_fun h j) unit.rfl, simp [value] at h, exact h },
  ext _ ⟨⟨⟨ rfl ⟩⟩⟩, simp only [value, ipfunctor.append_contents, append_fun, ipfunctor.then_def],
  rw [← abs_map',← abs_map',ipfunctor.map_eq',ipfunctor.map_eq',← split_fun_comp,← split_fun_comp],
  congr' 3, ext, apply ih,
end

theorem fix.rec_unique {β : fam J} (g : F.obj (append1 α β) ⟶ β) (h : fix F α ⟶ β)
    (hyp : fix.mk ≫ h = F.map (append_fun (𝟙 _) h) ≫ g) :
  fix.rec g = h :=
begin
  apply fix.ind_rec,
  intros X x hyp', reassoc hyp',
  rw [hyp, ←hyp', fix.rec_eq]
end

theorem fix.mk_dest : fix.dest ≫ fix.mk = 𝟙 (fix F α) :=
begin
  apply fix.ind_rec,
  rw [fix.dest, fix.rec_eq_assoc, ←category_theory.functor.map_comp_assoc, ←append_fun_comp, category.id_comp, category.comp_id],
  intros X f h, reassoc h,
  rw [h,append_fun_id_id, category_theory.functor.map_id, category.id_comp]
end

theorem fix.dest_mk : fix.mk ≫ fix.dest = 𝟙 (F.obj (append1 α (fix F α))) :=
begin
  unfold fix.dest, rw [fix.rec_eq, ←fix.dest, ←category_theory.functor.map_comp],
  rw [← append_fun_comp, category.id_comp],
  rw [fix.mk_dest, append_fun_id_id, category_theory.functor.map_id]
end

theorem fix.ind {α : fam I} (p : fam.Pred (fix F α))
    (h : ∀ j (x : unit j ⟶ F.obj (α.append1 (fix F α))), liftp (pred_last α p) x → ∀ a, p j (fix.mk $ x a)) :
  ∀ j x, p j x :=
begin
  intros j a,
  apply quot.induction_on a, clear a,
  intro x,
  apply q.P.W_ind _ _ x, clear x j,
  intros i a f' f ih,
  change p _ ⟦q.P.W_mk a f' f⟧,
  rw [←fix.ind_aux a f' f],
  apply h i (value _ _ (abs _ (append1 α (fix F α))
          ⟨a,
           ipfunctor.append_contents (P F) f' (λ (i_1 : J) (x : (ipfunctor.last (P F)).B i a i_1), ⟦f x⟧)⟩))
          _ unit.rfl,
  rw [iqpf.liftp_iff₀],
  rintros k ⟨⟨rfl⟩⟩,
  refine ⟨a, _, rfl, _⟩,
  rintros (i|i) x, { triv },
  dsimp [pred_last],
  apply ih
end

instance iqpf_fix : iqpf (pFix F) :=
{ P         := q.P.Wp,
  abs       := λ α, fix.quot.mk,
  repr      := λ α, fix.quot.dest,
  abs_repr  := by { intros α, ext i x, apply quot.induction_on x, intro a, apply quot.sound, apply Wrepr_equiv },
  abs_map   :=
    begin
      intros α β g, conv { to_rhs, dsimp [pFix,functor.map]},
      ext i x, simp only [fix.map, ipfunctor.then_def],
      apply quot.sound, apply Wequiv.refl
    end }

end iqpf
