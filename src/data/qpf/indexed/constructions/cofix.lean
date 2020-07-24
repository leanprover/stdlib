/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

The initial algebra of a multivariate qpf is again a qpf.
-/
import data.pfunctor.indexed.M
import data.qpf.indexed.basic
import data.prod

universe u

namespace iqpf

open category_theory.functor.fam (liftp liftr) fam category_theory

variables {I J : Type u} {F : fam (I⊕J) ⥤ fam J} [q : iqpf F]
include q

/-- Corecursor for the M-type of `F` using `F` for the shape of the computation -/
def corecF {α : fam I} {β : fam J} (g : β ⟶ F.obj (α.append1 β)) : β ⟶ q.P.M α :=
q.P.M_corec (g ≫ repr _ _)

@[reassoc]
theorem corecF_eq {α : fam I} {β : fam J} (g : β ⟶ F.obj (α.append1 β)) :
  corecF g ≫ q.P.M_dest = g ≫ repr _ _ ≫ q.P.map (append_fun (𝟙 _) (corecF g)) :=
by rw [corecF, q.P.M_dest_corec'', category.assoc]

/-- A pre-congruence on q.P.M *viewed as an F-coalgebra*. Not necessarily symmetric. -/
def is_precongr {α : fam I} (r : fam.Pred (q.P.M α ⊗ q.P.M α)) : Prop :=
  ∀ ⦃i⦄ ⦃x : unit i ⟶ q.P.M α ⊗ q.P.M α⦄, x ⊨ r →
    x ≫ fam.prod.fst ≫ q.P.M_dest ≫ q.P.map (append_fun (𝟙 _) (fam.quot.mk r)) ≫ abs _ _ =
    x ≫ fam.prod.snd ≫ q.P.M_dest ≫ q.P.map (append_fun (𝟙 _) (fam.quot.mk r)) ≫ abs _ _

section
variables F

/-- The maximal congruence on q.P.M -/
def Mcongr (α : fam I) : Pred (q.P.M α ⊗ q.P.M α) :=
λ i x, ∃ r : Pred (q.P.M α ⊗ q.P.M α), is_precongr r ∧ r i x

end

/-- Convert a witness of a pre-congruence relation into a witness of the Mcongr
relation -/
def mk_Mcongr {α : fam I} (r : fam.Pred (q.P.M α ⊗ q.P.M α)) (hr : is_precongr r) :
  subtype r ⟶ subtype (Mcongr F α) :=
λ i ⟨x,h⟩, ⟨x,r,hr,h⟩

@[simp, reassoc]
lemma mk_Mcongr_val  {α : fam I} (r : fam.Pred (q.P.M α ⊗ q.P.M α)) (hr : is_precongr r) :
  mk_Mcongr r hr ≫ fam.subtype.val = fam.subtype.val :=
by ext _ ⟨ ⟩ : 2; refl

lemma Mcongr_intro {α : fam I} (r : fam.Pred (q.P.M α ⊗ q.P.M α)) (hr : is_precongr r)
  {X} {f : X ⟶ q.P.M α ⊗ q.P.M α} :
  f ⊨ r → f ⊨ Mcongr F α
| ⟨g,h⟩ := ⟨g ≫ mk_Mcongr _ hr, by rw [category.assoc,mk_Mcongr_val,h] ⟩

/-- The greatest fixed point of functor `F` -/
def cofix (F : fam (I ⊕ J) ⥤ fam J) [q : iqpf F] (α : fam I) : fam J :=
fam.quot (Mcongr F α)

lemma Mcongr_elim {α : fam I} {j} (a : unit j ⟶ q.P.M α ⊗ q.P.M α) (h : a ⊨ Mcongr F α) :
  ∃ r, is_precongr r ∧ a ⊨ r :=
begin
  cases h with a' h,
  have : psigma _ := classical.indefinite_description' _ (a' (fam.unit.star j)).2,
  rcases this with ⟨r,hr,hr'⟩,
  existsi [r,hr],
  existsi [fam.value j _ $ subtype.mk _ hr'],
  rw h, ext i ⟨ ⟨ rfl ⟩ ⟩ : 2, refl
end

lemma exists_precongr {α : fam I} {j} (a : unit j ⟶ subtype (Mcongr F α)) :
  ∃ r hr x, x ≫ mk_Mcongr r hr = a :=
begin
  have := Mcongr_elim (a ≫ fam.subtype.val) _,
  { rcases this with ⟨r,hr,a',hr'⟩,
    existsi [r,hr,a'], apply fam.subtype.ext,
    rw [hr',category.assoc], congr,
    ext _ ⟨ ⟩ : 2, refl },
  refine ⟨a,rfl⟩,
end

/-- `map` on `cofix F α` -/
def cofix.map ⦃α β : fam I⦄ (g : α ⟶ β) : cofix F α ⟶ cofix F β :=
fam.quot.lift _ (q.P.Mp.map g ≫ fam.quot.mk (Mcongr F β))
  begin
    rintros i a ⟨a',ha⟩,
    have := @fam.quot.sound _ _ _ (Mcongr F β) (a ≫ fam.prod.map (ipfunctor.map (ipfunctor.Mp (P F)) g) (ipfunctor.map (ipfunctor.Mp (P F)) g)) _,
    { simp at this, exact this },
    let map := fam.prod.map (q.P.Mp.map g) (q.P.Mp.map g),
    existsi a' ≫ fam.subtype.map _ _ map _,
    { rw [category.assoc,subtype.map_val,ha,category.assoc], },
    dsimp [Mcongr],
    rintros i x ⟨r,h,h'⟩,
    let r' : Pred (q.P.M β ⊗ q.P.M β) := λ i b, ∃ a : (subtype r) i,
        (fam.subtype.val ≫ map) a = b,
    existsi [r',_],
    { dsimp [r'], existsi subtype.mk x h', refl },
    { rintros j b ⟨c,hr'⟩,
      let u : quot r ⟶ quot r' := fam.quot.lift r (q.P.Mp.map g ≫ fam.quot.mk _)
        (by { intros, repeat { rw ← category.assoc },
              apply fam.quot.sound', apply sat_intro,
              rintro i x, simp [(≫),(∘),fam.prod.map,r',diag],
              existsi ((a_1 x).1,(a_1 x).2),
              have := sat_elim _ _ a_2 x,
              cases z : (a_1 x), rw z at this,
              existsi [this], refl }),
      have hu : q.P.Mp.map g ≫ fam.quot.mk r' = fam.quot.mk r ≫ u,
      { ext, refl },
      have hh : ∃ k, k ≫ fam.subtype.val ≫ map = b,
      { let k : unit j ⟶ subtype r := λ i y, (classical.some (c y).2),
        existsi k, rw hr', ext j y : 2, refine classical.some_spec (c y).2, },
      cases hh with k hh,
      rw [← hh], simp [map,ipfunctor.M_dest_map_assoc],
      have hh' : k ≫ fam.subtype.val ⊨ r,
      { existsi k, refl, },
      clear_except hh' hu h,
      specialize h hh', reassoc! h,
      rw [← functor.map_comp,← append_fun_comp,hu,category.comp_id,← category.id_comp g,append_fun_comp,functor.map_comp,← abs_map_assoc,h] },
  end

/-- Corecursor for `cofix F α` -/
def cofix.corec {α : fam I} {β : fam J} (g : β ⟶ F.obj (α.append1 β)) : β ⟶ cofix F α :=
corecF g ≫ fam.quot.mk _

/-- Destructor for `cofix F α` -/
def cofix.dest {α : fam I} : cofix F α ⟶ F.obj (α.append1 (cofix F α)) :=
fam.quot.lift _ (q.P.M_dest ≫ abs _ _ ≫ F.map (append_fun (𝟙 _) (fam.quot.mk _)))
begin
  rintros i a h,
  obtain ⟨r,hr,hr'⟩ := Mcongr_elim _ h,
  have : ∀ i (f : unit i ⟶ ipfunctor.M (P F) α ⊗ ipfunctor.M (P F) α), f ⊨ r → f ⊨ Mcongr F α,
  { rintros i f ⟨a, h⟩, refine ⟨a ≫ mk_Mcongr _ hr,_⟩,
    simp [h], },
  rw ← quot.indexed.factor_mk_eq _ _ this,
  specialize hr hr', reassoc! hr,
    conv { to_lhs,
      rw [append_fun_comp_right, functor.map_comp, ←abs_map_assoc, hr, abs_map_assoc,
         ←functor.map_comp, ← append_fun_comp_right] },
end

/-- Corecursor with escape hatch for `cofix F α`. The escape hatch allows
a corecursive computation to yield a fully formed value rather than a
recursive call embedded in a constructor application -/
def cofix.corec' {α : fam I} {β : fam J} (g : β ⟶ F.obj (α.append1 (cofix F α ⊕' β))) : β ⟶ cofix F α :=
fam.sum.inr ≫ cofix.corec (fam.sum.map (cofix.dest ≫ F.map (append_fun (𝟙 _) fam.sum.inl)) g ≫ codiag)

@[reassoc]
theorem cofix.dest_corec {α : fam I} {β : fam J} (g : β ⟶ F.obj (α.append1 β)) :
  cofix.corec g ≫ cofix.dest = g ≫ F.map (append_fun (𝟙 _) (cofix.corec g)) :=
begin
  conv { to_lhs, rw [cofix.dest, cofix.corec] }, dsimp [cofix.corec],
  simp,
  rw [corecF_eq_assoc, abs_map_assoc, abs_repr_assoc, ←functor.map_comp, ←append_fun_comp_right]
end

/-- Constructor for `cofix F α` -/
def cofix.mk {α : fam I} : F.obj (α.append1 $ cofix F α) ⟶ cofix F α :=
cofix.corec $ F.map $ append_fun (𝟙 _) cofix.dest

section eq
omit q
lemma eq_refl {α : fam I} : diag ⊨ fam.eq α :=
sat_intro _ _ $ λ i a, rfl

lemma fst_eq_snd_of_sat_eq {α β : fam I} (x : α ⟶ β ⊗ β) (h : x ⊨ fam.eq _) :
  x ≫ fam.prod.fst = x ≫ fam.prod.snd :=
by ext i a; apply sat_elim _ _ h

@[simp, reassoc]
lemma map_swap {α α' β β' : fam I} (f : α ⟶ β) (f' : α' ⟶ β') :
  (f ⊗ f') ≫ fam.quot.prod.swap = fam.quot.prod.swap ≫ (f' ⊗ f) :=
by apply fam.prod.ext; simp

@[simp, reassoc]
lemma diag_swap {α : fam I} :
  diag ≫ fam.quot.prod.swap = (diag : α ⟶ _) :=
by apply fam.prod.ext; simp

@[simp, reassoc]
lemma swap_swap {α β : fam I} :
  fam.quot.prod.swap ≫ fam.quot.prod.swap = 𝟙 (α ⊗ β) :=
by apply fam.prod.ext; simp

/-- Convert a quotient around `r` into one around the
inverse relation of `r` -/
def quot_swap {α : fam I} (r : Pred (α ⊗ α)) :
  fam.quot r ⟶ fam.quot (r.map fam.quot.prod.swap) :=
fam.quot.lift _ (fam.quot.mk _) (λ i x h, eq.symm $
  fam.quot.sound'' (x ≫ fam.prod.snd) (x ≫ fam.prod.fst)
    (sat_map₀ _ _ _ (by simp [diag_map_comp,diag_map_fst_snd,h]))
    (by simp) (by simp))

@[simp]
lemma quot_mk_map_swap {α : fam I} {r : Pred (α ⊗ α)} :
  fam.quot.mk (r.map fam.quot.prod.swap) = fam.quot.mk r ≫ quot_swap _ :=
by dunfold quot_swap; simp

section rel

variables {α β γ : fam I} (r r' : Pred (α ⊗ α)) (r₀ : Pred (α ⊗ β)) (r₁ : Pred (β ⊗ γ))
open relation function

/-- Transitive closure of a relation defined as a `Pred (α ⊗ α)` -/
def trans : Pred (α ⊗ α) :=
λ i x, trans_gen (curry $ r i) x.1 x.2

/-- Union of two relations defined as a `Pred (α ⊗ α)` -/
def union : Pred (α ⊗ α) :=
λ i x, r _ x ∨ r' _ x

/-- Relational composition of two relations defined as a `Pred (α ⊗ α)` -/
def rcomp : Pred (α ⊗ γ) :=
λ i x, ∃ z, r₀ i (x.1, z) ∧ r₁ i (z, x.2)

infix ` ≫ᵣ `:80 := rcomp
infix ` ∪ᵣ `:70 := union

variables {r₀ r₁ r r'}

lemma trans_base {X} {x : X ⟶ α ⊗ α} (h : x ⊨ r) : x ⊨ trans r :=
sat_intro _ _ $ λ i y, trans_gen.single $ match x y, sat_elim _ _ h y with
                                          | (a,b), h := h
                                          end

lemma unionl {X} {x : X ⟶ α ⊗ α} (h : x ⊨ r) : x ⊨ union r r' :=
sat_intro _ _ $ λ i y, or.inl $ sat_elim _ _ h y

lemma unionr {X} {x : X ⟶ α ⊗ α} (h : x ⊨ r') : x ⊨ union r r' :=
sat_intro _ _ $ λ i y, or.inr $ sat_elim _ _ h y

lemma rcomp_intro {X} {x : X ⟶ α ⊗ β ⊗ γ} (h₀ : x ≫ quot.lpair ⊨ r₀) (h₁ : x ≫ quot.rpair ⊨ r₁) :
  x ≫ quot.sides ⊨ r₀ ≫ᵣ r₁ :=
sat_intro _ _ $ λ i y, ⟨(x y).fst.snd,
  by cases h : x y with a c; cases a with a b;
     split; [convert sat_elim _ _ h₀ y,convert sat_elim _ _ h₁ y];
     simp [quot.sides,fam.prod.fst,fam.prod.snd,fam.prod.map,h,quot.lpair]⟩

lemma sat_trans_ind {i} {x : unit i ⟶ α ⊗ α} {C : (unit i ⟶ α ⊗ α) → Prop} (h : x ⊨ trans r)
  (h₀ : x ⊨ r → C x)
  (h₁ : ∀ y : (unit i ⟶ α ⊗ α ⊗ α), y ≫ fam.prod.fst ⊨ trans r → y ≫ (fam.prod.snd ⊗ 𝟙 _) ⊨ trans r → C (y ≫ (fam.prod.fst ⊗ 𝟙 _))) :
  C x :=
begin
  replace h := sat_elim _ _ h unit.rfl,
  cases h,
  case relation.trans_gen.single :
  { apply h₀, apply sat_intro, rintro _ ⟨ ⟩, simp [curry] at h_a, exact h_a },
  case relation.trans_gen.tail : z
  { specialize h₁ (value i _ (((x unit.rfl).1, z), (x unit.rfl).2 )) _ _,
    convert h₁, ext _ ⟨ ⟩; refl,
    { apply sat_intro, rintro _ ⟨ ⟩, apply h_a, },
    { apply sat_intro, rintro _ ⟨ ⟩, apply trans_gen.single h_a_1 } }
end

lemma sat_union_ind {i} {x : unit i ⟶ α ⊗ α} {C : (unit i ⟶ α ⊗ α) → Prop} (h : x ⊨ union r r')
  (h₀ : x ⊨ r → C x)
  (h₁ : x ⊨ r' → C x) :
  C x :=
begin
  replace h := sat_elim _ _ h unit.rfl, cases h; [apply h₀, apply h₁];
  apply sat_intro; rintro _ ⟨ ⟩; exact h
end

lemma sat_rcomp_ind {i} {x : unit i ⟶ α ⊗ γ} {C : (unit i ⟶ α ⊗ γ) → Prop} (h : x ⊨ (r₀ ≫ᵣ r₁))
  (h' : ∀ y : unit i ⟶ α ⊗ β ⊗ γ, y ≫ fam.prod.fst ⊨ r₀ → y ≫ (fam.prod.snd ⊗ 𝟙 _) ⊨ r₁ → C (y ≫ (fam.prod.fst ⊗ 𝟙 _))) :
  C x :=
begin
  replace h := sat_elim _ _ h unit.rfl, dsimp [(≫ᵣ)] at h,
  rcases h with ⟨z, h₀, h₁⟩, specialize h' (diag ≫ (diag ⊗ 𝟙 _) ≫ (x ≫ fam.prod.fst ⊗ value i _ z ⊗ x ≫ fam.prod.snd)) _ _,
  { convert h', apply fam.prod.ext; simp, },
  all_goals { simp, apply sat_intro, rintro _ ⟨ ⟩, simp [diag], assumption }
end

attribute [simp] diag_map diag_map_assoc diag_map_comp diag_map_comp_assoc
                 diag_map_fst_snd diag_map_fst_snd_assoc diag_map_fst_snd_comp diag_map_fst_snd_comp_assoc

/-- Middle introduction into a union of relations -/
def quot_rcompl' : fam.quot r ⟶ fam.quot (r ≫ᵣ r' ∪ᵣ r ∪ᵣ r') :=
fam.quot.lift _ (fam.quot.mk _) $ λ i x h,
  fam.quot.sound _ (unionl $ unionr h)

/-- Right introduction into a union of relations -/
def quot_rcompr' : fam.quot r' ⟶ fam.quot (r ≫ᵣ r' ∪ᵣ r ∪ᵣ r') :=
fam.quot.lift _ (fam.quot.mk _) $ λ i x h,
  fam.quot.sound _ (unionr h)

lemma quot_mk_rcompr' : fam.quot.mk (r ≫ᵣ r' ∪ᵣ r ∪ᵣ r') = fam.quot.mk r' ≫ quot_rcompr' :=
by dunfold quot_rcompr'; simp

lemma quot_mk_rcompl' : fam.quot.mk (r ≫ᵣ r' ∪ᵣ r ∪ᵣ r') = fam.quot.mk r ≫ quot_rcompl' :=
by dunfold quot_rcompl'; simp

/-- Left introduction into the transitive closure of a relation -/
def quot_trans_unionl : fam.quot r ⟶ fam.quot (trans $ union r r') :=
fam.quot.lift _ (fam.quot.mk _) (λ i x h,
  fam.quot.sound'' (x ≫ fam.prod.fst) (x ≫ fam.prod.snd) (trans_base (unionl (by simp *))) (by simp) (by simp))

/-- Right introduction into the transitive closure of a relation -/
def quot_trans_unionr : fam.quot r' ⟶ fam.quot (trans $ union r r') :=
fam.quot.lift _ (fam.quot.mk _) (λ i x h,
  fam.quot.sound'' (x ≫ fam.prod.fst) (x ≫ fam.prod.snd) (trans_base (unionr (by simp *))) (by simp) (by simp))

lemma quot_mk_trans_unionl : fam.quot.mk (trans $ union r r') = fam.quot.mk r ≫ quot_trans_unionl :=
by dunfold quot_trans_unionl; simp

lemma quot_mk_trans_unionr : fam.quot.mk (trans $ union r r') = fam.quot.mk r' ≫ quot_trans_unionr :=
by dunfold quot_trans_unionr; simp

end rel

end eq

lemma eq_is_precongr {α : fam I} : is_precongr (fam.eq (q.P.M α)) :=
begin
  intros i a h, replace h := fst_eq_snd_of_sat_eq _ h,
  reassoc h, rw h,
end

example {I J : Type u} {F : fam (I ⊕ J) ⥤ fam J} [q : iqpf F] {α : fam I}
  {i : J}
  (f : unit i ⟶ ipfunctor.M (P F) α ⊗ ipfunctor.M (P F) α ⊗ ipfunctor.M (P F) α)
  (r₀ : Pred (ipfunctor.M (P F) α ⊗ ipfunctor.M (P F) α)) (ha₀ : is_precongr r₀)
  (hb₀ : f ≫ quot.lpair ⊨ r₀)
  (r₁ : Pred (ipfunctor.M (P F) α ⊗ ipfunctor.M (P F) α)) (ha₁ : is_precongr r₁)
  (hb₁ : f ≫ quot.rpair ⊨ r₁) :
  f ≫ quot.sides ⊨ r₀ ≫ᵣ r₁ :=
begin
  apply rcomp_intro; assumption,
end

lemma Mcongr_eqv {α} : fam.quot.equiv (Mcongr F α) :=
{ refl := Mcongr_intro (fam.eq _) eq_is_precongr eq_refl,
  symm := by { introv h, replace h := Mcongr_elim f h, rcases h with ⟨r,h,h'⟩,
               apply Mcongr_intro (r.map quot.prod.swap),
               { intros j a h'', replace h'' := sat_map₁ _ _ _ h'',
                 specialize h h'', simp only [abs_map, quot.prod.swap_snd_assoc, quot.prod.swap_fst_assoc, category.assoc] at h, reassoc! h,
                 simp only [h, append_fun_comp_right, iqpf.quot_mk_map_swap, iqpf.abs_map, category_theory.functor.map_comp] },
               { apply sat_map₀, simp only [h', category_theory.category.comp_id, iqpf.swap_swap, category_theory.category.assoc], } },
  trans := by { introv h₀ h₁, rcases Mcongr_elim _ h₀ with ⟨r₀,ha₀,hb₀⟩,
                rcases Mcongr_elim _ h₁ with ⟨r₁,ha₁,hb₁⟩, clear h₀ h₁,
                apply Mcongr_intro (r₀ ≫ᵣ r₁ ∪ᵣ r₀ ∪ᵣ r₁),
                { intros i a h, apply iqpf.sat_union_ind h,
                  clear h, intro h, apply iqpf.sat_union_ind h,
                  clear h, intro h, apply iqpf.sat_rcomp_ind h,
                  { introv hy₀ hy₁,
                    specialize ha₀ hy₀, simp only [abs_map, category.assoc] at ha₀, reassoc! ha₀,
                    specialize ha₁ hy₁, simp only [prod.map_fst_assoc, abs_map, prod.map_snd_assoc, category.id_comp, category.assoc] at ha₁, reassoc! ha₁,
                    conv { to_lhs, rw [quot_mk_rcompl',append_fun_comp_right], },
                    conv { to_rhs, rw [quot_mk_rcompr',append_fun_comp_right], },
                    simp only [ha₀, prod.map_fst_assoc, abs_map, prod.map_snd_assoc, category.id_comp, functor.map_comp, category.assoc], rw ← ha₁, clear ha₀ ha₁,
                    rw [← functor.map_comp,← functor.map_comp,← append_fun_comp_right,← append_fun_comp_right],
                    rw [← quot_mk_rcompl',← quot_mk_rcompr'] },
                  { clear h, intro hr,
                    specialize ha₀ hr, simp only [abs_map] at ha₀, reassoc! ha₀,
                    rw [quot_mk_rcompl',append_fun_comp_right],
                    simp only [ha₀, iqpf.abs_map, category_theory.functor.map_comp] },
                  { clear h, intro hr,
                    specialize ha₁ hr, simp only [abs_map] at ha₁, reassoc! ha₁,
                    rw [quot_mk_rcompr',append_fun_comp_right],
                    simp only [ha₁, iqpf.abs_map, category_theory.functor.map_comp], } },
                { apply unionl, apply unionl,
                  apply rcomp_intro; assumption } } }

section

omit q

variables {α β γ : fam I} {r : Pred (γ ⊗ γ)} {f : β ⟶ γ} {g g' : α ⟶ β}

lemma foo''
  (h : g ≫ f = g' ≫ f)
  (h' : diag ⊨ r) :
  g ≫ fam.quot.mk (r.map $ f ⊗ f) = g' ≫ fam.quot.mk (r.map $ f ⊗ f) :=
begin
  apply fam.quot.sound', apply sat_map₀, simp [h,h'],
  apply comp_sat _ _ _ (comp_sat _ _ _ h'),
end

end

private theorem cofix.bisim_aux {α : fam I}
    (r : Pred (cofix F α ⊗ cofix F α))
    (h' : diag ⊨ r)
    (h : ∀ {i} x : unit i ⟶ cofix F α ⊗ cofix F α, x ⊨ r →
               x ≫ fam.prod.fst ≫ cofix.dest ≫ F.map (append_fun (𝟙 _) (fam.quot.mk r)) =
               x ≫ fam.prod.snd ≫ cofix.dest ≫ F.map (append_fun (𝟙 _) (fam.quot.mk r)))
  {X} (x y : X ⟶ cofix F α) (h₀ : diag ≫ (x ⊗ y) ⊨ r) :
  x = y :=
begin
  cases quot.ind_on x with x₀ hx₀,
  cases quot.ind_on y with x₁ hx₁,
  rw [hx₀,hx₁], apply fam.quot.sound',
  let map := (fam.prod.map (fam.quot.mk (Mcongr F α)) (fam.quot.mk (Mcongr F α))),
  let r' := r.map map,
  have : is_precongr r',
  { intros _ _ h'',
    replace h := h _ (sat_map₁ _ _ _ h''),
    simp [cofix.dest] at h,
    rw [← functor.map_comp, ← abs_map,← append_fun_comp_right] at h,
    let f := fam.quot.lift r (fam.quot.lift (Mcongr F α) (fam.quot.mk $ r.map map) _) _,
    show ∀ {i : J} (a : unit i ⟶ ipfunctor.M (P F) α ⊗ ipfunctor.M (P F) α),
              a ⊨ Mcongr F α →
               a ≫ fam.prod.fst ≫ fam.quot.mk (r.map map) =
               a ≫ fam.prod.snd ≫ fam.quot.mk (r.map map),
    { intros j a ha, rw [← category.assoc,← category.assoc],
      apply foo'', -- rw [← category.assoc,← category.assoc], congr' 1,
      apply fam.quot.sound'' (a ≫ fam.prod.fst) (a ≫ fam.prod.snd),
      { simp [diag_map_comp,diag_map_fst_snd,ha] },
      all_goals { simp * } },
    swap,
    { intros j a ha,
      apply fam.quot.sound'' (a ≫ fam.prod.fst ≫ fam.quot.out _) (a ≫ fam.prod.snd ≫ fam.quot.out _),
      { apply sat_map₀, simp [map,diag_map_comp,diag_map_fst_snd_comp],
        erw [prod.map_id,category.comp_id], exact ha },
      all_goals { simp, rw quot.lift_eq_out, apply Mcongr_eqv, } },
    have d : fam.quot.mk _ ≫ fam.quot.mk r ≫ f = fam.quot.mk (r.map map),
    { simp [f], },
    dsimp [r'], rw ← d,
    { reassoc h,
      conv in (append_fun _ _) { rw [← category.assoc,append_fun_comp_right] },
      rw [ipfunctor.map_comp,category.assoc,abs_map,h], clear_except, congr' 3,
      rw [← abs_map,← ipfunctor.map_comp_assoc, ← append_fun_comp_right], refl } },
  apply Mcongr_intro _ this,
  apply sat_map₀,
  simp [hx₀.symm,hx₁.symm,h₀],
end

section

omit q
lemma sat_eq_elim {α β : fam I} (x : α ⟶ β ⊗ β) (h : x ⊨ fam.eq _) :
  x ≫ fam.prod.fst = x ≫ fam.prod.snd :=
by ext; simp [fam.prod.fst,fam.prod.snd];
   have := sat_elim _ _ h;
   simp [fam.eq] at this; rw this

end

theorem cofix.bisim_rel {α : fam I}
    (r : Pred $ cofix F α ⊗ cofix F α)
    (h : ∀ {i} x : unit i ⟶ cofix F α ⊗ cofix F α, x ⊨ r →
      x ≫ fam.prod.fst ≫ cofix.dest ≫ F.map (append_fun (𝟙 _) (fam.quot.mk r)) =
      x ≫ fam.prod.snd ≫ cofix.dest ≫ F.map (append_fun (𝟙 _) (fam.quot.mk r))) :
  ∀ {X} x y : X ⟶ cofix F α, diag ≫ (x ⊗ y) ⊨ r → x = y :=
let r' := fam.eq _ ∪ᵣ r  in
begin
  intros X x y rxy,
  apply cofix.bisim_aux r',
  { apply unionl, apply eq_refl },
  { intros j y r'y,
    apply sat_union_ind r'y, intro hr,
    { replace hr := sat_eq_elim _ hr, reassoc hr, rw hr, },
    { intro hr,
      have : ∀ (i : J) (a : unit i ⟶ cofix F α ⊗ cofix F α), a ⊨ r → a ⊨ r',
      { introv h, apply unionr h },
      rw ←quot.indexed.factor_mk_eq r r' this,
      specialize h _ hr, reassoc! h,
      rw [append_fun_comp_right,functor.map_comp,h], } },
  { apply unionr rxy }
end

open category_theory.functor

theorem cofix.bisim {α : fam I}
    (r : Pred $ cofix F α ⊗ cofix F α)
    (h : ∀ {i} x : unit i ⟶ cofix F α ⊗ cofix F α, x ⊨ r  →
           liftr (fam.rel_last α r) (x ≫ fam.prod.fst ≫ cofix.dest) (x ≫ fam.prod.snd ≫ cofix.dest)) :
  ∀ {X} x y : X ⟶ cofix F α, diag ≫ (x ⊗ y) ⊨ r → x = y :=
begin
  intros x y,
  apply cofix.bisim_rel,
  intros i x rxy,
  have := (liftr_iff₀' (fam.rel_last α r) _ _).mp (h x rxy),
  rcases (liftr_iff₀' (fam.rel_last α r) _ _).mp (h x rxy)  with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩,
  reassoc! dxeq, reassoc! dyeq,
  rw [dxeq, dyeq, ← abs_map, ipfunctor.map_eq_assoc, ipfunctor.map_eq_assoc],
  rw [←split_drop_fun_last_fun f₀, ←split_drop_fun_last_fun f₁],
  rw [fam.append_fun_comp_split_fun, fam.append_fun_comp_split_fun],
  erw [category.comp_id, category.comp_id],
  congr' 3, ext i j, cases i with _ i; simp [split_fun],
  { apply h' _ j },
  apply quot.sound,
  apply h' _ j
end

open function

theorem cofix.bisim' {α : fam I} {β : fam J} (Q : Pred β) (u v : β ⟶ cofix F α) {i}
    (h : ∀ {i} (x : unit i ⟶ β), x ⊨ Q → ∃ a f' f₀ f₁,
      x ≫ u ≫ cofix.dest = value i (q.P.obj _) ⟨a, q.P.append_contents f' f₀⟩ ≫ abs _ _ ∧
      x ≫ v ≫ cofix.dest = value i (q.P.obj _) ⟨a, q.P.append_contents f' f₁⟩ ≫ abs _ _ ∧
      ∀ j y, ∃ x' : unit j ⟶ β, x' ⊨ Q ∧ y ≫ f₀ = x' ≫ u ∧ y ≫ f₁ = x' ≫ v) :
  ∀ x : unit i ⟶ _, x ⊨ Q → x ≫ u = x ≫ v :=
λ x Qx,
let R : Pred (cofix F α ⊗ cofix F α) := Pred.mk $ λ j w, ∃ x' : unit j ⟶ _, x' ⊨ Q ∧ w = x' ≫ diag ≫ (u ⊗ v) in
cofix.bisim R
begin
  rintro j x Rx,
  obtain ⟨x',Qx',xeq⟩ : ∃ x', x' ⊨ Q ∧ x = x' ≫ diag ≫ (u ⊗ v),
  { apply sat_mk_elim _ _ Rx },
  rw liftr_iff₀',
  rcases h x' Qx' with ⟨a, f', f₀, f₁, ux'eq, vx'eq, h'⟩, clear h,
  refine ⟨a,q.P.append_contents f' f₀,q.P.append_contents f' f₁,_,_,_⟩,
  { simp [xeq,*], },
  { simp [xeq,*], },
  { rintro (i|i) a, dsimp [fam.rel_last,uncurry], refl,
    dsimp [fam.rel_last,uncurry,R,ipfunctor.append_contents,split_fun],
    rcases h' _ (value i _ a) with ⟨x',Qx',ueq,veq⟩, clear h',
    refine ⟨_,Qx',_⟩, apply fam.prod.ext; simp;
    [rw ← ueq,rw ← veq]; ext _ ⟨ ⟩; refl },
end _ _
(sat_intro _ _ $ by rintro _ ⟨ ⟩; simp [diag,fam.prod.map,R]; refine ⟨_,Qx,by ext _ ⟨ ⟩; refl⟩)

@[reassoc]
lemma cofix.mk_dest {α : fam I} : cofix.dest ≫ cofix.mk = 𝟙 (cofix F α) :=
begin
  let R : Pred (cofix F α ⊗ cofix F α) := Pred.mk (λ i x, x ≫ fam.prod.fst = x ≫ fam.prod.snd ≫ cofix.dest ≫ cofix.mk),
  apply cofix.bisim_rel R,
  { introv Rx, replace Rx := sat_mk_elim _ _ Rx (𝟙 _),
    rw [category.id_comp] at Rx, reassoc! Rx, rw Rx, clear Rx,
    conv { to_lhs, congr, skip,
      rw [cofix.mk,cofix.dest_corec_assoc,← functor.map_comp,← functor.map_comp,
          ← append_fun_comp_right,← append_fun_comp_right], },
    congr' 5, apply quot.sound'' (cofix.dest ≫ cofix.corec (F.map (append_fun (𝟙 α) cofix.dest))) (𝟙 _),
    { apply sat_mk_intro, intros, simp, refl  },
    all_goals { simp } },
  { apply sat_mk_intro, intros, simp, }
end

lemma cofix.dest_mk {α : fam I} : cofix.mk ≫ cofix.dest = 𝟙 (F.obj (α.append1 $ cofix F α)) :=
by rw [cofix.mk, cofix.dest_corec, ←functor.map_comp, ←cofix.mk, ← append_fun_comp_right, cofix.mk_dest, append_fun_id_id, category_theory.functor.map_id]

/-- Abstraction function for `cofix F α` -/
def cofix.abs {α} : q.P.M α ⟶ cofix F α :=
fam.quot.mk _

/-- Representation function for `cofix F α` -/
def cofix.repr {α} : cofix F α ⟶ q.P.M α :=
ipfunctor.M_corec _ $ cofix.dest ≫ repr _ _

lemma cofix.abs_repr {α}  :
  cofix.repr ≫ cofix.abs = 𝟙 (cofix F α) :=
begin
  let R : Pred (cofix F α ⊗ cofix F α) :=
    Pred.mk (λ i x, x ≫ fam.prod.fst = x ≫ fam.prod.snd ≫ cofix.repr ≫ cofix.abs),
  refine cofix.bisim_rel R _ _ _ _,
  { introv Rx, replace Rx := sat_mk_elim _ _ Rx (𝟙 _),
    reassoc! Rx, rw Rx, clear Rx, congr' 2,
    rw [cofix.repr,cofix.abs],
    conv { to_lhs, congr, skip,
      rw [cofix.dest], },
    simp only [quot.mk_lift__assoc,ipfunctor.M_dest_corec''_assoc,category.assoc,abs_map_assoc,abs_repr_assoc,← map_comp,← append_fun_comp_right],
    rw [← cofix.repr, ← cofix.abs], congr,
    apply quot.sound'' (cofix.repr ≫ cofix.abs) (𝟙 _),
    { apply sat_mk_intro, intros, simp },
    { simp },
    { simp } },
  { apply sat_mk_intro, intros, simp }
end

variables (F)

/-- The co-fixed point of a QPF is a functor -/
def pCofix : fam I ⥤ fam J :=
{ obj := cofix F,
  map := cofix.map }

instance iqpf_cofix : iqpf (pCofix F) :=
{ P         := q.P.Mp,
  abs       := λ α, cofix.abs,
  repr     := λ α, cofix.repr,
  abs_repr := λ α, cofix.abs_repr,
  abs_map   := λ α β g, rfl
}

end iqpf
