/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import category_theory.sites.grothendieck
import category_theory.sites.pretopology
import category_theory.full_subcategory
import category_theory.types
import category_theory.limits.types
import category_theory.limits.shapes.types
import tactic.equiv_rw

universes v u
namespace category_theory

open category_theory category limits sieve classical

namespace grothendieck_topology

variables {C : Type u} [category.{v} C]

variables {P : Cᵒᵖ ⥤ Type v}
variables {X Y : C} {S : sieve X} {R : presieve X}
variables (J J₂ : grothendieck_topology C)

/--
A family of elements for a presheaf `P` given a collection of arrows `R` with fixed codomain `X`
consists of an element of `P Y` for every `f : Y ⟶ X` in `R`.
A presheaf is a sheaf (resp, separated) if every *consistent* family of elements has exactly one
(resp, at most one) amalgamation.

This data is referred to as a `family` in [MM92], Chapter III, Section 4. It is also a concrete
version of the middle object in https://stacks.math.columbia.edu/tag/00VM which is more useful for
direct calculations. It is also used implicitly in Definition C2.1.2 in [Elephant].
-/
def family_of_elements (P : Cᵒᵖ ⥤ Type v) (R : presieve X) :=
Π ⦃Y : C⦄ (f : Y ⟶ X), R f → P.obj (opposite.op Y)

/--
A family of elements for a presheaf on the presieve `R₂` can be restricted to a smaller presieve
`R₁`.
-/
def family_of_elements.restrict {R₁ R₂ : presieve X} (h : R₁ ≤ R₂) :
  family_of_elements P R₂ → family_of_elements P R₁ :=
λ x Y f hf, x f (h _ hf)

/--
A family of elements for the arrow set `R` is consistent if for any `f₁ : Y₁ ⟶ X` and `f₂ : Y₂ ⟶ X`
in `R`, and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂`, if the square `g₁ ≫ f₁ = g₂ ≫ f₂` commutes then
the elements of `P Z` obtained by restricting the element of `P Y₁` along `g₁` and restricting
the element of `P Y₂` along `g₂` are the same.

In special cases, this condition can be simplified, see `is_pullback_consistent_iff` and
`is_sieve_consistent_iff`.

This is referred to as a "compatible family" in Definition C2.1.2 of [Elephant].
-/
def family_of_elements.consistent (x : family_of_elements P R) : Prop :=
∀ ⦃Y₁ Y₂ Z⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄
  (h₁ : R f₁) (h₂ : R f₂), g₁ ≫ f₁ = g₂ ≫ f₂ → P.map g₁.op (x f₁ h₁) = P.map g₂.op (x f₂ h₂)

/--
If the category `C` has pullbacks, this is an alternative condition for a family of elements to be
consistent: For any `f : Y ⟶ X` and `g : Z ⟶ X` in the presieve `R`, the restriction of the
given elements for `f` and `g` to the pullback agree.
This is equivalent to being consistent (provided `C` has pullbacks), shown in
`is_pullback_consistent_iff`.

This is the definition for a "matching" family given in [MM92], Chapter III, Section 4,
Equation (5). Viewing the type `family_of_elements` as the middle object of the fork in
https://stacks.math.columbia.edu/tag/00VM, this condition expresses that `pr₀* (x) = pr₁* (x)`,
using the notation defined there.
-/
def family_of_elements.pullback_consistent (x : family_of_elements P R) [has_pullbacks C] : Prop :=
∀ ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
  P.map (pullback.fst : pullback f₁ f₂ ⟶ _).op (x f₁ h₁) = P.map pullback.snd.op (x f₂ h₂)

lemma is_pullback_consistent_iff (x : family_of_elements P R) [has_pullbacks C] :
  x.consistent ↔ x.pullback_consistent :=
begin
  split,
  { intros t Y₁ Y₂ f₁ f₂ hf₁ hf₂,
    apply t,
    apply pullback.condition },
  { intros t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm,
    rw [←pullback.lift_fst _ _ comm, op_comp, functor_to_types.map_comp_apply, t hf₁ hf₂,
        ←functor_to_types.map_comp_apply, ←op_comp, pullback.lift_snd] }
end

/-- The restriction of a consistent family is consistent. -/
lemma family_of_elements.consistent.restrict {R₁ R₂ : presieve X} (h : R₁ ≤ R₂)
  {x : family_of_elements P R₂} : x.consistent → (x.restrict h).consistent :=
λ q Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm, q g₁ g₂ (h _ h₁) (h _ h₂) comm

/--
Extend a family of elements to the sieve generated by an arrow set.
This is the construction described as "easy" in Lemma C2.1.3 of [Elephant].
-/
noncomputable def family_of_elements.sieve_extend (x : family_of_elements P R) :
  family_of_elements P (generate R) :=
λ Z f hf, P.map (some (some_spec hf)).op (x _ (some_spec (some_spec (some_spec hf))).1)

/-- The extension of a consistent family to the generated sieve is consistent. -/
lemma family_of_elements.consistent.sieve_extend (x : family_of_elements P R) (hx : x.consistent) :
  x.sieve_extend.consistent :=
begin
  intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm,
  rw [←(some_spec (some_spec (some_spec h₁))).2, ←(some_spec (some_spec (some_spec h₂))).2,
      ←assoc, ←assoc] at comm,
  dsimp [family_of_elements.sieve_extend],
  rw [← functor_to_types.map_comp_apply, ← functor_to_types.map_comp_apply],
  apply hx _ _ _ _ comm,
end

/-- The extension of a family agrees with the original family. -/
lemma extend_agrees {x : family_of_elements P R} (t : x.consistent) {f : Y ⟶ X} (hf : R f) :
  x.sieve_extend f ⟨_, 𝟙 _, f, hf, id_comp _⟩ = x f hf :=
begin
  have h : (generate R) f := ⟨_, _, _, hf, id_comp _⟩,
  change P.map (some (some_spec h)).op (x _ _) = x f hf,
  rw t (some (some_spec h)) (𝟙 _) _ hf _,
  { simp },
  simp_rw [id_comp],
  apply (some_spec (some_spec (some_spec h))).2,
end

/-- The restriction of an extension is the original. -/
@[simp]
lemma restrict_extend {x : family_of_elements P R} (t : x.consistent) :
  x.sieve_extend.restrict (le_generate R) = x :=
begin
  ext Y f hf,
  exact extend_agrees t hf,
end

/--
If the arrow set for a family of elements is actually a sieve (i.e. it is downward closed) then the
consistency condition can be simplified.
This is an equivalent condition, see `is_sieve_consistent_iff`.

This is the notion of "matching" given for families on sieves given in [MM92], Chapter III,
Section 4, Equation 1.
See also the discussion before Lemma C2.1.4 of [Elephant].
-/
def family_of_elements.sieve_consistent (x : family_of_elements P S) : Prop :=
∀ ⦃Y Z⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (hf), x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf)

lemma is_sieve_consistent_iff (x : family_of_elements P S) :
  x.consistent ↔ x.sieve_consistent :=
begin
  split,
  { intros h Y Z f g hf,
    simpa using h (𝟙 _) g (S.downward_closed hf g) hf (id_comp _) },
  { intros h Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ k,
    simp_rw [← h f₁ g₁ h₁, k, h f₂ g₂ h₂] }
end

lemma family_of_elements.consistent.to_sieve_consistent {x : family_of_elements P S}
  (t : x.consistent) : x.sieve_consistent :=
(is_sieve_consistent_iff x).1 t

lemma restrict_inj {x₁ x₂ : family_of_elements P (generate R)}
  (t₁ : x₁.consistent) (t₂ : x₂.consistent) :
  x₁.restrict (le_generate R) = x₂.restrict (le_generate R) → x₁ = x₂ :=
begin
  intro h,
  ext Z f ⟨Y, f, g, hg, rfl⟩,
  rw is_sieve_consistent_iff at t₁ t₂,
  erw [t₁ g f ⟨_, _, g, hg, id_comp _⟩, t₂ g f ⟨_, _, g, hg, id_comp _⟩],
  congr' 1,
  apply congr_fun (congr_fun (congr_fun h _) g) hg,
end

@[simp]
lemma extend_restrict {x : family_of_elements P (generate R)} (t : x.consistent) :
  (x.restrict (le_generate R)).sieve_extend = x :=
begin
  apply restrict_inj,
  { exact (t.restrict (le_generate R)).sieve_extend _ },
  { exact t },
  rw restrict_extend,
  exact t.restrict (le_generate R),
end

def is_amalgamation_for (x : family_of_elements P R)
  (t : P.obj (opposite.op X)) : Prop :=
∀ ⦃Y : C⦄ (f : Y ⟶ X) (h : R f), P.map f.op t = x f h

lemma is_consistent_of_exists_amalgamation (x : family_of_elements P R)
  (h : ∃ t, is_amalgamation_for x t) : x.consistent :=
begin
  cases h with t ht,
  intros Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm,
  rw [←ht _ h₁, ←ht _ h₂, ←functor_to_types.map_comp_apply, ←op_comp, comm],
  simp,
end

lemma is_amalgamation_for_restrict {R₁ R₂ : presieve X} (h : R₁ ≤ R₂)
  (x : family_of_elements P R₂) (t : P.obj (opposite.op X)) (ht : is_amalgamation_for x t) :
  is_amalgamation_for (x.restrict h) t :=
λ Y f hf, ht f (h Y hf)

lemma is_amalgamation_for_extend {R : presieve X}
  (x : family_of_elements P R) (t : P.obj (opposite.op X)) (ht : is_amalgamation_for x t) :
  is_amalgamation_for x.sieve_extend t :=
begin
  intros Y f hf,
  dsimp [family_of_elements.sieve_extend],
  rw [←ht _, ←functor_to_types.map_comp_apply, ←op_comp, (some_spec (some_spec (some_spec hf))).2],
end

/-- A presheaf is separated for a presieve if there is at most one amalgamation. -/
def is_separated_for (P : Cᵒᵖ ⥤ Type v) (R : presieve X) : Prop :=
∀ (x : family_of_elements P R) (t₁ t₂),
  is_amalgamation_for x t₁ → is_amalgamation_for x t₂ → t₁ = t₂

lemma is_separated_for.ext {R : presieve X} (hR : is_separated_for P R)
  {t₁ t₂ : P.obj (opposite.op X)} (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : R f), P.map f.op t₁ = P.map f.op t₂) :
t₁ = t₂ :=
hR (λ Y f hf, P.map f.op t₂) t₁ t₂ (λ Y f hf, h hf) (λ Y f hf, rfl)

lemma is_separated_for_iff_generate :
  is_separated_for P R ↔ is_separated_for P (generate R) :=
begin
  split,
  { intros h x t₁ t₂ ht₁ ht₂,
    apply h (x.restrict (le_generate R)) t₁ t₂ _ _,
    { exact is_amalgamation_for_restrict _ x t₁ ht₁ },
    { exact is_amalgamation_for_restrict _ x t₂ ht₂ } },
  { intros h x t₁ t₂ ht₁ ht₂,
    apply h (x.sieve_extend),
    { exact is_amalgamation_for_extend x t₁ ht₁ },
    { exact is_amalgamation_for_extend x t₂ ht₂ } }
end

lemma is_separated_for_top (P : Cᵒᵖ ⥤ Type v) : is_separated_for P (⊤ : presieve X) :=
λ x t₁ t₂ h₁ h₂,
begin
  have q₁ := h₁ (𝟙 X) (by simp),
  have q₂ := h₂ (𝟙 X) (by simp),
  simp only [op_id, functor_to_types.map_id_apply] at q₁ q₂,
  rw [q₁, q₂],
end

def is_sheaf_for (P : Cᵒᵖ ⥤ Type v) (R : presieve X) : Prop :=
∀ (x : family_of_elements P R), x.consistent → ∃! t, is_amalgamation_for x t

def yoneda_sheaf_condition (P : Cᵒᵖ ⥤ Type v) (S : sieve X) : Prop :=
∀ (f : S.functor ⟶ P), ∃! g, S.functor_inclusion ≫ g = f

example {α : Sort*} {p q : α → Prop} : (∀ (x : {a // p a}), q x.1) ↔ ∀ a, p a → q a :=
begin
  simpa only [subtype.forall, subtype.val_eq_coe],
end

def nat_trans_equiv_consistent_family :
  (S.functor ⟶ P) ≃ {x : family_of_elements P S // x.consistent} :=
{ to_fun := λ α,
  begin
    refine ⟨λ Y f hf, _, _⟩,
    { apply α.app (opposite.op Y) ⟨_, hf⟩ },
    { rw is_sieve_consistent_iff,
      intros Y Z f g hf,
      dsimp,
      rw ← functor_to_types.naturality _ _ α g.op,
      refl }
  end,
  inv_fun := λ t,
  { app := λ Y f, t.1 _ f.2,
    naturality' := λ Y Z g,
    begin
      ext ⟨f, hf⟩,
      apply t.2.to_sieve_consistent _,
    end },
  left_inv := λ α,
  begin
    ext X ⟨_, _⟩,
    refl
  end,
  right_inv :=
  begin
    rintro ⟨x, hx⟩,
    refl,
  end }

def yoneda_equiv {F : Cᵒᵖ ⥤ Type v} : (yoneda.obj X ⟶ F) ≃ F.obj (opposite.op X) :=
(yoneda_sections X F).to_equiv.trans equiv.ulift

lemma extension_iff_amalgamation (x : S.functor ⟶ P) (g : yoneda.obj X ⟶ P) :
  S.functor_inclusion ≫ g = x ↔ is_amalgamation_for (nat_trans_equiv_consistent_family x).1 (yoneda_equiv g) :=
begin
  dsimp [is_amalgamation_for, yoneda_equiv, yoneda_lemma, nat_trans_equiv_consistent_family],
  split,
  { rintro rfl,
    intros Y f hf,
    rw ← functor_to_types.naturality _ _ g,
    change g.app (opposite.op Y) (f ≫ 𝟙 X) = g.app (opposite.op Y) f,
    simp only [comp_id] },
  { intro h,
    ext Y ⟨f, hf⟩,
    have : _ = x.app Y _ := h f hf,
    rw [← this, ← functor_to_types.naturality _ _ g],
    dsimp,
    simp },
end

lemma equiv.exists_unique_congr {α β : Type*} (p : β → Prop) (e : α ≃ β) :
  (∃! (y : β), p y) ↔ ∃! (x : α), p (e x) :=
begin
  split,
  { rintro ⟨b, hb₁, hb₂⟩,
    exact ⟨e.symm b, by simpa using hb₁, λ x hx, by simp [←hb₂ (e x) hx]⟩ },
  { rintro ⟨a, ha₁, ha₂⟩,
    refine ⟨e a, ha₁, λ y hy, _⟩,
    rw ← equiv.symm_apply_eq,
    apply ha₂,
    simpa using hy },
end

lemma yoneda_condition_iff_sheaf_condition :
  is_sheaf_for P S ↔ yoneda_sheaf_condition P S :=
begin
  rw [is_sheaf_for, yoneda_sheaf_condition],
  simp_rw [extension_iff_amalgamation],
  rw equiv.forall_congr_left' nat_trans_equiv_consistent_family,
  rw subtype.forall,
  apply ball_congr,
  intros x hx,
  rw ← equiv.exists_unique_congr _ _,
  simp,
end

lemma separated_for_and_exists_amalgamation_iff_sheaf_for :
  is_separated_for P R ∧ (∀ (x : family_of_elements P R), x.consistent → ∃ t, is_amalgamation_for x t) ↔ is_sheaf_for P R :=
begin
  rw [is_separated_for, ←forall_and_distrib],
  apply forall_congr,
  intro x,
  split,
  { intros z hx, exact exists_unique_of_exists_of_unique (z.2 hx) z.1 },
  { intros h,
    refine ⟨_, (exists_of_exists_unique ∘ h)⟩,
    intros t₁ t₂ ht₁ ht₂,
    apply (h _).unique ht₁ ht₂,
    exact is_consistent_of_exists_amalgamation x ⟨_, ht₂⟩ }
end

lemma is_separated_for.is_sheaf_for (t : is_separated_for P R) :
  (∀ (x : family_of_elements P R), x.consistent → ∃ t, is_amalgamation_for x t) →
  is_sheaf_for P R :=
begin
  rw ← separated_for_and_exists_amalgamation_iff_sheaf_for,
  apply and.intro t,
end

noncomputable def is_sheaf_for.amalgamate
  (t : is_sheaf_for P R) (x : family_of_elements P R) (hx : x.consistent) :
  P.obj (opposite.op X) :=
classical.some (t x hx).exists

lemma is_sheaf_for.is_amalgamation_for
  (t : is_sheaf_for P R) {x : family_of_elements P R} (hx : x.consistent) :
  is_amalgamation_for x (t.amalgamate x hx) :=
classical.some_spec (t x hx).exists

@[simp]
lemma is_sheaf_for.valid_glue
  (t : is_sheaf_for P R) {x : family_of_elements P R} (hx : x.consistent) (f : Y ⟶ X) (Hf : R f) :
  P.map f.op (t.amalgamate x hx) = x f Hf :=
t.is_amalgamation_for hx f Hf

lemma is_sheaf_for.is_separated_for : is_sheaf_for P R → is_separated_for P R :=
λ q, (separated_for_and_exists_amalgamation_iff_sheaf_for.2 q).1

/-- C2.1.3 in Elephant -/
lemma is_sheaf_for_iff_generate :
  is_sheaf_for P R ↔ is_sheaf_for P (generate R) :=
begin
  rw ← separated_for_and_exists_amalgamation_iff_sheaf_for,
  rw ← separated_for_and_exists_amalgamation_iff_sheaf_for,
  rw ← is_separated_for_iff_generate,
  apply and_congr (iff.refl _),
  split,
  { intros q x hx,
    apply exists_imp_exists _ (q _ (hx.restrict (le_generate R))),
    intros t ht,
    simpa [hx] using is_amalgamation_for_extend _ _ ht },
  { intros q x hx,
    apply exists_imp_exists _ (q _ (hx.sieve_extend _)),
    intros t ht,
    simpa [hx] using is_amalgamation_for_restrict (le_generate R) _ _ ht },
end

/--
Every presheaf is a sheaf for the family {𝟙 X}.

Elephant: C2.1.5(i)
-/
lemma is_sheaf_for_singleton_iso (P : Cᵒᵖ ⥤ Type v) :
  is_sheaf_for P (presieve.singleton (𝟙 X)) :=
begin
  intros x hx,
  refine ⟨x _ (presieve.singleton_self _), _, _⟩,
  { rintro _ _ ⟨rfl, rfl⟩,
    simp },
  { intros t ht,
    simpa using ht _ (presieve.singleton_self _) }
end

/--
Every presheaf is a sheaf for the maximal sieve.

Elephant: C2.1.5(ii)
-/
lemma is_sheaf_for_top_sieve (P : Cᵒᵖ ⥤ Type v) :
  is_sheaf_for P ((⊤ : sieve X) : presieve X) :=
begin
  rw ← generate_of_singleton_split_epi (𝟙 X),
  rw ← is_sheaf_for_iff_generate,
  apply is_sheaf_for_singleton_iso,
end

/--
If `P` is a sheaf for `S`, and it is iso to `P'`, then `P'` is a sheaf for `S`. This shows that
"being a sheaf for a presieve" is a mathematical or hygenic property.
-/
lemma is_sheaf_for_iso {P' : Cᵒᵖ ⥤ Type v} (i : P ≅ P') : is_sheaf_for P R → is_sheaf_for P' R :=
begin
  rw [is_sheaf_for_iff_generate, yoneda_condition_iff_sheaf_condition, is_sheaf_for_iff_generate,
      yoneda_condition_iff_sheaf_condition],
  intros h f,
  obtain ⟨g, hg₁, hg₂⟩ := h (f ≫ i.inv),
  refine ⟨g ≫ i.hom, by simpa [iso.eq_comp_inv] using hg₁, _⟩,
  { intros g' hg',
    rw ← iso.comp_inv_eq,
    apply hg₂,
    rw reassoc_of hg' },
end

/--
If a family of arrows `R` on `X` has a subsieve `S` such that:
* `P` is a sheaf for `S`.
* For every `f` in `R`, `P` is separated for the pullback of `S` along `f`
then `P` is a sheaf for `R`.
-/
lemma is_sheaf_for_subsieve_aux (P : Cᵒᵖ ⥤ Type v) {S : sieve X} {R : presieve X}
  (h : (S : presieve X) ≤ R)
  (hS : is_sheaf_for P S)
  (trans : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, R f → is_separated_for P (S.pullback f)) :
  is_sheaf_for P R :=
begin
  rw ← separated_for_and_exists_amalgamation_iff_sheaf_for,
  refine ⟨_, _⟩,
  { intros x t₁ t₂ ht₁ ht₂,
    exact hS.is_separated_for _ _ _ (is_amalgamation_for_restrict h x t₁ ht₁)
                                    (is_amalgamation_for_restrict h x t₂ ht₂) },
  { intros x hx,
    use hS.amalgamate _ (hx.restrict h),
    intros W j hj,
    apply (trans hj).ext,
    intros Y f hf,
    rw [←functor_to_types.map_comp_apply, ←op_comp,
        hS.valid_glue (hx.restrict h) _ hf, family_of_elements.restrict,
        ←hx (𝟙 _) f _ _ (id_comp _)],
    simp },
end

lemma is_sheaf_for_subsieve (P : Cᵒᵖ ⥤ Type v) {S : sieve X} {R : presieve X}
  (h : (S : presieve X) ≤ R)
  (trans : Π ⦃Y⦄ (f : Y ⟶ X), is_sheaf_for P (S.pullback f)) :
  is_sheaf_for P R :=
is_sheaf_for_subsieve_aux P h (by simpa using trans (𝟙 _)) (λ Y f hf, (trans f).is_separated_for)

/-- A presheaf is separated if it is separated for every sieve in the topology. -/
def is_separated (P : Cᵒᵖ ⥤ Type v) : Prop :=
∀ {X} (S : sieve X), S ∈ J X → is_separated_for P S

/-- A presheaf is a sheaf if it is a sheaf for every sieve in the topology. -/
def is_sheaf (P : Cᵒᵖ ⥤ Type v) : Prop :=
∀ {X} (S : sieve X), S ∈ J X → is_sheaf_for P S

lemma is_sheaf_for_coarser_topology (P : Cᵒᵖ ⥤ Type v) {J₁ J₂ : grothendieck_topology C} :
  J₁ ≤ J₂ → is_sheaf J₂ P → is_sheaf J₁ P :=
λ h t X S hS, t S (h _ hS)

lemma separated_of_sheaf (P : Cᵒᵖ ⥤ Type v) (h : is_sheaf J P) : is_separated J P :=
λ X S hS, (h S hS).is_separated_for

/-- The property of being a sheaf is preserved by isomorphism. -/
lemma is_sheaf_iso {P' : Cᵒᵖ ⥤ Type v} (i : P ≅ P') (h : is_sheaf J P) : is_sheaf J P' :=
λ X S hS, is_sheaf_for_iso i (h S hS)

lemma is_sheaf_yoneda (h : ∀ {X} (S : sieve X), S ∈ J X → yoneda_sheaf_condition P S) :
  is_sheaf J P :=
begin
  intros X S hS,
  rw yoneda_condition_iff_sheaf_condition,
  apply h _ hS,
end

/--
For a topology generated by a basis, it suffices to check the sheaf condition on the basis
presieves only.
-/
lemma is_sheaf_for_pretopology [has_pullbacks C] (K : pretopology C) :
  is_sheaf (K.to_grothendieck C) P ↔ (∀ {X : C} (R : presieve X), R ∈ K X → is_sheaf_for P R) :=
begin
  split,
  { intros PJ X R hR,
    rw is_sheaf_for_iff_generate,
    apply PJ (sieve.generate R) ⟨_, hR, le_generate R⟩ },
  { rintro PK X S ⟨R, hR, RS⟩,
    have gRS : ⇑(generate R) ≤ S,
    { apply gi_generate.gc.monotone_u,
      rwa sets_iff_generate },
    apply is_sheaf_for_subsieve P gRS _,
    intros Y f,
    rw [← pullback_arrows_comm, ← is_sheaf_for_iff_generate],
    exact PK (pullback_arrows f R) (K.pullbacks f R hR) }
end

end grothendieck_topology

lemma type_equalizer {X Y Z : Type v} (f : X ⟶ Y) (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h) :
  (∀ (y : Y), g y = h y → ∃! (x : X), f x = y) ↔ nonempty (is_limit (fork.of_ι _ w)) :=
begin
  split,
  { intro t,
    apply nonempty.intro,
    apply fork.is_limit.mk',
    intro s,
    refine ⟨λ i, _, _, _⟩,
    { apply classical.some (t (s.ι i) _),
      apply congr_fun s.condition i },
    { ext i,
      apply (classical.some_spec (t (s.ι i) _)).1 },
    { intros m hm,
      ext i,
      apply (classical.some_spec (t (s.ι i) _)).2,
      apply congr_fun hm i } },
  { rintro ⟨t⟩ y hy,
    let y' : punit ⟶ Y := λ _, y,
    have hy' : y' ≫ g = y' ≫ h := funext (λ _, hy),
    refine ⟨(fork.is_limit.lift' t _ hy').1 ⟨⟩, congr_fun (fork.is_limit.lift' t y' _).2 ⟨⟩, _⟩,
    intros x' hx',
    suffices : (λ (_ : punit), x') = (fork.is_limit.lift' t y' hy').1,
      rw ← this,
    apply fork.is_limit.hom_ext t,
    ext ⟨⟩,
    apply hx'.trans (congr_fun (fork.is_limit.lift' t _ hy').2 ⟨⟩).symm },
end

namespace equalizer

variables {C : Type v} [small_category C] {X : C} (R : presieve X) (S : sieve X) (P : Cᵒᵖ ⥤ Type v)

noncomputable theory

def first_obj : Type v :=
∏ (λ (f : Σ Y, {f : Y ⟶ X // R f}), P.obj (opposite.op f.1))

@[simps]
def first_obj_eq_family : first_obj R P ≅ grothendieck_topology.family_of_elements P R :=
{ hom := λ t Y f hf, pi.π (λ (f : Σ Y, {f : Y ⟶ X // R f}), P.obj (opposite.op f.1)) ⟨_, _, hf⟩ t,
  inv := pi.lift (λ f x, x _ f.2.2),
  hom_inv_id' :=
  begin
    ext ⟨Y, f, hf⟩ p,
    simpa,
  end,
  inv_hom_id' :=
  begin
    ext x Y f hf,
    apply limits.types.limit.lift_π_apply,
  end }

namespace sieve_equalizer

def second_obj : Type v :=
∏ (λ (f : Σ Y Z (g : Z ⟶ Y), {f' : Y ⟶ X // S f'}), P.obj (opposite.op f.2.1))

def first_map : first_obj S P ⟶ second_obj S P :=
pi.lift (λ fg, pi.π _ (⟨_, _, S.downward_closed fg.2.2.2.2 fg.2.2.1⟩ : Σ Y, {f : Y ⟶ X // S f}))

def second_map : first_obj S P ⟶ second_obj S P :=
pi.lift (λ fg, pi.π _ ⟨_, fg.2.2.2⟩ ≫ P.map (fg.2.2.1.op))

def fork_map : P.obj (opposite.op X) ⟶ first_obj S P :=
pi.lift (λ f, P.map f.2.1.op)

lemma w : fork_map S P ≫ first_map S P = fork_map S P ≫ second_map S P :=
begin
  apply limit.hom_ext,
  rintro ⟨Y, Z, g, f, hf⟩,
  simp [first_map, second_map, fork_map],
end

lemma consistent_iff (x : first_obj S P) :
  ((first_obj_eq_family S P).hom x).consistent ↔ first_map S P x = second_map S P x :=
begin
  rw grothendieck_topology.is_sieve_consistent_iff,
  split,
  { intro t,
    ext ⟨Y, Z, g, f, hf⟩,
    simpa [first_map, second_map] using t _ g hf },
  { intros t Y Z f g hf,
    have : (first_map S P ≫ pi.π _ (⟨Y, Z, g, f, hf⟩ : Σ (Y Z : C) (g : Z ⟶ Y), {f' // S f'})) x =
           (second_map S P ≫ pi.π _ (⟨Y, Z, g, f, hf⟩ : Σ (Y Z : C) (g : Z ⟶ Y), {f' // S f'})) x,
    { dsimp, rw t },
    simpa [first_map, second_map] using this }
end

lemma equalizer_sheaf_condition :
  grothendieck_topology.is_sheaf_for P S ↔ nonempty (is_limit (fork.of_ι _ (w S P))) :=
begin
  rw [← type_equalizer, ← equiv.forall_congr_left (first_obj_eq_family S P).to_equiv.symm],
  simp_rw ← consistent_iff,
  simp only [inv_hom_id_apply, iso.to_equiv_symm_fun],
  apply ball_congr,
  intros x tx,
  apply exists_unique_congr,
  intro t,
  rw ← iso.to_equiv_symm_fun,
  rw equiv.eq_symm_apply,
  split,
  { intros q,
    ext Y f hf,
    simpa [first_obj_eq_family, fork_map] using q _ _ },
  { intros q Y f hf,
    rw ← q,
    simp [first_obj_eq_family, fork_map] }
end

end sieve_equalizer

namespace presieve_equalizer

variables [has_pullbacks C]

def first_obj : Type v :=
∏ λ (f : Σ Y, {f : Y ⟶ X // R f}), P.obj (opposite.op f.1)

def second_obj : Type v :=
∏ (λ (fg : (Σ Y, {f : Y ⟶ X // R f}) × (Σ Z, {g : Z ⟶ X // R g})),
  P.obj (opposite.op (pullback fg.1.2.1 fg.2.2.1)))

def first_map : first_obj R P ⟶ second_obj R P :=
pi.lift (λ fg, pi.π _ _ ≫ P.map pullback.fst.op)

def second_map : first_obj R P ⟶ second_obj R P :=
pi.lift (λ fg, pi.π _ _ ≫ P.map pullback.snd.op)

def fork_map : P.obj (opposite.op X) ⟶ first_obj R P :=
pi.lift (λ f, P.map f.2.1.op)

lemma w : fork_map R P ≫ first_map R P = fork_map R P ≫ second_map R P :=
begin
  apply limit.hom_ext,
  rintro ⟨⟨Y, f, hf⟩, ⟨Z, g, hg⟩⟩,
  simp only [first_map, second_map, fork_map],
  simp only [limit.lift_π, limit.lift_π_assoc, assoc, fan.mk_π_app, subtype.coe_mk,
             subtype.val_eq_coe],
  rw [← P.map_comp, ← op_comp, pullback.condition],
  simp,
end

lemma consistent_iff (x : first_obj R P) :
  ((first_obj_eq_family R P).hom x).consistent ↔ first_map R P x = second_map R P x :=
begin
  rw grothendieck_topology.is_pullback_consistent_iff,
  split,
  { intro t,
    ext ⟨⟨Y, f, hf⟩, Z, g, hg⟩,
    simpa [first_map, second_map] using t hf hg },
  { intros t Y Z f g hf hg,
    have : (first_map R P ≫ pi.π _ (⟨⟨Y, f, hf⟩, Z, g, hg⟩ : (Σ Y, {f : Y ⟶ X // R f}) × (Σ Z, {g : Z ⟶ X // R g}))) x =
           (second_map R P ≫ pi.π _ (⟨⟨Y, f, hf⟩, Z, g, hg⟩ : (Σ Y, {f : Y ⟶ X // R f}) × (Σ Z, {g : Z ⟶ X // R g}))) x,
    { dsimp, rw t },
    simpa [first_map, second_map] using this }
end


lemma equalizer_sheaf_condition :
  grothendieck_topology.is_sheaf_for P R ↔ nonempty (is_limit (fork.of_ι _ (w R P))) :=
begin
  rw ← type_equalizer,
  erw ← equiv.forall_congr_left (first_obj_eq_family R P).to_equiv.symm,
  simp_rw [← consistent_iff, ← iso.to_equiv_fun, equiv.apply_symm_apply],
  apply ball_congr,
  intros x hx,
  apply exists_unique_congr,
  intros t,
  rw equiv.eq_symm_apply,
  split,
  { intros q,
    ext Y f hf,
    simpa [fork_map] using q _ _ },
  { intros q Y f hf,
    rw ← q,
    simp [fork_map] }
end

end presieve_equalizer
end equalizer

-- variables (C J)

-- structure Sheaf :=
-- (P : Cᵒᵖ ⥤ Type v)
-- (sheaf_cond : sheaf_condition J P)

-- instance : category (Sheaf C J) := induced_category.category Sheaf.P

end category_theory
