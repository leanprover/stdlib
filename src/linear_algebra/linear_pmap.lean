/-
Copyright (c) 2020 Yury Kudryashov All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import linear_algebra.basic
import linear_algebra.prod

/-!
# Partially defined linear maps

A `linear_pmap R E F` is a linear map from a submodule of `E` to `F`. We define
a `semilattice_inf_bot` instance on this this, and define three operations:

* `mk_span_singleton` defines a partial linear map defined on the span of a singleton.
* `sup` takes two partial linear maps `f`, `g` that agree on the intersection of their
  domains, and returns the unique partial linear map on `f.domain ⊔ g.domain` that
  extends both `f` and `g`.
* `Sup` takes a `directed_on (≤)` set of partial linear maps, and returns the unique
  partial linear map on the `Sup` of their domains that extends all these maps.

Partially defined maps are currently used in `mathlib` to prove Hahn-Banach theorem
and its variations. Namely, `linear_pmap.Sup` implies that every chain of `linear_pmap`s
is bounded above.

Another possible use (not yet in `mathlib`) would be the theory of unbounded linear operators.
-/

open set

universes u v w

/-- A `linear_pmap R E F` is a linear map from a submodule of `E` to `F`. -/
structure linear_pmap (R : Type u) [ring R] (E : Type v) [add_comm_group E] [module R E]
  (F : Type w) [add_comm_group F] [module R F] :=
(domain : submodule R E)
(to_fun : domain →ₗ[R] F)

variables {R : Type*} [ring R] {E : Type*} [add_comm_group E] [module R E]
  {F : Type*} [add_comm_group F] [module R F]
  {G : Type*} [add_comm_group G] [module R G]

namespace linear_pmap

open submodule

instance : has_coe_to_fun (linear_pmap R E F) :=
⟨λ f : linear_pmap R E F, f.domain → F, λ f, f.to_fun⟩

@[simp] lemma to_fun_eq_coe (f : linear_pmap R E F) (x : f.domain) :
  f.to_fun x = f x := rfl

@[simp] lemma map_zero (f : linear_pmap R E F) : f 0 = 0 := f.to_fun.map_zero

lemma map_add (f : linear_pmap R E F) (x y : f.domain) : f (x + y) = f x + f y :=
f.to_fun.map_add x y

lemma map_neg (f : linear_pmap R E F) (x : f.domain) : f (-x) = -f x :=
f.to_fun.map_neg x

lemma map_sub (f : linear_pmap R E F) (x y : f.domain) : f (x - y) = f x - f y :=
f.to_fun.map_sub x y

lemma map_smul (f : linear_pmap R E F) (c : R) (x : f.domain) : f (c • x) = c • f x :=
f.to_fun.map_smul c x

@[simp] lemma mk_apply (p : submodule R E) (f : p →ₗ[R] F) (x : p) :
  mk p f x = f x := rfl

/-- The unique `linear_pmap` on `R ∙ x` that sends `x` to `y`. This version works for modules
over rings, and requires a proof of `∀ c, c • x = 0 → c • y = 0`. -/
noncomputable def mk_span_singleton' (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) :
  linear_pmap R E F :=
{ domain := R ∙ x,
  to_fun :=
  have H : ∀ c₁ c₂ : R, c₁ • x = c₂ • x → c₁ • y = c₂ • y,
  { intros c₁ c₂ h,
    rw [← sub_eq_zero, ← sub_smul] at h ⊢,
    exact H _ h },
  { to_fun := λ z, (classical.some (mem_span_singleton.1 z.prop) • y),
    map_add' := λ y z, begin
      rw [← add_smul],
      apply H,
      simp only [add_smul, sub_smul, classical.some_spec (mem_span_singleton.1 _)],
      apply coe_add
    end,
    map_smul' := λ c z, begin
      rw [smul_smul],
      apply H,
      simp only [mul_smul, classical.some_spec (mem_span_singleton.1 _)],
      apply coe_smul
    end } }

@[simp] lemma domain_mk_span_singleton (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0) :
  (mk_span_singleton' x y H).domain = R ∙ x := rfl

@[simp] lemma mk_span_singleton_apply (x : E) (y : F) (H : ∀ c : R, c • x = 0 → c • y = 0)
  (c : R) (h) :
  mk_span_singleton' x y H ⟨c • x, h⟩ = c • y :=
begin
  dsimp [mk_span_singleton'],
  rw [← sub_eq_zero, ← sub_smul],
  apply H,
  simp only [sub_smul, one_smul, sub_eq_zero],
  apply classical.some_spec (mem_span_singleton.1 h),
end

/-- The unique `linear_pmap` on `span R {x}` that sends a non-zero vector `x` to `y`.
This version works for modules over division rings. -/
@[reducible] noncomputable def mk_span_singleton {K E F : Type*} [division_ring K]
  [add_comm_group E] [module K E] [add_comm_group F] [module K F] (x : E) (y : F) (hx : x ≠ 0) :
  linear_pmap K E F :=
mk_span_singleton' x y $ λ c hc, (smul_eq_zero.1 hc).elim
  (λ hc, by rw [hc, zero_smul]) (λ hx', absurd hx' hx)

/-- Projection to the first coordinate as a `linear_pmap` -/
protected def fst (p : submodule R E) (p' : submodule R F) : linear_pmap R (E × F) E :=
{ domain := p.prod p',
  to_fun := (linear_map.fst R E F).comp (p.prod p').subtype }

@[simp] lemma fst_apply (p : submodule R E) (p' : submodule R F) (x : p.prod p') :
  linear_pmap.fst p p' x = (x : E × F).1 := rfl

/-- Projection to the second coordinate as a `linear_pmap` -/
protected def snd (p : submodule R E) (p' : submodule R F) : linear_pmap R (E × F) F :=
{ domain := p.prod p',
  to_fun := (linear_map.snd R E F).comp (p.prod p').subtype }

@[simp] lemma snd_apply (p : submodule R E) (p' : submodule R F) (x : p.prod p') :
  linear_pmap.snd p p' x = (x : E × F).2 := rfl

instance : has_neg (linear_pmap R E F) :=
⟨λ f, ⟨f.domain, -f.to_fun⟩⟩

@[simp] lemma neg_apply (f : linear_pmap R E F) (x) : (-f) x = -(f x) := rfl

instance : has_le (linear_pmap R E F) :=
⟨λ f g, f.domain ≤ g.domain ∧ ∀ ⦃x : f.domain⦄ ⦃y : g.domain⦄ (h : (x:E) = y), f x = g y⟩

lemma eq_of_le_of_domain_eq {f g : linear_pmap R E F} (hle : f ≤ g) (heq : f.domain = g.domain) :
  f = g :=
begin
  rcases f with ⟨f_dom, f⟩,
  rcases g with ⟨g_dom, g⟩,
  change f_dom = g_dom at heq,
  subst g_dom,
  have : f = g, from linear_map.ext (λ x, hle.2 rfl),
  subst g
end

/-- Given two partial linear maps `f`, `g`, the set of points `x` such that
both `f` and `g` are defined at `x` and `f x = g x` form a submodule. -/
def eq_locus (f g : linear_pmap R E F) : submodule R E :=
{ carrier   := {x | ∃ (hf : x ∈ f.domain) (hg : x ∈ g.domain), f ⟨x, hf⟩ = g ⟨x, hg⟩},
  zero_mem' := ⟨zero_mem _, zero_mem _, f.map_zero.trans g.map_zero.symm⟩,
  add_mem'  := λ x y ⟨hfx, hgx, hx⟩ ⟨hfy, hgy, hy⟩, ⟨add_mem _ hfx hfy, add_mem _ hgx hgy,
    by erw [f.map_add ⟨x, hfx⟩ ⟨y, hfy⟩, g.map_add ⟨x, hgx⟩ ⟨y, hgy⟩, hx, hy]⟩,
  smul_mem' := λ c x ⟨hfx, hgx, hx⟩, ⟨smul_mem _ c hfx, smul_mem _ c hgx,
    by erw [f.map_smul c ⟨x, hfx⟩, g.map_smul c ⟨x, hgx⟩, hx]⟩ }

instance : has_inf (linear_pmap R E F) :=
⟨λ f g, ⟨f.eq_locus g, f.to_fun.comp $ of_le $ λ x hx, hx.fst⟩⟩

instance : has_bot (linear_pmap R E F) := ⟨⟨⊥, 0⟩⟩

instance : inhabited (linear_pmap R E F) := ⟨⊥⟩

instance : semilattice_inf_bot (linear_pmap R E F) :=
{ le := (≤),
  le_refl := λ f, ⟨le_refl f.domain, λ x y h, subtype.eq h ▸ rfl⟩,
  le_trans := λ f g h ⟨fg_le, fg_eq⟩ ⟨gh_le, gh_eq⟩,
    ⟨le_trans fg_le gh_le, λ x z hxz,
      have hxy : (x:E) = of_le fg_le x, from rfl,
      (fg_eq hxy).trans (gh_eq $ hxy.symm.trans hxz)⟩,
  le_antisymm := λ f g fg gf, eq_of_le_of_domain_eq fg (le_antisymm fg.1 gf.1),
  bot := ⊥,
  bot_le := λ f, ⟨bot_le, λ x y h,
    have hx : x = 0, from subtype.eq ((mem_bot R).1 x.2),
    have hy : y = 0, from subtype.eq (h.symm.trans (congr_arg _ hx)),
    by rw [hx, hy, map_zero, map_zero]⟩,
  inf := (⊓),
  le_inf := λ f g h ⟨fg_le, fg_eq⟩ ⟨fh_le, fh_eq⟩,
    ⟨λ x hx, ⟨fg_le hx, fh_le hx,
      by refine (fg_eq _).symm.trans (fh_eq _); [exact ⟨x, hx⟩, refl, refl]⟩,
    λ x ⟨y, yg, hy⟩ h, by { apply fg_eq, exact h }⟩,
  inf_le_left := λ f g, ⟨λ x hx, hx.fst,
    λ x y h, congr_arg f $ subtype.eq $ by exact h⟩,
  inf_le_right := λ f g, ⟨λ x hx, hx.snd.fst,
    λ ⟨x, xf, xg, hx⟩ y h, hx.trans $ congr_arg g $ subtype.eq $ by exact h⟩ }

lemma le_of_eq_locus_ge {f g : linear_pmap R E F} (H : f.domain ≤ f.eq_locus g) :
  f ≤ g :=
suffices f ≤ f ⊓ g, from le_trans this inf_le_right,
⟨H, λ x y hxy, ((inf_le_left : f ⊓ g ≤ f).2 hxy.symm).symm⟩

lemma domain_mono : strict_mono (@domain R _ E _ _ F _ _) :=
λ f g hlt, lt_of_le_of_ne hlt.1.1 $ λ heq, ne_of_lt hlt $
eq_of_le_of_domain_eq (le_of_lt hlt) heq

private lemma sup_aux (f g : linear_pmap R E F)
  (h : ∀ (x : f.domain) (y : g.domain), (x:E) = y → f x = g y) :
  ∃ fg : ↥(f.domain ⊔ g.domain) →ₗ[R] F,
    ∀ (x : f.domain) (y : g.domain) (z),
      (x:E) + y = ↑z → fg z = f x + g y :=
begin
  choose x hx y hy hxy using λ z : f.domain ⊔ g.domain, mem_sup.1 z.prop,
  set fg := λ z, f ⟨x z, hx z⟩ + g ⟨y z, hy z⟩,
  have fg_eq : ∀ (x' : f.domain) (y' : g.domain) (z' : f.domain ⊔ g.domain) (H : (x':E) + y' = z'),
    fg z' = f x' + g y',
  { intros x' y' z' H,
    dsimp [fg],
    rw [add_comm, ← sub_eq_sub_iff_add_eq_add, eq_comm, ← map_sub, ← map_sub],
    apply h,
    simp only [← eq_sub_iff_add_eq] at hxy,
    simp only [coe_sub, coe_mk, coe_mk, hxy, ← sub_add, ← sub_sub, sub_self, zero_sub, ← H],
    apply neg_add_eq_sub },
  refine ⟨{ to_fun := fg, .. }, fg_eq⟩,
  { rintros ⟨z₁, hz₁⟩ ⟨z₂, hz₂⟩,
    rw [← add_assoc, add_right_comm (f _), ← map_add, add_assoc, ← map_add],
    apply fg_eq,
    simp only [coe_add, coe_mk, ← add_assoc],
    rw [add_right_comm (x _), hxy, add_assoc, hxy, coe_mk, coe_mk] },
  { intros c z,
    rw [smul_add, ← map_smul, ← map_smul],
    apply fg_eq,
    simp only [coe_smul, coe_mk, ← smul_add, hxy] },
end

/-- Given two partial linear maps that agree on the intersection of their domains,
`f.sup g h` is the unique partial linear map on `f.domain ⊔ g.domain` that agrees
with `f` and `g`. -/
protected noncomputable def sup (f g : linear_pmap R E F)
  (h : ∀ (x : f.domain) (y : g.domain), (x:E) = y → f x = g y) :
  linear_pmap R E F :=
⟨_, classical.some (sup_aux f g h)⟩

@[simp] lemma domain_sup (f g : linear_pmap R E F)
  (h : ∀ (x : f.domain) (y : g.domain), (x:E) = y → f x = g y) :
  (f.sup g h).domain = f.domain ⊔ g.domain :=
rfl

lemma sup_apply {f g : linear_pmap R E F}
  (H : ∀ (x : f.domain) (y : g.domain), (x:E) = y → f x = g y)
  (x y z) (hz : (↑x:E) + ↑y = ↑z) :
  f.sup g H z = f x + g y :=
classical.some_spec (sup_aux f g H) x y z hz

protected lemma left_le_sup (f g : linear_pmap R E F)
  (h : ∀ (x : f.domain) (y : g.domain), (x:E) = y → f x = g y) :
  f ≤ f.sup g h :=
begin
  refine ⟨le_sup_left, λ z₁ z₂ hz, _⟩,
  rw [← add_zero (f _), ← g.map_zero],
  refine (sup_apply h _ _ _ _).symm,
  simpa
end

protected lemma right_le_sup (f g : linear_pmap R E F)
  (h : ∀ (x : f.domain) (y : g.domain), (x:E) = y → f x = g y) :
  g ≤ f.sup g h :=
begin
  refine ⟨le_sup_right, λ z₁ z₂ hz, _⟩,
  rw [← zero_add (g _), ← f.map_zero],
  refine (sup_apply h _ _ _ _).symm,
  simpa
end

protected lemma sup_le {f g h : linear_pmap R E F}
  (H : ∀ (x : f.domain) (y : g.domain), (x:E) = y → f x = g y)
  (fh : f ≤ h) (gh : g ≤ h) :
  f.sup g H ≤ h :=
have Hf : f ≤ (f.sup g H) ⊓ h, from le_inf (f.left_le_sup g H) fh,
have Hg : g ≤ (f.sup g H) ⊓ h, from le_inf (f.right_le_sup g H) gh,
le_of_eq_locus_ge $ sup_le Hf.1 Hg.1

/-- Hypothesis for `linear_pmap.sup` holds, if `f.domain` is disjoint with `g.domain`. -/
lemma sup_h_of_disjoint (f g : linear_pmap R E F) (h : disjoint f.domain g.domain)
  (x : f.domain) (y : g.domain) (hxy : (x:E) = y) :
  f x = g y :=
begin
  rw [disjoint_def] at h,
  have hy : y = 0, from subtype.eq (h y (hxy ▸ x.2) y.2),
  have hx : x = 0, from subtype.eq (hxy.trans $ congr_arg _ hy),
  simp [*]
end

section

variables {K : Type*} [division_ring K] [module K E] [module K F]

/-- Extend a `linear_pmap` to `f.domain ⊔ K ∙ x`. -/
noncomputable def sup_span_singleton (f : linear_pmap K E F) (x : E) (y : F) (hx : x ∉ f.domain) :
  linear_pmap K E F :=
f.sup (mk_span_singleton x y (λ h₀, hx $ h₀.symm ▸ f.domain.zero_mem)) $
  sup_h_of_disjoint _ _ $ by simpa [disjoint_span_singleton]

@[simp] lemma domain_sup_span_singleton (f : linear_pmap K E F) (x : E) (y : F)
  (hx : x ∉ f.domain) :
  (f.sup_span_singleton x y hx).domain = f.domain ⊔ K ∙ x := rfl

@[simp] lemma sup_span_singleton_apply_mk (f : linear_pmap K E F) (x : E) (y : F)
  (hx : x ∉ f.domain) (x' : E) (hx' : x' ∈ f.domain) (c : K) :
  f.sup_span_singleton x y hx ⟨x' + c • x,
    mem_sup.2 ⟨x', hx', _, mem_span_singleton.2 ⟨c, rfl⟩, rfl⟩⟩ = f ⟨x', hx'⟩ + c • y :=
begin
  erw [sup_apply _ ⟨x', hx'⟩ ⟨c • x, _⟩, mk_span_singleton_apply],
  refl,
  exact mem_span_singleton.2 ⟨c, rfl⟩
end

end

private lemma Sup_aux (c : set (linear_pmap R E F)) (hc : directed_on (≤) c) :
  ∃ f : ↥(Sup (domain '' c)) →ₗ[R] F, (⟨_, f⟩ : linear_pmap R E F) ∈ upper_bounds c :=
begin
  cases c.eq_empty_or_nonempty with ceq cne, { subst c, simp },
  have hdir : directed_on (≤) (domain '' c),
    from directed_on_image.2 (hc.mono domain_mono.monotone),
  have P : Π x : Sup (domain '' c), {p : c // (x : E) ∈ p.val.domain },
  { rintros x,
    apply classical.indefinite_description,
    have := (mem_Sup_of_directed (cne.image _) hdir).1 x.2,
    rwa [bex_image_iff, set_coe.exists'] at this },
  set f : Sup (domain '' c) → F := λ x, (P x).val.val ⟨x, (P x).property⟩,
  have f_eq : ∀ (p : c) (x : Sup (domain '' c)) (y : p.1.1) (hxy : (x : E) = y), f x = p.1 y,
  { intros p x y hxy,
    rcases hc (P x).1.1 (P x).1.2 p.1 p.2 with ⟨q, hqc, hxq, hpq⟩,
    refine (hxq.2 _).trans (hpq.2 _).symm,
    exacts [of_le hpq.1 y, hxy, rfl] },
  refine ⟨{ to_fun := f, .. }, _⟩,
  { intros x y,
    rcases hc (P x).1.1 (P x).1.2 (P y).1.1 (P y).1.2 with ⟨p, hpc, hpx, hpy⟩,
    set x' := of_le hpx.1 ⟨x, (P x).2⟩,
    set y' := of_le hpy.1 ⟨y, (P y).2⟩,
    rw [f_eq ⟨p, hpc⟩ x x' rfl, f_eq ⟨p, hpc⟩ y y' rfl, f_eq ⟨p, hpc⟩ (x + y) (x' + y') rfl,
      map_add] },
  { intros c x,
    rw [f_eq (P x).1 (c • x) (c • ⟨x, (P x).2⟩) rfl, ← map_smul] },
  { intros p hpc,
    refine ⟨le_Sup $ mem_image_of_mem domain hpc, λ x y hxy, eq.symm _⟩,
    exact f_eq ⟨p, hpc⟩ _ _ hxy.symm }
end

/-- Glue a collection of partially defined linear maps to a linear map defined on `Sup`
of these submodules. -/
protected noncomputable def Sup (c : set (linear_pmap R E F)) (hc : directed_on (≤) c) :
  linear_pmap R E F :=
⟨_, classical.some $ Sup_aux c hc⟩

protected lemma le_Sup {c : set (linear_pmap R E F)} (hc : directed_on (≤) c)
  {f : linear_pmap R E F} (hf : f ∈ c) : f ≤ linear_pmap.Sup c hc :=
classical.some_spec (Sup_aux c hc) hf

protected lemma Sup_le {c : set (linear_pmap R E F)} (hc : directed_on (≤) c)
  {g : linear_pmap R E F} (hg : ∀ f ∈ c, f ≤ g) : linear_pmap.Sup c hc ≤ g :=
le_of_eq_locus_ge $ Sup_le $ λ _ ⟨f, hf, eq⟩, eq ▸
have f ≤ (linear_pmap.Sup c hc) ⊓ g, from le_inf (linear_pmap.le_Sup _ hf) (hg f hf),
this.1

end linear_pmap

namespace linear_map

/-- Restrict a linear map to a submodule, reinterpreting the result as a `linear_pmap`. -/
def to_pmap (f : E →ₗ[R] F) (p : submodule R E) : linear_pmap R E F :=
⟨p, f.comp p.subtype⟩

@[simp] lemma to_pmap_apply (f : E →ₗ[R] F) (p : submodule R E) (x : p) :
  f.to_pmap p x = f x := rfl

/-- Compose a linear map with a `linear_pmap` -/
def comp_pmap (g : F →ₗ[R] G) (f : linear_pmap R E F) : linear_pmap R E G :=
{ domain := f.domain,
  to_fun := g.comp f.to_fun }

@[simp] lemma comp_pmap_apply (g : F →ₗ[R] G) (f : linear_pmap R E F) (x) :
  g.comp_pmap f x = g (f x) := rfl

end linear_map

namespace linear_pmap

/-- Restrict codomain of a `linear_pmap` -/
def cod_restrict (f : linear_pmap R E F) (p : submodule R F) (H : ∀ x, f x ∈ p) :
  linear_pmap R E p :=
{ domain := f.domain,
  to_fun := f.to_fun.cod_restrict p H }

/-- Compose two `linear_pmap`s -/
def comp (g : linear_pmap R F G) (f : linear_pmap R E F)
  (H : ∀ x : f.domain, f x ∈ g.domain) :
  linear_pmap R E G :=
g.to_fun.comp_pmap $ f.cod_restrict _ H

/-- `f.coprod g` is the partially defined linear map defined on `f.domain × g.domain`,
and sending `p` to `f p.1 + g p.2`. -/
def coprod (f : linear_pmap R E G) (g : linear_pmap R F G) :
  linear_pmap R (E × F) G :=
{ domain := f.domain.prod g.domain,
  to_fun := (f.comp (linear_pmap.fst f.domain g.domain) (λ x, x.2.1)).to_fun +
    (g.comp (linear_pmap.snd f.domain g.domain) (λ x, x.2.2)).to_fun }

@[simp] lemma coprod_apply (f : linear_pmap R E G) (g : linear_pmap R F G) (x) :
  f.coprod g x = f ⟨(x : E × F).1, x.2.1⟩ + g ⟨(x : E × F).2, x.2.2⟩ :=
rfl

end linear_pmap
