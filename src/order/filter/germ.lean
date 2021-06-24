/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Abhimanyu Pallavi Sudhir
-/
import order.filter.basic
import algebra.module.pi

/-!
# Germ of a function at a filter

The germ of a function `f : α → β` at a filter `l : filter α` is the equivalence class of `f`
with respect to the equivalence relation `eventually_eq l`: `f ≈ g` means `∀ᶠ x in l, f x = g x`.

## Main definitions

We define

* `germ l β` to be the space of germs of functions `α → β` at a filter `l : filter α`;
* coercion from `α → β` to `germ l β`: `(f : germ l β)` is the germ of `f : α → β`
  at `l : filter α`; this coercion is declared as `has_coe_t`, so it does not require an explicit
  up arrow `↑`;
* coercion from `β` to `germ l β`: `(↑c : germ l β)` is the germ of the constant function
  `λ x:α, c` at a filter `l`; this coercion is declared as `has_lift_t`, so it requires an explicit
  up arrow `↑`, see [TPiL][TPiL_coe] for details.
* `map (F : β → γ) (f : germ l β)` to be the composition of a function `F` and a germ `f`;
* `map₂ (F : β → γ → δ) (f : germ l β) (g : germ l γ)` to be the germ of `λ x, F (f x) (g x)`
  at `l`;
* `f.tendsto lb`: we say that a germ `f : germ l β` tends to a filter `lb` if its representatives
  tend to `lb` along `l`;
* `f.comp_tendsto g hg` and `f.comp_tendsto' g hg`: given `f : germ l β` and a function
  `g : γ → α` (resp., a germ `g : germ lc α`), if `g` tends to `l` along `lc`, then the composition
  `f ∘ g` is a well-defined germ at `lc`;
* `germ.lift_pred`, `germ.lift_rel`: lift a predicate or a relation to the space of germs:
  `(f : germ l β).lift_pred p` means `∀ᶠ x in l, p (f x)`, and similarly for a relation.
[TPiL_coe]: https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes

We also define `map (F : β → γ) : germ l β → germ l γ` sending each germ `f` to `F ∘ f`.

For each of the following structures we prove that if `β` has this structure, then so does
`germ l β`:

* one-operation algebraic structures up to `comm_group`;
* `mul_zero_class`, `distrib`, `semiring`, `comm_semiring`, `ring`, `comm_ring`;
* `mul_action`, `distrib_mul_action`, `module`;
* `preorder`, `partial_order`, and `lattice` structures up to `bounded_lattice`;
* `ordered_cancel_comm_monoid` and `ordered_cancel_add_comm_monoid`.

## Tags

filter, germ
-/

namespace filter

variables {α β γ δ : Type*} {l : filter α} {f g h : α → β}

lemma const_eventually_eq' [ne_bot l] {a b : β} : (∀ᶠ x in l, a = b) ↔ a = b :=
eventually_const

lemma const_eventually_eq [ne_bot l] {a b : β} : ((λ _, a) =ᶠ[l] (λ _, b)) ↔ a = b :=
@const_eventually_eq' _ _ _ _ a b

lemma eventually_eq.comp_tendsto {f' : α → β} (H : f =ᶠ[l] f') {g : γ → α} {lc : filter γ}
  (hg : tendsto g lc l) :
  f ∘ g =ᶠ[lc] f' ∘ g :=
hg.eventually H

/-- Setoid used to define the space of germs. -/
def germ_setoid (l : filter α) (β : Type*) : setoid (α → β) :=
{ r := eventually_eq l,
  iseqv := ⟨eventually_eq.refl _, λ _ _, eventually_eq.symm, λ _ _ _, eventually_eq.trans⟩ }

/-- The space of germs of functions `α → β` at a filter `l`. -/
def germ (l : filter α) (β : Type*) : Type* := quotient (germ_setoid l β)

namespace germ

instance : has_coe_t (α → β) (germ l β) := ⟨quotient.mk'⟩

instance : has_lift_t β (germ l β) := ⟨λ c, ↑(λ (x : α), c)⟩

@[simp] lemma quot_mk_eq_coe (l : filter α) (f : α → β) : quot.mk _ f = (f : germ l β) := rfl

@[simp] lemma mk'_eq_coe (l : filter α) (f : α → β) : quotient.mk' f = (f : germ l β) := rfl

@[elab_as_eliminator]
lemma induction_on (f : germ l β) {p : germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
quotient.induction_on' f h

@[elab_as_eliminator]
lemma induction_on₂ (f : germ l β) (g : germ l γ) {p : germ l β → germ l γ → Prop}
  (h : ∀ (f : α → β) (g : α → γ), p f g) : p f g :=
quotient.induction_on₂' f g h

@[elab_as_eliminator]
lemma induction_on₃ (f : germ l β) (g : germ l γ) (h : germ l δ)
  {p : germ l β → germ l γ → germ l δ → Prop}
  (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p f g h) :
  p f g h :=
quotient.induction_on₃' f g h H

/-- Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l` to functions
eventually equal at `lc`, returns a map from `germ l β` to `germ lc δ`. -/
def map' {lc : filter γ} (F : (α → β) → (γ → δ)) (hF : (l.eventually_eq ⇒ lc.eventually_eq) F F) :
  germ l β → germ lc δ :=
quotient.map' F hF

/-- Given a germ `f : germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
def lift_on {γ : Sort*} (f : germ l β) (F : (α → β) → γ) (hF : (l.eventually_eq ⇒ (=)) F F) : γ :=
quotient.lift_on' f F hF

@[simp] lemma map'_coe {lc : filter γ} (F : (α → β) → (γ → δ))
  (hF : (l.eventually_eq ⇒ lc.eventually_eq) F F) (f : α → β) :
  map' F hF f = F f :=
rfl

@[simp, norm_cast] lemma coe_eq : (f : germ l β) = g ↔ (f =ᶠ[l] g) := quotient.eq'

alias coe_eq ↔ _ filter.eventually_eq.germ_eq

/-- Lift a function `β → γ` to a function `germ l β → germ l γ`. -/
def map (op : β → γ) : germ l β → germ l γ :=
map' ((∘) op) $ λ f g H, H.mono $ λ x H, congr_arg op H

@[simp] lemma map_coe (op : β → γ) (f : α → β) : map op (f : germ l β) = op ∘ f := rfl

@[simp] lemma map_id : map id = (id : germ l β → germ l β) := by { ext ⟨f⟩, refl }

lemma map_map (op₁ : γ → δ) (op₂ : β → γ) (f : germ l β) :
  map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
induction_on f $ λ f, rfl

/-- Lift a binary function `β → γ → δ` to a function `germ l β → germ l γ → germ l δ`. -/
def map₂ (op : β → γ → δ) : germ l β → germ l γ → germ l δ :=
quotient.map₂' (λ f g x, op (f x) (g x)) $ λ f f' Hf g g' Hg,
Hg.mp $ Hf.mono $ λ x Hf Hg, by simp only [Hf, Hg]

@[simp] lemma map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) :
  map₂ op (f : germ l β) g = λ x, op (f x) (g x) :=
rfl

/-- A germ at `l` of maps from `α` to `β` tends to `lb : filter β` if it is represented by a map
which tends to `lb` along `l`. -/
protected def tendsto (f : germ l β) (lb : filter β) : Prop :=
lift_on f (λ f, tendsto f l lb) $ λ f g H, propext (tendsto_congr' H)

@[simp, norm_cast] lemma coe_tendsto {f : α → β} {lb : filter β} :
  (f : germ l β).tendsto lb ↔ tendsto f l lb :=
iff.rfl

alias coe_tendsto ↔ _ filter.tendsto.germ_tendsto

/-- Given two germs `f : germ l β`, and `g : germ lc α`, where `l : filter α`, if `g` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def comp_tendsto' (f : germ l β) {lc : filter γ} (g : germ lc α) (hg : g.tendsto l) :
  germ lc β :=
lift_on f (λ f, g.map f) $ λ f₁ f₂ hF, (induction_on g $ λ g hg, coe_eq.2 $ hg.eventually hF) hg

@[simp] lemma coe_comp_tendsto' (f : α → β) {lc : filter γ} {g : germ lc α} (hg : g.tendsto l) :
  (f : germ l β).comp_tendsto' g hg = g.map f :=
rfl

/-- Given a germ `f : germ l β` and a function `g : γ → α`, where `l : filter α`, if `g` tends
to `l` along `lc : filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
def comp_tendsto (f : germ l β) {lc : filter γ} (g : γ → α) (hg : tendsto g lc l) :
  germ lc β :=
f.comp_tendsto' _ hg.germ_tendsto

@[simp] lemma coe_comp_tendsto (f : α → β) {lc : filter γ} {g : γ → α} (hg : tendsto g lc l) :
  (f : germ l β).comp_tendsto g hg = f ∘ g :=
rfl

@[simp] lemma comp_tendsto'_coe (f : germ l β) {lc : filter γ} {g : γ → α} (hg : tendsto g lc l) :
  f.comp_tendsto' _ hg.germ_tendsto = f.comp_tendsto g hg :=
rfl

@[simp, norm_cast] lemma const_inj [ne_bot l] {a b : β} : (↑a : germ l β) = ↑b ↔ a = b :=
coe_eq.trans $ const_eventually_eq

@[simp] lemma map_const (l : filter α) (a : β) (f : β → γ) :
  (↑a : germ l β).map f = ↑(f a) :=
rfl

@[simp] lemma map₂_const (l : filter α) (b : β) (c : γ) (f : β → γ → δ) :
  map₂ f (↑b : germ l β) ↑c = ↑(f b c) :=
rfl

@[simp] lemma const_comp_tendsto {l : filter α} (b : β) {lc : filter γ} {g : γ → α}
  (hg : tendsto g lc l) :
  (↑b : germ l β).comp_tendsto g hg = ↑b :=
rfl

@[simp] lemma const_comp_tendsto' {l : filter α} (b : β) {lc : filter γ} {g : germ lc α}
  (hg : g.tendsto l) :
  (↑b : germ l β).comp_tendsto' g hg = ↑b :=
induction_on g (λ _ _, rfl) hg

/-- Lift a predicate on `β` to `germ l β`. -/
def lift_pred (p : β → Prop) (f : germ l β) : Prop :=
lift_on f (λ f, ∀ᶠ x in l, p (f x)) $
λ f g H, propext $ eventually_congr $ H.mono $ λ x hx, hx ▸ iff.rfl

@[simp] lemma lift_pred_coe {p : β → Prop} {f : α → β} :
  lift_pred p (f : germ l β) ↔ ∀ᶠ x in l, p (f x) :=
iff.rfl

lemma lift_pred_const {p : β → Prop} {x : β} (hx : p x) :
  lift_pred p (↑x : germ l β) :=
eventually_of_forall $ λ y, hx

@[simp] lemma lift_pred_const_iff [ne_bot l] {p : β → Prop} {x : β} :
  lift_pred p (↑x : germ l β) ↔ p x :=
@eventually_const _ _ _ (p x)

/-- Lift a relation `r : β → γ → Prop` to `germ l β → germ l γ → Prop`. -/
def lift_rel (r : β → γ → Prop) (f : germ l β) (g : germ l γ) : Prop :=
quotient.lift_on₂' f g (λ f g, ∀ᶠ x in l, r (f x) (g x)) $
λ f g f' g' Hf Hg, propext $ eventually_congr $ Hg.mp $ Hf.mono $ λ x hf hg, hf ▸ hg ▸ iff.rfl

@[simp] lemma lift_rel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
  lift_rel r (f : germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) :=
iff.rfl

lemma lift_rel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) :
  lift_rel r (↑x : germ l β) ↑y :=
eventually_of_forall $ λ _, h

@[simp] lemma lift_rel_const_iff [ne_bot l] {r : β → γ → Prop} {x : β} {y : γ} :
  lift_rel r (↑x : germ l β) ↑y ↔ r x y :=
@eventually_const _ _ _ (r x y)

instance [inhabited β] : inhabited (germ l β) := ⟨↑(default β)⟩

section monoid

variables {M : Type*} {G : Type*}

@[to_additive]
instance [has_mul M] : has_mul (germ l M) := ⟨map₂ (*)⟩

@[simp, norm_cast, to_additive]
lemma coe_mul [has_mul M] (f g : α → M) : ↑(f * g) = (f * g : germ l M) := rfl

@[to_additive]
instance [has_one M] : has_one (germ l M) := ⟨↑(1:M)⟩

@[simp, norm_cast, to_additive]
lemma coe_one [has_one M] : ↑(1 : α → M) = (1 : germ l M) := rfl

@[to_additive]
instance [semigroup M] : semigroup (germ l M) :=
{ mul := (*), mul_assoc := by { rintros ⟨f⟩ ⟨g⟩ ⟨h⟩,
    simp only [mul_assoc, quot_mk_eq_coe, ← coe_mul] } }

@[to_additive]
instance [comm_semigroup M] : comm_semigroup (germ l M) :=
{ mul := (*),
  mul_comm := by { rintros ⟨f⟩ ⟨g⟩, simp only [mul_comm, quot_mk_eq_coe, ← coe_mul] },
  .. germ.semigroup }

@[to_additive add_left_cancel_semigroup]
instance [left_cancel_semigroup M] : left_cancel_semigroup (germ l M) :=
{ mul := (*),
  mul_left_cancel := λ f₁ f₂ f₃, induction_on₃ f₁ f₂ f₃ $ λ f₁ f₂ f₃ H,
    coe_eq.2 ((coe_eq.1 H).mono $ λ x, mul_left_cancel),
  .. germ.semigroup }

@[to_additive add_right_cancel_semigroup]
instance [right_cancel_semigroup M] : right_cancel_semigroup (germ l M) :=
{ mul := (*),
  mul_right_cancel := λ f₁ f₂ f₃, induction_on₃ f₁ f₂ f₃ $ λ f₁ f₂ f₃ H,
    coe_eq.2 $ (coe_eq.1 H).mono $ λ x, mul_right_cancel,
  .. germ.semigroup }

@[to_additive]
instance [monoid M] : monoid (germ l M) :=
{ mul := (*),
  one := 1,
  one_mul := λ f, induction_on f $ λ f, by { norm_cast, rw [one_mul] },
  mul_one := λ f, induction_on f $ λ f, by { norm_cast, rw [mul_one] },
  .. germ.semigroup }

/-- coercion from functions to germs as a monoid homomorphism. -/
@[to_additive]
def coe_mul_hom [monoid M] (l : filter α) : (α → M) →* germ l M := ⟨coe, rfl, λ f g, rfl⟩

/-- coercion from functions to germs as an additive monoid homomorphism. -/
add_decl_doc coe_add_hom

@[simp, to_additive]
lemma coe_coe_mul_hom [monoid M] : (coe_mul_hom l : (α → M) → germ l M) = coe := rfl

@[to_additive]
instance [comm_monoid M] : comm_monoid (germ l M) :=
{ mul := (*),
  one := 1,
  .. germ.comm_semigroup, .. germ.monoid }

@[to_additive]
instance [has_inv G] : has_inv (germ l G) := ⟨map has_inv.inv⟩

@[simp, norm_cast, to_additive]
lemma coe_inv [has_inv G] (f : α → G) : ↑f⁻¹ = (f⁻¹ : germ l G) := rfl

@[to_additive]
instance [has_div M] : has_div (germ l M) := ⟨map₂ (/)⟩

@[simp, norm_cast, to_additive]
lemma coe_div [has_div M] (f g : α → M) : ↑(f / g) = (f / g : germ l M) := rfl

@[to_additive]
instance [div_inv_monoid G] : div_inv_monoid (germ l G) :=
{ inv := has_inv.inv,
  div := has_div.div,
  div_eq_mul_inv := by { rintros ⟨f⟩ ⟨g⟩, exact congr_arg (quot.mk _) (div_eq_mul_inv f g) },
  .. germ.monoid }

@[to_additive]
instance [group G] : group (germ l G) :=
{ mul := (*),
  one := 1,
  mul_left_inv := by { rintros ⟨f⟩, exact congr_arg (quot.mk _) (mul_left_inv f) },
  .. germ.div_inv_monoid }

@[to_additive]
instance [comm_group G] : comm_group (germ l G) :=
{ mul := (*),
  one := 1,
  inv := has_inv.inv,
  .. germ.group, .. germ.comm_monoid }

end monoid

section ring

variables {R : Type*}

instance nontrivial [nontrivial R] [ne_bot l] : nontrivial (germ l R) :=
let ⟨x, y, h⟩ := exists_pair_ne R in ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩

instance [mul_zero_class R] : mul_zero_class (germ l R) :=
{ zero := 0,
  mul := (*),
  mul_zero := λ f, induction_on f $ λ f, by { norm_cast, rw [mul_zero] },
  zero_mul := λ f, induction_on f $ λ f, by { norm_cast, rw [zero_mul] } }

instance [distrib R] : distrib (germ l R) :=
{ mul := (*),
  add := (+),
  left_distrib := λ f g h, induction_on₃ f g h $ λ f g h, by { norm_cast, rw [left_distrib] },
  right_distrib := λ f g h, induction_on₃ f g h $ λ f g h, by { norm_cast, rw [right_distrib] } }

instance [semiring R] : semiring (germ l R) :=
{ .. germ.add_comm_monoid, .. germ.monoid, .. germ.distrib, .. germ.mul_zero_class }

/-- Coercion `(α → R) → germ l R` as a `ring_hom`. -/
def coe_ring_hom [semiring R] (l : filter α) : (α → R) →+* germ l R :=
{ to_fun := coe, .. (coe_mul_hom l : _ →* germ l R), .. (coe_add_hom l : _ →+ germ l R) }

@[simp] lemma coe_coe_ring_hom [semiring R] : (coe_ring_hom l : (α → R) → germ l R) = coe := rfl

instance [ring R] : ring (germ l R) :=
{ .. germ.add_comm_group, .. germ.monoid, .. germ.distrib, .. germ.mul_zero_class }

instance [comm_semiring R] : comm_semiring (germ l R) :=
{ .. germ.semiring, .. germ.comm_monoid }

instance [comm_ring R] : comm_ring (germ l R) :=
{ .. germ.ring, .. germ.comm_monoid }

end ring

section module

variables {M N R : Type*}

instance [has_scalar M β]  : has_scalar M (germ l β) :=
⟨λ c, map ((•) c)⟩

instance has_scalar' [has_scalar M β] : has_scalar (germ l M) (germ l β) :=
⟨map₂ (•)⟩

@[simp, norm_cast] lemma coe_smul [has_scalar M β] (c : M) (f : α → β) :
  ↑(c • f) = (c • f : germ l β) :=
rfl

@[simp, norm_cast] lemma coe_smul' [has_scalar M β] (c : α → M) (f : α → β) :
  ↑(c • f) = (c : germ l M) • (f : germ l β) :=
rfl

instance [monoid M] [mul_action M β]  : mul_action M (germ l β) :=
{ one_smul := λ f, induction_on f $ λ f, by { norm_cast, simp only [one_smul] },
  mul_smul := λ c₁ c₂ f, induction_on f $ λ f, by { norm_cast, simp only [mul_smul] } }

instance mul_action' [monoid M] [mul_action M β]  : mul_action (germ l M) (germ l β) :=
{ one_smul := λ f, induction_on f $ λ f, by simp only [← coe_one, ← coe_smul', one_smul],
  mul_smul := λ c₁ c₂ f, induction_on₃ c₁ c₂ f $ λ c₁ c₂ f, by { norm_cast, simp only [mul_smul] } }

instance [monoid M] [add_monoid N] [distrib_mul_action M N] :
  distrib_mul_action M (germ l N) :=
{ smul_add := λ c f g, induction_on₂ f g $ λ f g, by { norm_cast, simp only [smul_add] },
  smul_zero := λ c, by simp only [← coe_zero, ← coe_smul, smul_zero] }

instance distrib_mul_action' [monoid M] [add_monoid N] [distrib_mul_action M N] :
  distrib_mul_action (germ l M) (germ l N) :=
{ smul_add := λ c f g, induction_on₃ c f g $ λ c f g, by { norm_cast, simp only [smul_add] },
  smul_zero := λ c, induction_on c $ λ c, by simp only [← coe_zero, ← coe_smul', smul_zero] }

instance [semiring R] [add_comm_monoid M] [module R M] :
  module R (germ l M) :=
{ add_smul := λ c₁ c₂ f, induction_on f $ λ f, by { norm_cast, simp only [add_smul] },
  zero_smul := λ f, induction_on f $ λ f, by { norm_cast, simp only [zero_smul, coe_zero] } }

instance module' [semiring R] [add_comm_monoid M] [module R M] :
  module (germ l R) (germ l M) :=
{ add_smul := λ c₁ c₂ f, induction_on₃ c₁ c₂ f $ λ c₁ c₂ f, by { norm_cast, simp only [add_smul] },
  zero_smul := λ f, induction_on f $ λ f, by simp only [← coe_zero, ← coe_smul', zero_smul] }

end module

instance [has_le β] : has_le (germ l β) :=
⟨lift_rel (≤)⟩

@[simp] lemma coe_le [has_le β] : (f : germ l β) ≤ g ↔ (f ≤ᶠ[l] g) := iff.rfl

lemma le_def [has_le β] : ((≤) : germ l β → germ l β → Prop) = lift_rel (≤) := rfl

lemma const_le [has_le β] {x y : β} (h : x ≤ y) : (↑x : germ l β) ≤ ↑y :=
lift_rel_const h

@[simp, norm_cast]
lemma const_le_iff [has_le β] [ne_bot l] {x y : β} : (↑x : germ l β) ≤ ↑y ↔ x ≤ y :=
lift_rel_const_iff

instance [preorder β] : preorder (germ l β) :=
{ le := (≤),
  le_refl := λ f, induction_on f $ eventually_le.refl l,
  le_trans := λ f₁ f₂ f₃, induction_on₃ f₁ f₂ f₃ $ λ f₁ f₂ f₃, eventually_le.trans }

instance [partial_order β] : partial_order (germ l β) :=
{ le := (≤),
  le_antisymm := λ f g, induction_on₂ f g $ λ f g h₁ h₂, (eventually_le.antisymm h₁ h₂).germ_eq,
  .. germ.preorder }

instance [has_bot β] : has_bot (germ l β) := ⟨↑(⊥:β)⟩

@[simp, norm_cast] lemma const_bot [has_bot β] : (↑(⊥:β) : germ l β) = ⊥ := rfl

instance [order_bot β] : order_bot (germ l β) :=
{ bot := ⊥,
  le := (≤),
  bot_le := λ f, induction_on f $ λ f, eventually_of_forall $ λ x, bot_le,
  .. germ.partial_order }

instance [has_top β] : has_top (germ l β) := ⟨↑(⊤:β)⟩

@[simp, norm_cast] lemma const_top [has_top β] : (↑(⊤:β) : germ l β) = ⊤ := rfl

instance [order_top β] : order_top (germ l β) :=
{ top := ⊤,
  le := (≤),
  le_top := λ f, induction_on f $ λ f, eventually_of_forall $ λ x, le_top,
  .. germ.partial_order }

instance [has_sup β] : has_sup (germ l β) := ⟨map₂ (⊔)⟩

@[simp, norm_cast] lemma const_sup [has_sup β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : germ l β) := rfl

instance [has_inf β] : has_inf (germ l β) := ⟨map₂ (⊓)⟩

@[simp, norm_cast] lemma const_inf [has_inf β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : germ l β) := rfl

instance [semilattice_sup β] : semilattice_sup (germ l β) :=
{ sup := (⊔),
  le_sup_left := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall $ λ x, le_sup_left,
  le_sup_right := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall $ λ x, le_sup_right,
  sup_le := λ f₁ f₂ g, induction_on₃ f₁ f₂ g $ λ f₁ f₂ g h₁ h₂,
    h₂.mp $ h₁.mono $ λ x, sup_le,
  .. germ.partial_order }

instance [semilattice_inf β] : semilattice_inf (germ l β) :=
{ inf := (⊓),
  inf_le_left := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall $ λ x, inf_le_left,
  inf_le_right := λ f g, induction_on₂ f g $ λ f g,
    eventually_of_forall $ λ x, inf_le_right,
  le_inf := λ f₁ f₂ g, induction_on₃ f₁ f₂ g $ λ f₁ f₂ g h₁ h₂,
    h₂.mp $ h₁.mono $ λ x, le_inf,
  .. germ.partial_order }

instance [semilattice_inf_bot β] : semilattice_inf_bot (germ l β) :=
{ .. germ.semilattice_inf, .. germ.order_bot }

instance [semilattice_sup_bot β] : semilattice_sup_bot (germ l β) :=
{ .. germ.semilattice_sup, .. germ.order_bot }

instance [semilattice_inf_top β] : semilattice_inf_top (germ l β) :=
{ .. germ.semilattice_inf, .. germ.order_top }

instance [semilattice_sup_top β] : semilattice_sup_top (germ l β) :=
{ .. germ.semilattice_sup, .. germ.order_top }

instance [lattice β] : lattice (germ l β) :=
{ .. germ.semilattice_sup, .. germ.semilattice_inf }

instance [bounded_lattice β] : bounded_lattice (germ l β) :=
{ .. germ.lattice, .. germ.order_bot, .. germ.order_top }

@[to_additive]
instance [ordered_cancel_comm_monoid β] : ordered_cancel_comm_monoid (germ l β) :=
{ mul_le_mul_left := λ f g, induction_on₂ f g $ λ f g H h, induction_on h $ λ h,
    H.mono $ λ x H, mul_le_mul_left' H _,
  le_of_mul_le_mul_left := λ f g h, induction_on₃ f g h $ λ f g h H,
    H.mono $ λ x, le_of_mul_le_mul_left',
  .. germ.partial_order, .. germ.comm_monoid, .. germ.left_cancel_semigroup }

@[to_additive]
instance ordered_comm_group [ordered_comm_group β] : ordered_comm_group (germ l β) :=
{ mul_le_mul_left := λ f g, induction_on₂ f g $ λ f g H h, induction_on h $ λ h,
    H.mono $ λ x H, mul_le_mul_left' H _,
  .. germ.partial_order, .. germ.comm_group }

end germ

end filter
