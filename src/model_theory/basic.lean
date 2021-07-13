/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.nat.basic
import data.set_like
import data.set.lattice
import order.closure

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
* A `first_order.language.Structure` interprets the symbols of a given `first_order.language` in the
  context of a given type.
* A `first_order.language.hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
* A `first_order.language.embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

namespace first_order

/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
structure language :=
(functions : ℕ → Type*) (relations : ℕ → Type*)

namespace language

/-- The empty language has no symbols. -/
def empty : language := ⟨λ _, pempty, λ _, pempty⟩

instance : inhabited language := ⟨empty⟩

/-- The type of constants in a given language. -/
@[nolint has_inhabited_instance] def const (L : language) := L.functions 0

variable (L : language)

/-- A language is relational when it has no function symbols. -/
class is_relational : Prop :=
(empty_functions : ∀ n, L.functions n → false)

/-- A language is algebraic when it has no relation symbols. -/
class is_algebraic : Prop :=
(empty_relations : ∀ n, L.relations n → false)

variable {L}

instance is_relational_of_empty_functions {symb : ℕ → Type*} : is_relational ⟨λ _, pempty, symb⟩ :=
⟨by { intro n, apply pempty.elim }⟩

instance is_algebraic_of_empty_relations {symb : ℕ → Type*}  : is_algebraic ⟨symb, λ _, pempty⟩ :=
⟨by { intro n, apply pempty.elim }⟩

instance is_relational_empty : is_relational (empty) := language.is_relational_of_empty_functions
instance is_algebraic_empty : is_algebraic (empty) := language.is_algebraic_of_empty_relations

variables (L) (M : Type*)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
class Structure :=
(fun_map : ∀{n}, L.functions n → (fin n → M) → M)
(rel_map : ∀{n}, L.relations n → (fin n → M) → Prop)

variables (N : Type*) [L.Structure M] [L.Structure N]

open first_order.language.Structure

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
protected structure hom :=
(to_fun : M → N)
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r x → rel_map r (to_fun ∘ x) . obviously)

localized "notation A ` →[`:25 L `] ` B := L.hom A B" in first_order

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
protected structure embedding extends M ↪ N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r (to_fun ∘ x) ↔ rel_map r x . obviously)

localized "notation A ` ↪[`:25 L `] ` B := L.embedding A B" in first_order

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
protected structure equiv extends M ≃ N :=
(map_fun' : ∀{n} (f : L.functions n) x, to_fun (fun_map f x) = fun_map f (to_fun ∘ x) . obviously)
(map_rel' : ∀{n} (r : L.relations n) x, rel_map r (to_fun ∘ x) ↔ rel_map r x . obviously)

localized "notation A ` ≃[`:25 L `] ` B := L.equiv A B" in first_order

variables {L M N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]

instance : has_coe_t L.const M :=
⟨λ c, fun_map c fin.elim0⟩

lemma fun_map_eq_coe_const {c : L.const} {x : fin 0 → M} :
  fun_map c x = c := congr rfl (funext fin.elim0)

namespace hom

@[simps] instance has_coe_to_fun : has_coe_to_fun (M →[L] N) :=
⟨(λ _, M → N), first_order.language.hom.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : M →[L] N} : f.to_fun = (f : M → N) := rfl

lemma coe_injective : @function.injective (M →[L] N) (M → N) coe_fn
| f g h := by {cases f, cases g, cases h, refl}

@[ext]
lemma ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma map_fun (φ : M →[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_const (φ : M →[L] N) (c : L.const) : φ c = c :=
(φ.map_fun c fin.elim0).trans (congr rfl (funext fin.elim0))

@[simp] lemma map_rel (φ : M →[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r x → rel_map r (φ ∘ x) := φ.map_rel' r x

variables (L) (M)
/-- The identity map from a structure to itself -/
@[refl] def id : M →[L] M :=
{ to_fun := id }

variables {L} {M}

instance : inhabited (M →[L] M) := ⟨id L M⟩

@[simp] lemma id_apply (x : M) :
  id L M x = x := rfl

/-- Composition of first-order homomorphisms -/
@[trans] def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P :=
{ to_fun := hnp ∘ hmn,
  map_rel' := λ _ _ _ h, by simp [h] }

@[simp] lemma comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end hom

namespace embedding

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ↪[L] N) :=
⟨(λ _, M → N), λ f, f.to_fun⟩

@[simp] lemma map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_const (φ : M ↪[L] N) (c : L.const) : φ c = c :=
(φ.map_fun c fin.elim0).trans (congr rfl (funext fin.elim0))

@[simp] lemma map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x := φ.map_rel' r x

/-- A first-order embedding is also a first-order homomorphism. -/
def to_hom (f : M ↪[L] N) : M →[L] N :=
{ to_fun := f }

@[simp]
lemma coe_to_hom {f : M ↪[L] N} : (f.to_hom : M → N) = f := rfl

lemma coe_injective : @function.injective (M ↪[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ↪[L] N) : function.injective f := f.to_embedding.injective

variables (L) (M)
/-- The identity embedding from a structure to itself -/
@[refl] def refl : M ↪[L] M :=
{ to_embedding := function.embedding.refl M }

variables {L} {M}

instance : inhabited (M ↪[L] M) := ⟨refl L M⟩

@[simp] lemma refl_apply (x : M) :
  refl L M x = x := rfl

/-- Composition of first-order embeddings -/
@[trans] def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P :=
{ to_fun := hnp ∘ hmn,
  inj' := hnp.injective.comp hmn.injective }

@[simp] lemma comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order embeddings is associative. -/
lemma comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end embedding

namespace equiv

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm] def symm (f : M ≃[L] N) : N ≃[L] M :=
{ map_fun' := λ n f' x, begin
    simp only [equiv.to_fun_as_coe],
    rw [equiv.symm_apply_eq],
    refine eq.trans _ (f.map_fun' f' (f.to_equiv.symm ∘ x)).symm,
    rw [← function.comp.assoc, equiv.to_fun_as_coe, equiv.self_comp_symm, function.comp.left_id]
  end,
  map_rel' := λ n r x, begin
    simp only [equiv.to_fun_as_coe],
    refine (f.map_rel' r (f.to_equiv.symm ∘ x)).symm.trans _,
    rw [← function.comp.assoc, equiv.to_fun_as_coe, equiv.self_comp_symm, function.comp.left_id]
  end,
  .. f.to_equiv.symm }

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ≃[L] N) :=
⟨(λ _, M → N), λ f, f.to_fun⟩

@[simp] lemma map_fun (φ : M ≃[L] N) {n : ℕ} (f : L.functions n) (x : fin n → M) :
  φ (fun_map f x) = fun_map f (φ ∘ x) := φ.map_fun' f x

@[simp] lemma map_const (φ : M ≃[L] N) (c : L.const) : φ c = c :=
(φ.map_fun c fin.elim0).trans (congr rfl (funext fin.elim0))

@[simp] lemma map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x := φ.map_rel' r x

/-- A first-order equivalence is also a first-order embedding. -/
def to_embedding (f : M ≃[L] N) : M ↪[L] N :=
{ to_fun := f,
  inj' := f.to_equiv.injective }

/-- A first-order equivalence is also a first-order embedding. -/
def to_hom (f : M ≃[L] N) : M →[L] N :=
{ to_fun := f }

@[simp] lemma to_embedding_to_hom (f : M ≃[L] N) : f.to_embedding.to_hom = f.to_hom := rfl

@[simp]
lemma coe_to_hom {f : M ≃[L] N} : (f.to_hom : M → N) = (f : M → N) := rfl

@[simp] lemma coe_to_embedding (f : M ≃[L] N) : (f.to_embedding : M → N) = (f : M → N) := rfl

lemma coe_injective : @function.injective (M ≃[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ≃[L] N) : function.injective f := f.to_embedding.injective

variables (L) (M)
/-- The identity equivalence from a structure to itself -/
@[refl] def refl : M ≃[L] M :=
{ to_equiv := equiv.refl M }

variables {L} {M}

instance : inhabited (M ≃[L] M) := ⟨refl L M⟩

@[simp] lemma refl_apply (x : M) :
  refl L M x = x := rfl

/-- Composition of first-order equivalences -/
@[trans] def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
{ to_fun := hnp ∘ hmn,
  .. (hmn.to_equiv.trans hnp.to_equiv) }

@[simp] lemma comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end equiv

section closed_under

open set

variables {n : ℕ} (f : L.functions n) (s : set M)

/-- Indicates that a set in a given structure is a closed under a function symbol. -/
def closed_under : Prop :=
∀ (x : fin n → M), (∀ i : fin n, x i ∈ s) → fun_map f x ∈ s

variable (L)

@[simp] lemma closed_under_univ : closed_under f (univ : set M) :=
λ _ _, mem_univ _

variables {L f s} {t : set M}

namespace closed_under

lemma inter (hs : closed_under f s) (ht : closed_under f t) :
  closed_under f (s ∩ t) :=
λ x h, mem_inter (hs x (λ i, mem_of_mem_inter_left (h i)))
  (ht x (λ i, mem_of_mem_inter_right (h i)))

lemma inf (hs : closed_under f s) (ht : closed_under f t) :
  closed_under f (s ⊓ t) := hs.inter ht

variables {S : set (set M)}

lemma Inf (hS : ∀ s, s ∈ S → closed_under f s) : closed_under f (Inf S) :=
λ x h s hs, hS s hs x (λ i, h i s hs)

end closed_under
end closed_under

variables (L) (M)

/-- A substructure of a structure `M` is a set closed under application of function symbols. -/
structure substructure :=
(carrier : set M)
(fun_mem : ∀{n}, ∀ (f : L.functions n), closed_under f carrier)

variables {L} {M}

namespace substructure

instance : set_like (L.substructure M) M :=
⟨substructure.carrier, λ p q h, by cases p; cases q; congr'⟩

/-- See Note [custom simps projection] -/
def simps.coe (S : L.substructure M) : set M := S
initialize_simps_projections substructure (carrier → coe)

@[simp]
lemma mem_carrier {s : L.substructure M} {x : M} : x ∈ s.carrier ↔ x ∈ s := iff.rfl

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {S T : L.substructure M}
  (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T := set_like.ext h

/-- Copy a substructure replacing `carrier` with a set that is equal to it. -/
protected def copy (S : L.substructure M) (s : set M) (hs : s = S) : L.substructure M :=
{ carrier := s,
  fun_mem := λ n f, hs.symm ▸ (S.fun_mem f) }

variable {S : L.substructure M}

@[simp] lemma coe_copy {s : set M} (hs : s = S) :
  (S.copy s hs : set M) = s := rfl

lemma copy_eq {s : set M} (hs : s = S) : S.copy s hs = S :=
set_like.coe_injective hs

lemma const_mem {c : L.const} : ↑c ∈ S :=
mem_carrier.2 (S.fun_mem c _ fin.elim0)

/-- The substructure `M` of the structure `M`. -/
instance : has_top (L.substructure M) :=
⟨{ carrier := set.univ,
   fun_mem := λ n f x h, set.mem_univ _ }⟩

instance : inhabited (L.substructure M) := ⟨⊤⟩

@[simp] lemma mem_top (x : M) : x ∈ (⊤ : L.substructure M) := set.mem_univ x

@[simp] lemma coe_top : ((⊤ : L.substructure M) : set M) = set.univ := rfl

/-- The inf of two substructures is their intersection. -/
instance : has_inf (L.substructure M) :=
⟨λ S₁ S₂,
  { carrier := S₁ ∩ S₂,
    fun_mem := λ n f, (S₁.fun_mem f).inf (S₂.fun_mem f) }⟩

@[simp]
lemma coe_inf (p p' : L.substructure M) : ((p ⊓ p' : L.substructure M) : set M) = p ∩ p' := rfl

@[simp]
lemma mem_inf {p p' : L.substructure M} {x : M} : x ∈ p ⊓ p' ↔ x ∈ p ∧ x ∈ p' := iff.rfl

instance : has_Inf (L.substructure M) :=
⟨λ s, { carrier := ⋂ t ∈ s, ↑t,
        fun_mem := λ n f, closed_under.Inf begin
          rintro _ ⟨t, rfl⟩,
          by_cases h : t ∈ s,
          { simpa [h] using t.fun_mem f },
          { simp [h] }
        end }⟩

@[simp, norm_cast]
lemma coe_Inf (S : set (L.substructure M)) :
  ((Inf S : L.substructure M) : set M) = ⋂ s ∈ S, ↑s := rfl

lemma mem_Inf {S : set (L.substructure M)} {x : M} : x ∈ Inf S ↔ ∀ p ∈ S, x ∈ p :=
  set.mem_bInter_iff

lemma mem_infi {ι : Sort*} {S : ι → L.substructure M} {x : M} : (x ∈ ⨅ i, S i) ↔ ∀ i, x ∈ S i :=
by simp only [infi, mem_Inf, set.forall_range_iff]

@[simp, norm_cast]
lemma coe_infi {ι : Sort*} {S : ι → L.substructure M} : (↑(⨅ i, S i) : set M) = ⋂ i, S i :=
by simp only [infi, coe_Inf, set.bInter_range]

/-- Substructures of a structure form a complete lattice. -/
instance : complete_lattice (L.substructure M) :=
{ le           := (≤),
  lt           := (<),
  top          := (⊤),
  le_top       := λ S x hx, mem_top x,
  inf          := (⊓),
  Inf          := has_Inf.Inf,
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (L.substructure M) $ λ s,
    is_glb.of_image (λ S T,
      show (S : set M) ≤ T ↔ S ≤ T, from set_like.coe_subset_coe) is_glb_binfi }

variable (L)

/-- The `L.substructure` generated by a set. -/
def closure : lower_adjoint (coe : L.substructure M → set M) := ⟨λ s, Inf {S | s ⊆ S},
  λ s S, ⟨set.subset.trans (λ x hx, mem_Inf.2 $ λ S hS, hS hx), λ h, Inf_le h⟩⟩

variables {L} {s : set M}

lemma mem_closure {x : M} : x ∈ closure L s ↔ ∀ S : L.substructure M, s ⊆ S → x ∈ S :=
mem_Inf

/-- The substructure generated by a set includes the set. -/
@[simp]
lemma subset_closure : s ⊆ closure L s := (closure L).le_closure s

@[simp]
lemma closed (S : L.substructure M) : (closure L).closed (S : set M) :=
congr rfl ((closure L).eq_of_le set.subset.rfl (λ x xS, mem_closure.2 (λ T hT, hT xS)))

open set

/-- A substructure `S` includes `closure L s` if and only if it includes `s`. -/
@[simp]
lemma closure_le : closure L s ≤ S ↔ s ⊆ S := (closure L).closure_le_closed_iff_le s S.closed

/-- Substructure closure of a set is monotone in its argument: if `s ⊆ t`,
then `closure L s ≤ closure L t`. -/
lemma closure_mono ⦃s t : set M⦄ (h : s ⊆ t) : closure L s ≤ closure L t :=
(closure L).monotone h

lemma closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure L s) : closure L s = S :=
(closure L).eq_of_le h₁ h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function symbols, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_eliminator] lemma closure_induction {p : M → Prop} {x} (h : x ∈ closure L s)
  (Hs : ∀ x ∈ s, p x)
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f (set_of p)) : p x :=
(@closure_le L M _ ⟨set_of p, λ n, Hfun⟩ _).2 Hs h

/-- If `s` is a dense set in a structure `M`, `substructure.closure L s = ⊤`, then in order to prove
that some predicate `p` holds for all `x : M` it suffices to verify `p x` for `x ∈ s`, and verify
that `p` is preserved under function symbols. -/
@[elab_as_eliminator] lemma dense_induction {p : M → Prop} (x : M) {s : set M}
  (hs : closure L s = ⊤) (Hs : ∀ x ∈ s, p x)
  (Hfun : ∀ {n : ℕ} (f : L.functions n), closed_under f (set_of p)) : p x :=
have ∀ x ∈ closure L s, p x, from λ x hx, closure_induction hx Hs (λ n, Hfun),
by simpa [hs] using this x

variables (L) (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (@closure L M _) coe :=
{ choice := λ s _, closure L s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

variables {L} {M}

/-- Closure of a substructure `S` equals `S`. -/
@[simp] lemma closure_eq : closure L (S : set M) = S := (substructure.gi L M).l_u_eq S

@[simp] lemma closure_empty : closure L (∅ : set M) = ⊥ :=
(substructure.gi L M).gc.l_bot

@[simp] lemma closure_univ : closure L (univ : set M) = ⊤ :=
@coe_top L M _ ▸ closure_eq ⊤

lemma closure_union (s t : set M) : closure L (s ∪ t) = closure L s ⊔ closure L t :=
(substructure.gi L M).gc.l_sup

lemma closure_Union {ι} (s : ι → set M) : closure L (⋃ i, s i) = ⨆ i, closure L (s i) :=
(substructure.gi L M).gc.l_supr

end substructure

namespace hom

open substructure

/-- The substructure of elements `x : M` such that `f x = g x` -/
def eq_locus (f g : M →[L] N) : substructure L M :=
{ carrier := {x : M | f x = g x},
  fun_mem := λ n fn x hx, by {
    have h : f ∘ x = g ∘ x := by { ext, repeat {rw function.comp_apply}, apply hx, },
    simp [h], } }

/-- If two `L.hom`s are equal on a set, then they are equal on its substructure closure. -/
lemma eq_on_closure {f g : M →[L] N} {s : set M} (h : set.eq_on f g s) :
  set.eq_on f g (closure L s) :=
show closure L s ≤ f.eq_locus g, from closure_le.2 h

lemma eq_of_eq_on_top {f g : M →[L] N} (h : set.eq_on f g (⊤ : substructure L M)) :
  f = g :=
ext $ λ x, h trivial

variable {s : set M}

lemma eq_of_eq_on_dense (hs : closure L s = ⊤) {f g : M →[L] N} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_top $ hs ▸ eq_on_closure h

end hom

end language
end first_order
