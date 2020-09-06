import data.qpf.univariate.basic
import data.qpf.indexed.basic
import control.bifunctor

universes u
variables {F : Type u → Type u} [functor F]

namespace qpf

section box
variables (F)

/-- apply a functor to a set of values. taken from
 [Basil Fürer, Andreas Lochbihler, Joshua Schneider, Dmitriy Traytel *Quotients of Bounded Natural Functors*][fuerer-lochbihler-schneider-traytel2020]
henceforth referred to as the QBNF paper
 -/
def box {α} (A : set α) : set (F α) :=
{ x | ∀ β (f g : α → β), (∀ a ∈ A, f a = g a) → f <$> x = g <$> x }

variables {F}

/--
Alternate notion of support set based on `box`.
Taken from the QBNF paper
-/
def supp' {α} (x : F α) : set α :=
⋂ A ∈ { A : set α | x ∈ box F A}, A

/--
Alternate notion of predicate lifting based on `box`.
Taken from the QBNF paper
-/
def liftp' {α} (x : F α) (p : α → Prop) : Prop :=
∀ a ∈ supp' x, p a

end box

end qpf


namespace ex

/-- polynomial functor isomorph to `α × _` for some `α` -/
def prod.pfunctor (α : Type) : pfunctor :=
⟨ α, λ _, unit ⟩

instance {α} : qpf (prod α) :=
{ P := prod.pfunctor α,
  abs := λ β ⟨a,f⟩, (a, f ()),
  repr := λ β ⟨x,y⟩, ⟨x, λ _, y⟩,
  abs_repr := λ β ⟨x,y⟩, rfl,
  abs_map := λ β γ f ⟨a,g⟩, rfl }

/-- example relation for products -/
def foo.R (α : Type) (x y : bool × α) : Prop :=
x.1 = y.1 ∧ (x.1 → x.2 = y.2)

lemma equivalence_foo.R (α) : equivalence (foo.R α) :=
begin
  refine ⟨_,_,_⟩,
  { intro, exact ⟨rfl,λ _, rfl⟩ },
  { intros x y h, refine ⟨h.1.symm, λ _, (h.2 _).symm⟩,
    rwa h.1 },
  { rintros x y z ⟨ha,ha'⟩ ⟨hb,hb'⟩,
    refine ⟨ha.trans hb, λ hh, _⟩,
    refine (ha' hh).trans (hb' _),
    rwa ← ha }
end

/-- example of a qpf -/
def foo (α : Type) :=
quot $ foo.R α

instance {α} [inhabited α] : inhabited (foo α) := ⟨ quot.mk _ (default _) ⟩

/-- functor operation of `foo` -/
def foo.map {α β} (f : α → β) (x : foo α) : foo β :=
quot.lift_on x (λ x : bool × α, quot.mk (foo.R β) $ f <$> x)
  (λ ⟨a₀,a₁⟩ ⟨b₀,b₁⟩ h, quot.sound ⟨h.1,λ h', show f a₁ = f b₁, from congr_arg f (h.2 h')⟩)

instance : functor foo :=
{ map := @foo.map }

@[simp]
lemma foo.map_mk {α β : Type} (f : α → β) (x : bool × α) :
  (f <$> quot.mk _ x : foo β) = quot.mk _ (f <$> x) :=
by simp [(<$>),foo.map]

noncomputable instance qpf.foo : qpf foo :=
@qpf.quotient_qpf (prod bool) _ ex.qpf foo _ (λ α, quot.mk _) (λ α, quot.out)
  (by simp)
  (by intros; simp)

/-- constructor for `foo` -/
def foo.mk {α} (b : bool) (x : α) : foo α := quot.mk _ (b, x)

@[simp]
lemma foo.map_mk' {α β : Type} (f : α → β) (b : bool) (x : α) :
  f <$> foo.mk b x = foo.mk b (f x) :=
by simp only [foo.mk, foo.map_mk]; refl

@[simp]
lemma foo.map_tt {α : Type} (x y : α) :
  foo.mk tt x = foo.mk tt y ↔ x = y :=
by simp [foo.mk]; split; intro h; [replace h := quot.exact _ h, rw h];
   rw relation.eqv_gen_iff_of_equivalence at h;
   [exact h.2 rfl, apply equivalence_foo.R]

/-- consequence of original definition of `supp`. If there exists more than
one value of type `α`, then the support of `foo.mk ff x` is empty -/
lemma supp_mk_ff₀ {α} (x y : α) (h : ¬ x = y) : functor.supp (foo.mk ff x) = {} :=
begin
  dsimp [functor.supp], ext z, simp, -- split; intro h,
  classical, by_cases x = z,
  { use (λ a, ¬ z = a), subst z,
    dsimp [functor.liftp],
    simp, refine ⟨foo.mk ff ⟨y,h⟩,_⟩,
    simp, apply quot.sound, simp [foo.R] },
  { use (λ a, x = a),
    dsimp [functor.liftp],
    simp [h], use foo.mk ff ⟨x,rfl⟩,
    simp }
end

/-- consequence of original definition of `supp`. If there exists only
one value of type `α`, then the support of `foo.mk ff x` contains that value -/
lemma supp_mk_ff₁ {α} (x : α) (h : ∀ z, x = z) : functor.supp (foo.mk ff x) = {x} :=
begin
  dsimp [functor.supp], ext y, simp, split; intro h',
  { apply @h' (= x), dsimp [functor.liftp],
    use foo.mk ff ⟨x,rfl⟩, refl },
  { introv hp, simp [functor.liftp] at hp,
    rcases hp with ⟨⟨z,z',hz⟩,hp⟩,
    simp at hp, convert hz,
    rw [h'], apply h },
end

/--
Such a QPF is not uniform
-/
lemma foo_not_uniform : ¬ @qpf.is_uniform foo _ qpf.foo :=
begin
  simp only [qpf.is_uniform, foo, qpf.foo, set.image_univ, not_forall, not_imp],
  existsi [bool,ff,ff,λ a : unit, tt,λ a : unit, ff], split,
  { apply quot.sound, simp [foo.R,qpf.abs,qpf._match_1], },
  { simp! only [set.range, set.ext_iff],
    simp only [not_exists, false_iff, bool.forall_bool, eq_self_iff_true, exists_false, not_true,
      and_self, set.mem_set_of_eq, iff_false],
    exact λ h, h () }
end

/-- intuitive consequence of original definition of `supp`. -/
lemma supp_mk_tt {α} (x : α) : functor.supp (foo.mk tt x) = {x} :=
begin
  dsimp [functor.supp], ext y, simp, split; intro h',
  { apply @h' (= x), dsimp [functor.liftp],
    use foo.mk tt ⟨x,rfl⟩, refl },
  { introv hp, simp [functor.liftp] at hp,
    rcases hp with ⟨⟨z,z',hz⟩,hp⟩,
    simp at hp, replace hp := quot.exact _ hp,
    rw relation.eqv_gen_iff_of_equivalence (equivalence_foo.R _) at hp,
    rcases hp with ⟨⟨⟩,hp⟩, subst y,
    replace hp := hp rfl, cases hp,
    exact hz }
end

/-- simple consequence of the definition of `supp` from the QBNF paper -/
lemma supp_mk_ff' {α} (x : α) : qpf.supp' (foo.mk ff x) = {} :=
begin
  dsimp [qpf.supp'], ext, simp, dsimp [qpf.box],
  use ∅, simp [foo.mk], intros, apply quot.sound,
  dsimp [foo.R], split, refl, rintro ⟨ ⟩
end

/-- simple consequence of the definition of `supp` from the QBNF paper -/
lemma supp_mk_tt' {α} (x : α) : qpf.supp' (foo.mk tt x) = {x} :=
begin
  dsimp [qpf.supp'], ext, simp, dsimp [qpf.box], split; intro h,
  { specialize h {x} _, { simp at h, assumption },
    clear h, introv hfg, simp, rw hfg, simp },
  { introv hfg, subst x_1, classical,
    let f : α → α ⊕ bool := λ x, if x ∈ i then sum.inl x else sum.inr tt,
    let g : α → α ⊕ bool := λ x, if x ∈ i then sum.inl x else sum.inr ff,
    specialize hfg _ f g _,
    { simp [f,g] at hfg, split_ifs at hfg,
      assumption, cases hfg },
    { intros, simp [*,f,g,if_pos] } }
end
end ex

/-!
Example of constructions using `iqpf`

1. Length-indexed vectors
-/

namespace ex
local attribute [ext] fam.ext

inductive vec_shape (α : Type) (rec : ℕ → Type) : ℕ → Type
| nil : vec_shape 0
| cons {n} : α → rec n → vec_shape (n + 1)

inductive vec_branch (α : Type) :  Π i, vec_shape α (λ (_x : ℕ), unit) i → empty ⊕ ℕ → Type
| cons (x) {n} : vec_branch (n+1) (vec_shape.cons x ()) (sum.inr n)

def vec_shape.map (α : Type) (X Y : fam (empty ⊕ ℕ)) (f : X ⟶ Y) : Π i, vec_shape α (X ∘ sum.inr) i → vec_shape α (Y ∘ sum.inr) i
| 0 vec_shape.nil := vec_shape.nil
| (n+1) (vec_shape.cons x xs) := vec_shape.cons x (f _ xs)

def vec_shape' (α : Type) : fam (empty ⊕ ℕ) ⥤ fam ℕ :=
{ obj := λ f, vec_shape α (f ∘ sum.inr),
  map := λ X Y f, vec_shape.map α X Y f,
  map_id' := by intros; ext _ ⟨ ⟩; refl,
  map_comp' := by intros; ext _ ⟨ ⟩; refl }

def vec_P (α : Type) : ipfunctor (empty ⊕ ℕ) ℕ :=
⟨ vec_shape α (λ _, unit), vec_branch α ⟩

def unit' {I : Type} : fam I :=
λ _, unit

def abs {α} (f : fam (empty ⊕ ℕ)) : ipfunctor.obj (vec_P α) f ⟶ (vec_shape' α).obj f :=
λ i x,
       match i, x : Π i (x : ipfunctor.obj (vec_P α) f i), (vec_shape' α).obj f i with
       | 0, ⟨a,b⟩ := vec_shape.map _ ((vec_P α).B 0 a) _ b _ vec_shape.nil
       | j+1, ⟨a@(vec_shape.cons x ()),b⟩ := vec_shape.map _ ((vec_P α).B _ a) _ b _ (vec_shape.cons x $ @vec_branch.cons _ x j)
       end

def repr {α} (f : fam (empty ⊕ ℕ)) : (vec_shape' α).obj f ⟶ ipfunctor.obj (vec_P α) f :=
λ i x, (⟨vec_shape.map α f unit' (λ _ _, ()) i x, λ a b,
  match i, x, b with
  | nat.succ j, (vec_shape.cons a_1 a_2), b :=
    match a, b : Π a, vec_branch α (nat.succ j) (vec_shape.cons a_1 ()) a → f a with
    | sum.inr _, vec_branch.cons x := a_2
    end
  end ⟩ : ipfunctor.obj (vec_P α) f i)

instance {α} : iqpf (vec_shape' α) :=
{ P := vec_P α,
  abs := abs,
  repr := repr,
  abs_repr := by { intros, ext, cases x; refl },
  abs_map := by { intros, ext, cases x; cases i; [refl, rcases x_fst with _|⟨_,_,⟨⟨ ⟩⟩⟩]; refl }, }

end ex

/-!

2. rose-tree as mutual inductive types
-/

namespace ex_mutual

def pair (α) (β) : bool → Type
| tt := α
| ff := β

def pair.map {X X' Y Y'} (f : X → Y) (g : X' → Y') : pair X X' ⟶ pair Y Y' :=
λ b,
  match b : Π b : bool, pair X X' b ⟶ pair Y Y' b with
  | tt := f
  | ff := g
  end

/-!
Encoding

```lean
mutual inductive child, tree (α : Type)
with child : Type
| nil : child
| cons : tree → child → child
with tree : Type
| node : α → child → tree
```

as

```lean
inductive tree_child (α : Type) : bool → Type
| nil : tree_child ff
| cons : tree_child tt → tree_child ff → tree_child ff
| node : α → tree_child ff → tree_child tt
```

in turns encoded as functors `fam (empty ⊕ bool) ⥤ fam bool`
-/

inductive child_shape (f : empty ⊕ bool → Type) : Type
| nil : child_shape
| cons : f (sum.inr tt) → f (sum.inr ff) → child_shape

def child_shape.map {X Y : fam $ empty ⊕ bool} (f : X ⟶ Y) : child_shape X → child_shape Y
| child_shape.nil := child_shape.nil
| (child_shape.cons t xs) := child_shape.cons (f _ t) (f _ xs)

inductive tree_shape (α : Type) (f : empty ⊕ bool → Type) : Type
| node : α → f (sum.inr ff) → tree_shape

def tree_shape.map {α} {X Y : fam $ empty ⊕ bool} (f : X ⟶ Y) : tree_shape α X → tree_shape α Y
| (tree_shape.node x xs) := tree_shape.node x (f _ xs)

def mut_shape (α : Type) (f : fam $ empty ⊕ bool) : fam bool :=
pair (tree_shape α f) (child_shape f)

def mut_shape.map (α : Type) (X Y : fam $ empty ⊕ bool) (f : X ⟶ Y) : mut_shape α X ⟶ mut_shape α Y :=
pair.map (tree_shape.map f) (child_shape.map f)

def mut_shape' (α : Type) : fam (empty ⊕ bool) ⥤ fam bool :=
{ obj := mut_shape α,
  map := mut_shape.map α,
  map_id' := by intros; ext ⟨ ⟩ ⟨ ⟩ : 2; [refl, refl, skip]; ext ⟨ ⟩; refl,
  map_comp' := by intros; ext ⟨ ⟩ ⟨ ⟩ : 2; [refl, refl, skip]; ext ⟨ ⟩; refl }

inductive mut_children' (α : Type) : Π (i : bool), pair α bool i → (empty ⊕ bool) → Type u
| list_obj : mut_children' ff ff (sum.inr tt)
| list_tail : mut_children' ff ff (sum.inr ff)
| child (x) : mut_children' tt x (sum.inr ff)

def mut_P (α : Type) : ipfunctor (empty ⊕ bool) bool :=
{ A := pair α bool,
  B := mut_children' α }

def mut_P.abs {α} : Π (X : fam (empty ⊕ bool)), ipfunctor.obj (mut_P α) X ⟶ (mut_shape' α).obj X
| X tt := λ i, tree_shape.node i.1 $ i.2 _ $ mut_children'.child _
| X ff := λ i,
  match i with
  | ⟨tt,f⟩ := child_shape.nil
  | ⟨ff,f⟩ := child_shape.cons (f _ mut_children'.list_obj) (f _ mut_children'.list_tail)
  end

def mut_P.repr {α} : Π (X : fam (empty ⊕ bool)), (mut_shape' α).obj X ⟶ ipfunctor.obj (mut_P α) X
| X tt := λ i,
  match i with
  | tree_shape.node a b := ⟨a,λ j, sum.rec_on j
    (λ e, empty.elim e) $ λ b', bool.rec_on b' (λ c, b) (by intro x; cases x)⟩
  end
| X ff := λ i,
  match i with
  | child_shape.nil := ⟨tt,λ j, by intro x; cases x⟩
  | child_shape.cons x xs := ⟨ff,λ j a,
    match j, a with
    | sum.inr ff, mut_children'.list_tail := xs
    | sum.inr tt, mut_children'.list_obj := x
    end ⟩
  end

instance {α} : iqpf (mut_shape' α) :=
{ P := mut_P α,
  abs := mut_P.abs,
  repr := mut_P.repr,
  abs_repr := by intros; ext (_|_) (_|_); dsimp [(≫)]; try { refl }; ext ⟨ ⟩; refl,
  abs_map := by intros; ext (_|_) (_|_); dsimp [(≫)]; try { refl }; ext ⟨ ⟩; refl, }

end ex_mutual
