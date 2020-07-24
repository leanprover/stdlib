
import category_theory.category category_theory.types logic.relation

universes u v w

open category_theory

/-- Type family indexed by `I` as a category -/
@[reducible]
def fam (I : Type u) := I → Type u

instance {I} : has_one (fam I) :=
⟨ λ _, punit ⟩

namespace fam

variables  {I : Type u}

def drop {α : Type u} : fam (I ⊕ α) → fam I :=
λ x i, x (sum.inl i)

def last {α : Type u} : fam (I ⊕ α) → fam α :=
λ x i, x (sum.inr i)

def append1 {α : Type u} (f : fam I) (g : fam α) : fam (I ⊕ α)
| (sum.inl i) := f i
| (sum.inr i) := g i

end fam

section pis

variables {C : Type u} [𝒞 : category.{v} C]
include 𝒞

instance pi.category {α : Type w} : category $ α → C :=
{ hom := λ X Y, Π ⦃i⦄, X i ⟶ Y i,
  id := λ X i, 𝟙 (X i),
  comp := λ X Y Z f g i, @f i ≫ @g i }

end pis

instance fam.category {I : Type u} : category $ fam I :=
pi.category

namespace fam

variables {I J : Type u}

-- @[ext]
lemma ext (X Y : fam I) (f g : X ⟶ Y) (h : ∀ i (x : X i), f x = g x) : f = g :=
funext $ λ i, funext $ h _

def split_fun {α β : fam (I⊕J)} :
  Π (f : drop α ⟶ drop β) (g : last α ⟶ last β), α ⟶ β
| f g (sum.inl i) x := f x
| f g (sum.inr i) x := g x

def append_fun {α β : fam I} {α' β' : fam J} (f : α ⟶ β) (g : α' ⟶ β') : (α.append1 α' ⟶ β.append1 β') :=
split_fun f g

lemma split_fun_comp {α β γ : fam (I⊕J)}
  (f : drop α ⟶ drop β) (g : drop β ⟶ drop γ) (f' : last α ⟶ last β) (g' : last β ⟶ last γ) :
  split_fun (f ≫ g) (f' ≫ g') = split_fun f f' ≫ split_fun g g' :=
by ext (x|x) : 1; ext; refl

lemma append_fun_comp {α β γ : fam I} {α' β' γ' : fam J}
  (f : α ⟶ β) (f' : α' ⟶ β') (g : β ⟶ γ) (g' : β' ⟶ γ') :
  append_fun (f ≫ g) (f' ≫ g') = append_fun f f' ≫ append_fun g g' :=
by erw ← split_fun_comp; refl

lemma append_fun_comp_right {α γ : fam I} {α' β' γ' : fam J}
  (f : α ⟶ γ) (f' : α' ⟶ β') (g' : β' ⟶ γ') :
  append_fun f (f' ≫ g') = append_fun f f' ≫ append_fun (𝟙 _) g' :=
by erw ← split_fun_comp; refl

lemma split_fun_comp_right {α : fam (I⊕J)} {β γ : fam J} {γ' : fam I}
  (f : drop α ⟶ γ')
  (f' : last α ⟶ β) (g' : β ⟶ γ) :
  (split_fun f (f' ≫ g') : α ⟶ γ'.append1 γ) =
  (split_fun f f' : α ⟶ γ'.append1 β) ≫ split_fun (𝟙 _) g' :=
by rw [← split_fun_comp,category.comp_id]

def drop_fun {α β : fam (I⊕J)} : Π (f : α ⟶ β), drop α ⟶ drop β
| f i x := f x

def last_fun {α β : fam (I⊕J)} : Π (f : α ⟶ β), last α ⟶ last β
| f i x := f x

theorem eq_of_drop_last_eq {α β : fam (I⊕J)} {f g : α ⟶ β}
  (h₀ : ∀ j (x : α (sum.inl j)), drop_fun f x = drop_fun g x) (h₁ : last_fun f = last_fun g) :
  f = g :=
by { ext1 (i|j); ext1 x, apply h₀, apply congr_fun (congr_fun h₁ j), }
-- by ext1 i; rcases i with ⟨j, ieq⟩ | ieq; [apply h₀, apply h₁]

@[simp]
theorem split_drop_fun_last_fun {α α' : fam (I⊕J)} (f : α ⟶ α') :
  split_fun (drop_fun f) (last_fun f) = f :=
eq_of_drop_last_eq (λ _ _, rfl) (funext $ λ _, funext $ λ _, rfl)

theorem append_fun_id_id {α : fam I} {β : fam J} :
  append_fun (𝟙 α) (𝟙 β) = 𝟙 _ :=
by apply eq_of_drop_last_eq; intros; try { ext }; refl

inductive unit (i : I) : I → Type u
| rfl {} : unit i

def unit.star (i : I) : unit i i := unit.rfl

def value (i) (X : fam I) : X i → (unit i ⟶ X)
| x j unit.rfl := x

theorem value.get {i} {X : fam I} (f g : unit i ⟶ X) (h : f = g) : f unit.rfl = g unit.rfl :=
by rw h

theorem value.ext {i} {X : fam I} (f g : unit i ⟶ X) (h : f unit.rfl = g unit.rfl) : f = g :=
by ext _ ⟨ ⟩; exact h

@[simp]
lemma value_eq  (i) (X : fam I) (x : X i) : Π {u : unit i i}, value i X x u = x
| unit.rfl := rfl

section subtype

variables {F : fam I ⥤ fam J}

@[pp_nodot]
def Pred (α : fam I) : Sort* := ∀ i, α i → Prop

def Pred.mk {α : fam I} (p : Π i, (unit i ⟶ α) → Prop) : Pred α :=
λ i x, p i $ value i _ x

def Pred.apply {α : fam I} (p : Pred α) : ∀ ⦃i⦄, (unit i ⟶ α) → Prop :=
λ i f, p i $ f unit.rfl

@[simp]
lemma Pred.apply_mk {α : fam I} (p : Π i, (unit i ⟶ α) → Prop) :
  Pred.apply (Pred.mk p) = p :=
by ext : 2; simp [Pred.apply,Pred.mk]; congr'; ext _ ⟨ ⟩; refl

@[simp]
lemma Pred.mk_to_fun {α : fam I} (p : Π i, (unit i ⟶ α) → Prop) {i} (x : α i) :
  Pred.mk p i x = p i (value i _ x) := rfl

@[simp]
lemma Pred.mk_apply {α : fam I} (p : Pred α) :
  Pred.mk (Pred.apply p) = p := by ext; refl

def Pred.map {α β : fam I} (f : α ⟶ β) (p : Pred β) : Pred α :=
λ i x, p i (f x)

lemma Pred.map_mk {α β : fam I} (f : α ⟶ β) (p : Π ⦃i⦄, (unit i ⟶ β) → Prop) :
  Pred.map f (Pred.mk p) = Pred.mk (λ i g, p (g ≫ f)) :=
by ext; simp [Pred.mk,Pred.map]; congr'; ext _ ⟨ ⟩; refl

@[reducible]
def subtype {α : fam I} (p : Pred α) : fam I :=
λ i, subtype (p i)

def subtype.val {α : fam I} {p : Pred α} : fam.subtype p ⟶ α :=
λ i, subtype.val

def subtype.map {α β : fam I} (p : Pred α) (q : Pred β)
  (f : α ⟶ β) (h : ∀ i x, p i x → q i (f x)) :
  fam.subtype p ⟶ fam.subtype q :=
λ i (x : subtype p i), subtype.mk (f x.1) (h i _ x.2)

lemma subtype.ext {α : fam I} {p : Pred α } {X} (a b : X ⟶ subtype p)
  (h : a ≫ subtype.val = b ≫ subtype.val) : a = b :=
by ext : 2; rw subtype.ext_iff; apply congr_fun (congr_fun h x)

lemma subtype.map_val {α β : fam I} {p : Pred α} {q : Pred β} (a : α ⟶ β) (h) :
  subtype.map p q a h ≫ subtype.val = subtype.val ≫ a :=
by ext _ ⟨ ⟩ : 2; refl

def prod (α β : fam I) : fam I
| i := α i × β i

infix ` ⊗ `:35 := prod

def prod.fst : Π {α β : fam I}, α ⊗ β ⟶ α
| α β i x := _root_.prod.fst x

def prod.snd : Π {α β : fam I}, α ⊗ β ⟶ β
| α β i x := _root_.prod.snd x

def prod.map {α β α' β' : fam I} : (α ⟶ β) → (α' ⟶ β') → (α ⊗ α' ⟶ β ⊗ β')
| f g i x := (f x.1,g x.2)

infix ` ⊗ `:35 := prod.map

@[simp, reassoc]
lemma prod.map_fst {α β α' β' : fam I} (f : α ⟶ β) (g : α' ⟶ β') :
  prod.map f g ≫ prod.fst = prod.fst ≫ f :=
by ext; refl

@[simp, reassoc]
lemma prod.map_snd {α β α' β' : fam I} (f : α ⟶ β) (g : α' ⟶ β') :
  prod.map f g ≫ prod.snd = prod.snd ≫ g :=
by ext; refl

lemma prod.ext {α β β' : fam I} (f g : α ⟶ β ⊗ β')
  (h :  f ≫ prod.fst = g ≫ prod.fst)
  (h' : f ≫ prod.snd = g ≫ prod.snd) :
  f = g :=
by { ext i x,
     apply congr_fun (congr_fun h  i) x,
     apply congr_fun (congr_fun h' i) x }

@[simp]
lemma prod.map_id {α β : fam I} :
  prod.map (𝟙 α) (𝟙 β) = 𝟙 _ :=
by apply prod.ext; simp

@[simp, reassoc]
lemma prod.map_comp {α β γ α' β' γ' : fam I}
  (f :  α  ⟶ β)  (g  : β  ⟶ γ)
  (f' : α' ⟶ β') (g' : β' ⟶ γ') :
  prod.map f f' ≫ prod.map g g' = prod.map (f ≫ g) (f' ≫ g') :=
by apply prod.ext; simp

@[simp]
lemma prod.map_mk {α β α' β' : fam I}
  (f :  α  ⟶ β) (g  : α'  ⟶ β') {i} (x : α i) (y : α' i) :
  prod.map f g (x,y) = (f x,g y) :=
rfl

def diag : Π {α : fam I}, α ⟶ α ⊗ α
| α i x := (x,x)

@[reassoc]
lemma diag_map {α β : fam I} (f : α ⟶ β) : diag ≫ (f ⊗ f) = f ≫ diag :=
by ext; refl

@[reassoc]
lemma diag_map_fst_snd {α β : fam I} : diag ≫ (prod.fst ⊗ prod.snd) = 𝟙 (α ⊗ β) :=
by ext _ ⟨ ⟩; refl

@[reassoc]
lemma diag_map_comp {α β γ γ' : fam I} (f : α ⟶ β) (g : β ⟶ γ) (g' : β ⟶ γ') :
  diag ≫ (f ≫ g ⊗ f ≫ g') = f ≫ diag ≫ (g ⊗ g') :=
by ext; refl

@[reassoc]
lemma diag_map_fst_snd_comp {α β γ γ' : fam I} (g : α ⟶ γ) (g' : β ⟶ γ') :
  diag ≫ (prod.fst ≫ g ⊗ prod.snd ≫ g') = (g ⊗ g') :=
by ext _ ⟨ ⟩; refl

def sum (α β : fam I) : fam I
| i := α i ⊕ β i

infix ` ⊕' `:35 := sum

def sum.map {α β α' β' : fam I} : (α ⟶ β) → (α' ⟶ β') → (α ⊕' α' ⟶ β ⊕' β')
| f g i (sum.inl x) := sum.inl $ f x
| f g i (sum.inr x) := sum.inr $ g x

infix ` ⊕' `:35 := sum.map

def sum.inl : Π {α β : fam I}, α ⟶ α ⊕' β
| α β i x := _root_.sum.inl x

def sum.inr : Π {α β : fam I}, β ⟶ α ⊕' β
| α β i x := _root_.sum.inr x

@[simp, reassoc]
lemma sum.inl_map {α β α' β' : fam I} (f : α ⟶ β) (g : α' ⟶ β') :
  sum.inl ≫ sum.map f g = f ≫ sum.inl :=
by ext; refl

@[simp, reassoc]
lemma sum.inr_map {α β α' β' : fam I} (f : α ⟶ β) (g : α' ⟶ β') :
  sum.inr ≫ sum.map f g = g ≫ sum.inr :=
by ext; refl

lemma sum.ext {α β α' : fam I} (f g : α ⊕' α' ⟶ β)
  (h :  sum.inl ≫ f = sum.inl ≫ g)
  (h' : sum.inr ≫ f = sum.inr ≫ g) :
  f = g :=
by { ext i (x|x),
     apply congr_fun (congr_fun h  i) x,
     apply congr_fun (congr_fun h' i) x }

@[simp, reassoc]
lemma sum.map_comp {α β γ α' β' γ' : fam I}
  (f :  α  ⟶ β)  (g  : β  ⟶ γ)
  (f' : α' ⟶ β') (g' : β' ⟶ γ') :
  sum.map f f' ≫ sum.map g g' = sum.map (f ≫ g) (f' ≫ g') :=
by apply sum.ext; simp

def codiag : Π {α : fam I}, α ⊕' α ⟶ α
| α i (_root_.sum.inl x) := x
| α i (_root_.sum.inr x) := x

end subtype

@[simp]
lemma comp_app {α β γ : fam I} (f : α ⟶ β) (g : β ⟶ γ) {i} (x : α i) : (f ≫ g) x = g (f x) := rfl

protected def eq (α : fam I) : Pred (α ⊗ α) :=
λ i x, x.1 = x.2

def sat {X α : fam J} (f : X ⟶ α) (r : fam.Pred α) : Prop :=
∃ f' : X ⟶ subtype r, f = f' ≫ fam.subtype.val

infix ` ⊨ `:50 := sat

lemma congr_arrow {X Y : fam J} {f g : X ⟶ Y} (h : f = g) : ∀ ⦃i⦄ x, @f i x = @g i x :=
λ i, congr_fun (congr_fun h i)

lemma sat_intro {X α : fam J} (f : X ⟶ α) (p : fam.Pred α) (h : ∀ i x, p i (f x)) : f ⊨ p :=
⟨λ i x, ⟨f x,h i x⟩,by ext; refl⟩

lemma sat_elim {X α : fam J} (f : X ⟶ α) (p : fam.Pred α) : f ⊨ p → ∀ ⦃i⦄ x, p i (f x)
| ⟨a,b⟩ i x := b.symm ▸ (a x).property

lemma sat_mk_elim {X α : fam J} (f : X ⟶ α) (p : Π i, (unit i ⟶ α) → Prop) :
  f ⊨ Pred.mk p → ∀ ⦃i⦄ x, p i (x ≫ f)
| ⟨a,b⟩ i x := by convert (a $ x unit.rfl).property; ext _ ⟨ ⟩; rw b; refl

lemma sat_mk_intro {X α : fam J} (f : X ⟶ α) (p : Π i, (unit i ⟶ α) → Prop) (h : ∀ ⦃i⦄ x, p i (x ≫ f)) :
  f ⊨ Pred.mk p := sat_intro _ _ $ λ i x,
by simp; convert h (value i _ x); ext _ ⟨ ⟩; refl

lemma sat_map {α β X : fam J} (x : X ⟶ β) (f : β ⟶ α) (g : α ⟶ β)
  (r : Pred β) (hh : f ≫ g = 𝟙 _) :
  x ⊨ r → x ≫ f ⊨ r.map g
| ⟨h,h'⟩ := ⟨λ i y, ⟨f (h y).1,
  by { replace hh := congr_arrow hh, simp at hh,
       simp [Pred.map,hh], apply (h y).2 }⟩,
  by { ext, simp [h'], refl } ⟩

lemma sat_map₀ {α β X : fam J} (x : X ⟶ α) (g : α ⟶ β)
  (r : Pred β) :
  x ≫ g ⊨ r → x ⊨ r.map g
| ⟨h,h'⟩ := ⟨λ i y, ⟨x y,
  by { replace h' := congr_arrow h' y, simp at h',
       simp [Pred.map,h'], apply (h y).2 }⟩, by ext; refl⟩

lemma sat_map₁ {α β X : fam J} (x : X ⟶ α) (g : α ⟶ β)
  (r : Pred β) :
  x ⊨ r.map g → x ≫ g ⊨ r
| ⟨h,h'⟩ := ⟨λ i y, ⟨g (x y), h'.symm ▸ (h y).2⟩, by ext; refl ⟩

lemma comp_sat {α β X : fam J} (x : X ⟶ α) (g : α ⟶ β)
  (r : Pred β) :
  g ⊨ r → x ≫ g ⊨ r
| ⟨f,h⟩ := ⟨x ≫ f,by rw [h,category.assoc]⟩

-- lemma sat_map₀ {α β X : fam J} (x : X ⟶ α) (f : β ⟶ α) (g : α ⟶ β)
--   (r : Pred β) (hh : f ≫ g = 𝟙 _) :
--   x ≫ g ⊨ r → x ⊨ r.map g
-- | ⟨h,h'⟩ := ⟨λ i y, ⟨f (h y).1,
--   by { replace hh := congr_arrow hh, simp at hh,
--        simp [Pred.map,hh], apply (h y).2 }⟩,
--   by { ext, simp [h'], refl } ⟩

lemma sat_map' {α β X : fam J} (x : X ⟶ β) (f : β ⟶ α) (g : α ⟶ β)
  (r : Pred β) (hh : f ≫ g = 𝟙 _) :
  x ≫ f ⊨ r.map g → x ⊨ r
| ⟨h,h'⟩ := ⟨λ i x, ⟨g (h x).1,(h x).2⟩,
            by { ext, replace h' := congr_arrow h' x_2, simp [subtype.val] at h',
                 replace hh := congr_arrow hh, simp at hh,
                 simp [subtype.val,h'.symm,hh], refl }⟩

def quot {α : fam I} (r : Pred (α ⊗ α)) : fam I :=
λ i, quot (λ x y, r i (x,y))

namespace quot

variables {α β γ : fam I}  (r : Pred (α ⊗ α))

def lift (f : α ⟶ β)
  (h : ∀ {i} (a : unit i ⟶ α⊗α), a ⊨ r → a ≫ prod.fst ≫ f = a ≫ prod.snd ≫ f) :
  (quot r ⟶ β) :=
λ i x, quot.lift (@f i) (λ a b h',
  let d := value i (fam.subtype r) (subtype.mk (a,b) h') in
  value.get _ _ (h (value i _ (a,b)) ⟨d,by ext _ ⟨ ⟨ rfl ⟩ ⟩; refl⟩) ) x

-- def lift' ⦃i⦄ (f : α ⟶ β)
--   (h : ∀ (a : unit i ⟶ α⊗α), a ⊨ r → a ≫ prod.fst ≫ f = a ≫ prod.snd ≫ f) :
--   Π (x : unit i ⟶ quot r), unit i ⟶ β
-- | x _ unit.rfl := _root_.quot.lift (@f i) (λ a b h',
-- let h := h (value i _ (a,b)) ⟨value i (subtype r) ⟨(a,b),h'⟩,value.ext _ _ rfl⟩ in
-- value.get _ _ h) (x unit.rfl)

-- def of_unit (h : ∀ {i}, (unit i ⟶ α) → (unit i ⟶ β)) : α ⟶ β :=
-- λ i x, h (value i _ x) unit.rfl

-- λ j xx,
-- _root_.quot.lift (@f i) (λ a b h',
-- let h := h (value i _ _) in
-- _
-- ) (x xx)

def mk : α ⟶ quot r :=
λ (i : I) (x : α i), quot.mk _ x

noncomputable def out : quot r ⟶ α :=
λ i x, quot.out x

variables {r}

@[simp, reassoc]
lemma mk_lift_ (g : α ⟶ β) (h) :
  quot.mk r ≫ lift r g h = g :=
by ext; refl

@[reassoc, simp] -- keep that order: in _ ≫ g, g is a variable
lemma lift_comp (f : α ⟶ β) (g : β ⟶ γ) (h) :
  lift r f h ≫ g = lift r (f ≫ g) (by intros; reassoc h; rw h _ a_1) :=
by { ext, dsimp [lift,(≫)], induction x_1 using quot.ind, refl }

lemma lift_ext (f g : quot r ⟶ β)
      (hh : quot.mk r ≫ f = quot.mk r ≫ g) :
  f = g :=
begin
  ext a b, apply quot.induction_on b,
  intros y, apply congr_arrow hh
end

lemma sound (f : β ⟶ α⊗α)
      (hh : f ⊨ r) :
  f ≫ prod.fst ≫ quot.mk r = f ≫ prod.snd ≫ quot.mk r :=
begin
  cases hh with f' hh, rw hh,
  ext, simp [(≫)], apply quot.sound,
  rcases (f' x_1) with ⟨⟨a,b⟩,h⟩, exact h
end

lemma sound'' {f g : β ⟶ quot r} (f' g' : β ⟶ α)
      (hh : diag ≫ fam.prod.map f' g' ⊨ r)
      (hh_f : f = f' ≫ quot.mk r)
      (hh_g : g = g' ≫ quot.mk r) :
  f = g :=
by { ext; rw [hh_f,hh_g];
     apply _root_.quot.sound; cases hh with h h',
     replace h' := congr_arrow h' x_1,
     simp [fam.prod.map,diag] at h', erw [h'];
     apply subtype.property }

lemma sound' (f g : β ⟶ α)
      (hh : diag ≫ fam.prod.map f g ⊨ r) :
  f ≫ quot.mk r = g ≫ quot.mk r :=
by apply sound'' f g hh rfl rfl

lemma ind_on (f : β ⟶ quot r) : (∃ g, f = g ≫ quot.mk _) :=
⟨f ≫ fam.quot.out _, by ext; simp [mk,out]⟩

@[simp, reassoc]
lemma out_mk (r : Pred (α ⊗ α)) : quot.out r ≫ quot.mk r = 𝟙 _ :=
by ext; simp [mk,out]; refl

open function

@[simp, reassoc]
lemma prod.diag_fst : diag ≫ fam.prod.fst = 𝟙 α :=
by ext; refl

@[simp, reassoc]
lemma prod.diag_snd : diag ≫ fam.prod.snd = 𝟙 α :=
by ext; refl

/-- swap the components of a product -/
def prod.swap : α ⊗ β ⟶ β ⊗ α :=
diag ≫ (prod.snd ⊗ prod.fst)

@[simp, reassoc]
lemma prod.swap_fst : prod.swap ≫ fam.prod.fst = (fam.prod.snd : α ⊗ β ⟶ β) :=
by simp [prod.swap]

@[simp, reassoc]
lemma prod.swap_snd : prod.swap ≫ fam.prod.snd = (fam.prod.fst : α ⊗ β ⟶ α) :=
by simp [prod.swap]

/-- reassociate the components of two nested products -/
def prod.assoc : α ⊗ β ⊗ γ ⟶ α ⊗ (β ⊗ γ) :=
diag ≫ (prod.fst ≫ prod.fst ⊗ diag ≫ (prod.fst ≫ prod.snd ⊗ prod.snd))

/-- Projection from a product of three components to the
two left-most components -/
def lpair : α ⊗ β ⊗ γ ⟶ α ⊗ β := fam.prod.fst
/-- Projection from a product of three components to the
two right-most components -/
def rpair : α ⊗ β ⊗ γ ⟶ β ⊗ γ := fam.prod.snd ⊗ 𝟙 _
/-- Projection from a product of three components to the
left-most and right-most components -/
def sides : α ⊗ β ⊗ γ ⟶ α ⊗ γ := fam.prod.fst ⊗ 𝟙 _

/--
Definition of equivalence relations for predicates on products
-/
structure equiv (r : Pred (α ⊗ α)) : Prop :=
(refl : diag ⊨ r)
(symm : ∀ {i} (f : unit i ⟶ α ⊗ α), f ⊨ r → f ≫ prod.swap ⊨ r)
(trans : ∀ {i} (f : unit i ⟶ α ⊗ α ⊗ α), f ≫ lpair ⊨ r → f ≫ rpair ⊨ r → f ≫ sides ⊨ r)

lemma equiv.to_equivalence {r : Pred (α ⊗ α)} (h : equiv r) :
  ∀ i, equivalence $ curry (r i) :=
begin
  cases h, intro j, refine ⟨_,_,_⟩,
  { intros x, apply sat_elim _ _ h_refl },
  { intros x y h,
    have : value j (α ⊗ α) (x, y) ⊨ r,
    { apply sat_intro _ _, rintro _ ⟨ ⟩, exact h },
    specialize h_symm (value j _ (x,y)) this,
    exact sat_elim _ _ h_symm unit.rfl },
  { intros x y z h h',
    specialize h_trans (value j _ ((x,y),z)) _ _,
    { exact sat_elim _ _ h_trans unit.rfl },
    all_goals { apply sat_intro, rintros _ ⟨ ⟩, assumption }, },
end

lemma exact {r : Pred (β ⊗ β)} {f g : α ⟶ β} (h : f ≫ mk r = g ≫ mk r) (h' : equiv r) :
  diag ≫ (f ⊗ g) ⊨ r :=
begin
  apply sat_intro, intros i x,
  replace h' : ∀ i, equivalence $ curry (r i) := equiv.to_equivalence h',
  simp [diag,prod.map],
  change curry (r i) _ _, rw ← relation.eqv_gen_iff_of_equivalence (h' i),
  apply quot.exact, replace h := congr_arrow h x, simp [mk] at h, exact h,
end

lemma lift_eq_out (r : Pred (α ⊗ α)) (h : equiv r) (f : α ⟶ β) (h') : lift r f h' = out r ≫ f :=
lift_ext _ _
begin
  simp; ext i a, simp [out,mk],
  have : ∀ {i} x y, r i (x,y) → f x = f y,
  { intros j, introv hh, specialize h' (value j _ (x,y)) (sat_intro _ _ _),
    exact value.get _ _ h',
    rintro _ ⟨ ⟩, exact hh },
  replace h : ∀ i, equivalence $ curry (r i) := equiv.to_equivalence h,
  apply this, change curry (r i) _ _,
  rw ← relation.eqv_gen_iff_of_equivalence (h i),
  apply _root_.quot.exact,
  rw quot.out_eq, refl,
end

end quot

end fam
