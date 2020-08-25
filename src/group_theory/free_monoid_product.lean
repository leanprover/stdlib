import algebra.free_monoid
import group_theory.congruence
import tactic.simp_rw
import algebra.opposites

def {u v} quot.lift_of_eq {α : Sort u} {β : Sort v} {r : α → α → Prop} (g : α → β)
  (f : quot r → β) (H : ∀ x, g x = f (quot.mk r x)) (x : quot r) : β :=
quot.lift_on x g $ λ x y h, by rw [H, H, quot.sound h]

@[simp]
lemma {u v} quot.lift_of_eq_eq {α : Sort u} {β : Sort v} {r : α → α → Prop} (g : α → β)
  (f : quot r → β) (H : ∀ x, g x = f (quot.mk r x)) :
  quot.lift_of_eq g f H = f :=
funext $ λ x, quot.induction_on x H

def mul_equiv.of_eq {M N : Type*} [has_mul M] [has_mul N] (e : M ≃* N) (f : M → N) (g : N → M)
  (hf : ⇑e = f) (hg : ⇑e.symm = g) : M ≃* N :=
⟨f, g, hf ▸ hg ▸ e.left_inv, hf ▸ hg ▸ e.right_inv, hf ▸ e.map_mul⟩

open opposite

variables {ι : Type*} (M : Π i : ι, Type*)

section

open free_monoid (of)

def free_monoid_product.con [Π i, monoid (M i)] :
  con (free_monoid $ Σ i, M i) :=
Inf {r | (∀ i x y, r (of ⟨i, x * y⟩) (of ⟨i, x⟩ * of ⟨i, y⟩)) ∧ (∀ i, r (of ⟨i, 1⟩) 1)}

def free_monoid_product [Π i, monoid (M i)] := (free_monoid_product.con M).quotient

end

namespace free_monoid_product

variables [Π i, monoid (M i)] {M}

instance : monoid (free_monoid_product M) := (con M).monoid

def mk : free_monoid (Σ i, M i) →* free_monoid_product M :=
(con M).mk'

def of (i : ι) : M i →* free_monoid_product M :=
{ to_fun := λ x, mk (free_monoid.of ⟨i, x⟩),
  map_one' := (con M).eq.2 $ λ r hr, hr.2 i,
  map_mul' := λ x y, (con M).eq.2 $ λ r hr, hr.1 i x y }

lemma mk_def : mk = (con M).mk' := rfl

@[simp] lemma quot_mk_eq_mk (x) : quot.mk (@setoid.r _ (con M).to_setoid) x = mk x := rfl

@[simp] lemma mk_of (i : ι) (x : M i) : mk (free_monoid.of ⟨i, x⟩) = of i x := rfl

lemma mk_cons (hd : Σ i, M i) (tl : free_monoid (Σ i, M i)) :
  mk (hd :: tl) = of hd.fst hd.snd * mk tl :=
by { cases hd, refl }

lemma mk_eq_mk {x y} : mk x = mk y ↔ con M x y := (con M).eq

lemma of_one (i : ι) : of i (1 : M i) = 1 := (of i).map_one

lemma of_mul (i : ι) (x y : M i) : of i (x * y) = of i x * of i y :=
(of i).map_mul x y

@[elab_as_eliminator]
lemma induction_on {C : free_monoid_product M → Prop} (y : free_monoid_product M)
  (h : ∀ x, C (mk x)) : C y :=
con.induction_on y h

@[elab_as_eliminator]
lemma induction_on' {C : free_monoid_product M → Prop} (y : free_monoid_product M)
  (h1 : C 1) (hcons : ∀ i (x : M i) l, C l → C ((of i x) * l)) : C y :=
induction_on y $ λ l, list.rec_on l h1 $ λ ⟨i, x⟩ tl htl, hcons i x (mk tl) htl

def lift_on {β : Type*} (x : free_monoid_product M) (f : free_monoid (Σ i, M i) → β)
  (hmul : ∀ ⦃x₁ x₂⦄ (hx : f x₁ = f x₂) ⦃y₁ y₂⦄ (hy : f y₁ = f y₂), f (x₁ * y₁) = f (x₂ * y₂))
  (h1 : ∀ i, f (free_monoid.of ⟨i, 1⟩) = f 1)
  (h : ∀ i x y, f (free_monoid.of ⟨i, x * y⟩) = f (free_monoid.of ⟨i, x⟩ * free_monoid.of ⟨i, y⟩)) :
  β :=
con.lift_on x f $ λ a b hab,
  hab { mul' := λ _ _ _ _ h₁ h₂, hmul h₁ h₂, .. setoid.comap f ⊥ } $ ⟨h, h1⟩

@[simp] lemma lift_on_mk {β : Type*} (x : free_monoid (Σ i, M i)) (f : free_monoid (Σ i, M i) → β)
  (hmul : ∀ ⦃x₁ x₂⦄ (hx : f x₁ = f x₂) ⦃y₁ y₂⦄ (hy : f y₁ = f y₂), f (x₁ * y₁) = f (x₂ * y₂))
  (h1 : ∀ i, f (free_monoid.of ⟨i, 1⟩) = f 1)
  (h : ∀ i x y, f (free_monoid.of ⟨i, x * y⟩) = f (free_monoid.of ⟨i, x⟩ * free_monoid.of ⟨i, y⟩)) :
  lift_on (mk x) f hmul h1 h = f x :=
rfl

@[ext] lemma hom_eq {N : Type*} [monoid N]  ⦃f g : free_monoid_product M →* N⦄
  (h : ∀ i (x : M i), f (of i x) = g (of i x)) : f = g :=
(monoid_hom.cancel_right con.mk'_surjective).1 $ free_monoid.hom_eq $ λ ⟨i, x⟩, h i x

section lift

variables (M) (N : Type*) [monoid N]

def lift : (Π i, M i →* N) ≃ (free_monoid_product M →* N) :=
{ to_fun := λ f, (con M).lift (free_monoid.lift (Σ i, M i) N $ λ x, f x.1 x.2) $
    Inf_le ⟨λ i x y,
      by simp only [con.ker_rel, monoid_hom.map_mul, free_monoid.lift_eval_of],
      λ i, by simp only [con.ker_rel, free_monoid.lift_eval_of, monoid_hom.map_one]⟩,
  inv_fun := λ f i, f.comp (of i),
  left_inv := λ f, by { ext i x, apply free_monoid.lift_eval_of },
  right_inv := λ f, hom_eq (λ i x, free_monoid.lift_eval_of _ _) }

variables {M N}

@[simp] lemma lift_of (f : Π i, M i →* N) (i : ι) (x : M i) :
  lift M N f (of i x) = f i x :=
free_monoid.lift_eval_of _ _

@[simp] lemma lift_mk (f : Π i, M i →* N) (x : free_monoid (Σ i, M i)) :
  lift M N f (mk x) = free_monoid.lift (Σ i, M i) N (λ a, f a.1 a.2) x :=
rfl

end lift

section group

variables {G : ι → Type*} [Π i, group (G i)]

def inv_aux (xs : free_monoid (Σ i, G i)) :
  free_monoid_product G :=
mk $ list.reverse $ list.map (λ x : Σ i, G i, ⟨x.fst, x.snd⁻¹⟩) xs

lemma inv_aux_mul_rev (xs ys : free_monoid (Σ i, G i)) :
  inv_aux (xs * ys) = inv_aux ys * inv_aux xs :=
begin
  dunfold inv_aux,
  rw [free_monoid.mul_def, list.map_append, list.reverse_append, ← free_monoid.mul_def,
    mk.map_mul]
end

lemma inv_aux_of (i : ι) (x : G i) : inv_aux (free_monoid.of ⟨i, x⟩) = of G i x⁻¹ := rfl

instance has_inv : has_inv (free_monoid_product G) :=
⟨λ x, lift_on x inv_aux
  (λ x₁ x₂ hx y₁ y₂ hy, by simp only [inv_aux_mul_rev, *])
  (λ i, by rw [inv_aux_of, one_inv, (of G i).map_one]; refl)
  (λ i x y, by simp only [inv_aux_of, inv_aux_mul_rev, mul_inv_rev, (of G i).map_mul])⟩

protected lemma mul_inv_rev (x y : free_monoid_product G) :
  (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
by rcases x; rcases y; exact inv_aux_mul_rev _ _

lemma of_inv (i x) : (of G i x)⁻¹ = of G i x⁻¹ := rfl

instance group : group (free_monoid_product G) :=
{ inv := has_inv.inv,
  mul_left_inv := λ x, show (λ x : free_monoid_product G, x⁻¹ * x = 1) x,
    from induction_on' x rfl $ λ i x xs hxs,
    by rw [free_monoid_product.mul_inv_rev, mul_assoc, ← mul_assoc _ _ xs, of_inv, ← of_mul,
      mul_left_inv, of_one, one_mul, hxs],
  .. free_monoid_product.monoid}

end group

def is_normalized : list (Σ i, {x : M i // x ≠ 1}) → Prop :=
list.chain' $ λ x y, x.fst ≠ y.fst

lemma is_normalized.replace_head {a b : Σ i, {x : M i // x ≠ 1}} {l : list _}
  (hbl : is_normalized (b::l)) (hab : a.1 = b.1) :
  is_normalized (a::l) :=
hbl.imp' (λ _ _, id) (λ c, hab ▸ id)

variables (M)

def normalized := subtype (@is_normalized _ M _)

variables {M} [decidable_eq ι] [Π i, decidable_eq (M i)]

namespace normalized

instance : decidable_pred (@is_normalized _ M _) := by delta is_normalized; apply_instance

def tail (x : normalized M) : normalized M := ⟨x.val.tail, x.property.tail⟩

instance : has_one (normalized M) := ⟨⟨[], trivial⟩⟩

@[simp] lemma one_val : (1 : normalized M).1 = [] := rfl

@[simp] lemma nil_eq_one (hl) : (⟨[], hl⟩ : normalized M) = (1 : normalized M) := rfl

/-- An unbundled version of the embedding `M i → free_monoid_product.normalized M`.
We will define a `monoid_hom` version later. -/
def of' (i : ι) (x : M i) : normalized M :=
if hx : x = 1 then 1 else ⟨[⟨i, x, hx⟩], list.chain'_singleton _⟩

local attribute [simp]
lemma of'_one (i : ι) : (of' i 1 : normalized M) = 1 := dif_pos rfl

lemma of'_of_ne {i : ι} {x : M i} (hx : x ≠ 1) :
  of' i x = ⟨[⟨i, x, hx⟩], list.chain'_singleton _⟩ :=
dif_neg hx

lemma of'_val {i} (x : {x : M i // x ≠ 1}) :
  (of' i x : normalized M) = ⟨[⟨i, x⟩], list.chain'_singleton _⟩ :=
subtype.cases_on x $ λ x hx, of'_of_ne hx

lemma length_of'_le (i : ι) (x : M i) : list.length (of' i x).1 ≤ 1 :=
if h : x = 1 then by simp only [h, of'_one, one_val, list.length, zero_le]
else by simp only [of'_of_ne h, list.length]

lemma fst_of_mem_of' {i : ι} {x : M i} {y : Σ i, {x : M i // x ≠ 1}} (h : y ∈ (of' i x).1) :
  y.1 = i :=
begin
  by_cases hx : x = 1,
  { simp only [hx, of'_one, one_val] at h,
    exact h.elim },
  { simp only [of', dif_neg hx, list.mem_singleton] at h,
    rw h }
end

lemma fst_of_mem_last'_of' {i : ι} {x : M i} ⦃y : Σ i, {x : M i // x ≠ 1}⦄
  (h : y ∈ (of' i x).1.last') :
  y.1 = i :=
fst_of_mem_of' $ list.mem_of_mem_last' h

def append (xs ys : normalized M)
  (h : ∀ (a ∈ list.last' xs.1) (b ∈ list.head' ys.1), sigma.fst a ≠ sigma.fst b) :
  normalized M :=
⟨xs.1 ++ ys.1, xs.2.append ys.2 h⟩

@[simp] lemma append_val {xs ys : normalized M} (h) : (xs.append ys h).1 = xs.1 ++ ys.1 := rfl

def cancel_two (a b : Σ i, {x : M i // x ≠ 1}) : normalized M :=
if hij : a.fst = b.fst then of' b.1 ((eq.rec_on hij a.snd) * b.snd)
else ⟨[a, b], list.chain'_pair.2 hij⟩

lemma fst_of_mem_last'_cancel_two {a b : Σ i, {x : M i // x ≠ 1}} :
  ∀ c ∈ list.last' (cancel_two a b).1, sigma.fst c = b.1 :=
begin
  delta cancel_two,
  split_ifs,
  { exact fst_of_mem_last'_of' },
  { simp [-sigma.forall] }
end

lemma cancel_two_same (i : ι) (a b : {x : M i // x ≠ 1}) :
  (cancel_two ⟨i, a⟩ ⟨i, b⟩ : normalized M) = of' i (a * b) :=
dif_pos rfl

lemma length_cancel_two_le (a b : Σ i, {x : M i // x ≠ 1}) :
  list.length (cancel_two a b).1 ≤ 2 :=
begin
  simp only [cancel_two],
  split_ifs,
  exacts [le_trans (length_of'_le _ _) (le_of_lt one_lt_two), le_refl 2]
end

def cons (a : Σ i, {x : M i // x ≠ 1}) : normalized M → normalized M
| ⟨[], _⟩ := ⟨[a], list.chain'_singleton a⟩
| ⟨b :: l, h⟩ := (cancel_two a b).append ⟨l, h.tail⟩ $ λ c hc,
(fst_of_mem_last'_cancel_two _ hc).symm ▸ h.rel_head'

instance : has_mul (normalized M) := ⟨λ xs ys, list.foldr cons ys xs.val⟩

@[simp] lemma cons_one (a : Σ i, {x : M i // x ≠ 1}) :
  cons a 1 = ⟨[a], list.chain'_singleton a⟩ := rfl

lemma cons_same (i : ι) (x y : {x : M i // x ≠ 1}) (l hbl) :
  cons ⟨i, x⟩ ⟨⟨i, y⟩ :: l, hbl⟩ = (of' i (x * y : M i)).append ⟨l, hbl.tail⟩
    (λ a ha, (fst_of_mem_last'_of' ha).symm ▸ hbl.rel_head') :=
by simp only [cons, cancel_two, append_val, dif_pos rfl]

lemma mul_def (xs ys : normalized M) : xs * ys = list.foldr cons ys xs.val := rfl

lemma cancel_two_of_ne {a b : Σ i, {x : M i // x ≠ 1}} (hab : a.1 ≠ b.1) :
  (cancel_two a b : normalized M) = ⟨[a, b], list.chain'_pair.2 hab⟩ :=
subtype.eq $ by simp [cancel_two, dif_neg hab]

lemma cons_of_ne {a : Σ i, {x : M i // x ≠ 1}} {l : normalized M}
  (h : ∀ b ∈ l.1.head', a.1 ≠ sigma.fst b) :
  cons a l = ⟨a :: l.1, l.2.cons' h⟩ :=
begin
  apply subtype.eq,
  rcases l with ⟨_|⟨b,l⟩,hl⟩, { simp },
  simp [cons, cancel_two_of_ne (h b rfl)]
end

lemma length_cons_le (a) : ∀ xs : normalized M, list.length (cons a xs).1 ≤ list.length xs.1 + 1
| ⟨[], _⟩ := (le_refl 1)
| ⟨b::l, hl⟩ :=
  begin
    simp only [cons, append_val, list.length, list.length_append, ← add_assoc, add_comm _ 1],
    exact add_le_add_right (length_cancel_two_le a b) _
  end

lemma cons_mul' (x xs hx) (ys : normalized M) :
  (⟨x :: xs, hx⟩ * ys : normalized M) = cons x (⟨xs, hx.tail⟩ * ys) :=
rfl

/-- If `a :: l` is normalized and `, then `cons a l = a :: l`. -/
lemma cons_head_tail {a : Σ i, {x : M i // x ≠ 1}} (l : normalized M)
  (hal : is_normalized (a :: l.1)) :
  cons a l = ⟨a :: l.1, hal⟩ :=
cons_of_ne hal.rel_head'

lemma mul_of_is_normalized {l₁ l₂ : normalized M} (h : is_normalized (l₁.1 ++ l₂.1)) :
  l₁ * l₂ = ⟨l₁.1 ++ l₂.1, h⟩ :=
begin
  cases l₁ with xs h₁,
  induction xs with x xs ih, { exact subtype.eq rfl },
  simp only [list.cons_append] at h,
  simp only [cons_mul', list.cons_append],
  rw [ih _ h.tail],
  apply cons_head_tail
end

protected lemma mul_one (xs : normalized M) : xs * 1 = xs :=
begin
  rcases xs with ⟨xs, h⟩,
  rw mul_of_is_normalized; simp only [one_val, list.append_nil],
  exact h
end

lemma mul_def' (xs ys : normalized M) :
  xs * ys = list.foldr cons 1 (xs.val ++ ys.val) :=
by simp_rw [mul_def, list.foldr_append, ← mul_def, normalized.mul_one]

protected lemma one_mul (l : normalized M) : 1 * l = l := rfl

lemma of'_mul_same (i : ι) (x : M i) (y : {x : M i // x ≠ 1}) (l : list _)
  (hl : is_normalized (⟨i, y⟩ :: l)) :
  (of' i x) * ⟨⟨i, y⟩::l, hl⟩ = of' i (x * y) * ⟨l, hl.tail⟩ :=
begin
  by_cases hx : x = 1,
  { subst x,
    simp only [of'_one, normalized.one_mul, one_mul, of'_val, mul_def, list.foldr, one_val],
    exact (cons_head_tail ⟨l, hl.tail⟩ hl).symm },
  simp_rw [mul_def (of' i x), of'_of_ne hx, list.foldr, cons_same, append, subtype.coe_mk],
  symmetry,
  apply mul_of_is_normalized
end

lemma cons_cons (a b : Σ i, {x : M i // x ≠ 1}) (l : normalized M) :
  (cons a (cons b l) : normalized M) = (cancel_two a b) * l :=
begin
  -- First we get rid of two simple cases: `a.1 = b.1` and `is_normalized (b::l.1)`
  by_cases hij : a.1 = b.1, rotate,
  { simp only [cancel_two_of_ne hij, mul_def, list.foldr] },
  by_cases hbl : is_normalized (b::l.1),
  { simp only [cons_head_tail _ hbl, cons, append, subtype.eta],
    exact (mul_of_is_normalized _).symm },
  -- Now we deal with the main case: `a.1 = b.1 = l.head.1`
  rcases a with ⟨i, x⟩,
  rcases b with ⟨j, y⟩,
  rcases l with ⟨l, hl⟩,
  dsimp at hij hbl ⊢, subst j,
  obtain ⟨z, l, rfl⟩ : ∃ z l', l = ⟨i, z⟩::l',
  { simp only [is_normalized, list.chain'_cons'] at hbl,
    push_neg at hbl,
    rcases hbl.resolve_right (not_not_intro hl) with ⟨⟨i, z⟩, hz, rfl⟩,
    exact ⟨z, l.tail, (list.cons_head'_tail hz).symm⟩ },
  clear hbl,
  rw [cons_same, cancel_two_same, of'_mul_same, mul_assoc],
  by_cases hyz : (y * z : M i) = 1,
  { simp [hyz, append, of'_val, mul_def], refl },
  { simp only [of'_of_ne hyz, append, list.cons_append, list.nil_append, cons_same, subtype.coe_mk],
    symmetry,
    apply mul_of_is_normalized }
end

lemma cons_mul (x) (xs ys : normalized M) :
  (cons x xs) * ys = cons x (xs * ys) :=
begin
  rcases xs with ⟨_|⟨x', xs⟩, hl⟩, { refl },
  simp only [mul_def, list.foldr, list.foldr_append, cons, append_val],
  exact (cons_cons x x' (⟨xs, hl.tail⟩ * ys)).symm
end

instance : monoid (normalized M) :=
{ one := 1,
  mul := (*),
  mul_one := normalized.mul_one,
  one_mul := λ xs, rfl,
  mul_assoc := λ xs ys zs,
    begin
      rcases xs with ⟨xs, xs_norm⟩,
      induction xs with x xs hxs xs_norm,
      { refl },
      { rw [cons_mul', cons_mul', ← hxs, cons_mul] }
    end }

/-- Embedding of `M i` into `free_monoid_product.normalized M` as a `monoid_hom`. -/
def of (i : ι) : M i →* normalized M :=
{ to_fun := of' i,
  map_one' := of'_one i,
  map_mul' :=  λ x y, if h : y = 1 then by simp [h]
    else by simp [of'_of_ne h, of'_mul_same] }

variables {N : Type*} [monoid N]

lemma of_eq_of' (i : ι) (x : M i) : of i x = of' i x := rfl

lemma cons_eq_of_mul (a) (xs : normalized M) :
  cons a xs = of a.1 (a.2 : M a.1) * xs :=
by { simp only [of_eq_of', of'_val, sigma.eta], refl }

lemma closure_range_of : submonoid.closure (⋃ i, set.range (of i : M i →* normalized M)) = ⊤ :=
begin
  rw eq_top_iff,
  rintro ⟨l, hl⟩ H, clear H,
  induction l with a l ihl,
  { simp only [nil_eq_one, submonoid.one_mem] },
  simp only [← cons_head_tail ⟨l, hl.tail⟩, cons_eq_of_mul],
  exact submonoid.mul_mem _ (submonoid.subset_closure $
    set.mem_Union.2 ⟨_, set.mem_range_self _⟩) (ihl _)
end

@[ext] lemma hom_eq ⦃f g : normalized M →* N⦄
  (h : ∀ i (x : M i), f (of i x) = g (of i x)) :
  f = g :=
monoid_hom.eq_of_eq_on_mdense closure_range_of $
  λ y hy, let ⟨i, hi⟩ := set.mem_Union.1 hy in
  let ⟨x, hx⟩ := hi in hx ▸ h i x

lemma hom_family_map_of (f : Π i, M i →* N) (i x) :
  list.prod (list.map (λ a : Σ i, {x : M i // x ≠ 1}, f a.1 a.2)
    (of i (x : M i)).1) = f i x :=
begin
  by_cases hx : x = 1,
  { simp [hx, ← monoid_hom.map_mul] },
  { simp [of_eq_of', of'_of_ne hx] }
end

lemma hom_family_map_cancel_two (f : Π i, M i →* N) (a b) :
  list.prod (list.map (λ a : Σ i, {x : M i // x ≠ 1}, f a.1 a.2) (cancel_two a b).1) =
    f a.1 a.2 * f b.1 b.2 :=
begin
  by_cases hij : a.1 = b.1,
  { cases a with i x, cases b with j y,
    dsimp at *,
    subst j,
    rw [cancel_two_same, ← of_eq_of', hom_family_map_of, (f i).map_mul] },
  { simp [cancel_two_of_ne hij] }
end

variables (M N)

def lift : (Π i, M i →* N) ≃ (normalized M →* N) :=
{ to_fun := λ f,
    { to_fun := λ l, list.prod (list.map (λ a : Σ i, {x : M i // x ≠ 1}, f a.1 a.2) l.1),
      map_mul' :=
        begin
          rintro ⟨l₁, hl₁⟩ l₂,
          induction l₁ with a l₁ ihl₁, { simp },
          simp only [cons_mul', list.map_cons, list.prod_cons, mul_assoc, ← ihl₁ hl₁.tail],
          generalize : (⟨l₁, hl₁.tail⟩ * l₂ : normalized M) = l,
          clear_dependent l₁ l₂,
          cases l with l hl,
          induction l with b l ihl, { simp },
          simp only [cons, append_val, list.map_append, list.prod_append, list.map, list.prod_cons,
            hom_family_map_cancel_two, mul_assoc]
        end,
      map_one' := rfl },
  inv_fun := λ f i, f.comp (of i),
  left_inv := λ f, by { ext i x, apply hom_family_map_of },
  right_inv := λ f, by { ext i x, apply hom_family_map_of } }

variables {M N}

@[simp] lemma lift_of (f : Π i, M i →* N) (i : ι) :
  ∀ x : M i, (lift M N : (Π i, M i →* N) → normalized M →* N) f
    (of i x) = f i x :=
by { simp only [← monoid_hom.comp_apply, ← monoid_hom.ext_iff],
  exact congr_fun ((lift M N).symm_apply_apply f) i }

end normalized

def cons' (a : Σ i, M i) (l : normalized M) : normalized M :=
if h : a.2 = 1 then l else normalized.cons ⟨a.1, a.2, h⟩ l

@[simp] lemma cons'_one (i : ι) (l : normalized M) : cons' ⟨i, 1⟩ l = l :=
dif_pos rfl

lemma cons'_of_ne (a : Σ i, M i) (l : normalized M) (h : a.2 ≠ 1) :
  cons' a l = normalized.cons ⟨a.1, a.2, h⟩ l :=
dif_neg h

def equiv_normalized : free_monoid_product M ≃* normalized M :=
mul_equiv.of_eq
{ to_fun := lift M (normalized M) normalized.of,
  inv_fun := normalized.lift M (free_monoid_product M) of,
  map_mul' := monoid_hom.map_mul _,
  left_inv := λ l,
    begin
      conv { congr, rw ← monoid_hom.comp_apply, skip, rw ← monoid_hom.id_apply l },
      revert l,
      simp only [← monoid_hom.ext_iff],
      ext i x,
      simp
    end,
  right_inv := λ l,
    begin
      conv { congr, rw ← monoid_hom.comp_apply, skip, rw ← monoid_hom.id_apply l },
      revert l,
      simp only [← monoid_hom.ext_iff],
      ext i x,
      simp
    end
  } (quot.lift_of_eq (list.foldr cons' 1) ((lift M (normalized M) normalized.of) $ λ l,
begin
  simp only [quot_mk_eq_mk, lift_mk, free_monoid.lift_apply, list.prod_eq_foldr,
    list.foldr_map],
  congr,
  ext ⟨i, x⟩ l,
  dsimp only [(∘), cons', normalized.of_eq_of', normalized.of'],
  split_ifs; refl
end) (λ l, mk (l.1.map (λ a : Σ i, {x : M i // x ≠ 1}, ⟨a.1, a.2⟩)))
  (λ x, (quot.lift_of_eq_eq _ _ _).symm)
  (funext $ λ l, by simp [normalized.lift, mul_equiv.symm])


def normalize : free_monoid_product M → normalized M :=
quot.lift_of_eq (list.foldr cons' 1) (lift M (normalized M) normalized.of) $ λ l,
begin
  simp only [quot_mk_eq_mk, lift_mk, free_monoid.lift_apply, list.prod_eq_foldr,
    list.foldr_map],
  congr,
  ext ⟨i, x⟩ l,
  dsimp only [(∘), cons', normalized.of_eq_of', normalized.of'],
  split_ifs; refl
end

lemma normalize_eq_foldr (l : free_monoid (Σ i, M i)) :
  normalize (mk l) = list.foldr cons' 1 l := rfl

lemma normalize_eq_lift : normalize = lift M (normalized M)
normalized.of :=
quot.lift_of_eq_eq _ _ _

section

variable (M)

def equiv_normalized : free_monoid_product M ≃* normalized M :=

{ to_fun := normalize,
  inv_fun := λ l, mk (list.map (λ a : Σ i, {x : M i // x ≠ 1}, ⟨a.1, a.2⟩) l.1),
  map_mul' := by { rintros ⟨x⟩ ⟨y⟩, simp [normalize_eq_lift, ← monoid_hom.map_mul] },
  left_inv :=
    begin
      
    end,
  right_inv := λ l, _ }

end

namespace normalized

section lift

variables (M) (N : Type*) [monoid N]


section group

variables {G : ι → Type*} [Π i, group (G i)] [Π i, decidable_eq (G i)]

instance : has_inv (normalized G) :=
has_inv.mk $
begin
  refine λ xs, ⟨list.reverse (xs.val.map $ λ x, ⟨x.fst, x.snd.val⁻¹, _⟩), _⟩,
  { refine (λ h, x.snd.property $ inv_inj _),
    rwa one_inv },
  { refine list.chain'_reverse.mpr ((list.chain'_map _).mpr $ xs.2.imp _),
    exact (λ a b h, h.symm) }
end

instance : group (normalized G) :=
{ one := 1,
  mul := (*),
  inv := has_inv.inv,
  mul_left_inv :=
    begin
      rintros ⟨l, hl⟩,
      induction l with hd tl htl,
      { refl },
      { unfold_projs at htl ⊢,
        have : group.inv hd.snd.val * hd.snd.val = 1,
          from mul_left_inv hd.snd.val,
        simp only [list.map_cons, list.reverse_cons, list.foldr_append, list.foldr_cons,
          list.foldr_nil, cons, cancel_two, dif_pos rfl, dif_pos this, list.nil_append],
        exact htl _, }
    end,
  .. normalized.monoid }

end group

end normalized

end free_monoid_product
