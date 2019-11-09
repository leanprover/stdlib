import data.list.basic
import tactic.vampire.misc


namespace list

variables {α β : Type}

lemma exists_mem_append {p : α → Prop} {l₁ l₂ : list α} :
  (∃ x ∈ l₁ ++ l₂, p x) ↔ (∃ x ∈ l₁, p x) ∨ (∃ x ∈ l₂, p x) :=
begin
  constructor; intro h0,
  { rcases h0 with ⟨a, h1, h2⟩,
    rw list.mem_append at h1, cases h1,
    { left, refine ⟨_, h1, h2⟩ },
    right, refine ⟨_, h1, h2⟩ },
  cases h0; rcases h0 with ⟨a, h1, h2⟩;
  refine ⟨a, _, h2⟩; rw list.mem_append;
  [left, right]; assumption
end

def rot : nat → list α → list α
| _ [] := []
| 0 (a :: as) := (a :: as)
| (k + 1) (a :: as) :=
  match (rot k as) with
  | [] := (a :: as)
  | (a' :: as') := (a' :: a :: as')
  end

lemma mem_rot {a : α} :
  ∀ {as : list α}, ∀ k : nat, a ∈ as → a ∈ rot k as
| [] _ h0 := by cases h0
| (b :: as) 0 h0 := h0
| (b :: as) (k + 1) h0 :=
  begin
    cases h0; unfold rot;
    cases h1 : (rot k as) with b' as',
    { left, assumption },
    { right, left, assumption },
    { right, assumption },
    have h2 := mem_rot _ h0,
    rw h1 at h2, cases h2,
    { left, assumption },
    right, right, assumption
  end

lemma exists_mem_map_iff
  {p : α → Prop} {q : β → Prop} {f : α → β}
  (h : ∀ a : α, q (f a) ↔ p a) :
  ∀ as : list α,
  ((∃ b ∈ as.map f, q b) ↔ (∃ a ∈ as, p a))
| []        := by constructor; rintro ⟨_, ⟨_⟩, _⟩
| (a :: as) :=
  begin
    rw [list.map_cons],
    simp only [list.exists_mem_cons_iff],
    apply pred_mono_2 (h _),
    apply exists_mem_map_iff
  end

def try (f : α → option β) : list α → option β
| []        := none 
| (a :: as) := f a <|> try as

lemma map_eq_map_of_forall_mem_eq {f g : α → β} : 
  ∀ {as : list α}, (∀ a ∈ as, f a = g a) → as.map f = as.map g 
| []        _  := rfl
| (a :: as) h0 := 
  by { unfold map,
       rw [ h0 _ (or.inl rfl),
            map_eq_map_of_forall_mem_eq ],
       intros x h1,
       apply h0 _ (or.inr h1) }
      
lemma forall_mem_map_of_forall_mem 
  {p : α → Prop} {q : β → Prop} {f : α → β} (h0 : ∀ a : α, p a → q (f a)) :
  ∀ as : list α, (∀ a ∈ as, p a) → (∀ b ∈ as.map f, q b)
| [] _ _ h2 := by cases h2
| (a :: as) h1 b h2 := 
  by { cases h2,
       { rw h2, apply h0, 
         apply h1 _ (or.inl rfl) },
       apply forall_mem_map_of_forall_mem as _ _ h2,
       apply forall_mem_of_forall_mem_cons h1 }

def orelse : list (option α) → option α
| []        := none 
| (a :: as) := a <|> orelse as

def disj (ps : list Prop) : Prop := ∃ p ∈ ps, p
def conj (ps : list Prop) : Prop := ∀ p ∈ ps, p

lemma disj_cons (p : Prop) (ps : list Prop) :
  (p :: ps).disj ↔ p ∨ ps.disj :=
by { unfold disj, rw exists_mem_cons_iff }

def suffix : nat → list α → list α → Prop 
| 0       as1 as2        := as1 = as2 
| (k + 1) as1 (_ :: as2) := suffix k as1 as2 
| (k + 1) _   []         := false

lemma nth_eq_some_of_cons_suffix {a1 : α} {as1 : list α} :
  ∀ {k : nat} {as2 : list α},
  suffix k (a1 :: as1) as2 → as2.nth k = some a1
| 0       (a2 :: as2) h0 := by { cases h0, refl }
| (k + 1) (_ :: as2)  h0 := 
  begin
    unfold nth,
    apply nth_eq_some_of_cons_suffix,
    apply h0,
  end

lemma suffix_succ_of_suffix_cons {a1 : α} {as1 : list α} :
  ∀ {k : nat} {as2 : list α},
  suffix k (a1 :: as1) as2 → suffix (k + 1) as1 as2 
| 0 (_ :: as2) h0 := 
  begin
    cases h0, unfold suffix,
  end
| (k + 1) (_ :: as2) h0 := 
  begin
    unfold suffix,
    apply suffix_succ_of_suffix_cons,
    apply h0
  end

end list