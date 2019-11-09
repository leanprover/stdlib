/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek
-/

import tactic.vampire

section

/- Examples from finish. -/

variables {A B C D : Prop}

example : (A → B ∨ C) → (B → D) → (C → D) → A → D :=
by vampire 

example : ¬ A → A → C :=
by vampire 

example : (A ∧ A ∧ B) → (A ∧ C ∧ B) → A :=
by vampire 

example : A → ¬ B → ¬ (A → B) :=
by vampire 

example : A ∨ B → B ∨ A :=
by vampire

example : A ∧ B → B ∧ A :=
by vampire

example : A → (A → B) → (B → C) → C :=
by vampire

example : (A ∧ B) → (C ∧ B) → C :=
by vampire

example : A → B → C → D → (A ∧ B) ∧ (C ∧ D) :=
by vampire

example : (A ∧ B) → (B ∧ ¬ C) → A ∨ C :=
by vampire

example : (A → B) ∧ (B → C) → A → C :=
by vampire

example : (A → B) ∨ (B → A) :=
by vampire

example : ((A → B) → A) → A :=
by vampire

example : A → ¬ B → ¬ (A → B) :=
by vampire

example : ¬ (A ↔ ¬ A) :=
by vampire

example : (A ↔ B) → (A ∧ B → C) → (¬ A ∧ ¬ B → C) → C :=
by vampire

example : (A ↔ B) → ((A ∧ ¬ B) ∨ (¬ A ∧ B)) → C :=
by vampire

example : (A → B) → A → B :=
by vampire 

example : (A → B) → (B → C) → A → C :=
by vampire

example : (A → B ∨ C) → (B → D) → (C → D) → A → D :=
by vampire

example : A ∨ B → B ∨ A :=
by vampire

end

section

variables (α : Type) [inhabited α]
variables (a b c : α) (p q : α → Prop) (r : α → α → Prop)
variables (P Q R : Prop)
variable  (g : bool → nat)

example : (∀ x, p x → q x) → (∀ x, p x) → q a :=
by vampire 

example : (p a) → ∃ x, p x :=
by vampire

example : (p a) → (p b) → (q b) → ∃ x, p x ∧ q x :=
by vampire

example : (∃ x, p x ∧ r x x) → (∀ x, r x x → q x) → ∃ x, p x ∧ q x :=
by vampire

example : (∃ x, q x ∧ p x) → ∃ x, p x ∧ q x :=
by vampire

example : (∀ x, q x → p x) → (q a) → ∃ x, p x :=
by vampire

example : (∀ x, p x → q x → false) → (p a) → (p b) → (q b) → false :=
by vampire

example : (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x :=
by vampire

example : (∃ x, p x) → (∀ x, p x → q x) → ∃ x, q x :=
by vampire

example : (¬ ∀ x, ¬ p x) → (∀ x, p x → q x) → (∀ x, ¬ q x) → false :=
by vampire

example : (p a) → (p a → false) → false :=
by vampire

example : (¬ (P → Q ∨ R)) → (¬ (Q ∨ ¬ R)) → false :=
by vampire

example : (P → Q ∨ R) → (¬ Q) → P → R :=
by vampire

example : (∃ x, p x → P) ↔ (∀ x, p x) → P :=
by vampire

example : (∃ x, P → p x) ↔ (P → ∃ x, p x) :=
by vampire

end

section

  /- Some harder examples, from John Harrison's
     Handbook of Practical Logic and Automated Reasoning. -/

variables (α : Type) [inhabited α]

lemma gilmore_1 {F G H : α → Prop} :
  ∃ x, ∀ y z,
      ((F y → G y) ↔ F x) ∧
      ((F y → H y) ↔ G x) ∧
      (((F y → G y) → H y) ↔ H x)
      → F z ∧ G z ∧ H z :=
by vampire

lemma gilmore_6 {F G : α → α → Prop} {H : α → α → α → Prop} :
∀ x, ∃ y,
  (∃ u, ∀ v, F u x → G v u ∧ G u x)
   → (∃ u, ∀ v, F u y → G v u ∧ G u y) ∨
       (∀ u v, ∃ w, G v u ∨ H w y u → G u w) :=
by vampire

lemma gilmore_8 {G : α → Prop} {F : α → α → Prop} {H : α → α → α → Prop} :
  ∃ x, ∀ y z,
    ((F y z → (G y → (∀ u, ∃ v, H u v x))) → F x x) ∧
    ((F z x → G x) → (∀ u, ∃ v, H u v z)) ∧
    F x y → F z z := by vampire

lemma manthe_and_bry (agatha butler charles : α)
(lives : α → Prop) (killed hates richer : α → α → Prop) :
   lives agatha ∧ lives butler ∧ lives charles ∧
   (killed agatha agatha ∨ killed butler agatha ∨
    killed charles agatha) ∧
   (∀ x y, killed x y → hates x y ∧ ¬ richer x y) ∧
   (∀ x, hates agatha x → ¬ hates charles x) ∧
   (hates agatha agatha ∧ hates agatha charles) ∧
   (∀ x, lives(x) ∧ ¬ richer x agatha → hates butler x) ∧
   (∀ x, hates agatha x → hates butler x) ∧
   (∀ x, ¬ hates x agatha ∨ ¬ hates x butler ∨ ¬ hates x charles)
   → killed agatha agatha ∧
       ¬ killed butler agatha ∧
       ¬ killed charles agatha :=
by vampire

/- A logic puzzle by Raymond Smullyan. -/

lemma knights_and_knaves (me : α) (knight knave rich poor : α → α)
  (a_truth says : α → α → Prop) (and : α → α → α) :
  ( (∀ X Y, ¬ a_truth (knight X) Y ∨ ¬ a_truth (knave X) Y ) ∧
    (∀ X Y, a_truth (knight X) Y ∨ a_truth (knave X) Y ) ∧
    (∀ X Y, ¬ a_truth (rich X) Y ∨ ¬ a_truth (poor X) Y ) ∧
    (∀ X Y, a_truth (rich X) Y ∨ a_truth (poor X) Y ) ∧
    (∀ X Y Z, ¬ a_truth (knight X) Z ∨ ¬ says X Y ∨ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knight X) Z ∨ says X Y ∨ ¬ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knave X) Z ∨ ¬ says X Y ∨ ¬ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (knave X) Z ∨ says X Y ∨ a_truth Y Z ) ∧
    (∀ X Y Z, ¬ a_truth (and X Y) Z ∨ a_truth X Z ) ∧
    (∀ X Y Z, ¬ a_truth (and X Y) Z ∨ a_truth Y Z ) ∧
    (∀ X Y Z, a_truth (and X Y) Z ∨ ¬ a_truth X Z ∨ ¬ a_truth Y Z ) ∧
    (∀ X, ¬ says me X ∨ ¬ a_truth (and (knave me) (rich me)) X ) ∧
    (∀ X, says me X ∨ a_truth (and (knave me) (rich me)) X ) ) → false :=
by vampire

end

section

variables {α : Type} [inhabited α]
variables {f g i : α → α}
variables {p q : α → Prop}

open tactic expr vampire

example : ∀ x y : ℕ, x = y ∨ ¬ x = y := 
by vampire

example (x y z : nat) (p : ℕ → Prop) :
  x = y → y = z → (∀ w, w = z → p w) → p x :=
by vampire

example : ∀ x y, (p x ∧ x = f y) → p (f y) :=
by vampire

example :
  (∀ x, p x → q x) ∧ (∃ x, p x) ∧
  (∀ x y, q x ∧ q y → x = y) → 
  ∀ y, q y → p y := 
by vampire

example (p q : nat) :
   (forall x y z : nat, x * (y * z) = (x * y) * z) ∧ p * q * p = p
   → exists q' : nat, p * q' * p = p ∧ q' * p * q' = q' := 
by vampire

/- This one times out -/

-- example (α : Type) [inhabited α] (f g : α → α) :
--    (exists x, x = f (g x) ∧ forall x', x' = f (g x') → x = x') ↔
--    (exists y, y = g (f y) ∧ forall y', y' = g (f y') → y = y') :=
-- by vampire

/- Examples that discharge, but report weird type errors -/

-- instance int.inhabited : inhabited int := ⟨0⟩ 
 
-- example (i : int → int) (e : int) :
--    (forall x y z : int, x * (y * z) = (x * y) * z) ∧
--    (forall x, e * x = x) ∧
--    (forall x, i(x) * x = e) → 
--    forall x, x * i x = e := 
-- by vampire
 
-- example (i : int → int) (e : int) :
--    (forall x y z : int, x * (y * z) = (x * y) * z) ∧
--    (forall x : int, e * x = x) ∧
--    (forall x : int, i x * x = e) → 
--    forall x : int, x * e = x := 
-- by vampire
 
-- example (i : nat → nat) (e : nat) :
--    (forall x y z : nat, x * (y * z) = (x * y) * z) ∧
--    (forall x : nat, e * x = x) ∧
--    (forall x : nat, i x * x = e) →
--    forall x : nat, x * i x = e :=
-- by vampire

end