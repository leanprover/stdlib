
/-
  Copyright (c) 2019 Seul Baek. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Author: Seul Baek
-/

import tactic.vampire.main
import tactic.vampire.main

meta def v1 : tactic unit := vampire.vampire none
meta def v2 : tactic unit := vampire none

meta def vtest : tactic unit := v2 >> v2
section

variables (α : Type) [inhabited α]
variables (a b c : α) (p q : α → Prop) (r : α → α → Prop)
variables (P Q R : Prop)
variable  (g : bool → nat)

/-
example : (∀ x, p x → q x) → (∀ x, p x) → q a :=
by v2

example : (p a) → ∃ x, p x :=
by v2

example : (p a) → (p b) → (q b) → ∃ x, p x ∧ q x :=
by v2

example : (∃ x, p x ∧ r x x) → (∀ x, r x x → q x) → ∃ x, p x ∧ q x :=
by v2

example : (∃ x, q x ∧ p x) → ∃ x, p x ∧ q x :=
by v2

example : (∀ x, q x → p x) → (q a) → ∃ x, p x :=
by v2

example : (∀ x, p x → q x → false) → (p a) → (p b) → (q b) → false :=
by v2

example : (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x :=
by v2

example : (∃ x, p x) → (∀ x, p x → q x) → ∃ x, q x :=
by v2

example : (¬ ∀ x, ¬ p x) → (∀ x, p x → q x) → (∀ x, ¬ q x) → false :=
by v2

example : (p a) → (p a → false) → false :=
by v2

example : (¬ (P → Q ∨ R)) → (¬ (Q ∨ ¬ R)) → false :=
by v2

example : (P → Q ∨ R) → (¬ Q) → P → R :=
by v2
-/

example : (∃ x, p x → P) ↔ (∀ x, p x) → P :=
by v2

example : (∃ x, P → p x) ↔ (P → ∃ x, p x) :=
by v2

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
by v2


lemma gilmore_6 {F G : α → α → Prop} {H : α → α → α → Prop} :
∀ x, ∃ y,
  (∃ u, ∀ v, F u x → G v u ∧ G u x)
   → (∃ u, ∀ v, F u y → G v u ∧ G u y) ∨
       (∀ u v, ∃ w, G v u ∨ H w y u → G u w) :=
by v2

lemma gilmore_8 {G : α → Prop} {F : α → α → Prop} {H : α → α → α → Prop} :
  ∃ x, ∀ y z,
    ((F y z → (G y → (∀ u, ∃ v, H u v x))) → F x x) ∧
    ((F z x → G x) → (∀ u, ∃ v, H u v z)) ∧
    F x y → F z z := by v2

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
by v2

/- A logic puzzle by Raymond Smullyan. -/


#exit
set_option profiler true

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
by v2

#exit

-- To do : find a way to avoid deep recursion with large proofs
"
n10n0en11101n110sn1sn111sppn10sn111sppmn11110n111sman10n10n1
n1011en1n110sn1sn111sppn10sn111sppmatn1010en10n110sn1sn111sp
pn10sn111sppmn11n11sn111spmn100n10sn111spmartn1n110en1110n11
0sn1sn111sppn10sn111sppmn1111n100sn111spmn10000n111sman1n1en
11011n110sn1sn111sppn10sn111sppmn11100n111smatrn1n1n10en1100
1n100sn111spmn11010n111smatn1n10n111en1011n100sn111spmn1100n
100sn111spmn1101n111sman1000en1000n100sn111spmn1010n10sn111s
pmn1001n11sn111spman1n1100en0n100sn111spmatrrtctrn1001en101n
100sn111spmn110n11sn111spmn111n10sn111spman1n1100en0n100sn11
1spmatrrtcrn1n11en10111n110sn1sn111sppn10sn111sppmn11000n111
smatrtrtrtcn1001en101n110sn1sn111sppn10sn111sppmn110n10sn111
spmn111n1sn111spman1n10n1n1n100en10100n110sn1sn111sppn10sn11
1sppmn10101n110sn1sn111sppn10sn111sppmn10110n111sman1n10n0en
11101n110sn1sn111sppn10sn111sppmn11110n111sman10n10n1n1011en
1n110sn1sn111sppn10sn111sppmatn1010en10n110sn1sn111sppn10sn1
11sppmn11n11sn111spmn100n10sn111spmartn1n110en1110n110sn1sn1
11sppn10sn111sppmn1111n100sn111spmn10000n111sman1n1en11011n1
10sn1sn111sppn10sn111sppmn11100n111smatrn1n1n10en11001n100sn
111spmn11010n111smatn1n10n111en1011n100sn111spmn1100n100sn11
1spmn1101n111sman1000en1000n100sn111spmn1010n10sn111spmn1001
n11sn111spman1n1100en0n100sn111spmatrrtctrn1001en101n100sn11
1spmn110n11sn111spmn111n10sn111spman1n1100en0n100sn111spmatr
rtcrn1n11en10111n110sn1sn111sppn10sn111sppmn11000n111smatrtr
trtcn1n1en11011n110sn1sn111sppn10sn111sppmn11100n111smatrtrn
10n111en1011n110sn1sn111sppn10sn111sppmn1100n110sn1sn111sppn
10sn111sppmn1101n111sman1000en1000n110sn1sn111sppn10sn111spp
mn1010n10sn111spmn1001n11sn111spman1n1100en0n110sn1sn111sppn
10sn111sppmatrrtcrtn1n10n10n1n11n1n10n101en10001n110sn1sn111
sppn10sn111sppmn10010n110sn1sn111sppn10sn111sppmn10011n111sm
an1n10n0en11101n110sn1sn111sppn10sn111sppmn11110n111sman10n1
0n1n1011en1n110sn1sn111sppn10sn111sppmatn1010en10n110sn1sn11
1sppn10sn111sppmn11n11sn111spmn100n10sn111spmartn1n110en1110
n110sn1sn111sppn10sn111sppmn1111n100sn111spmn10000n111sman1n
1en11011n110sn1sn111sppn10sn111sppmn11100n111smatrn1n1n10en1
1001n100sn111spmn11010n111smatn1n10n111en1011n100sn111spmn11
00n100sn111spmn1101n111sman1000en1000n100sn111spmn1010n10sn1
11spmn1001n11sn111spman1n1100en0n100sn111spmatrrtctrn1001en1
01n100sn111spmn110n11sn111spmn111n10sn111spman1n1100en0n100s
n111spmatrrtcrn1n11en10111n110sn1sn111sppn10sn111sppmn11000n
111smatrtrtrtcn1n1en11011n110sn1sn111sppn10sn111sppmn11100n1
11smatrtrtn10n111en1011n110sn1sn111sppn10sn111sppmn1100n110s
n1sn111sppn10sn111sppmn1101n111sman1000en1000n110sn1sn111spp
n10sn111sppmn1010n10sn111spmn1001n11sn111spman1n1100en0n110s
n1sn111sppn10sn111sppmatrrtcrtn10n100en10100n110sn1sn111sppn
10sn111sppmn10101n110sn1sn111sppn10sn111sppmn10110n111sman10
n111en1011n110sn1sn111sppn10sn111sppmn1100n110sn1sn111sppn10
sn111sppmn1101n111sman1n1en11011n110sn1sn111sppn10sn111sppmn
11100n111smatrtrn10n111en1011n110sn1sn111sppn10sn111sppmn110
0n110sn1sn111sppn10sn111sppmn1101n111sman1000en1000n110sn1sn
111sppn10sn111sppmn1010n10sn111spmn1001n11sn111spman1n1100en
0n110sn1sn111sppn10sn111sppmatrrtcrtrtcttctctrttctcrrn1n0en1
1101n10sn111spmn11110n111smatn1n10n1n1n100en10100n10sn111spm
n10101n10sn111spmn10110n111sman1n10n0en11101n10sn111spmn1111
0n111sman10n10n1n1011en1n10sn111spmatn1010en10n10sn111spmn11
n11sn111spmn100n10sn111spmartn1n110en1110n10sn111spmn1111n10
0sn111spmn10000n111sman1n1en11011n10sn111spmn11100n111smatrn
1n1n10en11001n100sn111spmn11010n111smatn1n10n111en1011n100sn
111spmn1100n100sn111spmn1101n111sman1000en1000n100sn111spmn1
010n10sn111spmn1001n11sn111spman1n1100en0n100sn111spmatrrtct
rn1001en101n100sn111spmn110n11sn111spmn111n10sn111spman1n110
0en0n100sn111spmatrrtcrn1n11en10111n10sn111spmn11000n111smat
rtrtrtcn1n1en11011n10sn111spmn11100n111smatrtrn10n111en1011n
10sn111spmn1100n10sn111spmn1101n111sman1000en1000n10sn111spm
n1010n10sn111spmn1001n11sn111spman1n1100en0n10sn111spmatrrtc
rtn1n10n10n1n11n1n10n101en10001n10sn111spmn10010n10sn111spmn
10011n111sman1n10n0en11101n10sn111spmn11110n111sman10n10n1n1
011en1n10sn111spmatn1010en10n10sn111spmn11n11sn111spmn100n10
sn111spmartn1n110en1110n10sn111spmn1111n100sn111spmn10000n11
1sman1n1en11011n10sn111spmn11100n111smatrn1n1n10en11001n100s
n111spmn11010n111smatn1n10n111en1011n100sn111spmn1100n100sn1
11spmn1101n111sman1000en1000n100sn111spmn1010n10sn111spmn100
1n11sn111spman1n1100en0n100sn111spmatrrtctrn1001en101n100sn1
11spmn110n11sn111spmn111n10sn111spman1n1100en0n100sn111spmat
rrtcrn1n11en10111n10sn111spmn11000n111smatrtrtrtcn1n1en11011
n10sn111spmn11100n111smatrtrtn10n111en1011n10sn111spmn1100n1
0sn111spmn1101n111sman1000en1000n10sn111spmn1010n10sn111spmn
1001n11sn111spman1n1100en0n10sn111spmatrrtcrtn10n100en10100n
10sn111spmn10101n10sn111spmn10110n111sman10n111en1011n10sn11
1spmn1100n10sn111spmn1101n111sman1n1en11011n10sn111spmn11100
n111smatrtrn10n111en1011n10sn111spmn1100n10sn111spmn1101n111
sman1000en1000n10sn111spmn1010n10sn111spmn1001n11sn111spman1
n1100en0n10sn111spmatrrtcrtrtcttctctrttctcrn10n1000en1000n10
sn111spmn1010n1sn111spmn1001n10sn111spman1n111en1011n10sn111
spmn1100n110sn1sn111sppn10sn111sppmn1101n111sman1n1en11011n1
0sn111spmn11100n111smatrtrtcrr
"
