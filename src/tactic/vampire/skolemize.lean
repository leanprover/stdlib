import tactic.vampire.frm
import data.vector

namespace vampire

local notation f `₀↦` a := assign a f
local notation `v*` := xtrm.vr
local notation `f*` := xtrm.fn
local notation `[]*` := xtrm.nil
local notation h `::*` ts  := xtrm.cons h ts
local notation `r*`     := atm.rl 
local notation t `=*` s := atm.eq t s 
local notation `+*`     := frm.atm tt
local notation `-*`     := frm.atm ff
local notation p `∨*` q := frm.bin tt p q
local notation p `∧*` q := frm.bin ff p q
local notation `∃*` p   := frm.qua tt p
local notation `∀*` p   := frm.qua ff p
local notation F `∀⟹` k := forall_ext k F
local notation F `∃⟹` k := exists_ext k F

variables {α : Type}
variables {R : rls α} {F : fns α} {V V' : vas α}

def ex_count : frm → nat
| (frm.atm _ _)   := 0
| (frm.bin _ _ _) := 0
| (∀* f)          := ex_count f
| (∃* f)          := ex_count f + 1

def skolem_args : nat → nat → trms 
| 0       _ := []*
| (k + 1) m := v* m ::* skolem_args k (m + 1)

def skolem_trm (k : nat) : trm := 
f* 0 (skolem_args k 1)

@[reducible] def trm.skolem_vsub
  (k : nat) (s : trm) (t : trm) :=
(trm.vsub k s t.finc).vdec k

@[reducible] def atm.skolem_vsub
  (k : nat) (s : trm) (a : atm) :=
(a.finc.vsub k s).vdec k

@[reducible] def frm.skolem_vsub
  (k : nat) (s : trm) (f : frm) :=
(f.finc.vsub k s).vdec k

def skolemize_one : frm → nat → frm
| (∀* f) k := ∀* (skolemize_one f (k + 1))
| (∃* f) k := f.skolem_vsub 0 (skolem_trm k)
| _      _ := frm.default

def skolemize_core : nat → frm → frm
| 0       f := f
| (k + 1) f := skolemize_core k (skolemize_one f 0)

def skolemize (f : frm) : frm :=
skolemize_core (ex_count f) f

lemma AF_of_QF :
  ∀ f : frm, ex_count f = 0 → f.QF → f.AF
| (frm.atm b _)   h0 h1 := trivial
| (frm.bin b f g) h0 h1 := h1
| (∀* f)          h0 h1 := AF_of_QF f h0 h1

lemma ex_count_vdec :
  ∀ f : frm, ∀ m : nat, ex_count (f.vdec m) = ex_count f
| (frm.atm _ _)   m := rfl
| (frm.bin b f g) m := rfl
| (frm.qua b f)   m :=
  by cases b;
     simp [ frm.vdec, ex_count,
       ex_count_vdec _ (m + 1) ]

lemma ex_count_finc :
  ∀ f : frm, ex_count f.finc = ex_count f
| (frm.atm _ _)   := rfl
| (frm.bin _ _ _) := rfl
| (frm.qua b f)   :=
  by cases b;
     simp [ frm.finc, ex_count,
       ex_count_finc f ]

lemma ex_count_vsub :
  ∀ f : frm, ∀ k : nat, ∀ t : trm,
  ex_count (f.vsub k t) = ex_count f
| (frm.atm _ _)   _ _ := rfl
| (frm.bin _ _ _) _ _ := rfl
| (frm.qua b _)   _ _ :=
  by cases b;
     simp [ frm.vsub, ex_count,
       ex_count_vsub ]

lemma ex_count_skolemize_one_eq {k : nat} :
  ∀ {f : frm}, ∀ m : nat,
  ex_count f = k + 1 →
  ex_count (skolemize_one f m) = k
| (∀* f) m h0 :=
  by { unfold skolemize_one,
       apply ex_count_skolemize_one_eq (m + 1) ,
       apply h0 }
| (∃* f) m h0 :=
  begin
    unfold skolemize_one,
    unfold frm.skolem_vsub,
    unfold ex_count at h0,
    rw [ ex_count_vdec,
         ex_count_vsub,
         ex_count_finc,
         nat.succ_inj h0 ],
  end

local notation f `₀↦` a := assign a f


variable {β : Type}

def lassign : list β → (nat → β) → nat → β
| []        f k       := f k
| (b :: bs) f 0       := b
| (b :: bs) f (k + 1) := lassign bs f k

def vassign {k : nat} (v : vector β k) (f : nat → β) : nat → β :=
lassign v.val f

lemma ext_lassign (f : nat → β) :
  ∀ (k : nat) (l : list β),
  l.length = k → ext k (lassign l f) f
| 0       []        _  _ := rfl
| (k + 1) []        h0 _ := by cases h0
| 0       (b :: bs) h0 _ := by cases h0
| (k + 1) (b :: bs) h0 m :=
  by apply ext_lassign k bs (nat.succ_inj h0)

lemma ext_vassign {k : nat} (v : vector β k) (f : nat → β) :
  ext k (vassign v f) f :=
by { apply ext_lassign, apply v.property }

def to_fn [inhabited α] {k : nat} (f : vector α k → α) : fn α
| l := if h : l.length = k then f ⟨l, h⟩ else default α

lemma exists_eq_lassign_of_ext :
  ∀ k : nat, ∀ f g : nat → α,
  ext k f g → ∃ l : list α, l.length = k ∧ f = lassign l g
| 0       f g h0 := ⟨[], rfl, eq_of_ext_zero h0⟩
| (k + 1) f g h0 :=
  by { cases exists_eq_lassign_of_ext k (f ∘ nat.succ) g _ with l h1,
       { refine ⟨f 0 :: l, _, _⟩,
         { simp only [list.length, h1.left] },
         apply funext, rintro ⟨m⟩,
         { refl },
         simp only [lassign, h1.right.symm] },
       apply h0 }

lemma exists_eq_vassign_of_ext {k : nat} {f g : nat → α} :
  ext k f g → ∃ v : vector α k, f = vassign v g :=
by { intro h0, cases exists_eq_lassign_of_ext _ _ _ h0 with l h1,
     refine ⟨⟨l, h1.left⟩, h1.right⟩ }

def splice (k : nat) (a : α) (W V : vas α) : Prop :=
(∀ m < k, W m = V m) ∧ W k = a ∧ (∀ m ≥ k, W (m + 1) = V m)

lemma frm.skolem_vsub_qua
  (b : bool) (f : frm) (k : nat) (s : trm) :
  (frm.qua b f).skolem_vsub k s =
  frm.qua b (f.skolem_vsub (k + 1) (s.vinc 0 1)) := rfl

lemma frm.skolem_vsub_atm
  (b : bool) (a : atm) (k : nat) (s : trm) :
  (frm.atm b a).skolem_vsub k s = frm.atm b (a.skolem_vsub k s) := rfl

lemma frm.skolem_vsub_bin
  (b : bool) (f g : frm) (k : nat) (s : trm) :
  (frm.bin b f g).skolem_vsub k s =
  frm.bin b (f.skolem_vsub k s) (g.skolem_vsub k s) := rfl

lemma trm.skolem_vsub_fn
  {k m : nat} {r : trm} {ts : trms}  :
  trm.skolem_vsub m r (f* k ts) =
  f* (k + 1) (trms.tmap (trm.skolem_vsub m r) ts) :=
begin
  unfold trm.skolem_vsub,
  rw [ trm.finc_fn, trm.vsub_fn, trm.vdec_fn,
    trms.tmap_tmap, trms.tmap_tmap ]
end

lemma atm.skolem_vsub_rl
  {k m : nat} {ts : list trm} {r : trm} :
  (r* k ts).skolem_vsub m r = 
  r* k (ts.map $ trm.skolem_vsub m r) := 
by { simp only [atm.skolem_vsub, list.map_map, 
       atm.finc, atm.vsub, atm.vdec, trm.skolem_vsub],
     constructor; refl }

lemma atm.skolem_vsub_eq
  {t s : trm} {m : nat} {r : trm} :
  (t =* s).skolem_vsub m r = 
  (trm.skolem_vsub m r t =* trm.skolem_vsub m r s) := rfl

lemma trm.skolem_vsub_eq_of_lt
  {k m : nat} {s : trm} (h0 : m < k) :
  trm.skolem_vsub k s (v* m) = v* m :=
by { unfold trm.skolem_vsub, 
     rw [ trm.finc_vr, trm.vsub_vr, if_neg (ne_of_lt h0),
       trm.vdec_vr, if_neg (not_lt_of_gt h0) ] } 

lemma trm.skolem_vsub_eq_of_eq
  {k m : nat} {s : trm} (h0 : m = k) :
  trm.skolem_vsub k s (v* m) = s.vdec k :=
by { unfold trm.skolem_vsub,
     rw [ trm.finc_vr, trm.vsub_vr, if_pos h0 ], }

lemma trm.skolem_vsub_eq_of_gt
  {k m : nat} {s : trm} (h0 : m > k) :
  trm.skolem_vsub k s (v* m) = v* (m - 1) :=
by { unfold trm.skolem_vsub, 
     rw [ trm.finc_vr, trm.vsub_vr, 
       if_neg (ne_of_gt h0), trm.vdec_vr, if_pos h0 ] } 

open nat

lemma splice_succ {k : nat} {a b : α} {W V : vas α} :
  splice k a W V → splice (k + 1) a (W ₀↦ b) (V ₀↦ b) :=
by { rintro ⟨h0, h1, h2⟩,
     constructor,
     { rintros ⟨m⟩ h3,
       { refl },
       apply h0,
       apply lt_of_succ_lt_succ h3 },
     refine ⟨h1, _⟩,
     rintros ⟨m⟩ h3,
     { cases h3 },
     apply h2,
     apply le_of_succ_le_succ h3 }

lemma holds_qua_of_holds_qua
  {R S : rls α} {F G : fns α} {V W : vas α} {b : bool} {f g : frm} :
  (∀ x : α, f.holds R F (V ₀↦ x) → g.holds S G (W ₀↦ x)) →
  (frm.qua b f).holds R F V →
  (frm.qua b g).holds S G W :=
by { intros h0 h1, cases b,
     { intro x, apply h0 x (h1 x) },
     cases h1 with x h2,
     refine ⟨x, h0 x h2⟩ }

lemma val_vdec_succ_vinc_zero {m : nat} {x : α}:
   ∀ t : trm,
   ((t.vinc 0 1).vdec (m + 1)).val F (V ₀↦ x) =
   (t.vdec m).val F V :=
trm.rec 
 (begin
    intro k,
    rw [ trm.vinc_vr, trm.vdec_vr, trm.val_vr,
      trm.vdec_vr, trm.val_vr ],
    rw [ if_neg (not_lt_zero _), nat.add_sub_cancel ],
    by_cases h0 : m < k,
    { cases k,
      { apply false.elim (not_lt_zero _ h0) },
      rw [ if_pos h0, if_pos (succ_lt_succ h0) ],
      refl },
    rw [ if_neg h0, if_neg (λ h1, _) ],
    { refl },
    apply h0 (lt_of_succ_lt_succ h1)
  end)
 (begin
    intros k ts ih, 
    rw [ trm.vinc_fn, trm.vdec_fn, trm.val_fn,
      trm.vdec_fn, trm.val_fn ], 
    repeat {rw trms.lmap_tmap}, 
    apply congr_arg,
    apply trms.lmap_eq_lmap ih,
  end)

lemma trm.val_skolem_vsub
  {x : α} {y : fn α} {r : trm} {m : nat} {W V : vas α}
  (h0 : splice m x W V) (h1 : (r.vdec m).val (F ₀↦ y) V = x) :
  ∀ t : trm, (trm.skolem_vsub m r t).val (F ₀↦ y) V = t.val F W := 
trm.rec 
 (begin
    intro k,
    rcases nat.lt_trichotomy k m with h2 | h2 | h2,
    { rw [ trm.skolem_vsub_eq_of_lt h2, 
        trm.val_vr, trm.val_vr, h0.left _ h2 ] },
    { rw [ trm.skolem_vsub_eq_of_eq h2, 
        trm.val_vr, h1, h0.right.left.symm, h2 ] },
    rw [ trm.skolem_vsub_eq_of_gt h2,
      trm.val_vr, trm.val_vr ],
    cases k, { cases h2 },
    rw lt_succ_iff at h2,
    apply (h0.right.right k h2).symm 
  end)
 (begin
    intros k ts ih,
    rw [ trm.skolem_vsub_fn, trm.val_fn, 
      trm.val_fn, trms.lmap_tmap ],
    apply congr_arg,
    apply trms.lmap_eq_lmap ih,
  end)

lemma atm.holds_skolem_vsub
  {x : α} {y : fn α} {s : trm} {k : nat} (R : rls α) {W V : vas α}
  (h0 : splice k x W V) (h1 : (s.vdec k).val (F ₀↦ y) V = x) :
  ∀ {a : atm}, ((a.skolem_vsub k s).holds R (F ₀↦ y) V ↔ a.holds R F W)
| (atm.rl k ts) :=
  begin
    rw atm.skolem_vsub_rl,
    unfold atm.holds,
    rw [list.map_map],
    apply iff_of_eq (congr_arg _ _),
    apply list.map_eq_map_of_forall_mem_eq,
    intros t h4,
    apply trm.val_skolem_vsub h0 h1 
  end
| (atm.eq t s) :=
  begin
    rw atm.skolem_vsub_eq,
    unfold atm.holds,
    rw [ trm.val_skolem_vsub h0 h1,
      trm.val_skolem_vsub h0 h1 ] 
  end

lemma holds_skolem_vsub {x : α} {y : fn α} :
  ∀ {f : frm} {k : nat} {s : trm} {W V : vas α},
  splice k x W V →
  ((s.vdec k).val (F ₀↦ y) V = x) →
  (f.holds R F W) →
  (f.skolem_vsub k s).holds R (F ₀↦ y) V 
| (frm.atm b a) k s W V h1 h2 h4 :=
  by { rw frm.skolem_vsub_atm,
       cases b; unfold frm.holds;
       rw atm.holds_skolem_vsub R h1 h2;
       exact h4 }
| (frm.bin b f g) k s W V h1 h2 h3 :=
  by { rw frm.skolem_vsub_bin,
       apply holds_bin_of_holds_bin _ _ h3;
       apply holds_skolem_vsub h1 h2;
       assumption }
| (frm.qua b f) k s W V h1 h2 h3 :=
  by { rw frm.skolem_vsub_qua,
       apply holds_qua_of_holds_qua _ h3,
       intros a h3,
       apply holds_skolem_vsub _ _ h3,
       { apply splice_succ h1 },
       rw val_vdec_succ_vinc_zero,
       apply h2 }

lemma to_fn_eq [inhabited α] {k : nat} (s : vector α k → α) (v : vector α k) :
  to_fn s v.val = s v :=
begin
  unfold to_fn, unfold dite,
  cases (nat.decidable_eq v.val.length k) with h0 h0,
  { exact false.elim (h0 v.property) },
  simp only [list.length, subtype.eta]
end

open nat

lemma lassign_eq_of_lt :
  ∀ {k m : nat} {l : list α} (h0 : m < k) (h1 : l.length = k),
  lassign l V m = l.nth_le m (by {rw h1, exact h0})
| 0       _ _               h0 h1 := by cases h0
| (k + 1) _ []              h0 h1 := by cases h1
| (k + 1) 0 (a :: as)       h0 h1 := rfl
| (k + 1) (m + 1) (a :: as) h0 h1 :=
  lassign_eq_of_lt (lt_of_succ_lt_succ h0) (succ_inj h1)

lemma lassign_eq_of_nth_eq_some {a : α} :
  ∀ {k : nat} {as : list α},
  as.nth k = some a → lassign as V k = a  
| 0       as h0 := by {cases as; cases h0, refl } 
| (k + 1) as h0 :=
  begin
    cases as with _ as, { cases h0 },
    unfold list.nth at h0,
    unfold lassign,
    apply lassign_eq_of_nth_eq_some h0,
  end

lemma vassign_eq_of_lt {k m : nat} (v : vector α k) (h0 : m < k) :
  vassign v V m = v.val.nth_le m (by {rw v.property, exact h0}) :=
lassign_eq_of_lt _ _

lemma list.drop_eq_cons_of_lt :
  ∀ {l : list α} {k m : nat} (h0 : m < k) (h1 : l.length = k),
  l.drop m = l.nth_le m (by {rw h1, exact h0}) :: l.drop (m + 1)
| _         0       _       h0 h1 := by cases h0
| []        (k + 1) _       _  h1 := by cases h1
| (a :: as) (k + 1) 0       h0 h1 := rfl
| (a :: as) (k + 1) (m + 1) h0 h1 :=
  begin
    simp only [list.drop, list.nth_le],
    apply list.drop_eq_cons_of_lt,
    { apply lt_of_succ_lt_succ h0 },
    apply succ_inj h1,
  end

lemma splice_zero (x : α) (V : vas α) : splice 0 x (V ₀↦ x) V :=
⟨λ _ h0, by cases h0, rfl, λ m _, rfl⟩

lemma lmap_val_skolem_args (as1 : list α) :
  ∀ as2 : list α, ∀ m : nat, 
  list.suffix m as2 as1 → 
  (trms.lmap (trm.val F (lassign as1 V)) (skolem_args as2.length m)) = as2
| []         _  _ := rfl
| (a :: as2) m h0 :=
  begin
    unfold list.length, 
    unfold skolem_args,
    unfold trms.lmap,
    rw trm.val_vr,
    have h1 := list.nth_eq_some_of_cons_suffix h0,
    have h2 := lassign_eq_of_nth_eq_some h1,
    rw [h2, lmap_val_skolem_args],
    apply list.suffix_succ_of_suffix_cons h0
  end

lemma tmap_vdec_skolem_args :
  ∀ k m : nat, trms.tmap (trm.vdec 0) (skolem_args k (m + 1)) = skolem_args k m 
| 0       m := rfl
| (k + 1) m :=
  begin
    unfold skolem_args, 
    unfold trms.tmap,
    rw [trm.vdec_vr, if_pos (zero_lt_succ _)],
    apply congr_arg,
    apply tmap_vdec_skolem_args, 
  end

lemma holds_skolemize_one_aux [inhabited α] {k : nat} {f : frm} :
  (V ∀⟹ k) (λ V', ∃ a : α, f.holds R F (V' ₀↦ a)) →
  ∃ g : fn α, (V ∀⟹ k)
    (λ V', (f.skolem_vsub 0 (skolem_trm k)).holds R (F ₀↦ g) V') :=
begin 
  intro h0,
  have h1 : ∀ v : vector α k, ∃ a : α, f.holds R F ((vassign v V) ₀↦ a),
  { intro v, apply h0 (vassign v V) (ext_vassign _ _) },
  rw classical.skolem at h1,
  cases h1 with s h1,
  refine ⟨to_fn s, _⟩, intros V' h2,
  cases exists_eq_vassign_of_ext h2 with v h3, 
  rw h3,
  apply holds_skolem_vsub (splice_zero (s v) _),
  { unfold skolem_trm,
    rw [trm.vdec_fn, trm.val_fn, tmap_vdec_skolem_args],
    apply eq.trans (congr_arg _ _) (to_fn_eq _ _),
    have h4 := lmap_val_skolem_args v.val v.val 0 rfl,
    rw v.property at h4,
    apply h4 },
  apply h1 
end
     
def AE : frm → Prop
| (∀* f) := AE f
| (∃* f) := true
| _      := false

def AxE (f : frm) : nat → frm
| 0       := ∃* f
| (k + 1) := ∀* (AxE k)

def Ax (f : frm) : nat → frm
| 0       := f
| (k + 1) := ∀* (Ax k)

lemma exists_kernel_of_AE :
  ∀ f : frm, AE f → ∃ g : frm, ∃ k : nat, f = AxE g k
| (frm.atm _ _)   h0 := by cases h0
| (frm.bin b f g) h0 := by cases h0
| (∃* f)          h0 := ⟨f, 0, rfl⟩
| (∀* f)          h0 :=
  by { rcases exists_kernel_of_AE f h0 with ⟨g, k, h1⟩,
       refine ⟨g, k + 1, _⟩,
       unfold AxE, rw h1 }

lemma holds_AxE_imp :
  ∀ k : nat, ∀ V : vas α, ∀ f : frm, 
  ((AxE f k).holds R F V) →
  (V ∀⟹ k) (λ V', ∃ a : α, f.holds R F (V' ₀↦ a))
| 0 V f h0 :=
  by { intros V' h1, rw eq_of_ext_zero h1, apply h0 }
| (k + 1) V f h0 :=
  by { intros V' h1,
       apply holds_AxE_imp k _ f (h0 (V' k)) V',
       intro m, cases m,
       { simp only [zero_add, assign] },
       simp only [assign, (h1 m).symm, succ_add],
       refl }

lemma skolemize_one_AxE (f : frm) :
  ∀ k m : nat, skolemize_one (AxE f k) m =
  Ax ((f.finc.vsub 0 (skolem_trm (k + m))).vdec 0) k
| 0 m := by { rw zero_add, refl }
| (k + 1) m :=
  by { simp only [ AxE, skolemize_one, Ax,
         skolemize_one_AxE k (m + 1), succ_add ],
    refine ⟨rfl, rfl⟩ }

lemma holds_Ax :
  ∀ k : nat, ∀ f : frm, ∀ V : vas α,
  (Ax f k).holds R F V ↔ (V ∀⟹ k) (λ V', f.holds R F V')
| 0 f V :=
  by { constructor; intro h0,
       { intros V' h1,
         rw eq_of_ext_zero h1,
         apply h0 },
       apply h0,
       apply ext_zero_refl }
| (k + 1) f V :=
  by{ simp only [Ax, frm.holds],
      constructor; intro h0,
      { intros V' h1,
        have h2 := h0 (V' k),
        rw holds_Ax at h2,
        apply h2 _ (ext_assign h1) },
      intro a,
      rw holds_Ax,
      intros V' h1,
      apply h0 _ (ext_succ h1) }

lemma holds_skolemize_one_of_not_AE :
  ∀ f : frm, ¬ AE f →
  ∀ R : rls α, ∀ F : fns α, ∀ V : vas α, ∀ k : nat,
  (skolemize_one f k).holds R F V
| (∀* f) h0 R F V k :=
  by { unfold skolemize_one, intro a,
       apply holds_skolemize_one_of_not_AE f h0 }
| (∃* f) h0 R F V k := false.elim (h0 trivial)
| (frm.atm _ _)   h0 R F V k := rfl
| (frm.bin _ _ _) h0 R F V k := rfl

lemma holds_skolemize_one [inhabited α] {f : frm} :
  f.holds R F V →
  ∃ g : fn α, (skolemize_one f 0).holds R (F ₀↦ g) V :=
begin
  intros h0, 
  cases (classical.em $ AE f) with h1 h1,
  { rcases exists_kernel_of_AE _ h1 with ⟨g, k, h2⟩,
    subst h2, 
    cases holds_skolemize_one_aux 
      (holds_AxE_imp _ _ _ h0) with x h2,
    refine ⟨x, _⟩,
    rw [skolemize_one_AxE, add_zero, holds_Ax],
    exact h2 },
  refine ⟨λ _, default α, _⟩,
  apply holds_skolemize_one_of_not_AE,
  apply h1,
end

lemma exists_fxt_holds_skolemize_core [inhabited α] :
  ∀ k : nat, ∀ F : fns α, ∀ f : frm,
  ex_count f = k → f.holds R F V →
  (F ∃⟹ k) (λ F', (skolemize_core k f).holds R F' V)
| 0       F f h0 h1 := ⟨F, ext_zero_refl _, h1⟩
| (k + 1) F f h0 h1 :=
  begin
    unfold skolemize_core,
    cases holds_skolemize_one h1 with g h2,
    rcases exists_fxt_holds_skolemize_core
      k (F ₀↦ g) (skolemize_one f 0) 
      (ex_count_skolemize_one_eq  _ h0) h2 with ⟨F', h3, h4⟩,
    { refine ⟨F', _, h4⟩,
      apply ext_succ h3 }
  end

lemma holds_skolemize [inhabited α] {f : frm} :
  f.holds R F V →
  (F ∃⟹ ex_count f) (λ F', (skolemize f).holds R F' V) :=
λ h1, exists_fxt_holds_skolemize_core _ _ _ rfl h1

lemma F_vdec :
  ∀ f : frm, ∀ m : nat, f.F → (f.vdec m).F
| (frm.atm _ _)   m h0 := trivial
| (frm.bin b f g) m h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vdec; assumption }

lemma QF_vdec :
  ∀ f : frm, ∀ m : nat, f.QF → (f.vdec m).QF
| (frm.atm _ _)   m h0 := trivial
| (frm.bin b f g) m h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vdec; assumption }
| (frm.qua b f)   m h0 := QF_vdec f _ h0

lemma F_finc :
  ∀ f : frm, f.F → f.finc.F
| (frm.atm _ _)   h0 := trivial
| (frm.bin b f g) h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_finc; assumption }

lemma QF_finc :
  ∀ f : frm, f.QF → (f.finc).QF
| (frm.atm _ _)   h0 := trivial
| (frm.bin b f g) h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_finc; assumption }
| (frm.qua b f)   h0 := QF_finc f h0

lemma F_vsub :
  ∀ f : frm, ∀ k : nat, ∀ t : trm,
  f.F → (f.vsub k t).F
| (frm.atm _ _)   k t h0 := trivial
| (frm.bin b f g) k t h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vsub; assumption }

lemma QF_vsub :
  ∀ f : frm, ∀ k : nat, ∀ t : trm,
  f.QF → (f.vsub k t).QF
| (frm.atm _ _)   k t h0 := trivial
| (frm.bin b f g) k t h0 :=
  by { cases h0 with hf hg, constructor;
       apply F_vsub; assumption }
| (frm.qua b f)   k t h0 := QF_vsub f _ _ h0

lemma QF_skolemize_one :
  ∀ f : frm, ∀ m : nat,
  f.QF → (skolemize_one f m).QF
| (frm.atm _ _)   m h0 := trivial
| (frm.bin _ _ _) m h0 := trivial
| (∀* f)           m h0 := QF_skolemize_one f _ h0
| (∃* f)           m h0 :=
  begin
    apply QF_vdec,
    apply QF_vsub,
    apply QF_finc,
    exact h0
  end

lemma AF_skolemize_core :
  ∀ k : nat, ∀ {f : frm},
  ex_count f = k → f.QF → (skolemize_core k f).AF
| 0       f h0 h1 := AF_of_QF _ h0 h1
| (k + 1) f h0 h1 :=
  begin
    unfold skolemize_core,
    apply AF_skolemize_core,
    { apply ex_count_skolemize_one_eq _ h0 },
    apply QF_skolemize_one _ _ h1
  end

lemma AF_skolemize {f : frm} :
  f.QF → (skolemize f).AF :=
by { intro h0, unfold skolemize,
     apply AF_skolemize_core _ rfl h0 }

end vampire