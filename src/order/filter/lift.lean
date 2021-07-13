/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import order.filter.bases

/-!
# Lift filters along filter and set functions
-/

open set

open_locale classical filter

namespace filter
variables {α : Type*} {β : Type*} {γ : Type*} {ι : Sort*}

section lift

/-- A variant on `bind` using a function `g` taking a set instead of a member of `α`.
This is essentially a push-forward along a function mapping each set to a filter. -/
protected def lift (f : filter α) (g : set α → filter β) :=
⨅s ∈ f, g s

variables {f f₁ f₂ : filter α} {g g₁ g₂ : set α → filter β}

@[simp] lemma lift_top (g : set α → filter β) : (⊤ : filter α).lift g = g univ :=
by simp [filter.lift]

/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type, see `filter.has_basis.lift`.
This lemma states the corresponding `mem_iff` statement without using a sigma type. -/
lemma has_basis.mem_lift_iff {ι} {p : ι → Prop} {s : ι → set α} {f : filter α}
  (hf : f.has_basis p s) {β : ι → Type*} {pg : Π i, β i → Prop} {sg : Π i, β i → set γ}
  {g : set α → filter γ} (hg : ∀ i, (g $ s i).has_basis (pg i) (sg i)) (gm : monotone g)
  {s : set γ} :
  s ∈ f.lift g ↔ ∃ (i : ι) (hi : p i) (x : β i) (hx : pg i x), sg i x ⊆ s :=
begin
  refine (mem_binfi _ ⟨univ, univ_sets _⟩).trans _,
  { intros t₁ ht₁ t₂ ht₂,
    exact ⟨t₁ ∩ t₂, inter_mem_sets ht₁ ht₂, gm $ inter_subset_left _ _,
      gm $ inter_subset_right _ _⟩ },
  { simp only [← (hg _).mem_iff],
    exact hf.exists_iff (λ t₁ t₂ ht H, gm ht H) }
end

/-- If `(p : ι → Prop, s : ι → set α)` is a basis of a filter `f`, `g` is a monotone function
`set α → filter γ`, and for each `i`, `(pg : β i → Prop, sg : β i → set α)` is a basis
of the filter `g (s i)`, then `(λ (i : ι) (x : β i), p i ∧ pg i x, λ (i : ι) (x : β i), sg i x)`
is a basis of the filter `f.lift g`.

This basis is parametrized by `i : ι` and `x : β i`, so in order to formulate this fact using
`has_basis` one has to use `Σ i, β i` as the index type. See also `filter.has_basis.mem_lift_iff`
for the corresponding `mem_iff` statement formulated without using a sigma type. -/
lemma has_basis.lift {ι} {p : ι → Prop} {s : ι → set α} {f : filter α} (hf : f.has_basis p s)
  {β : ι → Type*} {pg : Π i, β i → Prop} {sg : Π i, β i → set γ} {g : set α → filter γ}
  (hg : ∀ i, (g $ s i).has_basis (pg i) (sg i)) (gm : monotone g) :
  (f.lift g).has_basis (λ i : Σ i, β i, p i.1 ∧ pg i.1 i.2) (λ i : Σ i, β i, sg i.1 i.2) :=
begin
  refine ⟨λ t, (hf.mem_lift_iff hg gm).trans _⟩,
  simp [sigma.exists, and_assoc, exists_and_distrib_left]
end

lemma mem_lift_sets (hg : monotone g) {s : set β} :
  s ∈ f.lift g ↔ ∃t∈f, s ∈ g t :=
(f.basis_sets.mem_lift_iff (λ s, (g s).basis_sets) hg).trans $
  by simp only [id, ← exists_sets_subset_iff]

lemma mem_lift {s : set β} {t : set α} (ht : t ∈ f) (hs : s ∈ g t) :
  s ∈ f.lift g :=
le_principal_iff.mp $ show f.lift g ≤ 𝓟 s,
  from infi_le_of_le t $ infi_le_of_le ht $ le_principal_iff.mpr hs

lemma lift_le {f : filter α} {g : set α → filter β} {h : filter β} {s : set α}
  (hs : s ∈ f) (hg : g s ≤ h) : f.lift g ≤ h :=
infi_le_of_le s $ infi_le_of_le hs $ hg

lemma le_lift {f : filter α} {g : set α → filter β} {h : filter β}
  (hh : ∀s∈f, h ≤ g s) : h ≤ f.lift g :=
le_infi $ assume s, le_infi $ assume hs, hh s hs

lemma lift_mono (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) : f₁.lift g₁ ≤ f₂.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi2 $ assume hs, ⟨hf hs, hg s⟩

lemma lift_mono' (hg : ∀s∈f, g₁ s ≤ g₂ s) : f.lift g₁ ≤ f.lift g₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, hg s hs

lemma tendsto_lift {m : γ → β} {l : filter γ} :
  tendsto m l (f.lift g) ↔ ∀ s ∈ f, tendsto m l (g s) :=
by simp only [filter.lift, tendsto_infi]

lemma map_lift_eq {m : β → γ} (hg : monotone g) : map m (f.lift g) = f.lift (map m ∘ g) :=
have monotone (map m ∘ g),
  from map_mono.comp hg,
filter.ext $ λ s,
  by simp only [mem_lift_sets hg, mem_lift_sets this, exists_prop, mem_map, function.comp_app]

lemma comap_lift_eq {m : γ → β} (hg : monotone g) : comap m (f.lift g) = f.lift (comap m ∘ g) :=
have monotone (comap m ∘ g),
  from comap_mono.comp hg,
begin
  ext,
  simp only [mem_lift_sets hg, mem_lift_sets this, mem_comap_sets, exists_prop, mem_lift_sets],
  exact ⟨λ ⟨b, ⟨a, ha, hb⟩, hs⟩, ⟨a, ha, b, hb, hs⟩, λ ⟨a, ha, b, hb, hs⟩, ⟨b, ⟨a, ha, hb⟩, hs⟩⟩
end

theorem comap_lift_eq2 {m : β → α} {g : set β → filter γ} (hg : monotone g) :
  (comap m f).lift g = f.lift (g ∘ preimage m) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs,
    infi_le_of_le (preimage m s) $ infi_le _ ⟨s, hs, subset.refl _⟩)
  (le_infi $ assume s, le_infi $ assume ⟨s', hs', (h_sub : preimage m s' ⊆ s)⟩,
    infi_le_of_le s' $ infi_le_of_le hs' $ hg h_sub)

lemma map_lift_eq2 {g : set β → filter γ} {m : α → β} (hg : monotone g) :
  (map m f).lift g = f.lift (g ∘ image m) :=
le_antisymm
  (infi_le_infi2 $ assume s, ⟨image m s,
    infi_le_infi2 $ assume hs, ⟨
      f.sets_of_superset hs $ assume a h, mem_image_of_mem _ h,
      le_refl _⟩⟩)
  (infi_le_infi2 $ assume t, ⟨preimage m t,
    infi_le_infi2 $ assume ht, ⟨ht,
      hg $ assume x, assume h : x ∈ m '' preimage m t,
        let ⟨y, hy, h_eq⟩ := h in
        show x ∈ t, from h_eq ▸ hy⟩⟩)

lemma lift_comm {g : filter β} {h : set α → set β → filter γ} :
  f.lift (λs, g.lift (h s)) = g.lift (λt, f.lift (λs, h s t)) :=
le_antisymm
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)
  (le_infi $ assume i, le_infi $ assume hi, le_infi $ assume j, le_infi $ assume hj,
    infi_le_of_le j $ infi_le_of_le hj $ infi_le_of_le i $ infi_le _ hi)

lemma lift_assoc {h : set β → filter γ} (hg : monotone g)  :
  (f.lift g).lift h = f.lift (λs, (g s).lift h) :=
le_antisymm
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le t $ infi_le _ $ (mem_lift_sets hg).mpr ⟨_, hs, ht⟩)
  (le_infi $ assume t, le_infi $ assume ht,
    let ⟨s, hs, h'⟩ := (mem_lift_sets hg).mp ht in
    infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le t $ infi_le _ h')

lemma lift_lift_same_le_lift {g : set α → set α → filter β} :
  f.lift (λs, f.lift (g s)) ≤ f.lift (λs, g s s) :=
le_infi $ assume s, le_infi $ assume hs, infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le s $
  infi_le _ hs

lemma lift_lift_same_eq_lift {g : set α → set α → filter β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)) :
  f.lift (λs, f.lift (g s)) = f.lift (λs, g s s) :=
le_antisymm
  lift_lift_same_le_lift
  (le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
    infi_le_of_le (s ∩ t) $
    infi_le_of_le (inter_mem_sets hs ht) $
    calc g (s ∩ t) (s ∩ t) ≤ g s (s ∩ t) : hg₂ (s ∩ t) (inter_subset_left _ _)
      ... ≤ g s t                        : hg₁ s (inter_subset_right _ _))

lemma lift_principal {s : set α} (hg : monotone g) :
  (𝓟 s).lift g = g s :=
le_antisymm
  (infi_le_of_le s $ infi_le _ $ subset.refl _)
  (le_infi $ assume t, le_infi $ assume hi, hg hi)

theorem monotone_lift [preorder γ] {f : γ → filter α} {g : γ → set α → filter β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift (g c)) :=
assume a b h, lift_mono (hf h) (hg h)

lemma lift_ne_bot_iff (hm : monotone g) : (ne_bot $ f.lift g) ↔ (∀s∈f, ne_bot (g s)) :=
begin
  rw [filter.lift, infi_subtype', infi_ne_bot_iff_of_directed', subtype.forall'],
  { rintros ⟨s, hs⟩ ⟨t, ht⟩,
    exact ⟨⟨s ∩ t, inter_mem_sets hs ht⟩, hm (inter_subset_left s t), hm (inter_subset_right s t)⟩ }
end

@[simp] lemma lift_const {f : filter α} {g : filter β} : f.lift (λx, g) = g :=
le_antisymm (lift_le univ_mem_sets $ le_refl g) (le_lift $ assume s hs, le_refl g)

@[simp] lemma lift_inf {f : filter α} {g h : set α → filter β} :
  f.lift (λx, g x ⊓ h x) = f.lift g ⊓ f.lift h :=
by simp only [filter.lift, infi_inf_eq, eq_self_iff_true]

@[simp] lemma lift_principal2 {f : filter α} : f.lift 𝓟 = f :=
le_antisymm
  (assume s hs, mem_lift hs (mem_principal_self s))
  (le_infi $ assume s, le_infi $ assume hs, by simp only [hs, le_principal_iff])

lemma lift_infi {f : ι → filter α} {g : set α → filter β}
  [hι : nonempty ι] (hg : ∀{s t}, g s ⊓ g t = g (s ∩ t)) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
    have g_mono : monotone g,
      from assume s t h, le_of_inf_eq $ eq.trans hg $ congr_arg g $ inter_eq_self_of_subset_left h,
    have ∀t∈(infi f), (⨅ (i : ι), filter.lift (f i) g) ≤ g t,
      from assume t ht, infi_sets_induct ht
        (let ⟨i⟩ := hι in infi_le_of_le i $ infi_le_of_le univ $ infi_le _ univ_mem_sets)
        (assume i s₁ s₂ hs₁ hs₂,
          @hg s₁ s₂ ▸ le_inf (infi_le_of_le i $ infi_le_of_le s₁ $ infi_le _ hs₁) hs₂)
        (assume s₁ s₂ hs₁ hs₂, le_trans hs₂ $ g_mono hs₁),
    begin
      simp only [mem_lift_sets g_mono,  exists_imp_distrib],
      exact assume t ht hs, this t ht hs
    end)

end lift

section lift'
/-- Specialize `lift` to functions `set α → set β`. This can be viewed as a generalization of `map`.
This is essentially a push-forward along a function mapping each set to a set. -/
protected def lift' (f : filter α) (h : set α → set β) :=
f.lift (𝓟 ∘ h)

variables {f f₁ f₂ : filter α} {h h₁ h₂ : set α → set β}

@[simp] lemma lift'_top (h : set α → set β) : (⊤ : filter α).lift' h = 𝓟 (h univ) :=
lift_top _

lemma mem_lift' {t : set α} (ht : t ∈ f) : h t ∈ (f.lift' h) :=
le_principal_iff.mp $ show f.lift' h ≤ 𝓟 (h t),
  from infi_le_of_le t $ infi_le_of_le ht $ le_refl _

lemma tendsto_lift' {m : γ → β} {l : filter γ} :
  tendsto m l (f.lift' h) ↔ ∀ s ∈ f, ∀ᶠ a in l, m a ∈ h s :=
by simp only [filter.lift', tendsto_lift, tendsto_principal]

lemma has_basis.lift' {ι} {p : ι → Prop} {s} (hf : f.has_basis p s) (hh : monotone h) :
  (f.lift' h).has_basis p (h ∘ s) :=
begin
  refine ⟨λ t, (hf.mem_lift_iff _ (monotone_principal.comp hh)).trans _⟩,
  show ∀ i, (𝓟 (h (s i))).has_basis (λ j : unit, true) (λ (j : unit), h (s i)),
    from λ i, has_basis_principal _,
  simp only [exists_const]
end

lemma mem_lift'_sets (hh : monotone h) {s : set β} : s ∈ (f.lift' h) ↔ (∃t∈f, h t ⊆ s) :=
mem_lift_sets $ monotone_principal.comp hh

lemma eventually_lift'_iff (hh : monotone h) {p : β → Prop} :
  (∀ᶠ y in f.lift' h, p y) ↔ (∃ t ∈ f, ∀ y ∈ h t, p y) :=
mem_lift'_sets hh

lemma lift'_le {f : filter α} {g : set α → set β} {h : filter β} {s : set α}
  (hs : s ∈ f) (hg : 𝓟 (g s) ≤ h) : f.lift' g ≤ h :=
lift_le hs hg

lemma lift'_mono (hf : f₁ ≤ f₂) (hh : h₁ ≤ h₂) : f₁.lift' h₁ ≤ f₂.lift' h₂ :=
lift_mono hf $ assume s, principal_mono.mpr $ hh s

lemma lift'_mono' (hh : ∀s∈f, h₁ s ⊆ h₂ s) : f.lift' h₁ ≤ f.lift' h₂ :=
infi_le_infi $ assume s, infi_le_infi $ assume hs, principal_mono.mpr $ hh s hs

lemma lift'_cong (hh : ∀s∈f, h₁ s = h₂ s) : f.lift' h₁ = f.lift' h₂ :=
le_antisymm (lift'_mono' $ assume s hs, le_of_eq $ hh s hs)
  (lift'_mono' $ assume s hs, le_of_eq $ (hh s hs).symm)

lemma map_lift'_eq {m : β → γ} (hh : monotone h) : map m (f.lift' h) = f.lift' (image m ∘ h) :=
calc map m (f.lift' h) = f.lift (map m ∘ 𝓟 ∘ h) :
    map_lift_eq $ monotone_principal.comp hh
  ... = f.lift' (image m ∘ h) : by simp only [(∘), filter.lift', map_principal, eq_self_iff_true]

lemma map_lift'_eq2 {g : set β → set γ} {m : α → β} (hg : monotone g) :
  (map m f).lift' g = f.lift' (g ∘ image m) :=
map_lift_eq2 $ monotone_principal.comp hg

theorem comap_lift'_eq {m : γ → β} (hh : monotone h) :
  comap m (f.lift' h) = f.lift' (preimage m ∘ h) :=
calc comap m (f.lift' h) = f.lift (comap m ∘ 𝓟 ∘ h) :
    comap_lift_eq $ monotone_principal.comp hh
  ... = f.lift' (preimage m ∘ h) :
    by simp only [(∘), filter.lift', comap_principal, eq_self_iff_true]

theorem comap_lift'_eq2 {m : β → α} {g : set β → set γ} (hg : monotone g) :
  (comap m f).lift' g = f.lift' (g ∘ preimage m) :=
comap_lift_eq2 $ monotone_principal.comp hg

lemma lift'_principal {s : set α} (hh : monotone h) :
  (𝓟 s).lift' h = 𝓟 (h s) :=
lift_principal $ monotone_principal.comp hh

lemma lift'_pure {a : α} (hh : monotone h) :
  (pure a : filter α).lift' h = 𝓟 (h {a}) :=
by rw [← principal_singleton, lift'_principal hh]

lemma lift'_bot (hh : monotone h) : (⊥ : filter α).lift' h = 𝓟 (h ∅) :=
by rw [← principal_empty, lift'_principal hh]

lemma principal_le_lift' {t : set β} (hh : ∀s∈f, t ⊆ h s) :
  𝓟 t ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs, principal_mono.mpr (hh s hs)

theorem monotone_lift' [preorder γ] {f : γ → filter α} {g : γ → set α → set β}
  (hf : monotone f) (hg : monotone g) : monotone (λc, (f c).lift' (g c)) :=
assume a b h, lift'_mono (hf h) (hg h)

lemma lift_lift'_assoc {g : set α → set β} {h : set β → filter γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift h = f.lift (λs, h (g s)) :=
calc (f.lift' g).lift h = f.lift (λs, (𝓟 (g s)).lift h) :
    lift_assoc (monotone_principal.comp hg)
  ... = f.lift (λs, h (g s)) : by simp only [lift_principal, hh, eq_self_iff_true]

lemma lift'_lift'_assoc {g : set α → set β} {h : set β → set γ}
  (hg : monotone g) (hh : monotone h) :
  (f.lift' g).lift' h = f.lift' (λs, h (g s)) :=
lift_lift'_assoc hg (monotone_principal.comp hh)

lemma lift'_lift_assoc {g : set α → filter β} {h : set β → set γ}
  (hg : monotone g) : (f.lift g).lift' h = f.lift (λs, (g s).lift' h) :=
lift_assoc hg

lemma lift_lift'_same_le_lift' {g : set α → set α → set β} :
  f.lift (λs, f.lift' (g s)) ≤ f.lift' (λs, g s s) :=
lift_lift_same_le_lift

lemma lift_lift'_same_eq_lift' {g : set α → set α → set β}
  (hg₁ : ∀s, monotone (λt, g s t)) (hg₂ : ∀t, monotone (λs, g s t)) :
  f.lift (λs, f.lift' (g s)) = f.lift' (λs, g s s) :=
lift_lift_same_eq_lift
  (assume s, monotone_principal.comp (hg₁ s))
  (assume t, monotone_principal.comp (hg₂ t))

lemma lift'_inf_principal_eq {h : set α → set β} {s : set β} :
  f.lift' h ⊓ 𝓟 s = f.lift' (λt, h t ∩ s) :=
by simp only [filter.lift', filter.lift, (∘), ← inf_principal, infi_subtype', ← infi_inf]

lemma lift'_ne_bot_iff (hh : monotone h) : (ne_bot (f.lift' h)) ↔ (∀s∈f, (h s).nonempty) :=
calc (ne_bot (f.lift' h)) ↔ (∀s∈f, ne_bot (𝓟 (h s))) :
    lift_ne_bot_iff (monotone_principal.comp hh)
  ... ↔ (∀s∈f, (h s).nonempty) : by simp only [principal_ne_bot_iff]

@[simp] lemma lift'_id {f : filter α} : f.lift' id = f :=
lift_principal2

lemma le_lift' {f : filter α} {h : set α → set β} {g : filter β}
  (h_le : ∀s∈f, h s ∈ g) : g ≤ f.lift' h :=
le_infi $ assume s, le_infi $ assume hs,
  by simpa only [h_le, le_principal_iff, function.comp_app] using h_le s hs

lemma lift_infi' {f : ι → filter α} {g : set α → filter β}
  [nonempty ι] (hf : directed (≥) f) (hg : monotone g) : (infi f).lift g = (⨅i, (f i).lift g) :=
le_antisymm
  (le_infi $ assume i, lift_mono (infi_le _ _) (le_refl _))
  (assume s,
  begin
    rw mem_lift_sets hg,
    simp only [exists_imp_distrib, mem_infi hf],
    exact assume t i ht hs, mem_infi_sets i $ mem_lift ht hs
  end)

lemma lift'_infi {f : ι → filter α} {g : set α → set β}
  [nonempty ι] (hg : ∀{s t}, g s ∩ g t = g (s ∩ t)) : (infi f).lift' g = (⨅i, (f i).lift' g) :=
lift_infi $ λ s t, by simp only [principal_eq_iff_eq, inf_principal, (∘), hg]

lemma lift'_inf (f g : filter α) {s : set α → set β} (hs : ∀ {t₁ t₂}, s t₁ ∩ s t₂ = s (t₁ ∩ t₂)) :
  (f ⊓ g).lift' s = f.lift' s ⊓ g.lift' s :=
have (⨅ b : bool, cond b f g).lift' s = ⨅ b : bool, (cond b f g).lift' s :=
  lift'_infi @hs,
by simpa only [infi_bool_eq]

theorem comap_eq_lift' {f : filter β} {m : α → β} :
  comap m f = f.lift' (preimage m) :=
filter.ext $ λ s, (mem_lift'_sets monotone_preimage).symm

lemma lift'_infi_powerset {f : ι → filter α} :
  (infi f).lift' powerset = (⨅i, (f i).lift' powerset) :=
begin
  casesI (is_empty_or_nonempty ι).symm,
  { exact (lift'_infi $ λ _ _, (powerset_inter _ _).symm) },
  { rw [infi_of_empty, infi_of_empty, lift'_top, powerset_univ, principal_univ] }
end

lemma lift'_inf_powerset (f g : filter α) :
  (f ⊓ g).lift' powerset = f.lift' powerset ⊓ g.lift' powerset :=
lift'_inf f g $ λ _ _, (powerset_inter _ _).symm

lemma eventually_lift'_powerset {f : filter α} {p : set α → Prop} :
  (∀ᶠ s in f.lift' powerset, p s) ↔ ∃ s ∈ f, ∀ t ⊆ s, p t :=
eventually_lift'_iff monotone_powerset

lemma eventually_lift'_powerset' {f : filter α} {p : set α → Prop}
  (hp : ∀ ⦃s t⦄, s ⊆ t → p t → p s) :
  (∀ᶠ s in f.lift' powerset, p s) ↔ ∃ s ∈ f, p s :=
eventually_lift'_powerset.trans $ exists_congr $ λ s, exists_congr $
  λ hsf, ⟨λ H, H s (subset.refl s), λ hs t ht, hp ht hs⟩

instance lift'_powerset_ne_bot (f : filter α) : ne_bot (f.lift' powerset) :=
(lift'_ne_bot_iff monotone_powerset).2 $ λ _ _, powerset_nonempty

lemma tendsto_lift'_powerset_mono {la : filter α} {lb : filter β} {s t : α → set β}
  (ht : tendsto t la (lb.lift' powerset)) (hst : ∀ᶠ x in la, s x ⊆ t x) :
  tendsto s la (lb.lift' powerset) :=
begin
  simp only [filter.lift', filter.lift, (∘), tendsto_infi, tendsto_principal] at ht ⊢,
  exact λ u hu, (ht u hu).mp (hst.mono $ λ a hst ht, subset.trans hst ht)
end

@[simp] lemma eventually_lift'_powerset_forall {f : filter α} {p : α → Prop} :
  (∀ᶠ s in f.lift' powerset, ∀ x ∈ s, p x) ↔ ∀ᶠ x in f, p x :=
iff.trans (eventually_lift'_powerset' $ λ s t hst ht x hx, ht x (hst hx))
  exists_sets_subset_iff

alias eventually_lift'_powerset_forall ↔
  filter.eventually.of_lift'_powerset filter.eventually.lift'_powerset

@[simp] lemma eventually_lift'_powerset_eventually {f g : filter α} {p : α → Prop} :
  (∀ᶠ s in f.lift' powerset, ∀ᶠ x in g, x ∈ s → p x) ↔ ∀ᶠ x in f ⊓ g, p x :=
calc _ ↔ ∃ s ∈ f, ∀ᶠ x in g, x ∈ s → p x :
  eventually_lift'_powerset' $ λ s t hst ht, ht.mono $ λ x hx hs, hx (hst hs)
... ↔ ∃ (s ∈ f) (t ∈ g), ∀ x, x ∈ t → x ∈ s → p x :
  by simp only [eventually_iff_exists_mem]
... ↔ ∀ᶠ x in f ⊓ g, p x :
  by simp only [filter.eventually, mem_inf_sets, subset_def, mem_inter_iff,
    ← and_imp, and_comm, mem_set_of_eq]

end lift'

section prod
variables {f : filter α}

lemma prod_def {f : filter α} {g : filter β} : f ×ᶠ g = (f.lift $ λs, g.lift' $ set.prod s) :=
have ∀(s:set α) (t : set β),
    𝓟 (set.prod s t) = (𝓟 s).comap prod.fst ⊓ (𝓟 t).comap prod.snd,
  by simp only [principal_eq_iff_eq, comap_principal, inf_principal]; intros; refl,
begin
  simp only [filter.lift', function.comp, this, lift_inf, lift_const, lift_inf],
  rw [← comap_lift_eq monotone_principal, ← comap_lift_eq monotone_principal],
  simp only [filter.prod, lift_principal2, eq_self_iff_true]
end

lemma prod_same_eq : f ×ᶠ f = f.lift' (λt, set.prod t t) :=
by rw [prod_def];
from lift_lift'_same_eq_lift'
  (assume s, set.monotone_prod monotone_const monotone_id)
  (assume t, set.monotone_prod monotone_id monotone_const)

lemma mem_prod_same_iff {s : set (α×α)} :
  s ∈ f ×ᶠ f ↔ (∃t∈f, set.prod t t ⊆ s) :=
by rw [prod_same_eq, mem_lift'_sets]; exact set.monotone_prod monotone_id monotone_id

lemma tendsto_prod_self_iff {f : α × α → β} {x : filter α} {y : filter β} :
  filter.tendsto f (x ×ᶠ x) y ↔
  ∀ W ∈ y, ∃ U ∈ x, ∀ (x x' : α), x ∈ U → x' ∈ U → f (x, x') ∈ W :=
by simp only [tendsto_def, mem_prod_same_iff, prod_sub_preimage_iff, exists_prop, iff_self]

variables {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}

lemma prod_lift_lift
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → filter β₁} {g₂ : set α₂ → filter β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  (f₁.lift g₁) ×ᶠ (f₂.lift g₂) = f₁.lift (λs, f₂.lift (λt, g₁ s ×ᶠ g₂ t)) :=
begin
  simp only [prod_def],
  rw [lift_assoc],
  apply congr_arg, funext x,
  rw [lift_comm],
  apply congr_arg, funext y,
  rw [lift'_lift_assoc],
  exact hg₂,
  exact hg₁
end

lemma prod_lift'_lift'
  {f₁ : filter α₁} {f₂ : filter α₂} {g₁ : set α₁ → set β₁} {g₂ : set α₂ → set β₂}
  (hg₁ : monotone g₁) (hg₂ : monotone g₂) :
  f₁.lift' g₁ ×ᶠ f₂.lift' g₂ = f₁.lift (λs, f₂.lift' (λt, (g₁ s).prod (g₂ t))) :=
begin
  rw [prod_def, lift_lift'_assoc],
  apply congr_arg, funext x,
  rw [lift'_lift'_assoc],
  exact hg₂,
  exact set.monotone_prod monotone_const monotone_id,
  exact hg₁,
  exact (monotone_lift' monotone_const $ monotone_lam $
    assume x, set.monotone_prod monotone_id monotone_const)
end

end prod

end filter
