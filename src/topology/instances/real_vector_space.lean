/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.algebra.module
import topology.instances.real

/-!
# Continuous additive maps are `ℝ`-linear

In this file we prove that a continuous map `f : E →+ F` between two topological vector spaces
over `ℝ` is `ℝ`-linear
-/

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [has_continuous_smul ℝ E] {F : Type*} [add_comm_group F] [module ℝ F]
  [topological_space F] [has_continuous_smul ℝ F] [t2_space F]

namespace add_monoid_hom

/-- A continuous additive map between two vector spaces over `ℝ` is `ℝ`-linear. -/
lemma map_real_smul (f : E →+ F) (hf : continuous f) (c : ℝ) (x : E) :
  f (c • x) = c • f x :=
suffices (λ c : ℝ, f (c • x)) = λ c : ℝ, c • f x, from _root_.congr_fun this c,
dense_embedding_of_rat.dense.equalizer
  (hf.comp $ continuous_id.smul continuous_const)
  (continuous_id.smul continuous_const)
  (funext $ λ r, f.map_rat_cast_smul r x)

/-- Reinterpret a continuous additive homomorphism between two real vector spaces
as a continuous real-linear map. -/
def to_real_linear_map (f : E →+ F) (hf : continuous f) : E →L[ℝ] F :=
⟨{ to_fun := f, map_add' := f.map_add, map_smul' := f.map_real_smul hf }, hf⟩

@[simp] lemma coe_to_real_linear_map (f : E →+ F) (hf : continuous f) :
  ⇑(f.to_real_linear_map hf) = f := rfl

end add_monoid_hom
