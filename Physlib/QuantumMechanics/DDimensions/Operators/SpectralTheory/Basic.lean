/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
/-!

# Spectral theory for closed operators

## i. Overview

In this module we develop the basics for the spectral theory of closed unbounded operators.
This forms the basis for the spectral theory of self-adjoint unbounded operators,
which are of central importance in quantum mechanics.

## ii. Key results

## iii. Table of contents

- A. Regularity domain

## iv. References

- [Konrad Schmüdgen, *Unbounded Self-Adjoint Operators on Hilbert Space*][Schmudgen2012]

-/

@[expose] public section

namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

noncomputable section

/-!
## A. Regularity domain
-/

/-- `IsLowerBound T z c` means that `c * ‖x‖ ≤ ‖T x - z • x‖` for all `x : T.domain`. -/
def IsLowerBound (T : H →ₗ.[ℂ] H) (z : ℂ) (c : ℝ) : Prop := ∀ x : T.domain, c * ‖x‖ ≤ ‖T x - z • x‖

lemma isLowerBound_of_le
    {T : H →ₗ.[ℂ] H} {z : ℂ} {c c' : ℝ} (hle : c' ≤ c) (h : IsLowerBound T z c) :
    IsLowerBound T z c' :=
  fun x ↦ (mul_le_mul_of_nonneg_right hle (norm_nonneg x)).trans (h x)

lemma isLowerBound_of_ge
    {T₁ T₂ : H →ₗ.[ℂ] H} (hle : T₁ ≤ T₂) {z : ℂ} {c : ℝ} (h : IsLowerBound T₂ z c) :
    IsLowerBound T₁ z c :=
  fun x ↦ @hle.2 x ⟨x, hle.1 x.2⟩ rfl ▸ h ⟨x, hle.1 x.2⟩

lemma isLowerBound_closure {T : H →ₗ.[ℂ] H} {z : ℂ} {c : ℝ} (h : IsLowerBound T z c) :
    IsLowerBound T.closure z c := by
  by_cases hT : T.IsClosable
  · intro x
    obtain ⟨b, hb, hb'⟩ := mem_closure_iff_seq_limit.mp <|
      hT.graph_closure_eq_closure_graph ▸ T.closure.mem_graph x
    rw [nhds_prod_eq] at hb'
    have hb₁ := hb'.fst.norm.const_mul c
    have hb₂ := (hb'.snd.sub <| hb'.fst.const_smul z).norm
    refine le_of_tendsto_of_tendsto' hb₁ hb₂ fun n ↦ ?_
    obtain ⟨y, hy₁, hy₂⟩ := (mem_graph_iff _).mp (hb n)
    exact hy₁ ▸ hy₂ ▸ h y
  · rwa [closure_def' hT]

end

end LinearPMap
