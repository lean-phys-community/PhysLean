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

open Metric
open Complex

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

-- Def 2.1
/-- The regular points for `T`.

  `z : ℂ` is a regular point for `T` iff there exists a constant `c > 0` such that
  `c * ‖x‖ ≤ ‖(T - z • 1) x‖` for all `x ∈ (T - z • 1).domain`. -/
def regularityDomain (T : H →ₗ.[ℂ] H) : Set ℂ := {z : ℂ | ∃ c > 0, IsLowerBound T z c}

/-- `T ≤ T'` implies `T'.regularityDomain ⊆ T.regularityDomain`. -/
lemma regularityDomain_antitone : Antitone (regularityDomain (H := H)) :=
  fun _ _ hle _ ⟨c, hc, h⟩ ↦ ⟨c, hc, isLowerBound_of_ge hle h⟩

-- Prop 2.1.i
/-- `z` is a regular point for `T` iff `T - z • 1` has a bounded inverse. -/
lemma mem_regularityDomain_iff {T : H →ₗ.[ℂ] H} {z : ℂ} :
    z ∈ T.regularityDomain ↔ (T - z • 1).toFun.ker = ⊥ ∧ (T - z • 1).inverse.IsBounded := by
  constructor
  · intro ⟨c, hc, h_bound⟩
    have h_ker : (T - z • 1).toFun.ker = ⊥ := by
      ext x
      constructor <;> intro
      · have : c * ‖x‖ ≤ 0 → ‖x‖ ≤ 0 := fun h' ↦ nonpos_of_mul_nonpos_right h' hc
        specialize h_bound ⟨x, x.2.1⟩
        simp_all [sub_apply]
      · simp_all
    refine ⟨h_ker, c⁻¹, inv_pos.mpr hc, fun ⟨x, hx⟩ ↦ ?_⟩
    rw [inverse_domain] at hx
    obtain ⟨y, hy⟩ := hx
    specialize h_bound ⟨y, y.2.1⟩
    simp_all [le_inv_mul_iff₀, sub_apply, inverse_apply_eq h_ker (y := ⟨x, hx⟩) hy]
  · rintro ⟨h_ker, c, hc, h_bound⟩
    refine ⟨c⁻¹, inv_pos.mpr hc, fun x ↦ ?_⟩
    apply (inv_mul_le_iff₀ hc).mpr
    have hx : ↑x ∈ (T - z • 1).domain := by simp [sub_domain]
    specialize h_bound ⟨(T - z • 1) ⟨x, hx⟩, by simp [inverse_domain]⟩
    rw [inverse_apply_eq h_ker (x := ⟨x, hx⟩) rfl] at h_bound
    simp_all [sub_apply]

/-- The regularity domain of `T` contains open balls with radii controlled by the lower bounds. -/
lemma ball_subset_regularityDomain
    {T : H →ₗ.[ℂ] H} {z : ℂ} {c : ℝ} (h : IsLowerBound T z c) :
    ball z c ⊆ T.regularityDomain := by
  intro z' hzc
  refine ⟨c - ‖z - z'‖, by simp_all [dist_eq, norm_sub_rev], fun x ↦ ?_⟩
  calc
    _ = c * ‖x‖ - ‖(z - z') • x‖ := by simp [sub_mul, norm_smul]
    _ ≤ ‖T x - z • x‖ - ‖(z - z') • x‖ := by linarith [h x]
    _ ≤ ‖T x - z • x + (z - z') • x‖ := norm_sub_le_norm_add _ _
    _ = ‖T x - z' • x‖ := by simp [sub_smul]

end

end LinearPMap
