/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.DDimensions.Operators.Unbounded
public import Physlib.QuantumMechanics.DDimensions.SpaceDHilbertSpace.SchwartzSubmodule
/-!

# Multiplication operators on `SpaceDHilbertSpace`

## i. Overview

In this module we introduce unbounded operators defined by multiplication by a function
`f : Space d → ℂ` which is `AEStronglyMeasurable`. The domain is defined to be as large as possible,
namely a vector `ψ ∈ SpaceDHilbertSpace d` is in the domain iff `f • ψ ∈ SpaceDHilbertSpace d`.

## ii. Key results

## iii. Table of contents

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace
noncomputable section

open MeasureTheory
open AEEqFun
open Filter

variable {d : ℕ}

/-- The `LinearPMap` which maps `ψ` to `f • ψ` with domain `{ψ | f • ψ ∈ SpaceDHilbertSpace d}`. -/
def mulLPM (f : Space d → ℂ) : SpaceDHilbertSpace d →ₗ.[ℂ] SpaceDHilbertSpace d where
  domain := {
    carrier := {ψ : SpaceDHilbertSpace d | MemHS (f • ψ.val.cast)}
    add_mem' := by
      intro ψ φ hψ hφ
      refine memHS_of_ae _ (memHS_add hψ hφ) ?_
      filter_upwards [coeFn_add ψ.val φ.val] with x h
      simp [mul_add, h]
    zero_mem' := memHS_of_ae 0 zero_memHS (by filter_upwards; simp)
    smul_mem' c ψ hψ := by
      refine memHS_of_ae _ (memHS_const_smul (c := c) hψ) ?_
      filter_upwards [coeFn_smul c ψ.val] with x h
      change _ = (f • (c • ψ.val).cast) x
      simp [h, mul_left_comm]
  }
  toFun := {
    toFun ψ := mk ψ.prop
    map_add' ψ φ := by
      rw [← mk_add, mk_eq_iff]
      filter_upwards [coeFn_add ψ.1.val φ.1.val] with x h
      simp [h, mul_add]
    map_smul' c ψ := by
      rw [← mk_const_smul, mk_eq_iff]
      filter_upwards [coeFn_smul c ψ.1.val] with x h
      change (f • (c • ψ.1.val).cast) x = _
      simp [h, mul_left_comm]
  }

lemma mulLPM_dense_domain {f : Space d → ℂ} (hf : AEStronglyMeasurable f) :
    Dense ((mulLPM f).domain : Set (SpaceDHilbertSpace d)) := by
  intro ξ
  apply mem_closure_iff_seq_limit.mpr
  obtain ⟨ψ, hψ, hψξ⟩ := mem_closure_iff_seq_limit.mp (SchwartzSubmodule.dense d ξ)
  obtain ⟨u, hu, hfu⟩ := AEStronglyMeasurable.aemeasurable hf
  let s : ℕ → Set (Space d) := fun n ↦ u ⁻¹' (Metric.closedBall 0 n)
  have hs : ∀ n, MeasurableSet (s n) := fun n ↦ hu measurableSet_closedBall
  let φ : ℕ → SpaceDHilbertSpace d := fun n ↦ mk (f := (s n).indicator (ψ n)) <| by
    apply memHS_iff.mpr
    have hsψ : AEStronglyMeasurable ((s n).indicator (ψ n)) volume :=
      AEStronglyMeasurable.indicator (by fun_prop) (hs n)
    refine ⟨hsψ, by fun_prop, ?_⟩
    refine HasFiniteIntegral.mono (memHS_iff.mp (coe_hilbertSpace_memHS (ψ n))).2.2 ?_
    refine Eventually.of_forall (fun x ↦ ?_)
    by_cases hx : x ∈ s n <;> simp [hx]
  have hφ : ∀ n, φ n =ᵐ[volume] (s n).indicator (ψ n) := fun n ↦ coe_mk_ae _
  use φ
  constructor
  · intro n
    apply memHS_iff.mpr
    have hfφ : AEStronglyMeasurable (f • (φ n).val.cast) volume := by
      change AEStronglyMeasurable (fun x ↦ f x * φ n x) volume
      fun_prop
    refine ⟨hfφ, by fun_prop, ?_⟩
    refine HasFiniteIntegral.mono (memHS_iff.mp (coe_hilbertSpace_memHS (n • φ n))).2.2 ?_
    filter_upwards [hfu, coeFn_smul n (φ n).val, hφ n] with x h₁ h₂ h₃
    by_cases hx : x ∈ s n
    · simp_rw [norm_pow, norm_norm, sq_le_sq, abs_norm]
      calc
        _ = ‖u x‖ * ‖φ n x‖ := by simp [h₁]
        _ ≤ n * ‖φ n x‖ := mul_le_mul_of_nonneg_right (by simp_all [s]) (norm_nonneg _)
        _ = ‖(n • φ n) x‖ := by simp [h₂]
    · simp [h₃, hx]
  · refine tendsto_of_sub_tendsto_zero ξ hψξ ?_
    let σ : ℕ → SpaceDHilbertSpace d := fun n ↦ mk (f := (s n).indicator ξ) <| by
      apply memHS_iff.mpr
      have hsξ : AEStronglyMeasurable ((s n).indicator ξ) volume :=
        AEStronglyMeasurable.indicator (by fun_prop) (hs n)
      refine ⟨hsξ, by fun_prop, ?_⟩
      refine HasFiniteIntegral.mono (memHS_iff.mp (coe_hilbertSpace_memHS ξ)).2.2 ?_
      refine Eventually.of_forall fun x ↦ ?_
      by_cases hx : x ∈ s n <;> simp [hx]
    have hσ : ∀ n, σ n =ᵐ[volume] (s n).indicator ξ := fun n ↦ coe_mk_ae _
    refine tendsto_of_sub_tendsto_zero (f := fun n ↦ σ n - ξ) 0 ?_ ?_
    · apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mpr
      have h : ∀ n, ∫⁻ x, ‖(σ n - ξ) x‖ₑ ^ 2 = ∫⁻ x, ‖(s n)ᶜ.indicator ξ x‖ₑ ^ 2 := by
        intro n
        refine lintegral_congr_ae ?_
        filter_upwards [coeFn_sub (σ n).val ξ.val, hσ n] with x h₁ h₂
        by_cases hx : x ∈ s n <;> simp [hx, h₁, h₂]
      simp_rw [h]
      rw [← MeasureTheory.lintegral_zero (α := Space d) (μ := volume)]
      refine tendsto_lintegral_of_dominated_convergence' (fun x ↦ ‖ξ x‖ₑ ^ 2) ?_ ?_ ?_ ?_
      · intro n
        refine AEMeasurable.pow_const ?_ 2
        refine AEMeasurable.enorm ?_
        exact AEMeasurable.indicator (by fun_prop) (hs n).compl
      · intro n
        filter_upwards with x
        by_cases hx : x ∈ s n <;> simp [hx]
      · have : ∫⁻ x, ‖‖ξ x‖ ^ 2‖ₑ ≠ ⊤ := (memHS_iff.mp (coe_hilbertSpace_memHS ξ)).2.2.ne
        simp_all
      · filter_upwards with x
        rw [← zero_pow two_ne_zero, ← enorm_zero (E := ℂ)]
        refine ENNReal.Tendsto.pow ?_
        refine Tendsto.enorm ?_
        refine tendsto_nhds_of_eventually_eq ?_
        apply eventually_atTop.mpr
        use ⌈‖u x‖⌉.toNat
        intro n hn
        suffices ‖u x‖ ≤ n by simp [s, this]
        calc
          _ ≤ (⌈‖u x‖⌉ : ℝ) := Int.le_ceil _
          _ ≤ ⌈‖u x‖⌉.toNat := Int.cast_le.mpr (Int.self_le_toNat _)
          _ ≤ n := Nat.cast_le.mpr hn
    · apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mpr
      have h : Tendsto (fun n ↦ ∫⁻ x, ‖ψ n x - ξ x‖ₑ ^ 2) atTop (nhds 0) := by
        have := sub_self ξ ▸ Tendsto.sub_const hψξ ξ
        apply tendsto_zero_iff_tendsto_zero_lintegral_enorm_sq.mp at this
        refine (tendsto_congr fun n ↦ ?_).mp this
        refine lintegral_congr_ae ?_
        filter_upwards [coeFn_sub (ψ n).val ξ.val]
        simp_all
      refine Tendsto.squeeze tendsto_const_nhds h (zero_le _) fun n ↦ ?_
      refine lintegral_mono_ae ?_
      filter_upwards [coeFn_sub (φ n).val (ψ n).val, coeFn_sub (σ n).val ξ.val,
        coeFn_sub (φ n - ψ n).val (σ n - ξ).val, hφ n, hσ n] with x
      by_cases hx : x ∈ s n
      · simp_all
      · simp_all [enorm, nnnorm, norm_neg_add]

end
end SpaceDHilbertSpace
end QuantumMechanics
