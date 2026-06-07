/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Tactic.Cases

/-!

# Parametric Integration

In this module we give some lemmas around parametric integration in Lean.
These extend some lemmas in Mathlib, and give them in a more physics-friendly way.

-/

@[expose] public section
noncomputable section
open Module
open scoped InnerProductSpace

variable {M N : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M]
    [NormedAddCommGroup N] [NormedSpace ℝ N]
open MeasureTheory
lemma hasFDerivAt_parametric_intervalIntegral_of_contDiff
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) (x₀ : M) :
    HasFDerivAt (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume))
      (∫ (t : ℝ) in 0..1, fderiv ℝ (F · t) x₀ ∂(volume)) x₀ := by
  let F' : M → ℝ → M →L[ℝ] N := fun x t => fderiv ℝ (F · t) x
  let s (x₀) : Set M := Metric.closedBall x₀ 1
  have hF' : Continuous ↿F' := by fun_prop
  obtain ⟨a, ha⟩ := IsCompact.exists_isMaxOn (s := s x₀ ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))
      (by exact (isCompact_closedBall x₀ 1).prod <|
        ConditionallyCompleteLinearOrder.isCompact_Icc 0 1)
      (f := fun (a : M × ℝ) => ‖F' a.1 a.2‖)
      (by simp [s])
      (by
        apply (Continuous.comp ?_ hF').continuousOn
        change Continuous (@norm _ ContinuousLinearMap.toSeminormedAddCommGroup.toNorm)
        fun_prop)
  change HasFDerivAt (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume))
      (∫ (t : ℝ) in 0..1, F' x₀ t ∂(volume)) x₀
  have hx :=hf.differentiable (by simp)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (s := s x₀)
    (bound := fun t => ‖F' a.1 a.2‖)
  · exact Metric.closedBall_mem_nhds x₀ (by simp)
  · filter_upwards with x
    apply Continuous.aestronglyMeasurable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop
  · refine IntervalIntegrable.aestronglyMeasurable' ?_
    simp only [zero_le_one, sup_of_le_right, inf_of_le_left]
    apply Continuous.intervalIntegrable
    exact Continuous.uncurry_left x₀ (by fun_prop)
  · filter_upwards with t
    intro h x hx
    have hx2 := ha.2
    rw [isMaxOn_iff] at hx2
    apply hx2 (x, t)
    simp at h
    grind
  · apply Continuous.intervalIntegrable
    fun_prop
  · filter_upwards with t
    intro h x hx
    dsimp [F']
    apply DifferentiableAt.hasFDerivAt
    fun_prop

lemma fderiv_apply_parameteric_intervalIntegral
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) (x₀ : M) (v : M) :
    fderiv ℝ (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) x₀ v =
      ∫ (t : ℝ) in 0..1, fderiv ℝ (F · t) x₀ v ∂(volume) := by
  have h := hasFDerivAt_parametric_intervalIntegral_of_contDiff hf x₀
  rw [h.fderiv]
  refine ContinuousLinearMap.intervalIntegral_apply ?_ v
  apply Continuous.intervalIntegrable
  fun_prop

lemma fderiv_parameteric_intervalIntegral
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) (x₀ : M) :
    fderiv ℝ (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) =
      fun x => ∫ (t : ℝ) in 0..1, fderiv ℝ (F · t) x ∂(volume) := by
  have h := hasFDerivAt_parametric_intervalIntegral_of_contDiff hf x₀
  ext1 x
  ext1 v
  rw [fderiv_apply_parameteric_intervalIntegral]
  symm
  refine ContinuousLinearMap.intervalIntegral_apply ?_ v
  apply Continuous.intervalIntegrable
  fun_prop
  fun_prop

lemma contDiff_one_parametric_intervalIntegral_of_contDiff
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) :
    ContDiff ℝ 1 (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) := by
  rw [contDiff_one_iff_hasFDerivAt]
  use fun x₀ => (∫ (t : ℝ) in 0..1, fderiv ℝ (F · t) x₀ ∂(volume))
  apply And.intro
  · fun_prop
  · intro x
    exact hasFDerivAt_parametric_intervalIntegral_of_contDiff hf x

lemma contDiff_succ_parametric_intervalIntegral_of_contDiff {n : ℕ} [FiniteDimensional ℝ M]
    {F : M → ℝ → N} (hf : ContDiff ℝ (n + 1) ↿F) :
    ContDiff ℝ (n + 1) (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) := by
  induction' n with n ih generalizing F
  · apply contDiff_one_parametric_intervalIntegral_of_contDiff
    exact hf
  · rw [contDiff_succ_iff_fderiv]
    constructor
    · apply ContDiff.differentiable (n := 1)
      · apply contDiff_one_parametric_intervalIntegral_of_contDiff
        exact hf.of_le (by simp)
      · simp
    simp only [Nat.cast_add, Nat.cast_one, WithTop.add_eq_top, WithTop.natCast_ne_top,
      WithTop.one_ne_top, or_self, IsEmpty.forall_iff, true_and]
    rw [contDiff_clm_apply_iff]
    intro y
    conv =>
      enter [3, x];
      rw [fderiv_apply_parameteric_intervalIntegral (hf.of_le (by simp))]
    apply ih
    fun_prop

lemma contDiff_parametric_intervalIntegral_of_contDiff {n : ℕ} {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M] [FiniteDimensional ℝ M]
    {F : M → ℝ → N} (hf : ContDiff ℝ n ↿F) :
    ContDiff ℝ n (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) := by
  induction' n with n ih generalizing F
  · simp
    fun_prop
  · exact contDiff_succ_parametric_intervalIntegral_of_contDiff (hf.of_le (by simp))
