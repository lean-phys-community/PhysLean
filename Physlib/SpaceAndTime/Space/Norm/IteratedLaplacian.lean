/-
Copyright (c) 2026 Lazar Milikic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lazar Milikic
-/
module

public import Physlib.SpaceAndTime.Space.Norm.Basic
/-!

# Iterated Laplacians of norm distributions

## i. Overview

This file proves the distributional identity corresponding to the classical odd-dimensional
formula that, in dimension `2 * m + 1`, applying the Laplacian `m + 1` times to the norm
gives a nonzero constant multiple of the Dirac delta at the origin.

## ii. Key results

- `iterated_distLaplacian_norm_zpow_odd_eq_smul_diracDelta` : The `(m + 1)`-fold
  Laplacian of the norm in dimension `2 * m + 1` is a nonzero multiple of the Dirac delta.

## iii. Table of contents

- A. The odd-dimensional iterated Laplacian of the norm

## iv. References

-/

@[expose] public section

open SchwartzMap NNReal Physlib
noncomputable section

namespace Space

open MeasureTheory
open Distribution

/-!

## A. The odd-dimensional iterated Laplacian of the norm

-/

/-- The scalar factor in the odd-dimensional iterated Laplacian of the norm. -/
noncomputable def oddNormIteratedLaplacianCoeff (m : ℕ) : ℝ :=
  (∏ k ∈ Finset.range m,
      ((((1 : ℤ) - 2 * (k : ℤ) : ℤ) : ℝ) *
        ((((1 : ℤ) - 2 * (k : ℤ) - 2 + (2 * m + 1 : ℤ) : ℤ) : ℝ)))) *
    (((1 : ℤ) - 2 * (m : ℤ) : ℝ) * (2 * m + 1 : ℝ) *
      (volume (α := Space (2 * m + 1))).real (Metric.ball 0 1))

private lemma oddNormIteratedLaplacianCoeff_factor_ne_zero {m k : ℕ} (hk : k < m) :
    ((((1 : ℤ) - 2 * (k : ℤ) : ℤ) : ℝ) *
      ((((1 : ℤ) - 2 * (k : ℤ) - 2 + (2 * m + 1 : ℤ) : ℤ) : ℝ))) ≠ 0 := by
  apply mul_ne_zero
  · have h : (1 : ℤ) - 2 * (k : ℤ) ≠ 0 := by omega
    exact_mod_cast h
  · have h : (1 : ℤ) - 2 * (k : ℤ) - 2 + (2 * m + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast h

/-- The scalar factor in the odd-dimensional iterated Laplacian of the norm is nonzero. -/
lemma oddNormIteratedLaplacianCoeff_ne_zero (m : ℕ) :
    oddNormIteratedLaplacianCoeff m ≠ 0 := by
  unfold oddNormIteratedLaplacianCoeff
  apply mul_ne_zero
  · rw [Finset.prod_ne_zero_iff]
    intro k hk
    exact oddNormIteratedLaplacianCoeff_factor_ne_zero (by simpa using hk)
  · repeat' apply mul_ne_zero
    · have h : (1 : ℤ) - 2 * (m : ℤ) ≠ 0 := by omega
      exact_mod_cast h
    · exact_mod_cast (by omega : (2 * m + 1 : ℕ) ≠ 0)
    · exact ne_of_gt <| ENNReal.toReal_pos
        (Metric.measure_ball_pos volume 0 one_pos).ne'
        measure_ball_lt_top.ne

private lemma distLaplacian_norm_zpow_odd_boundary (m : ℕ) :
    Δᵈ (distOfFunction (fun x : Space (2 * m + 1) =>
      ‖x‖ ^ ((1 : ℤ) - 2 * (m : ℤ)))
      (IsDistBounded.pow _ (by omega))) =
      (((1 : ℤ) - 2 * (m : ℤ) : ℝ) * (2 * m + 1 : ℝ) *
        (volume (α := Space (2 * m + 1))).real (Metric.ball 0 1)) •
          diracDelta ℝ 0 := by
  rcases m with _ | m
  · rw [distLaplacian]
    change ∇ᵈ ⬝ (∇ᵈ (distOfFunction (fun x : Space 1 => ‖x‖ ^ (1 : ℤ))
      (IsDistBounded.pow 1 (by omega)))) = _
    rw [distGrad_distOfFunction_norm_zpow 1 (by omega)]
    simp only [Int.cast_one, one_mul]
    convert! distDiv_inv_pow_eq_dim (d := 1) using 1
    · ext x
      ring_nf
  · convert! distLaplacian_fundamentalSolution_norm_zpow_of_three_le
      (d := 2 * m.succ + 1) (by omega) using 4
    · simp [Nat.succ_eq_add_one]
      ring
    · simp [Nat.succ_eq_add_one]

private lemma iterated_distLaplacian_norm_zpow_odd_until_boundary
    (m k : ℕ) (hk : k ≤ m) :
    ((distLaplacian (d := 2 * m + 1))^[k])
      (distOfFunction (fun x : Space (2 * m + 1) => ‖x‖ ^ (1 : ℤ))
        (IsDistBounded.pow 1 (by omega))) =
      (∏ j ∈ Finset.range k,
          ((((1 : ℤ) - 2 * (j : ℤ) : ℤ) : ℝ) *
            ((((1 : ℤ) - 2 * (j : ℤ) - 2 + (2 * m + 1 : ℤ) : ℤ) : ℝ)))) •
        distOfFunction (fun x : Space (2 * m + 1) => ‖x‖ ^ ((1 : ℤ) - 2 * (k : ℤ)))
          (IsDistBounded.pow _ (by omega)) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hk_le : k ≤ m := Nat.le_of_succ_le hk
      rw [Function.iterate_succ_apply']
      rw [ih hk_le]
      rw [map_smul]
      rw [distLaplacian_distOfFunction_norm_zpow
        (d := 2 * m) ((1 : ℤ) - 2 * (k : ℤ)) (by omega) (by omega)]
      rw [smul_smul]
      have hdist :
          distOfFunction
              (fun x : Space (2 * m + 1) => ‖x‖ ^ ((1 : ℤ) - 2 * (k : ℤ) - 2))
              (IsDistBounded.pow _ (by omega)) =
            distOfFunction
              (fun x : Space (2 * m + 1) => ‖x‖ ^ ((1 : ℤ) - 2 * ((k + 1 : ℕ) : ℤ)))
              (IsDistBounded.pow _ (by omega)) := by
        have hexp :
            ((1 : ℤ) - 2 * (k : ℤ) - 2) =
              ((1 : ℤ) - 2 * ((k + 1 : ℕ) : ℤ)) := by
          norm_num
          ring
        ext η
        simp [distOfFunction_apply, hexp]
      rw [hdist]
      rw [Finset.prod_range_succ]
      congr 1

/-- In dimension `2 * m + 1`, the `(m + 1)`-fold distributional Laplacian of the
distribution induced by the norm is a nonzero multiple of the Dirac delta at the origin. -/
lemma iterated_distLaplacian_norm_zpow_odd_eq_smul_diracDelta (m : ℕ) :
    ((distLaplacian (d := 2 * m + 1))^[m + 1])
      (distOfFunction (fun x : Space (2 * m + 1) => ‖x‖ ^ (1 : ℤ))
        (IsDistBounded.pow 1 (by omega))) =
      oddNormIteratedLaplacianCoeff m • diracDelta ℝ 0 := by
  rw [Function.iterate_succ_apply']
  rw [iterated_distLaplacian_norm_zpow_odd_until_boundary m m le_rfl]
  rw [map_smul]
  rw [distLaplacian_norm_zpow_odd_boundary m]
  rw [smul_smul]
  unfold oddNormIteratedLaplacianCoeff
  rfl

end Space
