/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.InnerProductSpace.Calculus
/-!

# Gaussians in inner product spaces

-/

@[expose] public section

open ContinuousLinearMap Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (x : E)

/-- Crude bounds on the norms of iterated Fréchet derivatives of `innerSL ℝ`
  in the form required by `norm_iteratedFDeriv_comp_le`. -/
private lemma norm_iteratedFDeriv_innerSL_le_pow {n : ℕ} (hn : 1 ≤ n) :
    ‖iteratedFDeriv ℝ n (fun x : E ↦ innerSL ℝ x x) x‖ ≤ (2 + ‖x‖ ^ 2) ^ n := by
  have h_id₁ : ‖iteratedFDeriv ℝ 1 id x‖ ≤ 1 := by simp [norm_id_le]
  have h_id : ∀ k ≥ 2, ‖iteratedFDeriv ℝ k id x‖ = 0 := by
    intro k hk
    rw [show k = k - 2 + 2 by omega, norm_eq_zero]
    ext
    simp [iteratedFDeriv_succ_apply_right]
  calc
    _ ≤ ∑ k ∈ Finset.range (n + 1),
        n.choose k * ‖iteratedFDeriv ℝ k id x‖ * ‖iteratedFDeriv ℝ (n - k) id x‖ :=
      (innerSL ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
        contDiff_id contDiff_id x (Nat.cast_le.mpr n.le_succ) (norm_innerSL_le ℝ)
    _ = n.choose 0 * ‖iteratedFDeriv ℝ 0 id x‖ * ‖iteratedFDeriv ℝ (n - 0) id x‖ +
        n.choose 1 * ‖iteratedFDeriv ℝ 1 id x‖ * ‖iteratedFDeriv ℝ (n - 1) id x‖ := by
      refine Finset.sum_eq_add_of_mem 0 1 ?_ ?_ zero_ne_one fun k hk hk₀₁ ↦ ?_
      · simp
      · simp [Nat.zero_lt_of_lt hn]
      · simp [h_id, hk₀₁, Nat.two_le_iff]
    _ ≤ ‖x‖ * ‖iteratedFDeriv ℝ n id x‖ + n.choose 1 * ‖iteratedFDeriv ℝ (n - 1) id x‖ := by bound
  rcases (show n = 1 ∨ n = 2 ∨ 2 < n by omega) with rfl | rfl | hn'
  · refine le_trans (b := 2 * ‖x‖) ?_ (by nlinarith)
    simp [← le_sub_iff_add_le, two_mul, mul_le_of_le_one_right, norm_id_le]
  · refine le_trans ?_ (le_trans (le_self_pow₀ one_le_two two_ne_zero) (by bound))
    simp [h_id, norm_id_le]
  · rw [h_id n (by omega), h_id (n - 1) (by omega), mul_zero, mul_zero, add_zero]
    positivity
