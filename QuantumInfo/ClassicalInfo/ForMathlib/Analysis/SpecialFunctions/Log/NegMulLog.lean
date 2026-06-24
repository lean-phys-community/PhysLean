/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Monotonicity of `Real.negMulLog`

## i. Overview

This module provides monotonicity facts for `Real.negMulLog` (the function `x ↦ -x * log x`),
showing it is strictly increasing on `[0, exp (-1)]`, strictly decreasing on `[exp (-1), ∞)`, and
hence bounded above by `exp (-1)`.

## ii. Key results

- `Real.negMulLog_strictMonoOn` : `negMulLog` is strictly monotone on `Set.Icc 0 (exp (-1))`.
- `Real.negMulLog_strictAntiOn` : `negMulLog` is strictly antitone on `Set.Ici (exp (-1))`.
- `Real.negMulLog_le_rexp_neg_one` : for `0 ≤ x`, `negMulLog x ≤ exp (-1)`.

## iii. Table of contents

This can be filled in later.

## iv. References

-/

@[expose] public section

noncomputable section
open NNReal

namespace Real

theorem negMulLog_strictMonoOn : StrictMonoOn Real.negMulLog (Set.Icc 0 (exp (-1))) := by
  apply strictMonoOn_of_deriv_pos
  · exact convex_Icc 0 (exp (-1))
  · exact continuous_negMulLog.continuousOn
  · intro x hx
    rw [interior_Icc, Set.mem_Ioo] at hx
    linarith only [log_exp (-1), log_lt_log hx.left hx.right, deriv_negMulLog hx.left.ne']

theorem negMulLog_strictAntiOn : StrictAntiOn Real.negMulLog (Set.Ici (exp (-1))) := by
  apply strictAntiOn_of_deriv_neg
  · exact convex_Ici (exp (-1))
  · exact continuous_negMulLog.continuousOn
  · intro x hx
    rw [interior_Ici' Set.nonempty_Iio, Set.mem_Ioi] at hx
    have hx' : x ≠ 0 := by grind [exp_nonneg]
    linarith [log_exp (-1), log_lt_log (exp_pos (-1)) hx, deriv_negMulLog hx']

theorem negMulLog_le_rexp_neg_one {x : ℝ} (hx : 0 ≤ x) : negMulLog x ≤ exp (-1) := by
  by_cases hp : x < exp (-1)
  · grw [negMulLog_strictMonoOn.monotoneOn (by grind) (by grind) hp.le]
    simp [negMulLog]
  by_cases hp' : Real.exp (-1) < x
  · grw [negMulLog_strictAntiOn.antitoneOn (by grind) (by grind) hp'.le]
    simp [negMulLog]
  · simp [show x = exp (-1) by order, negMulLog]

end Real
