/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

@[expose] public section

noncomputable section
open NNReal

namespace Real

theorem negMulLog_strictMonoOn : StrictMonoOn Real.negMulLog (Set.Icc 0 (exp (-1))) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) continuous_negMulLog.continuousOn
    fun x hx ↦ ?_
  rw [interior_Icc, Set.mem_Ioo] at hx
  linarith only [log_exp (-1), log_lt_log hx.left hx.right, deriv_negMulLog hx.left.ne']

theorem negMulLog_strictAntiOn : StrictAntiOn Real.negMulLog (Set.Ici (exp (-1))) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici _) continuous_negMulLog.continuousOn
    fun x hx ↦ ?_
  rw [interior_Ici' Set.nonempty_Iio, Set.mem_Ioi] at hx
  linarith [log_exp (-1), log_lt_log (exp_pos (-1)) hx,
    deriv_negMulLog ((exp_pos (-1)).trans hx).ne']

theorem negMulLog_le_rexp_neg_one {x : ℝ} (hx : 0 ≤ x) : negMulLog x ≤ exp (-1) := by
  rcases le_total x (exp (-1)) with h | h
  · simpa [negMulLog] using negMulLog_strictMonoOn.monotoneOn (by grind) (by grind) h
  · simpa [negMulLog] using negMulLog_strictAntiOn.antitoneOn (by grind) (by grind) h

end Real
