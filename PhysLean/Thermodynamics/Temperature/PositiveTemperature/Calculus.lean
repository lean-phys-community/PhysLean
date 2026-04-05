/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trong-Nghia Be, Matteo Cipollina, Tan-Phuoc-Hung Le, Joseph Tooby-Smith
-/
module

import Mathlib.Analysis.Calculus.Deriv.Inv
import PhysLean.Thermodynamics.Temperature.Basic
import PhysLean.Mathematics.PosReal
import PhysLean.Thermodynamics.Temperature.PositiveTemperature.Basic

/-!
# Calculus relating temperature and inverse temperature

This file establishes the derivative of `β` with respect to (positive) temperature `T`,
and provides a chain rule for composing functions of `β` with the
temperature-to-beta map, leveraging `PositiveTemperature`.

## Main results

* `PositiveTemperature.deriv_β_wrt_T` : The derivative of the `β` formula is `-1 / (kB * T²)`.
* `PositiveTemperature.chain_rule_T_β` : Chain rule for composing through the `β` formula.
-/

open NNReal

namespace PositiveTemperature
open Constants
open Set


/-- The real-valued function mapping `t ↦ 1 / (kB * t)` has the full derivative `-1 / (kB * T²)`
at the evaluation point `(T : ℝ)`.

Note that `t` is a positive real variable, since it represents positive temperature.
-/
lemma deriv_β_wrt_T (T : PositiveTemperature) : HasDerivAt (fun (t : ℝ) => (1 : ℝ) / (kB * t))
    (-1 / (kB * (T : ℝ)^2)) (T : ℝ) := by
  convert ((hasDerivAt_inv (x := (T : ℝ)) (ne_of_gt T.zero_lt_toReal)).const_mul (kB)⁻¹) using 1
  · ext t
    ring
  · ring

/-- Chain rule for `β(T)`:

- If `F` is a real-valued function of a real variable, and `F` has a derivative `F'`
at the point `β(T)`,  then the composition function `F(β(T))` or `t ↦ F(1 / (kB * t))`
has a derivative `F' * (-1 / (kB * T²))` at the evaluation point `(T : ℝ)`.
-/
lemma chain_rule_T_β {F : ℝ → ℝ} {F' : ℝ} (T : PositiveTemperature)
    (h_F_deriv : HasDerivAt F F' (β T : ℝ)) : HasDerivAt (fun (t : ℝ) => F ((1 : ℝ) / (kB * t)))
    (F' * (-1 / (kB * (T : ℝ)^2))) (T : ℝ) := h_F_deriv.comp (T : ℝ) (deriv_β_wrt_T T)

end PositiveTemperature
