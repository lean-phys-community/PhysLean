/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib

public import Mathlib.Tactic.Bound

@[expose] public section

open Topology

--This is a stupid name for a stupid lemma
theorem Filter.Tendsto_inv_nat_mul_div_real (m : ℕ)
   : Filter.Tendsto (fun (x : ℕ) => ((↑x)⁻¹ * ↑(x / m) : ℝ)) Filter.atTop (𝓝 (1 / ↑m)) := by
  rw [one_div]
  refine ((tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := (↑m)⁻¹) (by positivity)).comp
    tendsto_natCast_atTop_atTop).congr fun x => ?_
  simp [inv_mul_eq_div, Nat.floor_div_natCast]

--Similar to `ENNReal.tendsto_toReal_iff` in `Mathlib/Topology/Instances/ENNReal/Lemmas`, but
-- instead of requiring finiteness for all values, just eventually is needed.
open Filter Topology ENNReal in
theorem ENNReal.tendsto_toReal_iff_of_eventually_ne_top
  {ι} {fi : Filter ι} {f : ι → ℝ≥0∞} (hf : ∀ᶠ i in fi, f i ≠ ∞) {x : ℝ≥0∞}
    (hx : x ≠ ∞) : Tendsto (fun n => (f n).toReal) fi (𝓝 x.toReal) ↔ Tendsto f fi (𝓝 x) := by
  refine ⟨fun h => ?_, fun h => (ENNReal.tendsto_toReal hx).comp h⟩
  rw [← ENNReal.ofReal_toReal hx]
  exact (ENNReal.tendsto_ofReal h).congr' (hf.mono fun n hn => ENNReal.ofReal_toReal hn)
