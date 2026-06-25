/-
Copyright (c) 2026 Shaopeng Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shaopeng Zhu, Joseph Tooby-Smith
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# The origin of `Space` and the Euclidean chart

The choice of origin for `Space d` is its vector-space zero `(0 : Space d)`. This file provides
that `Zero` instance and the standard chart, isolated so they can be shared by the full module
structure (`Space/Module.lean`) and the Euclidean action (`Space/EuclideanGroup/Action.lean`)
without those depending on each other.

* `(0 : Space d)` — the coordinate origin, the point all of whose coordinates vanish.
* `Space.chartEuclidean` — the standard affine isometry `Space d ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)`,
  `p ↦ p -ᵥ 0`, identifying a point with its coordinate vector relative to the origin.
-/

@[expose] public section

namespace Space

instance {d} : Zero (Space d) where
  zero := ⟨fun _ => 0⟩

@[simp]
lemma zero_val {d : ℕ} : (0 : Space d).val = fun _ => 0 := rfl

@[simp]
lemma zero_apply {d : ℕ} (i : Fin d) :
    (0 : Space d) i = 0 := by
  simp [zero_val]

/-- A Euclidean vector, based at the chosen origin, viewed as a point of `Space d`. -/
noncomputable def vectorToSpace {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : Space d :=
  v +ᵥ (0 : Space d)

@[simp]
lemma vectorToSpace_apply {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    vectorToSpace v i = v i := by
  simp [vectorToSpace]

@[simp]
lemma vectorToSpace_vsub_zero {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    vectorToSpace v -ᵥ (0 : Space d) = v := by
  ext i
  simp [vectorToSpace]

/-- The standard chart `Space d ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d)`, `p ↦ p -ᵥ 0`, identifying a point
with its coordinate vector relative to the origin (the vector-space zero `(0 : Space d)`). -/
noncomputable def chartEuclidean (d : ℕ) :
    Space d ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin d) :=
  (AffineIsometryEquiv.vaddConst ℝ (0 : Space d)).symm

@[simp] lemma chartEuclidean_apply (d : ℕ) (p : Space d) :
    chartEuclidean d p = p -ᵥ (0 : Space d) := rfl

end Space
