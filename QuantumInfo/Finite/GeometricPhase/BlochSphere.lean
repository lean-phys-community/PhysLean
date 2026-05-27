/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/
module

public import QuantumInfo.Finite.GeometricPhase.BargmannInvariant
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Bloch Sphere

The Bloch sphere is the unit sphere S² in ℝ³, used to represent
pure states of a two-level quantum system (qubit). Each point on the
sphere corresponds to a qubit state up to global phase.

This file defines the Bloch sphere type, the Bloch vector parameterization
by polar and azimuthal angles, and the solid angle of a geodesic triangle
via the Van Vleck formula.

## Important definitions
 * `BlochSphere`: the unit sphere in ℝ³
 * `blochVec`: vector on S² parameterized by (α, θ)
 * `solidAngle`: solid angle via Van Vleck formula using `Complex.arg`

## Important results
 * `dot_blochVec`: dot product of Bloch vectors in terms of angles

## References
 * [S. Pancharatnam, *Generalized theory of interference, and its
   applications*, Proc. Indian Acad. Sci. A 44, 247–262 (1956)][pancharatnam1956]
 * [M. V. Berry, *Quantal phase factors accompanying adiabatic changes*,
   Proc. R. Soc. London A 392, 45–57 (1984)][berry1984]
-/

open Complex Matrix

noncomputable section

namespace GeometricPhase

/-! ## The Bloch sphere -/

/-- The Bloch sphere: unit sphere in ℝ³. Points are vectors with ‖v‖ = 1. -/
def BlochSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- The Bloch vector for polar angle `α` and azimuthal angle `θ`,
    as a raw vector in ℝ³. -/
def blochVec (α θ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin α * Real.cos θ, Real.sin α * Real.sin θ, Real.cos α]

/-! ## Solid angle via Van Vleck formula -/

/-- Solid angle of a geodesic triangle on S² with vertices given by
    angle pairs, computed via the Van Vleck formula using `Complex.arg`
    for full-quadrant support.

    `Ω = 2 · arg(den + num · i)` where
    `den = 1 + n₁·n₂ + n₂·n₃ + n₃·n₁` and `num = n₁ · (n₂ × n₃)`. -/
def solidAngle (α₁ θ₁ α₂ θ₂ α₃ θ₃ : ℝ) : ℝ :=
  let n₁ := blochVec α₁ θ₁
  let n₂ := blochVec α₂ θ₂
  let n₃ := blochVec α₃ θ₃
  let num := n₁ ⬝ᵥ n₂ ⨯₃ n₃
  let den := 1 + n₁ ⬝ᵥ n₂ + n₂ ⬝ᵥ n₃ + n₃ ⬝ᵥ n₁
  2 * Complex.arg ((den : ℝ) + (num : ℝ) * Complex.I)

/-! ## Dot product of Bloch vectors -/

/-- The dot product of two Bloch vectors expressed in angle differences. -/
lemma dot_blochVec (α₁ θ₁ α₂ θ₂ : ℝ) :
    blochVec α₁ θ₁ ⬝ᵥ blochVec α₂ θ₂ =
    Real.sin α₁ * Real.sin α₂ * Real.cos (θ₂ - θ₁) +
    Real.cos α₁ * Real.cos α₂ := by
  simp [blochVec, dotProduct, Fin.sum_univ_three]
  rw [show Real.cos (θ₂ - θ₁) = Real.cos θ₁ * Real.cos θ₂ +
    Real.sin θ₁ * Real.sin θ₂ from by rw [Real.cos_sub]; ring]
  ring

end GeometricPhase
