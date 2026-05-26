/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/
module

public import QuantumInfo.Finite.GeometricPhase.BargmannInvariant
public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Pancharatnam's Theorem: Solid Angle on the Bloch Sphere

Infrastructure for Pancharatnam's theorem connecting the Bargmann phase
to the solid angle on the Bloch sphere. This file defines the Bloch
vector parameterization and the solid angle via the Van Vleck formula.

## Important definitions
 * `blochVector`: unit vector on S² parameterized by (α, θ)
 * `solidAngle`: solid angle via Van Vleck formula using `Complex.arg`

## Important results
 * `dot_blochVector`: dot product of Bloch vectors in terms of angles

## References
 * [S. Pancharatnam, *Generalized theory of interference, and its
   applications*, Proc. Indian Acad. Sci. A 44, 247–262 (1956)][pancharatnam1956]
 * [M. V. Berry, *Quantal phase factors accompanying adiabatic changes*,
   Proc. R. Soc. London A 392, 45–57 (1984)][berry1984]
-/

open Complex Matrix

noncomputable section

namespace GeometricPhase

/-! ## Bloch sphere coordinates for qubits -/

/-- The Bloch vector on S² for polar angle `α` and azimuthal angle `θ`. -/
def blochVector (α θ : ℝ) : Fin 3 → ℝ :=
  ![Real.sin α * Real.cos θ, Real.sin α * Real.sin θ, Real.cos α]

/-! ## Solid angle via Van Vleck formula -/

/-- Solid angle of a geodesic triangle on S² with vertices at three
    Bloch vectors, computed via the Van Vleck formula using `Complex.arg`
    for full-quadrant support.

    `Ω = 2 · arg(den + num · i)` where
    `den = 1 + n₁·n₂ + n₂·n₃ + n₃·n₁` and `num = n₁ · (n₂ × n₃)`. -/
def solidAngle (α₁ θ₁ α₂ θ₂ α₃ θ₃ : ℝ) : ℝ :=
  let n₁ := blochVector α₁ θ₁
  let n₂ := blochVector α₂ θ₂
  let n₃ := blochVector α₃ θ₃
  let num := n₁ ⬝ᵥ n₂ ⨯₃ n₃
  let den := 1 + n₁ ⬝ᵥ n₂ + n₂ ⬝ᵥ n₃ + n₃ ⬝ᵥ n₁
  2 * Complex.arg ((den : ℝ) + (num : ℝ) * Complex.I)

/-! ## Dot product of Bloch vectors -/

/-- The dot product of two Bloch vectors expressed in angle differences. -/
lemma dot_blochVector (α₁ θ₁ α₂ θ₂ : ℝ) :
    (blochVector α₁ θ₁) ⬝ᵥ (blochVector α₂ θ₂) =
    Real.sin α₁ * Real.sin α₂ * Real.cos (θ₂ - θ₁) +
    Real.cos α₁ * Real.cos α₂ := by
  simp [blochVector, dotProduct, Fin.sum_univ_three]
  rw [show Real.cos (θ₂ - θ₁) = Real.cos θ₁ * Real.cos θ₂ +
    Real.sin θ₁ * Real.sin θ₂ from by rw [Real.cos_sub]; ring]
  ring

end GeometricPhase
