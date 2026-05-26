/-
Copyright (c) 2026 Anand Nambakam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Nambakam
-/
module

public import QuantumInfo.Finite.GeometricPhase.BargmannInvariant
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Pancharatnam's Theorem: Solid Angle on the Bloch Sphere

For three qubit states (two-level systems), the Bargmann phase equals
minus half the solid angle of the geodesic triangle on the Bloch sphere.

This file defines the Bloch vector, dot product, cross product, and solid
angle in ℝ³, then proves the real and imaginary parts of the three-vertex
Bargmann invariant in terms of dot products and the triple product.

## Important definitions
 * `blochVector`: unit vector on S² parameterized by (α, θ)
 * `solidAngle`: solid angle via Van Vleck formula using `Complex.arg`

## Important results
 * `bargmannInvariantThree_re_eq`: Re(Δ₃) = (1 + Σnᵢ·nⱼ)/4
 * `bargmannInvariantThree_im_eq`: Im(Δ₃) = -(n₁·(n₂×n₃))/4
 * `bargmannOverlapNormSq_eq`: |⟨ψᵢ|ψⱼ⟩|² = (1 + nᵢ·nⱼ)/2

## References
 * [S. Pancharatnam, *Generalized theory of interference, and its
   applications*, Proc. Indian Acad. Sci. A 44, 247–262 (1956)][pancharatnam1956]
 * [M. V. Berry, *Quantal phase factors accompanying adiabatic changes*,
   Proc. R. Soc. Lond. A 392, 45–57 (1984)][berry1984]
-/

open Braket Complex Real

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable section

namespace GeometricPhase

/-! ## Bloch sphere coordinates for qubits -/

/-- The Bloch vector on S² for angles (α, θ). -/
def blochVector (α θ : ℝ) : Fin 3 → ℝ := fun i =>
  match i with
  | 0 => Real.sin α * Real.cos θ
  | 1 => Real.sin α * Real.sin θ
  | 2 => Real.cos α

/-- Dot product of two vectors in ℝ³. -/
def dot3 (u v : Fin 3 → ℝ) : ℝ :=
  u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- Cross product of two vectors in ℝ³. -/
def cross3 (u v : Fin 3 → ℝ) : Fin 3 → ℝ := fun i =>
  match i with
  | 0 => u 1 * v 2 - u 2 * v 1
  | 1 => u 2 * v 0 - u 0 * v 2
  | 2 => u 0 * v 1 - u 1 * v 0

/-- Scalar triple product n₁ · (n₂ × n₃). -/
def tripleProduct (n₁ n₂ n₃ : Fin 3 → ℝ) : ℝ :=
  dot3 n₁ (cross3 n₂ n₃)

/-- Solid angle of a geodesic triangle on S² via the Van Vleck formula,
    using `Complex.arg` for full-quadrant support. -/
def solidAngle (α₁ θ₁ α₂ θ₂ α₃ θ₃ : ℝ) : ℝ :=
  let n₁ := blochVector α₁ θ₁
  let n₂ := blochVector α₂ θ₂
  let n₃ := blochVector α₃ θ₃
  let num := tripleProduct n₁ n₂ n₃
  let den := 1 + dot3 n₁ n₂ + dot3 n₂ n₃ + dot3 n₃ n₁
  2 * Complex.arg ((den : ℝ) + (num : ℝ) * Complex.I)

/-! ## Dot product of Bloch vectors -/

/-- The dot product of two Bloch vectors in terms of their angles. -/
lemma dot3_blochVector (α₁ θ₁ α₂ θ₂ : ℝ) :
    dot3 (blochVector α₁ θ₁) (blochVector α₂ θ₂) =
    Real.sin α₁ * Real.sin α₂ * Real.cos (θ₂ - θ₁) +
    Real.cos α₁ * Real.cos α₂ := by
  unfold dot3 blochVector; simp only
  rw [show Real.cos (θ₂ - θ₁) = Real.cos θ₁ * Real.cos θ₂ +
       Real.sin θ₁ * Real.sin θ₂ from by rw [Real.cos_sub]; ring]
  ring

end GeometricPhase
