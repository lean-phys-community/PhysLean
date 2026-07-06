/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.ClassicalMechanics.RigidBody.Motion
public import Physlib.Mathematics.CrossProductMatrix
public import Physlib.SpaceAndTime.Time.MatrixDerivatives
/-!

# The angular velocity of a rigid body

For a rigid body in motion the orientation `R(t) = orientation t` is a time-dependent rotation. Its
instantaneous rate of change is encoded by the *angular velocity tensor*
`Ω(t) = Ṙ(t) R(t)ᵀ`, the antisymmetric tensor `Ω` appearing in the Landau–Lifshitz decomposition
`v = V + Ω × r` of the velocity of a point of the body.

A basic consistency check is that `Ω` is skew-symmetric, `Ωᵀ = -Ω` (equivalently `Ω ∈ 𝔰𝔬(d)`); this
follows by differentiating the orthogonality identity `R Rᵀ = 1`. The general product and transpose
rules for time derivatives of matrices used for this live in
`Physlib.SpaceAndTime.Time.MatrixDerivatives`.

In three dimensions the skew-symmetric tensor `Ω` is dual to the *angular velocity vector*
`ω(t) = Ωᵛ` via the hat map (`Physlib.Mathematics.CrossProductMatrix`), with `[ω]ₓ = Ω`; `ω` is the
angular velocity proper, appearing in the decomposition `v = V + ω × r` as an honest cross product.

## References
- Landau and Lifshitz, Mechanics, Section 31.
-/

@[expose] public section

open Time Manifold Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace RigidBodyMotion

variable {d : ℕ}

/-- The angular velocity tensor `Ω(t) = Ṙ(t) R(t)ᵀ` of a rigid body in motion, where
`R(t) = orientation t`. It is the antisymmetric tensor `Ω` in the Landau–Lifshitz decomposition
`v = V + Ω × r` of the velocity of a point of the body. -/
noncomputable def angularVelocityTensor (M : RigidBodyMotion d) (t : Time) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∂ₜ (fun s => (M.orientation s).1) t * ((M.orientation t).1)ᵀ

lemma angularVelocityTensor_eq (M : RigidBodyMotion d) (t : Time) :
    M.angularVelocityTensor t = ∂ₜ (fun s => (M.orientation s).1) t * ((M.orientation t).1)ᵀ :=
  rfl

/-- The angular velocity tensor is skew-symmetric, `Ωᵀ = -Ω`: it lies in the Lie algebra `𝔰𝔬(d)`.
This is the litmus check that `Ω = Ṙ Rᵀ` is a genuine angular-velocity tensor, and follows by
differentiating the orthogonality identity `R Rᵀ = 1`. -/
lemma angularVelocityTensor_transpose (M : RigidBodyMotion d) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    (M.angularVelocityTensor t)ᵀ = - M.angularVelocityTensor t := by
  have hconst : (fun s => (M.orientation s).1 * ((M.orientation s).1)ᵀ)
      = fun _ => (1 : Matrix (Fin d) (Fin d) ℝ) := by
    funext s
    exact M.orientation_mul_transpose s
  have hderiv0 : ∂ₜ (fun s => (M.orientation s).1 * ((M.orientation s).1)ᵀ) t = 0 := by
    rw [hconst]
    exact Time.deriv_const 1
  have hprod := Time.deriv_matrix_mul (fun s => (M.orientation s).1)
    (fun s => ((M.orientation s).1)ᵀ) t hR hR.matrix_transpose
  rw [Time.deriv_matrix_transpose (fun s => (M.orientation s).1) t hR, hderiv0] at hprod
  rw [angularVelocityTensor, transpose_mul, transpose_transpose]
  exact eq_neg_of_add_eq_zero_left hprod.symm

/-- A rigid body whose orientation is constant in time has zero angular velocity. -/
lemma angularVelocityTensor_of_orientation_const (M : RigidBodyMotion d)
    (R : Matrix.specialOrthogonalGroup (Fin d) ℝ) (h : M.orientation = fun _ => R) :
    M.angularVelocityTensor = 0 := by
  funext t
  have hconst : (fun s => (M.orientation s).1) = fun _ => R.1 := by
    funext s
    rw [h]
  rw [angularVelocityTensor_eq, hconst, Time.deriv_eq]
  simp

/-- The angular velocity *vector* `ω(t)` of a rigid body moving in three-dimensional space: the
vector dual to the angular velocity tensor `Ω(t)` under the hat map, `ω = Ωᵛ`. It is the angular
velocity `ω` in the Landau–Lifshitz decomposition `v = V + ω × r` of the velocity of a point of the
body, where `ω × r` is the cross product with `ω`. -/
noncomputable def angularVelocity (M : RigidBodyMotion 3) (t : Time) : Fin 3 → ℝ :=
  crossProductVee (M.angularVelocityTensor t)

lemma angularVelocity_eq (M : RigidBodyMotion 3) (t : Time) :
    M.angularVelocity t = crossProductVee (M.angularVelocityTensor t) := rfl

/-- The hat map recovers the angular velocity tensor from the angular velocity vector, `[ω]ₓ = Ω`.
This is the defining relationship between the vector and tensor forms of the angular velocity in
three dimensions; it holds because `Ω` is skew-symmetric. -/
lemma crossProductMatrix_angularVelocity (M : RigidBodyMotion 3) (t : Time)
    (hR : DifferentiableAt ℝ (fun s => (M.orientation s).1) t) :
    crossProductMatrix (M.angularVelocity t) = M.angularVelocityTensor t := by
  rw [angularVelocity_eq,
    crossProductMatrix_crossProductVee (M.angularVelocityTensor_transpose t hR)]

/-- A rigid body whose orientation is constant in time has zero angular velocity vector. -/
lemma angularVelocity_of_orientation_const (M : RigidBodyMotion 3)
    (R : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (h : M.orientation = fun _ => R) :
    M.angularVelocity = 0 := by
  funext t i
  rw [angularVelocity_eq, congrFun (M.angularVelocityTensor_of_orientation_const R h) t]
  fin_cases i <;> simp [crossProductVee]

end RigidBodyMotion
