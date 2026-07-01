/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.ClassicalMechanics.RigidBody.Motion
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

## References
- Landau and Lifshitz, Mechanics, Section 31.
-/

@[expose] public section

open Time Manifold Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace RigidBodyMotion

variable {d : ℕ}

/-- The orientation of the body as a matrix-valued function of time: the underlying matrix of
`orientation`. -/
noncomputable def orientationMatrix (M : RigidBodyMotion d) : Time → Matrix (Fin d) (Fin d) ℝ :=
  fun s => (M.orientation s).val

lemma orientationMatrix_apply (M : RigidBodyMotion d) (t : Time) :
    M.orientationMatrix t = (M.orientation t).val := rfl

/-- The orientation matrix is special orthogonal, so `R Rᵀ = 1`. -/
lemma orientationMatrix_mul_transpose (M : RigidBodyMotion d) (t : Time) :
    M.orientationMatrix t * (M.orientationMatrix t)ᵀ = 1 :=
  (mem_orthogonalGroup_iff (Fin d) ℝ).mp
    (mem_specialOrthogonalGroup_iff.mp (M.orientation t).2).1

/-- The angular velocity tensor `Ω(t) = Ṙ(t) R(t)ᵀ` of a rigid body in motion, where
`R(t) = orientation t`. It is the antisymmetric tensor `Ω` in the Landau–Lifshitz decomposition
`v = V + Ω × r` of the velocity of a point of the body. -/
noncomputable def angularVelocityTensor (M : RigidBodyMotion d) (t : Time) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∂ₜ M.orientationMatrix t * (M.orientationMatrix t)ᵀ

lemma angularVelocityTensor_eq (M : RigidBodyMotion d) (t : Time) :
    M.angularVelocityTensor t = ∂ₜ M.orientationMatrix t * (M.orientationMatrix t)ᵀ := rfl

/-- The angular velocity tensor is skew-symmetric, `Ωᵀ = -Ω`: it lies in the Lie algebra `𝔰𝔬(d)`.
This is the litmus check that `Ω = Ṙ Rᵀ` is a genuine angular-velocity tensor, and follows by
differentiating the orthogonality identity `R Rᵀ = 1`. -/
lemma angularVelocityTensor_transpose (M : RigidBodyMotion d) (t : Time)
    (hR : DifferentiableAt ℝ M.orientationMatrix t) :
    (M.angularVelocityTensor t)ᵀ = - M.angularVelocityTensor t := by
  have hconst : (fun s => M.orientationMatrix s * (M.orientationMatrix s)ᵀ)
      = fun _ => (1 : Matrix (Fin d) (Fin d) ℝ) := by
    funext s
    exact M.orientationMatrix_mul_transpose s
  have hderiv0 : ∂ₜ (fun s => M.orientationMatrix s * (M.orientationMatrix s)ᵀ) t = 0 := by
    rw [hconst]
    exact Time.deriv_const 1
  have hRt : DifferentiableAt ℝ (fun s => (M.orientationMatrix s)ᵀ) t :=
    Matrix.transposeCLM.differentiableAt.comp t hR
  have hprod :=
    Time.deriv_matrix_mul M.orientationMatrix (fun s => (M.orientationMatrix s)ᵀ) t hR hRt
  rw [Time.deriv_matrix_transpose M.orientationMatrix t hR, hderiv0] at hprod
  rw [angularVelocityTensor, transpose_mul, transpose_transpose]
  exact eq_neg_of_add_eq_zero_left hprod.symm

/-- A rigid body whose orientation is constant in time has zero angular velocity. -/
lemma angularVelocityTensor_of_orientation_const (M : RigidBodyMotion d)
    (R : Matrix.specialOrthogonalGroup (Fin d) ℝ) (h : M.orientation = fun _ => R) :
    M.angularVelocityTensor = 0 := by
  funext t
  have hconst : M.orientationMatrix = fun _ => R.val := by
    funext s
    rw [orientationMatrix_apply, h]
  rw [angularVelocityTensor_eq, hconst, Time.deriv_eq]
  simp

end RigidBodyMotion
