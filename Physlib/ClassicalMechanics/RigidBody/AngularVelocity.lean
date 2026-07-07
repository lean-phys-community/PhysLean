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

/-- The time derivative of the orientation is `Ṙ = Ω R`, recovering the orientation path from its
angular velocity tensor `Ω = Ṙ Rᵀ` via the orthogonality `Rᵀ R = 1`. -/
lemma angularVelocityTensor_mul_orientation (M : RigidBodyMotion d) (t : Time) :
    M.angularVelocityTensor t * (M.orientation t).1 = ∂ₜ (fun s => (M.orientation s).1) t := by
  rw [angularVelocityTensor_eq, mul_assoc,
    mul_eq_one_comm.mp (M.orientation_mul_transpose t), mul_one]

/-- The velocity of a body point decomposes as `v = Ṙ (y − c) + V`: the rate of change of the
orientation acting on the body-frame position, plus the centre-of-mass velocity. -/
lemma velocity_eq_deriv_orientation (M : RigidBodyMotion d) (y : Space d) (t : Time) (i : Fin d)
    (hR : Differentiable ℝ (fun s => (M.orientation s).1)) (hX : Differentiable ℝ M.comTrajectory) :
    M.velocity y t i
      = (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j) i
        + M.centerOfMassVelocity t i := by
  have hentry : ∀ a b : Fin d, Differentiable ℝ (fun s => (M.orientation s).1 a b) := fun a b =>
    ((Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap).differentiable.comp hR
  have hXcoord : ∀ k : Fin d, Differentiable ℝ (fun s => M.comTrajectory s k) := fun k =>
    (Space.eval_differentiable k).comp hX
  have hd : Differentiable ℝ (fun s => M.displacement s y) := by
    have hcoord : ∀ k : Fin d, Differentiable ℝ (fun s => M.displacement s y k) := by
      intro k
      simp only [displacement_apply]
      exact (Differentiable.fun_sum
        (fun j _ => (hentry k j).mul_const (y j - M.centerOfMass j))).add (hXcoord k)
    exact Space.mk_differentiable.comp (differentiable_pi.mpr hcoord)
  have hmv : (∂ₜ (fun s => (M.orientation s).1) t *ᵥ fun j => y j - M.centerOfMass j) i
      = ∑ j, (∂ₜ (fun s => (M.orientation s).1) t) i j * (y j - M.centerOfMass j) := rfl
  rw [M.velocity_apply y t i hd]
  simp only [displacement_apply]
  rw [Time.deriv_add (fun s => ∑ j, (M.orientation s).1 i j * (y j - M.centerOfMass j))
      (fun s => M.comTrajectory s i)
      ((Differentiable.fun_sum
        fun j _ => (hentry i j).mul_const (y j - M.centerOfMass j)) t) ((hXcoord i) t),
    Time.deriv_fun_sum Finset.univ
      (fun j s => (M.orientation s).1 i j * (y j - M.centerOfMass j))
      (fun j _ => ((hentry i j).mul_const (y j - M.centerOfMass j)) t),
    Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) =>
      Time.deriv_mul_const (fun s => (M.orientation s).1 i j)
        (y j - M.centerOfMass j) ((hentry i j) t))]
  simp only [Time.deriv_matrix_apply (fun s => (M.orientation s).1) t (hR t)]
  rw [hmv, Time.deriv_space hX t i, ← centerOfMassVelocity_eq]

/-- The Landau–Lifshitz velocity decomposition `v = V + ω × r` for a rigid body in three
dimensions: the velocity of a body point is the centre-of-mass velocity plus the cross product of
the angular velocity with the point's position relative to the centre of mass. -/
theorem velocity_eq_angularVelocity (M : RigidBodyMotion 3) (y : Space 3) (t : Time) (i : Fin 3)
    (hR : Differentiable ℝ (fun s => (M.orientation s).1)) (hX : Differentiable ℝ M.comTrajectory) :
    M.velocity y t i = M.centerOfMassVelocity t i
        + (M.angularVelocity t ⨯₃ fun j => M.displacement t y j - M.comTrajectory t j) i := by
  have hRw : (M.orientation t).1 *ᵥ (fun j => y j - M.centerOfMass j)
      = fun j => M.displacement t y j - M.comTrajectory t j := by
    funext k
    show ((M.orientation t).1 *ᵥ fun j => y j - M.centerOfMass j) k
      = M.displacement t y k - M.comTrajectory t k
    rw [eq_sub_iff_add_eq, displacement_apply]
    rfl
  rw [M.velocity_eq_deriv_orientation y t i hR hX, add_comm]
  congr 1
  rw [← M.angularVelocityTensor_mul_orientation t, ← Matrix.mulVec_mulVec, hRw,
    ← M.crossProductMatrix_angularVelocity t (hR t), Matrix.crossProductMatrix_mulVec]

end RigidBodyMotion
