/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic
public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Geometric.Trajectory
/-!

# The simple pendulum in physical space

## i. Overview

The trajectory module places the bob in the plane along a lifted trajectory; this module fixes a
simple pendulum `S` and identifies the dynamics of `SimplePendulum.Basic`, written on the
Euclidean lift of the angle, with the dynamics of the bob moving in physical space. Along a lift
`θ` the bob is at `S.spaceTrajectory θ`, at the fixed distance `ℓ` from the pivot; its velocity
is obtained by differentiating the position componentwise, and the square of its speed is
`ℓ² θ̇²`. The chart kinetic energy `½ I θ̇²` is then exactly the kinetic energy `½ m ‖v‖²` of
the bob, the chart potential energy `m g ℓ (1 - cos θ)` is exactly the gravitational potential
`m g h` of the bob with the height `h` measured from the bottom of the swing, and the chart
Lagrangian is the constrained Lagrangian `T - V` of a point mass moving on the circle of radius
`ℓ` about the pivot. Velocities in this module are physical-space time derivatives; the
geometric velocity as a tangent vector to the configuration circle is deferred, as discussed in
the trajectory module.

## ii. Key results

- `SimplePendulum.spaceTrajectory` : the bob's position in the plane along a lifted trajectory,
  with the rod-length constraint `SimplePendulum.norm_spaceTrajectory`.
- `SimplePendulum.deriv_spaceTrajectory` : the bob's velocity along a lifted trajectory, with
  the square of its speed `SimplePendulum.norm_sq_deriv_spaceTrajectory`.
- `SimplePendulum.kineticEnergy_eq_space`, `SimplePendulum.potentialEnergy_eq_height` and
  `SimplePendulum.lagrangian_eq_space` : the chart kinetic energy, potential energy and
  Lagrangian are those of the bob in physical space; `SimplePendulum.energy_eq_space` is the
  corresponding statement for the total energy.

## iii. Table of contents

- A. The bob's position along a lifted trajectory
- B. The bob's velocity and speed
- C. The energies and the Lagrangian in physical space

## iv. References

- `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic` (the lifted dynamics: the
  energies and the Lagrangian on the Euclidean lift of the angle).
- `Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Geometric.Trajectory` (trajectories on
  the configuration circle and the position of the bob along them).
- Landau & Lifshitz, Mechanics, 3rd ed., §5, Problems 1–3 (pendulum configurations).

-/

@[expose] public section

open Real InnerProductSpace Time

namespace ClassicalMechanics.SimplePendulum

variable (S : SimplePendulum)

/-!

## A. The bob's position along a lifted trajectory

Fixing a pendulum `S`, the position of the bob in the plane along the trajectory described by a
lift `θ` of the angle is obtained by composing the lifted trajectory with the map to physical
space for a rod of length `S.ℓ`. Along it the bob is at `(ℓ sin θ, -ℓ cos θ)`, and since the
length of the rod is positive the bob stays at distance `ℓ` from the pivot at all times.

-/

/-- The position of the bob in the plane along the trajectory described by a lift `θ` of the
  angle, for the pendulum `S`. -/
noncomputable def spaceTrajectory (θ : Time → EuclideanSpace ℝ (Fin 1)) : Time → Space 2 :=
  Trajectory.toSpace S.ℓ (Trajectory.ofLift θ)

/-- Along the trajectory described by a lift `θ` of the angle the bob of the pendulum `S` is at
  `(ℓ sin (θ t 0), -ℓ cos (θ t 0))`. -/
lemma spaceTrajectory_eq (θ : Time → EuclideanSpace ℝ (Fin 1)) :
    S.spaceTrajectory θ = fun t => ⟨![S.ℓ * Real.sin (θ t 0), -S.ℓ * Real.cos (θ t 0)]⟩ :=
  funext fun t => Trajectory.toSpace_ofLift S.ℓ θ t

/-- The horizontal position of the bob along a lifted trajectory is `ℓ sin (θ t 0)`. -/
lemma spaceTrajectory_apply_zero (θ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    S.spaceTrajectory θ t 0 = S.ℓ * Real.sin (θ t 0) := by
  simp [S.spaceTrajectory_eq θ]

/-- The vertical position of the bob along a lifted trajectory is `-ℓ cos (θ t 0)`, the pivot
  being the origin and the second axis pointing upwards. -/
lemma spaceTrajectory_apply_one (θ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    S.spaceTrajectory θ t 1 = -S.ℓ * Real.cos (θ t 0) := by
  simp [S.spaceTrajectory_eq θ]

/-- The rod-length constraint along a lifted trajectory: the bob of the pendulum `S` stays at
  distance `ℓ` from the pivot, the length of the rod being positive. -/
lemma norm_spaceTrajectory (θ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    ‖S.spaceTrajectory θ t‖ = S.ℓ :=
  (Trajectory.norm_toSpace S.ℓ (Trajectory.ofLift θ) t).trans (abs_of_pos S.ℓ_pos)

/-!

## B. The bob's velocity and speed

Differentiating the position of the bob componentwise gives its velocity in the plane: along a
differentiable lift the bob's position is differentiable in time, and its velocity is
`(ℓ cos θ, ℓ sin θ)` times the angular velocity — the vector tangent to the circle of radius
`ℓ`, of length `ℓ |θ̇|`. The square of the speed is therefore `ℓ² θ̇²`, which is the identity
behind the identification of the kinetic energies in the next section. The two chain-rule
computations for the sine and the cosine of the angle read from a lift are recorded as
stand-alone lemmas.

-/

/-- The time derivative of the sine of the angle read from a lift is the cosine of the angle
  times the angular velocity. -/
lemma deriv_sin_coord (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : Differentiable ℝ θ)
    (t : Time) : ∂ₜ (fun s => Real.sin (θ s 0)) t = Real.cos (θ t 0) * (∂ₜ θ t) 0 := by
  rw [Time.deriv_eq, fderiv_sin, smul_apply, smul_eq_mul, ← Time.deriv_eq, Time.deriv_euclid hθ t]
  fun_prop

/-- The time derivative of the cosine of the angle read from a lift is minus the sine of the
  angle times the angular velocity. -/
lemma deriv_cos_coord (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : Differentiable ℝ θ)
    (t : Time) : ∂ₜ (fun s => Real.cos (θ s 0)) t = -Real.sin (θ t 0) * (∂ₜ θ t) 0 := by
  rw [Time.deriv_eq, fderiv_cos, smul_apply, smul_eq_mul, ← Time.deriv_eq, Time.deriv_euclid hθ t]
  fun_prop

/-- Along a differentiable lift of the angle the position of the bob is differentiable in
  time. -/
@[fun_prop]
lemma differentiable_spaceTrajectory (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : Differentiable ℝ θ) : Differentiable ℝ (S.spaceTrajectory θ) := by
  rw [S.spaceTrajectory_eq θ]
  apply Space.mk_differentiable.comp
  rw [differentiable_pi]
  intro i
  fin_cases i <;> (simp; fun_prop)

/-- The velocity of the bob along a differentiable lift `θ` of the angle is
  `(ℓ cos (θ t 0), ℓ sin (θ t 0))` times the angular velocity: the vector tangent to the circle
  of radius `ℓ` at the position of the bob. -/
lemma deriv_spaceTrajectory (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : Differentiable ℝ θ)
    (t : Time) :
    ∂ₜᵥ (S.spaceTrajectory θ) t =
      !₂[S.ℓ * Real.cos (θ t 0) * (∂ₜ θ t) 0, S.ℓ * Real.sin (θ t 0) * (∂ₜ θ t) 0] := by
  refine PiLp.ext fun i ↦ ?_
  fin_cases i <;> apply (Time.derivVec_space (by fun_prop) t _).trans
  · simp only [S.spaceTrajectory_apply_zero, Fin.zero_eta, Matrix.cons_val_zero]
    rw [Time.deriv_eq, fderiv_const_mul, smul_apply, smul_eq_mul, ← Time.deriv, deriv_sin_coord,
      mul_assoc]
    all_goals fun_prop
  · simp only [Fin.mk_one, S.spaceTrajectory_apply_one, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [Time.deriv_eq, fderiv_const_mul, smul_apply, smul_eq_mul, ← Time.deriv, deriv_cos_coord]
    ring
    all_goals fun_prop

/-- The square of the speed of the bob along a differentiable lift of the angle is `ℓ² θ̇²`. -/
lemma norm_sq_deriv_spaceTrajectory (θ : Time → EuclideanSpace ℝ (Fin 1))
    (hθ : Differentiable ℝ θ) (t : Time) :
    ‖∂ₜᵥ (S.spaceTrajectory θ) t‖ ^ 2 = S.ℓ ^ 2 * ((∂ₜ θ t) 0) ^ 2 := by
  rw [S.deriv_spaceTrajectory θ hθ t, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  show (S.ℓ * Real.cos (θ t 0) * (∂ₜ θ t) 0) ^ 2
      + (S.ℓ * Real.sin (θ t 0) * (∂ₜ θ t) 0) ^ 2 = _
  linear_combination S.ℓ ^ 2 * ((∂ₜ θ t) 0) ^ 2 * Real.sin_sq_add_cos_sq (θ t 0)

/-!

## C. The energies and the Lagrangian in physical space

The identities of the previous section identify the energies of `SimplePendulum.Basic`, written
on the lift of the angle, with the energies of the bob in the plane. The chart kinetic energy
`½ I θ̇²` is the kinetic energy `½ m ‖v‖²` of the bob, since `I = m ℓ²` and the square of the
speed is `ℓ² θ̇²`; the chart potential energy `m g ℓ (1 - cos θ)` is the gravitational
potential `m g h` of the bob, the height `h` above the bottom of the swing being the vertical
position of the bob plus `ℓ`. Consequently the chart Lagrangian is the constrained Lagrangian
`T - V` of a point mass moving on the circle of radius `ℓ`, and the chart energy is its total
energy `T + V`.

-/

/-- The chart kinetic energy of the pendulum along a differentiable lift of the angle is the
  kinetic energy of the bob in physical space. -/
lemma kineticEnergy_eq_space (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : Differentiable ℝ θ)
    (t : Time) :
    S.kineticEnergy θ t = (1 / (2 : ℝ)) * S.m * ‖∂ₜᵥ (S.spaceTrajectory θ) t‖ ^ 2 := by
  rw [S.norm_sq_deriv_spaceTrajectory θ hθ t]
  show (1 / (2 : ℝ)) * (S.m * S.ℓ ^ 2) * ⟪∂ₜ θ t, ∂ₜ θ t⟫_ℝ = _
  rw [PiLp.inner_apply, Fin.sum_univ_one, RCLike.inner_apply, conj_trivial]
  ring

/-- The chart potential energy of the pendulum is the gravitational potential of the bob in
  physical space, normalized to vanish at the bottom of the swing: the height of the bob above
  the bottom is its vertical position plus `ℓ`. -/
lemma potentialEnergy_eq_height (θ : Time → EuclideanSpace ℝ (Fin 1)) (t : Time) :
    S.potentialEnergy (θ t) = S.m * S.g * (S.spaceTrajectory θ t 1 + S.ℓ) := by
  rw [S.potentialEnergy_eq (θ t), S.spaceTrajectory_apply_one θ t]
  ring

/-- The chart Lagrangian of the pendulum along a differentiable lift of the angle is the
  constrained Lagrangian of the bob in physical space: the kinetic energy of the point mass
  minus its gravitational potential. -/
lemma lagrangian_eq_space (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : Differentiable ℝ θ)
    (t : Time) :
    S.lagrangian t (θ t) (∂ₜ θ t) =
      (1 / (2 : ℝ)) * S.m * ‖∂ₜᵥ (S.spaceTrajectory θ) t‖ ^ 2
        - S.m * S.g * (S.spaceTrajectory θ t 1 + S.ℓ) := by
  rw [S.lagrangian_eq_kineticEnergy_sub_potentialEnergy t θ, S.kineticEnergy_eq_space θ hθ t,
    S.potentialEnergy_eq_height θ t]

/-- The chart energy of the pendulum along a differentiable lift of the angle is the total
  energy of the bob in physical space: the kinetic energy of the point mass plus its
  gravitational potential. -/
lemma energy_eq_space (θ : Time → EuclideanSpace ℝ (Fin 1)) (hθ : Differentiable ℝ θ)
    (t : Time) :
    S.energy θ t =
      (1 / (2 : ℝ)) * S.m * ‖∂ₜᵥ (S.spaceTrajectory θ) t‖ ^ 2
        + S.m * S.g * (S.spaceTrajectory θ t 1 + S.ℓ) := by
  rw [← S.kineticEnergy_eq_space θ hθ t, ← S.potentialEnergy_eq_height θ t]
  rfl

end ClassicalMechanics.SimplePendulum

end
