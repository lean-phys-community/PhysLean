/-
Copyright (c) 2026 Aadarsh Agarwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aadarsh Agarwal
-/
module

public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Basic
public import Physlib.ClassicalMechanics.Pendulum.SimplePendulum.Geometric.Basic
/-!

# Independence of the lift for the simple pendulum

## i. Overview

The dynamics of the simple gravity pendulum in `SimplePendulum.Basic` is written on a lift of the
motion: the real angle `θ t 0` stands for the configuration `ConfigurationSpace.ofAngle (θ t 0)`,
and two lifts differing by a whole number of turns carry the same configurations. For the lifted
formulation to describe the pendulum faithfully, nothing dynamical may depend on the choice of
the lift. This module proves that the dynamical quantities — the potential and kinetic energies,
the torque, the energy, and the equation of motion together with its solutions — are invariant
under the deck transformations `θ ↦ θ + 2π n` of the angular lift, and closes by making the
starting point precise: the shifted lift describes the same configuration, by the periodicity of
the angular lift of the geometric configuration space. The packaging of this invariance at the
level of configuration-space trajectories comes with the geometric bridge in a later module.

## ii. Key results

- `SimplePendulum.potentialEnergy_add_int_mul_two_pi` and
  `SimplePendulum.torque_add_int_mul_two_pi`: the potential energy and the torque are unchanged
  by shifting the angle by a whole number of turns.
- `SimplePendulum.kineticEnergy_add_const` and `SimplePendulum.energy_add_int_mul_two_pi`: the
  kinetic energy is unchanged by any constant shift of the lift, and the energy by a shift by a
  whole number of turns.
- `SimplePendulum.equationOfMotion_add_int_mul_two_pi` and
  `SimplePendulum.isSolution_add_int_mul_two_pi`: the equation of motion and its solutions are
  invariant under shifting the lift by a whole number of turns.
- `SimplePendulum.ofAngle_add_int_mul_two_pi_coord`: the shifted lift describes the same
  configuration.

## iii. Table of contents

- A. Independence of the lift
  - A.1. Invariance of the potential energy and the torque
  - A.2. Invariance of the energy
  - A.3. Invariance of the equation of motion and its solutions
  - A.4. The shifted lift describes the same configuration

## iv. References

References for the simple gravity pendulum include:
- Landau & Lifshitz, Mechanics, 3rd ed., §5 and §21.
- Arnold, Mathematical Methods of Classical Mechanics, 2nd ed., §4.

-/

@[expose] public section

namespace ClassicalMechanics
open Real InnerProductSpace Time
open scoped ContDiff

namespace SimplePendulum

variable (S : SimplePendulum)

/-!

## A. Independence of the lift

The dynamics of `SimplePendulum.Basic` are written on a lift of the motion: the real angle
`θ t 0` stands for the configuration `ConfigurationSpace.ofAngle (θ t 0)`, and two lifts
differing by a whole number of turns carry the same configurations. This section proves that the
dynamical quantities listed below — the energies, the torque, and the equation of motion and its
solutions — are invariant under the deck transformations `θ ↦ θ + 2π n` of the angular lift;
the packaging of this invariance at the level of configuration-space trajectories comes with
the geometric bridge in a later module. The section closes by making the starting point
precise: the shifted lift does describe the same configuration, by the periodicity of the
angular lift of the geometric configuration space.

-/

/-!

### A.1. Invariance of the potential energy and the torque

The potential energy and the torque depend on the angle only through its cosine and its sine,
and both have period `2π`: neither quantity changes when the angle is shifted by a whole number
of turns.

-/

/-- The potential energy of the simple pendulum is invariant under shifting the angle by a
  whole number of turns. -/
lemma potentialEnergy_add_int_mul_two_pi (x : EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.potentialEnergy (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) =
      S.potentialEnergy x := by
  have h0 : (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) 0 =
      x 0 + n * (2 * Real.pi) := by
    simp
  rw [potentialEnergy_eq, potentialEnergy_eq, h0, Real.cos_add_int_mul_two_pi]

/-- The torque of the simple pendulum is invariant under shifting the angle by a whole number
  of turns. -/
lemma torque_add_int_mul_two_pi (x : EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.torque (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) = S.torque x := by
  have h0 : (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) 0 =
      x 0 + n * (2 * Real.pi) := by
    simp
  rw [torque_eq, torque_eq, h0, Real.sin_add_int_mul_two_pi]

/-!

### A.2. Invariance of the energy

The shift of the lift is constant in time, so it drops out of the velocity, and the kinetic
energy is unchanged by any constant shift at all; the potential energy is unchanged by the
invariance of A.1. Together the two give the invariance of the energy under shifting the lift
by a whole number of turns.

-/

/-- The kinetic energy of the simple pendulum along a lift of the angle is invariant under
  shifting the lift by any constant: the shift drops out of the velocity. -/
lemma kineticEnergy_add_const (θ : Time → EuclideanSpace ℝ (Fin 1))
    (c : EuclideanSpace ℝ (Fin 1)) :
    S.kineticEnergy (fun t => θ t + c) = S.kineticEnergy θ := by
  have hd : ∂ₜ (fun t => θ t + c) = ∂ₜ θ := by
    funext s
    rw [Time.deriv_eq, Time.deriv_eq, fderiv_add_const]
  funext t
  simp only [kineticEnergy_eq, hd]

/-- The energy of the simple pendulum along a lift of the angle is invariant under shifting the
  lift by a whole number of turns: A.1 supplies the invariance of the potential energy, and the
  velocity is unchanged by a constant shift. -/
lemma energy_add_int_mul_two_pi (θ : Time → EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.energy (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) =
      S.energy θ := by
  funext t
  simp only [energy_eq, S.kineticEnergy_add_const θ _, S.potentialEnergy_add_int_mul_two_pi (θ t) n]

/-!

### A.3. Invariance of the equation of motion and its solutions

Both sides of the equation of motion are invariant under the shift: the angular momentum,
because the shift is constant in time, and the torque, by the invariance of A.1. Smoothness is
likewise unaffected by adding a constant, so being a solution is invariant as well.

-/

/-- A lift of the angle shifted by a whole number of turns satisfies the equation of motion of
  the simple pendulum if and only if the lift itself does. -/
lemma equationOfMotion_add_int_mul_two_pi (θ : Time → EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.EquationOfMotion (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) ↔
      S.EquationOfMotion θ := by
  have hd : ∂ₜ (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) = ∂ₜ θ := by
    funext s
    rw [Time.deriv_eq, Time.deriv_eq, fderiv_add_const]
  simp only [EquationOfMotion, hd, torque_add_int_mul_two_pi]

/-- A lift of the angle shifted by a whole number of turns is a solution of the simple pendulum
  if and only if the lift itself is. -/
lemma isSolution_add_int_mul_two_pi (θ : Time → EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    S.IsSolution (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) ↔
      S.IsSolution θ := by
  have hcd : ContDiff ℝ ∞ (fun t => θ t + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1) ↔
      ContDiff ℝ ∞ θ := by
    constructor
    · intro h
      have h2 := h.sub (contDiff_const (c := (n * (2 * Real.pi)) • EuclideanSpace.single 0 1))
      simpa using h2
    · exact fun h => h.add contDiff_const
  exact and_congr hcd (S.equationOfMotion_add_int_mul_two_pi θ n)

/-!

### A.4. The shifted lift describes the same configuration

Finally the statement giving the previous invariances their meaning: the lift and its shift by
a whole number of turns project to the same point of the configuration space, by the
periodicity of the angular lift `ConfigurationSpace.ofAngle` with period `2π`.

-/

/-- A lift of the angle and its shift by a whole number of turns describe the same
  configuration of the simple pendulum. -/
lemma ofAngle_add_int_mul_two_pi_coord (x : EuclideanSpace ℝ (Fin 1)) (n : ℤ) :
    ConfigurationSpace.ofAngle
        ((x + (n * (2 * Real.pi)) • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0) =
      ConfigurationSpace.ofAngle (x 0) := by
  have h0 : (x + (n * (2 * Real.pi)) • EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)) 0 =
      x 0 + n * (2 * Real.pi) := by
    simp
  rw [h0]
  exact ConfigurationSpace.ofAngle_periodic.int_mul n (x 0)

end SimplePendulum

end ClassicalMechanics

end
