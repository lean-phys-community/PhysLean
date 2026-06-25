/-
Copyright (c) 2026 Pranav Magdum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pranav Magdum
-/
module

public import Physlib.SpaceAndTime.Time.Derivatives
public import Mathlib.Analysis.Calculus.MeanValue
/-!
# The Free Particle

## i. Overview

The free particle is one of the simplest systems in classical mechanics: a particle of mass `m`
moving with no external forces acting on it. Physically, this means the particle just keeps moving
at constant velocity.

In this file, we work in a simple 1D coordinate system where position and velocity are functions
of time with values in `ℝ`. This keeps things easy to reason about. A more complete treatment would
use manifolds and tangent bundles.

## ii. Key results

The main things we show about the free particle are:

In the `Basic` module:
- `FreeParticle` stores the mass of the particle.
- `NewtonsSecondLaw` encodes the equation `m * q'' = 0`.
- `accel_zero` shows that this implies `q'' = 0`.
- `velocity_const_of_zero_acc` shows that zero acceleration means velocity is constant.
- `linearMomentum_conserved` shows that linear momentum stays constant over time.
- `kineticEnergy_conserved` shows that kinetic energy stays constant over time.

So overall, we formalise the usual chain:
Newton’s law → zero acceleration → constant velocity → constant momentum and energy.

## iii. Table of contents

- A. The setup
- B. Equation of motion
  - B.1. Newton's second law
  - B.2. Zero acceleration
- C. What zero acceleration implies
  - C.1. Constant velocity
- D. Momentum
  - D.1. Linear momentum
  - D.2. Momentum conservation
- E. Energy
  - E.1. Kinetic energy
  - E.2. Energy conservation

## iv. References

-/

@[expose] public section

namespace ClassicalMechanics

open Time

/--
A classical free particle with positive mass.

A free particle is a mechanical system evolving in the absence of
external forces. The dynamics are therefore entirely determined by
Newton's second law with zero force.

The only parameter of the system is the particle mass. The assumption
that the mass is strictly positive is physically natural and is used
throughout the development when simplifying the equation of motion.
-/
structure FreeParticle where
  /--
  The mass of the free particle.

  This parameter determines the inertial response of the particle in
  Newton's second law.
  -/
  mass : ℝ
  mass_pos : 0 < mass

namespace FreeParticle

/--
A trajectory is a time-dependent position function describing the motion
of the particle in one spatial dimension. Defining the trajectory.
-/
abbrev Trajectory := Time → ℝ

set_option linter.unusedVariables false in
/--
The velocity of a trajectory at a given time.
This is defined as the time derivative of the position function.
-/
@[nolint unusedArguments]
noncomputable
def velocity (s : FreeParticle) (q : Trajectory) (t : Time) : ℝ :=
  deriv q t

/--
The linear momentum of the free particle along a trajectory.

This is given by the classical one-dimensional expression `p = m v`,
where `m` is the particle mass and `v` is the velocity.
-/
noncomputable
def linearMomentum (s : FreeParticle) (q : Trajectory) (t : Time) : ℝ :=
  s.mass * s.velocity q t

/--
The kinetic energy of the free particle along a trajectory.

This is given by the classical expression `E = (1 / 2) m v²`,
where `m` is the particle mass and `v` is the velocity.
-/
noncomputable
def kineticEnergy (s : FreeParticle) (q : Trajectory) (t : Time) : ℝ :=
  (1 / 2) * s.mass * (s.velocity q t)^2

/--
Newton's second law for the free particle.

Since no external forces act on the particle, Newton's second law
reduces to the equation `m q'' = 0`, expressing that the acceleration
vanishes identically.
-/
def NewtonsSecondLaw (s : FreeParticle) (q : Trajectory) (t : Time) : Prop :=
  s.mass * deriv (s.velocity q) t = 0

/--
Newton's second law for a free particle implies that the acceleration
vanishes identically.

Since the particle mass is strictly positive, the equation
`m q'' = 0` can be simplified to `q'' = 0` by cancelling the mass
factor.
-/
lemma accel_zero (s : FreeParticle) (q : Trajectory) (h : ∀ t, s.NewtonsSecondLaw q t) :
    ∀ t, deriv (deriv q) t = 0 := by
  intro t
  have h₀ : s.mass ≠ 0 := ne_of_gt s.mass_pos
  have h1 := h t
  exact (mul_eq_zero.mp h1).resolve_left h₀

/--
If the acceleration of a trajectory vanishes everywhere, then the
velocity is constant.

More precisely, if the second derivative of the trajectory is zero
for all times, then there exists a constant `v₀` such that the
velocity is equal to `v₀` at every time.

The second-order differentiability assumption is included to apply
standard results from real analysis relating vanishing derivatives to
constant functions.
-/
lemma velocity_const_of_zero_acc (q : Time → ℝ) (h : ∀ t, deriv (deriv q) t = 0)
    (hcont : ContDiff ℝ 2 q) : ∃ v₀, ∀ t, deriv q t = v₀ := by
  refine ⟨deriv q 0, fun t => ?_⟩
  refine is_const_of_fderiv_eq_zero (𝕜 := ℝ) (f := deriv q) ?_ ?_ t 0
  · change Differentiable ℝ ((fun L : Time →L[ℝ] ℝ => L 1) ∘ fun t => fderiv ℝ q t)
    fun_prop
  · intro t
    ext p
    simp only [zero_apply]
    have hp : p = p.val • (1 : Time) := by
      ext
      simp
    rw [hp]
    simp only [map_smul, smul_eq_mul, mul_eq_zero]
    right
    simpa [Time.deriv_eq] using h t

/--
If a free-particle trajectory has constant velocity, then its linear momentum is constant.
-/
lemma linearMomentum_conserved_of_velocity_const (s : FreeParticle) (q : Trajectory)
    (h : ∃ v₀, ∀ t, s.velocity q t = v₀) :
    ∃ p, ∀ t, s.linearMomentum q t = p := by
  rcases h with ⟨v₀, hv⟩
  refine ⟨s.mass * v₀, fun t => ?_⟩
  unfold linearMomentum
  rw [hv t]

/--
A free particle satisfying the equation of motion conserves linear momentum.

Newton's second law implies that the acceleration vanishes, so the velocity is constant.
Since the particle mass is fixed, the linear momentum is constant in time.
-/
theorem linearMomentum_conserved (s : FreeParticle) (q : Trajectory)
    (h : ∀ t, s.NewtonsSecondLaw q t) (hcont : ContDiff ℝ 2 q) :
    ∃ p, ∀ t, s.linearMomentum q t = p := by
  have h_acc : ∀ t, deriv (deriv q) t = 0 :=
    accel_zero s q h
  rcases velocity_const_of_zero_acc q h_acc hcont with ⟨v₀, hv⟩
  exact linearMomentum_conserved_of_velocity_const s q ⟨v₀, hv⟩

/--
A free particle satisfying the equation of motion conserves kinetic energy.

The proof follows the standard argument from classical mechanics:
Newton's second law implies that the acceleration vanishes, which in
turn implies that the velocity is constant. Since the kinetic energy
depends only on the square of the velocity, it follows that the kinetic
energy is constant in time.
-/
theorem kineticEnergy_conserved (s : FreeParticle) (q : Trajectory)
    (h : ∀ t, s.NewtonsSecondLaw q t) (hcont : ContDiff ℝ 2 q) :
    ∃ E, ∀ t, s.kineticEnergy q t = E := by
  -- get q'' = 0
  have h_acc : ∀ t, deriv (deriv q) t = 0 :=
    accel_zero s q h
  -- get constant velocity
  rcases velocity_const_of_zero_acc q h_acc hcont with ⟨v₀, hv⟩
  -- energy is constant
  refine ⟨(1 / 2) * s.mass * v₀^2, fun t => ?_⟩
  unfold kineticEnergy velocity
  rw [hv t]

end FreeParticle
end ClassicalMechanics
