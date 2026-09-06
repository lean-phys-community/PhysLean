/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.Algebra.Order.Positive.Field
public import Physlib.SpaceAndTime.ReferenceFrame
public import Physlib.SpaceAndTime.Time.Derivatives
/-!
# Point particles

This module defines point particles together with their motion relative to a
reference frame. A `Particle` has a constant positive mass and a position over
time. Velocity and acceleration are derived from that position rather than stored
as independent data.

The trajectory is part of the particle's description, but need not be given by an
explicit solution formula. Particle values can be considered subject to conditions
on their positions and on the forces acting on them. A particular mechanical model
can therefore be specified by constraints on particles, with the existence of
particles satisfying those constraints established separately.

A particle by itself carries no equation of motion or assumption about which
forces act on it. It is a constituent from which systems can be assembled, rather
than a specification of an isolated or unconstrained one-particle system. Newton's
laws are imposed when particles and forces are assembled in
`ClassicalMechanics.PointParticle.System`.

Position and its first time derivative are required to be differentiable when the
frame is inertial. This ensures that the velocity and acceleration used in
Newtonian systems are genuine derivatives. The trajectories in this definition
are defined for all `Time`.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.ReferenceFrame

variable {d : ℕ} {frame : ReferenceFrame d}

/-- Positive real numbers. -/
notation "ℝ+" => {x : ℝ // 0 < x}

/-- Scalar multiplication by a positive real. -/
instance : SMul ℝ+ frame.Vector where
  smul c x := c.val • x

/-!
## A. Point particles

A point particle has a positive mass and a trajectory relative to a reference frame.
-/

/-- A point particle in `frame`. -/
structure Particle (frame : ReferenceFrame d) where
  /-- The particle's mass. -/
  mass : ℝ+
  /-- The particle's position in frame coordinates. -/
  pos : Time → frame.Vector
  pos_twice_differentiable :
    frame.IsInertial → Differentiable ℝ pos ∧ Differentiable ℝ (Time.deriv pos)

namespace Particle

variable (particle : frame.Particle)

/-- Position is differentiable in an inertial frame. -/
instance [h : Fact frame.IsInertial] : Fact (Differentiable ℝ particle.pos) :=
  ⟨particle.pos_twice_differentiable h.out |>.left⟩

/-- The particle's velocity. -/
def velocity [_h : Fact (Differentiable ℝ particle.pos)] : Time → frame.Vector :=
  Time.deriv particle.pos

/-- Velocity is differentiable in an inertial frame. -/
instance [h : Fact frame.IsInertial] : Fact (Differentiable ℝ particle.velocity) :=
  ⟨particle.pos_twice_differentiable h.out |>.right⟩

/-- The particle's acceleration. -/
def acceleration [Fact (Differentiable ℝ particle.pos)]
    [_h : Fact (Differentiable ℝ particle.velocity)] : Time → frame.Vector :=
  Time.deriv particle.velocity

/-- The particle's position in affine space. -/
def pointInSpace (t : Time) : Space d :=
  Vector.dispEquiv t (particle.pos t) +ᵥ frame.origin t

end ClassicalMechanics.ReferenceFrame.Particle
