/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Physlib.SpaceAndTime.ReferenceFrame.Basic
public import Physlib.SpaceAndTime.Time.Derivatives
/-!
# Velocity in a reference frame

## i. Overview

The velocity of a trajectory is a displacement per unit time, so it is read off a frame's axes
as a `frame.Vector`. This is the velocity of the trajectory in space, expressed in the frame's
axes at that instant. For a frame whose axes turn with time it is not the velocity an observer
carried along by the frame would measure; that quantity, the time derivative of the coordinate
components, requires regularity of `frame.basis` and is recorded as a TODO at the end of the file.

The velocity of an inertial frame's origin, `IsInertial.velocity`, is defined through the
uniform motion of the origin. Here it is identified with the time derivative of the origin.

## ii. Key results

- `velocityComponents` : the velocity of a trajectory in the components of a frame.
- `velocityComponents_const` : a trajectory at rest has zero velocity in every frame.
- `IsInertial.derivVec_origin` : the velocity of an inertial frame's origin is the time
  derivative of that origin.
- `velocityComponents_origin` : the velocity of an inertial frame's origin, measured in that
  frame.

## iii. Table of contents

- A. The velocity of a trajectory in a frame
- B. The velocity of an inertial frame's origin

## iv. References

-/

@[expose] public noncomputable section

namespace ClassicalMechanics
namespace ReferenceFrame

open Time

variable {d : ℕ} {frame : ReferenceFrame d}

/-!
## A. The velocity of a trajectory in a frame
-/

/-- The velocity of the trajectory `x`, in the components of `frame` at time `t`. -/
def velocityComponents (frame : ReferenceFrame d) (x : Time → Space d) (t : Time) :
    frame.Vector :=
  (Vector.dispEquiv t).symm (∂ₜᵥ x t)

lemma velocityComponents_eq (x : Time → Space d) (t : Time) :
    frame.velocityComponents x t = (Vector.dispEquiv t).symm (∂ₜᵥ x t) := rfl

/-- A trajectory at rest has zero velocity in every frame. -/
@[simp]
lemma velocityComponents_const (p : Space d) (t : Time) :
    frame.velocityComponents (fun _ => p) t = 0 := by
  rw [velocityComponents_eq, Time.derivVec_const, map_zero]

/-!
## B. The velocity of an inertial frame's origin
-/

/-- The velocity of an inertial frame's origin is the time derivative of that origin. -/
lemma IsInertial.derivVec_origin (h : frame.IsInertial) (t : Time) :
    h.velocity = ∂ₜᵥ frame.origin t := by
  simp only [Time.derivVec_eq, h.origin_vsub, Time.sub_val]
  rw [fderiv_smul_const (by fun_prop), ContinuousLinearMap.smulRight_apply, fderiv_sub_const,
    Time.fderiv_val, one_smul]

/-- The velocity of an inertial frame's origin, measured in that frame. -/
lemma velocityComponents_origin (h : frame.IsInertial) (t : Time) :
    frame.velocityComponents frame.origin t = (Vector.dispEquiv t).symm h.velocity := by
  rw [velocityComponents_eq, ← h.derivVec_origin]

TODO "ReferenceFrame API-map requirement: the derivative of a trajectory expressed in a
  frame, giving the velocity and acceleration measured by that frame as the time derivative
  of its coordinate components. Plan: define the coordinate components of a trajectory,
  `(dispEquiv t).symm (x t -ᵥ frame.origin t)`, and for an inertial frame identify their
  time derivative with `velocityComponents x t` minus the origin's velocity components;
  acceleration is one further time derivative. A general frame needs regularity of
  `frame.basis`, which `ReferenceFrame` does not yet carry."

end ReferenceFrame
end ClassicalMechanics

end
