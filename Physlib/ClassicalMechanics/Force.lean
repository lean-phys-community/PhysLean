/-
Copyright (c) 2026 Raunak Chhatwal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raunak Chhatwal
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Physlib.SpaceAndTime.ReferenceFrame
/-!
# Forces

This module defines forces acting on objects, expressed in a reference frame.
A `Force` records its target and its vector value over time. An `InternalForce`
additionally records a distinct source object.

The time-dependent vector describes the force acting on the target, without
prescribing how that force is determined. For example, a gravitational force can
be specified directly from the target's mass, while a constraint force can be
specified by its relation to the motion of the objects. Representing both by the
same type allows Newton's laws to be stated independently of the particular
interactions present.

The reference frame appears in the type of a force's vector values, keeping their
coordinate dependence explicit. The definition lives in the
`ClassicalMechanics.ReferenceFrame` namespace to support dot notation such as
`frame.Force Object`, but also occupies a general name that future non-particle
Newtonian formalizations may need.

The target type `Object` is therefore deliberately left arbitrary. Newtonian mechanics is
not limited to point particles, so this force representation is kept independent
of any particular model of matter, with the intention it may get generalized for
rigid body mechanics, continuum mechanics, or other Newtonian models in the future.
-/

@[expose] public noncomputable section

open scoped BigOperators Classical

namespace ClassicalMechanics.ReferenceFrame

variable {d : ℕ} {frame : ReferenceFrame d} {Object : Type}

/-- A time-dependent force acting on an object. -/
structure Force (frame : ReferenceFrame d) (Object : Type) where
  /-- The force vector. -/
  value : Time → frame.Vector
  /-- The target object. -/
  target : Object

instance : CoeFun (frame.Force Object) (fun _ => Time → frame.Vector) where
  coe := Force.value

/-- A force between two objects. -/
structure InternalForce (frame : ReferenceFrame d) (Object : Type) extends frame.Force Object where
  /-- The source object. -/
  source : Object
  source_ne_target : source ≠ target

instance : CoeFun (frame.InternalForce Object) (fun _ => Time → frame.Vector) where
  coe force := force.value

instance : Coe (frame.InternalForce Object) (frame.Force Object) where
  coe := InternalForce.toForce

/-- The equal-and-opposite force with source and target exchanged. -/
def InternalForce.reverse (force : frame.InternalForce Object) : frame.InternalForce Object where
  value := -force.value
  target := force.source
  source := force.target
  source_ne_target := force.source_ne_target.symm

/-- The net force on `object`. -/
def netForce
    (object : Object)
    (internalForces : Multiset (frame.InternalForce Object))
    (externalForces : Multiset (frame.Force Object))
    (t : Time) : frame.Vector :=
  let forces := internalForces.map InternalForce.toForce + externalForces
  ∑ force : forces with force.1.target = object, force.1 t
