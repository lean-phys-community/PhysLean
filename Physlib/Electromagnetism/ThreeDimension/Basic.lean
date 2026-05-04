/-
Copyright (c) 2026 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
module

public import Physlib.Electromagnetism.Kinematics.MagneticField
/-!

# Three-Dimensional Electromagnetism

This directory provides a three-dimensional, vector-calculus-facing layer for
electromagnetism.

The backend theory is formulated in a tensorial and dimension-general way.
Here we re-express the relevant constructions in the familiar language of
scalar and vector potentials, electric and magnetic fields, and spatial
derivatives.

-/

@[expose] public section

namespace Electromagnetism
namespace ThreeDimension

open Time
open Space
open ElectromagneticPotential

variable (c : SpeedOfLight) (V : ElectromagneticPotential 3)

local notation "φ" => V.scalarPotential c
local notation "A" => V.vectorPotential c
local notation "E" => V.electricField c

/-!

# Fields from potentials

In this section we rewrite the electric and magnetic fields associated to an
electromagnetic potential in terms of the scalar and vector potentials, using
the standard vector-calculus expressions.

-/

/-- The electric field written in terms of the scalar and vector potentials as `- ∇ φ - ∂ₜ A`. -/
theorem electricField_eq_3D :
    E = fun t x => - ∇ (φ t) x - ∂ₜ (fun t => A t x) t := by
  rw [electricField_eq]

local notation "B" => V.magneticField c

/-- The magnetic field written as the curl of the vector potential as `∇ ⨯ A`. -/
theorem magneticField_eq_3D :
    B = fun t x => (∇ ⨯ (A t)) x := by
  rw [magneticField_eq]

end ThreeDimension
end Electromagnetism
