/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

module

public import Physlib.FluidMechanics.IdealFluids.Basic
public import Physlib.Mathematics.Calculus.Divergence
public import Physlib.SpaceAndTime.Time.Derivatives
public import Physlib.SpaceAndTime.Space.Derivatives.Grad
public import Physlib.SpaceAndTime.Space.Derivatives.Div

/-!
This module introduces the conservation of momentum in ideal fluids by formalizing
the `Euler's equation`.
-/

open scoped InnerProductSpace
open Time
open Space

namespace IdealFluid

/-- Defines the property of satisfying Euler's equation. -/
public def satisfiesEuler (F : IdealFluid) (g : Space → ℝ):
  Prop :=
    ∀ (t : Time) (pos : Space),
      let v := F.velocity t pos
      ∂ₜ (F.velocity · pos) t +
      (fun i => ⟪v, Space.grad (F.velocity t · i) pos⟫_ℝ)
      = -(1/F.density t pos) • Space.grad (F.pressure t ·) pos + Space.grad g pos

end IdealFluid
