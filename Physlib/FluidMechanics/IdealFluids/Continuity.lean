/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

module

public import Physlib.FluidMechanics.IdealFluids.Basic
public import Physlib.Mathematics.Calculus.Divergence
public import Physlib.SpaceAndTime.Time.Derivatives
public import Physlib.SpaceAndTime.Space.Derivatives.Div

/-!
# Continuity and Incompressibility

This module formulates mass conservation by defining the conditions for an ideal fluid to satisfy
the `Continuity Equation`.

Additionally, it defines the mathematical model for `incompressibility` of a fluid.

There is potential to extend this module broadly with various lemmas and theorems.
-/

open scoped InnerProductSpace
open Time
open Space

namespace IdealFluid

/-- defining satisfying the equation of continuity -/
public def satisfiesContinuity (F : IdealFluid):
    Prop :=
      ∀ (t : Time) (pos : Space),
      ∂ₜ (F.density · pos) t +
      Space.div (F.massFluxDensity t ·) pos = (0 : ℝ)

/-- Criterion for incompressibility -/
public def isIncompressible (F : IdealFluid):
  Prop :=
    ∀ (t : Time) (pos : Space), ∂ₜ (F.density · pos) t = 0

end IdealFluid
