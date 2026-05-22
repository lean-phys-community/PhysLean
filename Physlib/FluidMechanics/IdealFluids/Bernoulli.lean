/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

module

public import Physlib.FluidMechanics.IdealFluids.Basic
public import Physlib.FluidMechanics.IdealFluids.Euler
public import Physlib.Mathematics.Calculus.Divergence
public import Physlib.SpaceAndTime.Time.Derivatives

/-!
This module introduces:
steady flow,
material derivative,
isentropic behavious,
the bernoulli equation
-/

open scoped InnerProductSpace
open Time
open Space

/-- Determines whether a flow is steady -/
def IdealFluid.isSteady (F: IdealFluid) :
    Prop :=
      ∀ (pos : Space),
      ∂ₜ (F.velocity · pos) = 0

/-- Definition of a material derivative -/
noncomputable def IdealFluid.materialDerivative (t: Time) (pos: Space)
(F: IdealFluid) (f: Time → Space → ℝ) :
    ℝ :=
      ∂ₜ (f · pos) t +
      ⟪F.velocity t pos, ∇ (f t ·) pos ⟫_ℝ

/-- Determines whether a flow is isentropic -/
def IdealFluid.isIsentropic (F: IdealFluid):
    Prop :=
      ∀ (t: Time) (pos: Space),
      F.materialDerivative t pos F.entropy = 0

-- TODO: Make into material derivative

/-- The Bernoulli function (1/2)v^2 + w -/
noncomputable def IdealFluid.bernoulliEquation (F: IdealFluid)
(t: Time) (pos: Space) (g: Space → ℝ):
    ℝ :=
      let v := F.velocity t pos
      0.5 * ⟪v, v⟫_ℝ + F.enthalpy t pos + g pos
