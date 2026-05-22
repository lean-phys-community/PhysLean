/-
Copyright (c) 2026 Michał Mogielnicki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Mogielnicki
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Physlib.SpaceAndTime.Space.Module
public import Physlib.SpaceAndTime.Time.Basic

/-!
This module establishes the core mathematical structure of an ideal fluid. It defines the

- `continuous and differentiable fields` (dencity, velocity, pressure, entropy, and enthalpy)
- `mass, entropy, energy flux densities`
- `fluid volume structures` alongside surface integrals to compute various flows
-/

open scoped InnerProductSpace

/-- Introducing the structure of Ideal Fluids -/
public structure IdealFluid where
  /-- The density at a specific point and time -/
  density: Time → Space → ℝ
  /-- The velocity at a specific point and time -/
  velocity: Time → Space → EuclideanSpace ℝ (Fin 3)
  /-- The pressure at a specific point and time -/
  pressure: Time → Space → ℝ
  /-- The entropy at a specific point and time -/
  entropy: Time → Space → ℝ
  /-- The enthalpy at a specific point and time -/
  enthalpy: Time → Space → ℝ

  density_pos: ∀ t pos, 0 < density t pos

  /-- Ensuring that all are differentiable for more complex equations. -/
  density_contdiff: ContDiff ℝ 1 (fun (t, pos) => density t pos)
  velocity_contdiff: ContDiff ℝ 1 ( fun (t, pos) => velocity t pos)
  pressure_contdiff: ContDiff ℝ 1 ( fun (t, pos) => pressure t pos)

  entropy_contdiff: ContDiff ℝ 1 ( fun (t, pos) => entropy t pos)
  enthalpy_contdiff: ContDiff ℝ 1 ( fun(t, pos) => enthalpy t pos)

namespace IdealFluid
open MeasureTheory

/-- Mass flux density j=ρv -/
public abbrev massFluxDensity (F : IdealFluid) (t : Time) (pos : Space):
    EuclideanSpace ℝ (Fin 3) :=
      F.density t pos • F.velocity t pos

/-- Entropy flux density ρsv -/
public abbrev entropyFluxDensity (F : IdealFluid) (t : Time) (pos : Space):
    EuclideanSpace ℝ (Fin 3) :=
      F.entropy t pos • F.density t pos • F.velocity t pos

/-- Energy flux density ρv(1/2 |v|^2 + w) -/
noncomputable abbrev energyFluxDensity (F : IdealFluid) (t : Time) (pos : Space):
    EuclideanSpace ℝ (Fin 3) :=
      let w := F.enthalpy t pos
      let v := F.velocity t pos
      let v_sq: ℝ := ⟪v,v⟫_ℝ
      let scalar := (F.density t pos)*(0.5*v_sq + w)

      scalar • v

/-- Volume to introduce surface integrals -/
structure FluidVolume where
  /-- The 3D region -/
  region: Set Space
  /-- The normal pointing outwards -/
  normal: Space → EuclideanSpace ℝ (Fin 3)
  /-- 2D measure of the boundary -/
  surfaceMeasure: Measure Space

/-- Surface integral of a vector field -/
noncomputable def surfaceIntegral (V : FluidVolume) (flux : Space → EuclideanSpace ℝ (Fin 3)):
    ℝ :=
      ∫ (pos : Space) in frontier V.region, ⟪flux pos, V.normal pos⟫_ℝ ∂V.surfaceMeasure

/-- Mass flow out of volume -/
noncomputable def massFlowOut (F : IdealFluid) (t : Time) (V : FluidVolume):
    ℝ :=
      surfaceIntegral V (F.massFluxDensity t ·)

/-- Entropy flow out of volume -/
noncomputable def entropyFlowOut (F : IdealFluid) (t : Time) (V : FluidVolume):
    ℝ :=
      surfaceIntegral V (F.entropyFluxDensity t ·)

/-- Energy flow out of volume -/
noncomputable def energyFlowOut (F : IdealFluid) (t : Time) (V : FluidVolume):
    ℝ :=
      surfaceIntegral V (F.energyFluxDensity t ·)

end IdealFluid
