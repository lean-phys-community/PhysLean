/-
Copyright (c) 2026 Hannah Dawe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hannah Dawe
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Circular Orbit Vis Viva
The vis-viva equation relates the speed of an orbiting body to its position
and the mass of the central body. This module defines a simplified version of the
vis-viva equation that is restricted to circular orbits (v^2 = G M / r).
-/

@[expose] public section

namespace ClassicalMechanics

/-- System parameters for the vis-viva equation in circular orbital mechanics. -/
structure VisViva where
  /-- Gravitational constant. -/
  G : ℝ
  /-- Central mass body. -/
  M : ℝ
  /-- Orbiting mass body. -/
  m : ℝ

namespace VisViva

/-- Configuration space for orbital mechanics, defining the orbital radius. -/
structure ConfigurationSpace where
  /-- Orbital radius. -/
  r : ℝ

/-- The orbital speed required for a circular orbit at radius `r`. -/
noncomputable def speedCircular (sys : VisViva) (cfg : ConfigurationSpace) : ℝ :=
  Real.sqrt (sys.G * sys.M / cfg.r)

/-- Lemma: the square of the circular orbit speed equals G M / r. -/
lemma speedCircular_sq (sys : VisViva) (cfg : ConfigurationSpace) (hr : 0 < cfg.r) (hG : 0 < sys.G)
    (hM : 0 < sys.M) :
    (speedCircular sys cfg)^2 = sys.G * sys.M / cfg.r := by
  simp [speedCircular]
  apply Real.sq_sqrt
  positivity

end VisViva
end ClassicalMechanics
