/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Physlib.SpaceAndTime.Space.ConstantSliceDist
public import Physlib.SpaceAndTime.Space.Norm.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
/-!

## Spherical surfaces on Space.


-/
@[expose] public section

open SchwartzMap NNReal
noncomputable section
open Physlib Distribution
variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. The definition of the spherical shell surface

-/

/-- The map embedding the unit sphere in `Space d.succ` into `Space d.succ`. -/
def sphericalShell (d : ℕ) : Metric.sphere (0 : Space d.succ) 1 → Space d.succ := fun x => x.1

lemma sphericalShell_injective (d : ℕ) : Function.Injective (sphericalShell d) := by
  intro x y h
  simp [sphericalShell] at h
  grind

lemma sphericalShell_continuous (d : ℕ) : Continuous (sphericalShell d) := continuous_subtype_val

lemma sphericalShell_measurableEmbedding (d : ℕ) : MeasurableEmbedding (sphericalShell d) := by
  apply Continuous.measurableEmbedding
  · exact sphericalShell_continuous d
  · exact sphericalShell_injective d

@[simp]
lemma norm_sphericalShell (d : ℕ) (x : Metric.sphere (0 : Space d.succ) 1) :
    ‖sphericalShell d x‖ = 1 := by
  simp [sphericalShell, Metric.sphere]

/-!

## B. The measure associated with the spherical shell

-/

/-- The measure on `Space d.succ` corresponding to integration around a spherical shell. -/
def sphericalShellMeasure (d : ℕ) : Measure (Space d.succ) :=
  MeasureTheory.Measure.map (sphericalShell d) (MeasureTheory.Measure.toSphere volume)

instance sphericalShellMeasure_hasTemperateGrowth (d : ℕ) :
    (sphericalShellMeasure d).HasTemperateGrowth := by
  rw [sphericalShellMeasure]
  refine { exists_integrable := ?_ }
  use 0
  simp

/-!

## C. The distribution associated with the spherical shell

-/

/-- The distribution associated with a spherical shell.
  One can roughly think of this distribution as the distribution which
  takes test functions `f (r)` to `∫ d³r f(r) ρ(r)` where `ρ(r)` is the
  mass, charge or current etc. distribution. -/
def sphericalShellDist (d : ℕ) : (Space d.succ) →d[ℝ] ℝ  :=
  SchwartzMap.integralCLM ℝ (sphericalShellMeasure d)


lemma sphericalShellDist_apply_eq_integral_sphericalShellMeasure (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f = ∫ x, f x ∂sphericalShellMeasure d := by
  rw [sphericalShellDist, SchwartzMap.integralCLM_apply]

lemma sphericalShellDist_apply_eq_integral_sphere_volume (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    sphericalShellDist d f =
    ∫ x, f (sphericalShell d x) ∂(MeasureTheory.Measure.toSphere volume) := by
  rw [sphericalShellDist_apply_eq_integral_sphericalShellMeasure, sphericalShellMeasure,
   MeasurableEmbedding.integral_map (sphericalShell_measurableEmbedding d)]

end Space
