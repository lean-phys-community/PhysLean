/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module
public import PhyslibAlpha.SpaceAndTime.Space.Surfaces.SphericalShell
public import Physlib.SpaceAndTime.Space.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-!

## Solid sphere surfaces in `Space d`

The solid sphere is the closed unit ball in `Space d.succ`. Unlike the line or the spherical
shell, it is a region of positive ambient volume, so the measure associated with it is the
ambient volume restricted to the ball rather than a pushforward of a lower-dimensional measure.
The requirement that the surface has ambient measure zero is therefore not applicable here, and
is replaced by a statement that the solid sphere has positive ambient volume.

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

## A. The definition of the solid sphere surface

-/

/-- The map embedding the closed unit ball in `Space d.succ` into `Space d.succ`. -/
def solidSphere (d : ℕ) : Metric.closedBall (0 : Space d.succ) 1 → Space d.succ := fun x => x.1

lemma solidSphere_injective (d : ℕ) : Function.Injective (solidSphere d) := by
  intro x y h
  simp [solidSphere] at h
  grind

lemma solidSphere_continuous (d : ℕ) : Continuous (solidSphere d) := continuous_subtype_val

lemma solidSphere_measurableEmbedding (d : ℕ) : MeasurableEmbedding (solidSphere d) := by
  apply Continuous.measurableEmbedding
  · exact solidSphere_continuous d
  · exact solidSphere_injective d

@[simp]
lemma norm_solidSphere_le (d : ℕ) (x : Metric.closedBall (0 : Space d.succ) 1) :
    ‖solidSphere d x‖ ≤ 1 := by
  have hx := x.2
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
  exact hx

/-!

## B. The measure associated with the solid sphere

-/

/-- The measure on `Space d.succ` corresponding to integration over a solid sphere, i.e. the
  ambient volume measure restricted to the closed unit ball. -/
def solidSphereMeasure (d : ℕ) : Measure (Space d.succ) :=
  volume.restrict (Metric.closedBall (0 : Space d.succ) 1)

instance solidSphereMeasure_isFiniteMeasure (d : ℕ) :
    IsFiniteMeasure (solidSphereMeasure d) := by
  rw [solidSphereMeasure, isFiniteMeasure_restrict]
  exact (Metric.isBounded_closedBall).measure_lt_top.ne

instance solidSphereMeasure_hasTemperateGrowth (d : ℕ) :
    (solidSphereMeasure d).HasTemperateGrowth :=
  inferInstance

/-!

## C. The distribution associated with the solid sphere

-/

/-- The distribution on `Space d.succ` corresponding to integration over a solid sphere.
  One can roughly think of this distribution as taking a test function `f` to its integral against
  a mass, charge or current density spread over a solid ball. -/
def solidSphereDist (d : ℕ) : (Space d.succ) →d[ℝ] ℝ :=
  SchwartzMap.integralCLM ℝ (solidSphereMeasure d)

lemma solidSphereDist_apply_eq_integral_solidSphereMeasure (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    solidSphereDist d f = ∫ x, f x ∂solidSphereMeasure d := by
  rw [solidSphereDist, SchwartzMap.integralCLM_apply]

lemma solidSphereDist_apply_eq_integral_closedBall (d : ℕ) (f : 𝓢(Space d.succ, ℝ)) :
    solidSphereDist d f = ∫ x in Metric.closedBall (0 : Space d.succ) 1, f x := by
  rw [solidSphereDist_apply_eq_integral_solidSphereMeasure, solidSphereMeasure]

/-!

## D. The solid sphere has positive ambient volume

-/

lemma solidSphere_volume_pos (d : ℕ) :
    0 < volume (Metric.closedBall (0 : Space d.succ) 1) := by
  apply lt_of_lt_of_le (b := volume (Metric.ball (0 : Space d.succ) 1))
  · exact (Metric.isOpen_ball).measure_pos volume (Metric.nonempty_ball.mpr one_pos)
  · exact measure_mono Metric.ball_subset_closedBall

lemma solidSphereMeasure_univ_pos (d : ℕ) : 0 < solidSphereMeasure d Set.univ := by
  rw [solidSphereMeasure, Measure.restrict_apply_univ]
  exact solidSphere_volume_pos d

end Space
