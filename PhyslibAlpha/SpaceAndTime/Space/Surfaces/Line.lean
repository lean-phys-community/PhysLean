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

## Line surfaces in `Space d`

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

## A. The definition of the line surface

-/

/-- The coordinate line embedded in `Space d.succ.succ`. -/
def line (d : ℕ) : ℝ → Space d.succ.succ := fun r =>
  (slice (0 : Fin d.succ.succ)).symm (r, 0)

lemma line_eq (d : ℕ) :
    line d = (slice (0 : Fin d.succ.succ)).symm ∘ (fun r : ℝ => (r, 0)) := rfl

lemma line_injective (d : ℕ) : Function.Injective (line d) := by
  intro x y h
  have h0 := congrArg (fun p : Space d.succ.succ => p (0 : Fin d.succ.succ)) h
  simpa [line] using h0

@[fun_prop]
lemma line_continuous (d : ℕ) : Continuous (line d) := by
  rw [line_eq]
  fun_prop

lemma line_measurableEmbedding (d : ℕ) : MeasurableEmbedding (line d) :=
  Continuous.measurableEmbedding (line_continuous d) (line_injective d)

@[simp]
lemma norm_line (d : ℕ) (r : ℝ) : ‖line d r‖ = ‖r‖ := by
  rw [line, norm_slice_symm_eq]
  simp [Real.sqrt_sq_eq_abs]

lemma line_eq_smul_basis (d : ℕ) (r : ℝ) :
    line d r = r • basis (0 : Fin d.succ.succ) := by
  rw [line, basis_self_eq_slice]
  change (slice (0 : Fin d.succ.succ)).symm (r, 0) =
    r • (slice (0 : Fin d.succ.succ)).symm (1, 0)
  simpa using ((slice (0 : Fin d.succ.succ)).symm.map_smul r (1, (0 : Space d.succ)))

/-!

## B. The measure associated with the line

-/

/-- The measure on `Space d.succ.succ` corresponding to integration along a coordinate line. -/
def lineMeasure (d : ℕ) : Measure (Space d.succ.succ) :=
  MeasureTheory.Measure.map (line d) volume

instance lineMeasure_hasTemperateGrowth (d : ℕ) :
    (lineMeasure d).HasTemperateGrowth := by
  rw [lineMeasure]
  refine { exists_integrable := ?_ }
  obtain ⟨r, hr⟩ := Measure.HasTemperateGrowth.exists_integrable (μ := volume (α := ℝ))
  use r
  rw [MeasurableEmbedding.integrable_map_iff]
  · convert hr using 1
    ext x
    simp [norm_line]
  · exact line_measurableEmbedding d

/-!

## C. The distribution associated with the line

-/

/-- The distribution on `Space d.succ.succ` corresponding to integration along a coordinate line.
  One can roughly think of this distribution as taking a test function `f` to its integral against
  a mass, charge or current density concentrated on a line. -/
def lineDist (d : ℕ) : (Space d.succ.succ) →d[ℝ] ℝ :=
  SchwartzMap.integralCLM ℝ (lineMeasure d)

lemma lineDist_apply_eq_integral_lineMeasure (d : ℕ) (f : 𝓢(Space d.succ.succ, ℝ)) :
    lineDist d f = ∫ x, f x ∂lineMeasure d := by
  rw [lineDist, SchwartzMap.integralCLM_apply]

lemma lineDist_apply_eq_integral_volume (d : ℕ) (f : 𝓢(Space d.succ.succ, ℝ)) :
    lineDist d f = ∫ r : ℝ, f (line d r) := by
  rw [lineDist_apply_eq_integral_lineMeasure, lineMeasure,
    MeasurableEmbedding.integral_map (line_measurableEmbedding d)]

/-!

## D. The line has ambient volume zero

-/

/-- The linear subspace spanned by the coordinate line in `Space d.succ.succ`. -/
def lineSubmodule (d : ℕ) : Submodule ℝ (Space d.succ.succ) :=
  ℝ ∙ basis (0 : Fin d.succ.succ)

lemma line_mem_lineSubmodule (d : ℕ) (r : ℝ) : line d r ∈ lineSubmodule d := by
  rw [line_eq_smul_basis]
  exact Submodule.smul_mem _ r (Submodule.mem_span_singleton_self (basis (0 : Fin d.succ.succ)))

lemma range_line_subset_lineSubmodule (d : ℕ) :
    Set.range (line d) ⊆ (lineSubmodule d : Set (Space d.succ.succ)) := by
  rintro x ⟨r, rfl⟩
  exact line_mem_lineSubmodule d r

lemma lineSubmodule_ne_top (d : ℕ) : lineSubmodule d ≠ ⊤ := by
  intro htop
  have hbasis : basis (1 : Fin d.succ.succ) ∈ lineSubmodule d := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_singleton.mp hbasis)
  have hcoord := congrArg (fun p : Space d.succ.succ => p (1 : Fin d.succ.succ)) hc
  simp [basis_apply] at hcoord

lemma volume_line_range (d : ℕ) :
    volume (Set.range (line d) : Set (Space d.succ.succ)) = 0 := by
  refine measure_mono_null (range_line_subset_lineSubmodule d) ?_
  rw [volume_eq_addHaar]
  exact MeasureTheory.Measure.addHaar_submodule
    (Space.basis.toBasis.addHaar : Measure (Space d.succ.succ))
    (lineSubmodule d) (lineSubmodule_ne_top d)

end Space
