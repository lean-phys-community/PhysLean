/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Physlib.SpaceAndTime.Time.Derivatives
public import Mathlib.Analysis.Matrix.Normed
/-!

# Time derivatives of matrix-valued functions

General lemmas on the time derivative `∂ₜ` of square-matrix-valued functions of time: a product rule
and the commutation of the derivative with transpose. Together with `Matrix.transposeCLM` (transpose
as a continuous linear map) these are the tools needed to differentiate a path of matrices.

They rely on the (opt-in) operator-norm structure on matrices — activated here as local instances —
only to invoke the product rule and to view transpose as a continuous linear map. Since all norms
on a fixed finite-dimensional space induce the same topology, differentiability does not depend on
this choice.

-/

@[expose] public section

open Time Manifold Matrix
open scoped RightActions

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace Matrix

variable {d : ℕ}

/-- Transpose as a continuous linear map on square real matrices. -/
noncomputable def transposeCLM :
    Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ :=
  (Matrix.transposeLinearEquiv (Fin d) (Fin d) ℝ ℝ).toLinearMap.toContinuousLinearMap

@[simp]
lemma transposeCLM_apply (A : Matrix (Fin d) (Fin d) ℝ) : transposeCLM A = Aᵀ := rfl

end Matrix

namespace Time

variable {d : ℕ}

/-- Product rule for the time derivative of a product of matrix-valued functions. -/
lemma deriv_matrix_mul (A B : Time → Matrix (Fin d) (Fin d) ℝ) (t : Time)
    (hA : DifferentiableAt ℝ A t) (hB : DifferentiableAt ℝ B t) :
    ∂ₜ (fun s => A s * B s) t = A t * ∂ₜ B t + ∂ₜ A t * B t := by
  have h : HasFDerivAt (fun s => A s * B s)
      (A t • fderiv ℝ B t + fderiv ℝ A t <• B t) t := hA.hasFDerivAt.mul' hB.hasFDerivAt
  rw [Time.deriv_eq, h.fderiv, Time.deriv_eq, Time.deriv_eq, _root_.add_apply]
  simp only [_root_.smul_apply, smul_eq_mul, op_smul_eq_mul]

/-- The time derivative commutes with transpose. -/
lemma deriv_matrix_transpose (A : Time → Matrix (Fin d) (Fin d) ℝ) (t : Time)
    (hA : DifferentiableAt ℝ A t) :
    ∂ₜ (fun s => (A s)ᵀ) t = (∂ₜ A t)ᵀ := by
  have h : HasFDerivAt (fun s => (A s)ᵀ) (Matrix.transposeCLM.comp (fderiv ℝ A t)) t :=
    Matrix.transposeCLM.hasFDerivAt.comp t hA.hasFDerivAt
  rw [Time.deriv_eq, h.fderiv, Time.deriv_eq]
  simp

end Time
