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

General lemmas on the time derivative `∂ₜ` of square-matrix-valued functions of time: a product
rule, the commutation of the derivative with transpose, and the commutation of the derivative with
taking a matrix entry. These are the tools needed to differentiate a path of matrices.

They rely on the (opt-in) operator-norm structure on matrices — activated here as local instances —
only to invoke the product rule and to view transpose (through `Matrix.transposeLinearEquiv`) as a
continuous linear map. Since all norms on a fixed finite-dimensional space induce the same topology,
differentiability does not depend on this choice.

-/

@[expose] public section

open Time Manifold Matrix
open scoped RightActions

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {d : ℕ}

/-- The transpose of a differentiable matrix-valued function is differentiable
(cf. `Continuous.matrix_transpose`). -/
lemma DifferentiableAt.matrix_transpose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : E → Matrix (Fin d) (Fin d) ℝ} {t : E} (hA : DifferentiableAt ℝ A t) :
    DifferentiableAt ℝ (fun s => (A s)ᵀ) t :=
  ((transposeLinearEquiv (Fin d) (Fin d) ℝ ℝ).toLinearMap.toContinuousLinearMap).differentiableAt
    |>.comp t hA

namespace Time

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
  let T : Matrix (Fin d) (Fin d) ℝ →L[ℝ] Matrix (Fin d) (Fin d) ℝ :=
    (transposeLinearEquiv (Fin d) (Fin d) ℝ ℝ).toLinearMap.toContinuousLinearMap
  have h : HasFDerivAt (fun s => (A s)ᵀ) (T.comp (fderiv ℝ A t)) t :=
    T.hasFDerivAt.comp t hA.hasFDerivAt
  rw [Time.deriv_eq, h.fderiv, Time.deriv_eq]
  rfl

/-- The time derivative commutes with taking a matrix entry. -/
lemma deriv_matrix_apply (A : Time → Matrix (Fin d) (Fin d) ℝ) (t : Time)
    (hA : DifferentiableAt ℝ A t) (i j : Fin d) :
    ∂ₜ (fun s => A s i j) t = (∂ₜ A t) i j := by
  let E : Matrix (Fin d) (Fin d) ℝ →L[ℝ] ℝ :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap
  have h : HasFDerivAt (fun s => A s i j) (E.comp (fderiv ℝ A t)) t :=
    E.hasFDerivAt.comp t hA.hasFDerivAt
  rw [Time.deriv_eq, h.fderiv, Time.deriv_eq]
  rfl

end Time
