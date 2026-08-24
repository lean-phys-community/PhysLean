/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.MState

import QuantumInfo.ForMathlib

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [FiniteDimensional ℂ E]

/-- The trace distance between two quantum states: half the trace norm of the difference (ρ - σ).

This makes no reference to a basis; `TrDistance_eq_matrix_traceNorm` is the matrix analogue. -/
def TrDistance (ρ σ : DensityOp E) : ℝ :=
  (1/2 : ℝ) * (ρ.op - σ.op).traceNorm

namespace TrDistance

variable (ρ σ : DensityOp E)

/-- **Matrix analogue of `TrDistance`**: half the trace norm of the difference of the density
matrices in the preferred basis. -/
theorem eq_matrix_traceNorm {ι : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] :
    TrDistance ρ σ = (1/2 : ℝ) * Matrix.traceNorm (ρ.m - σ.m : Matrix ι ι ℂ) := by
  rw [TrDistance, HermitianOp.traceNorm_toMat (ι := ι), HermitianOp.toMat_sub]
  rfl

theorem ge_zero : 0 ≤ TrDistance ρ σ :=
  mul_nonneg (by norm_num) (HermitianOp.traceNorm_nonneg _)

/-- A density operator has unit trace norm. -/
theorem traceNorm_op (ρ : DensityOp E) : ρ.op.traceNorm = 1 := by
  rw [HermitianOp.traceNorm_of_nonneg ρ.op_nonneg, ρ.op_trace]

theorem le_one : TrDistance ρ σ ≤ 1 := by
  have h := HermitianOp.traceNorm_sub_le ρ.op σ.op
  rw [traceNorm_op, traceNorm_op] at h
  rw [TrDistance]
  linarith

/-- The trace distance, as a `Prob` probability with value between 0 and 1. -/
def prob : Prob :=
  ⟨TrDistance ρ σ, ⟨ge_zero ρ σ, le_one ρ σ⟩⟩

/-- The trace distance is a symmetric quantity. -/
theorem symm : TrDistance ρ σ = TrDistance σ ρ := by
  rw [TrDistance, TrDistance, ← HermitianOp.traceNorm_neg (ρ.op - σ.op), neg_sub]

/-- The trace distance is equal to half the 1-norm of the eigenvalues of their difference. -/
theorem eq_abs_eigenvalues (ρ σ : MState d) : TrDistance ρ σ = (1/2 : ℝ) *
    ∑ i, abs ((ρ.Hermitian.sub σ.Hermitian).eigenvalues i) := by
  rw [eq_matrix_traceNorm (ι := d),
    Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues (ρ.Hermitian.sub σ.Hermitian)]
  congr!

/-- **Data processing inequality for the trace distance**: a positive trace-preserving map never
increases the trace distance between two states. Complete positivity is not needed. -/
theorem DPI_PTP {d₂ : Type*} [Fintype d₂] [DecidableEq d₂] (ρ σ : MState d) (Λ : PTPMap d d₂) :
    TrDistance (Λ ρ) (Λ σ) ≤ TrDistance ρ σ := by
  have hmat : ∀ τ : MState d, ((Λ τ : MState d₂).m : Matrix d₂ d₂ ℂ) = Λ.map τ.m := fun τ ↦
    congrArg HermitianMat.mat (PTPOp.M_apply_MState Λ τ)
  have hin : (ρ.m - σ.m : Matrix d d ℂ) = ((ρ.M : HermitianMat d ℂ) - σ.M).mat := by
    rw [HermitianMat.mat_sub, DensityOp.mat_M, DensityOp.mat_M]
  rw [eq_matrix_traceNorm (ι := d₂), eq_matrix_traceNorm (ι := d), hmat, hmat, ← map_sub, hin]
  exact mul_le_mul_of_nonneg_left (Λ.map_pos.traceNorm_le Λ.map_TP _) (by norm_num)

/-- **Data processing inequality for the trace distance**: a quantum channel never increases the
trace distance between two states. -/
theorem DPI {d₂ : Type*} [Fintype d₂] [DecidableEq d₂] (ρ σ : MState d) (Φ : CPTPMap d d₂) :
    TrDistance (Φ ρ) (Φ σ) ≤ TrDistance ρ σ :=
  DPI_PTP ρ σ Φ.toPTPOp

-- Fuchs–van de Graaf inequalities
-- Relation to classical TV distance
