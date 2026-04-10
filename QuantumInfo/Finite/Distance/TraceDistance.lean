/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Finite.MState

public import QuantumInfo.ForMathlib

@[expose] public section

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

/--The trace distance between two quantum states: half the trace norm of the difference (ρ - σ). -/
def TrDistance (ρ σ : MState d) : ℝ :=
  (1/2:ℝ) * (ρ.m - σ.m).traceNorm

namespace TrDistance

variable {d d₂ : Type*} [Fintype d] [Fintype d₂] (ρ σ : MState d)

set_option backward.isDefEq.respectTransparency false in
theorem ge_zero : 0 ≤ TrDistance ρ σ := by
  rw [TrDistance]
  simp [Matrix.traceNorm_nonneg]

theorem le_one : TrDistance ρ σ ≤ 1 :=
  calc TrDistance ρ σ
    _ = (1/2:ℝ) * (ρ.m - σ.m).traceNorm := by rfl
    _ ≤ (1/2:ℝ) * (ρ.m.traceNorm + σ.m.traceNorm) := by
      linarith [Matrix.traceNorm_triangleIneq' ρ.m σ.m]
    _ = (1/2:ℝ) * (1 + 1) := by
      rw [ρ.traceNorm_eq_1, σ.traceNorm_eq_1]
    _ = 1 := by norm_num

/-- The trace distance, as a `Prob` probability with value between 0 and 1. -/
def prob : Prob :=
  ⟨TrDistance ρ σ, ⟨ge_zero ρ σ, le_one ρ σ⟩⟩

/-- The trace distance is a symmetric quantity. -/
theorem symm : TrDistance ρ σ = TrDistance σ ρ := by
  dsimp [TrDistance]
  rw [← Matrix.traceNorm_eq_neg_self, neg_sub]

/-- The trace distance is equal to half the 1-norm of the eigenvalues of their difference . -/
theorem eq_abs_eigenvalues : TrDistance ρ σ = (1/2:ℝ) *
    ∑ i, abs ((ρ.Hermitian.sub σ.Hermitian).eigenvalues i) := by
  rw [TrDistance, Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues]

-- Fuchs–van de Graaf inequalities
-- Relation to classical TV distance
