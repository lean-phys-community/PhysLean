/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap

noncomputable section

open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [FiniteDimensional ℂ E]

namespace DensityOp

/-- The fidelity of two quantum states. This is the quantum version of the Bhattacharyya
coefficient.

This makes no reference to a basis; `fidelity_eq_matrix` is the matrix analogue. -/
def fidelity (ρ σ : DensityOp E) : ℝ :=
  (σ.op.conj ρ.op.sqrt.op).sqrt.trace

variable (ρ σ : DensityOp E)

/-- **Matrix analogue of `DensityOp.fidelity`.** -/
theorem fidelity_eq_matrix {ι : Type*} [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι] :
    fidelity ρ σ = ((σ.M : HermitianMat ι ℂ).conj (ρ.M : HermitianMat ι ℂ).sqrt.mat).sqrt.trace := by
  have h : StdBasis.toMat ℂ E ι ρ.op.sqrt.op = ((ρ.M : HermitianMat ι ℂ).sqrt).mat := by
    rw [← HermitianOp.toMat_mat (ι := ι), HermitianOp.toMat_sqrt]
    rfl
  rw [fidelity, ← HermitianOp.trace_toMat (ι := ι), HermitianOp.toMat_sqrt,
    HermitianOp.toMat_conj, h]
  rfl

theorem fidelity_ge_zero : 0 ≤ fidelity ρ σ :=
  HermitianOp.trace_nonneg (HermitianOp.sqrt_nonneg _)

theorem fidelity_le_one : fidelity ρ σ ≤ 1 :=
  sorry --submultiplicativity of trace and sqrt

/-- The fidelity, as a `Prob` probability with value between 0 and 1. -/
def fidelity_prob : Prob :=
  ⟨fidelity ρ σ, ⟨fidelity_ge_zero ρ σ, fidelity_le_one ρ σ⟩⟩

/-- A state has perfect fidelity with itself. -/
theorem fidelity_self_eq_one : fidelity ρ ρ = 1 := by
  let _ : StdBasis ℂ E (Fin (Module.finrank ℂ E)) := StdBasis.some ℂ E
  rw [fidelity_eq_matrix (ι := Fin (Module.finrank ℂ E))]
  simp only [HermitianMat.sqrt_eq_cfc_rpow_half]
  conv =>
    enter [1, 1, 1, 2]
    rw [← HermitianMat.cfc_id (ρ.M : HermitianMat _ ℂ)]
  rw [HermitianMat.cfc_conj, ← HermitianMat.cfc_comp_apply]
  convert ρ.tr using 2
  convert (ρ.M : HermitianMat _ ℂ).cfc_id using 1
  apply HermitianMat.cfc_congr_of_nonneg ρ.nonneg
  intro x hx
  simp only [one_div, Pi.mul_apply, id_eq, Pi.pow_apply]
  rw [← Real.rpow_two, Real.rpow_inv_rpow hx (by norm_num), ← sq, ← Real.rpow_two]
  exact Real.rpow_rpow_inv hx (by norm_num)

/-- The fidelity is 1 if and only if the two states are the same. -/
theorem fidelity_eq_one_iff_self : fidelity ρ σ = 1 ↔ ρ = σ :=
  ⟨by sorry,
  fun h ↦ h ▸ fidelity_self_eq_one ρ⟩

/-- The fidelity is a symmetric quantity. -/
theorem fidelity_symm : fidelity ρ σ = fidelity σ ρ :=
  sorry --break into sqrts

/-- The fidelity cannot decrease under the application of a channel. -/
theorem fidelity_channel_nondecreasing [DecidableEq d₂] (ρ σ : MState d) (Λ : CPTPMap d d₂) :
    fidelity (Λ ρ) (Λ σ) ≥ fidelity ρ σ :=
  sorry

--TODO: Real.arccos ∘ fidelity forms a metric (triangle inequality), the Fubini–Study metric.
--Matches with classical (squared) Bhattacharyya coefficient
--Invariance under unitaries
--Uhlmann's theorem

end DensityOp
