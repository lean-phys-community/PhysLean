/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Finite.CPTPMap

@[expose] public section

noncomputable section

open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] (ρ σ : MState d)

namespace MState

/-- The fidelity of two quantum states. This is the quantum version of the Bhattacharyya coefficient. -/
def fidelity (ρ σ : MState d) : ℝ :=
  (σ.M.conj ρ.M.sqrt.mat).sqrt.trace

theorem fidelity_ge_zero : 0 ≤ fidelity ρ σ := by
  apply HermitianMat.trace_nonneg
  apply HermitianMat.sqrt_nonneg

theorem fidelity_le_one : fidelity ρ σ ≤ 1 :=
  sorry --submultiplicativity of trace and sqrt

/-- The fidelity, as a `Prob` probability with value between 0 and 1. -/
def fidelity_prob : Prob :=
  ⟨fidelity ρ σ, ⟨fidelity_ge_zero ρ σ, fidelity_le_one ρ σ⟩⟩

/-- A state has perfect fidelity with itself. -/
theorem fidelity_self_eq_one : fidelity ρ ρ = 1 := by
  simp only [fidelity, HermitianMat.sqrt_eq_cfc_rpow_half]
  conv =>
    enter [1, 1, 1, 2]
    rw [← HermitianMat.cfc_id ρ.M]
  rw [HermitianMat.cfc_conj, ← HermitianMat.cfc_comp_apply]
  convert ρ.tr using 2
  convert ρ.M.cfc_id using 1
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
theorem fidelity_channel_nondecreasing [DecidableEq d₂] (Λ : CPTPMap d d₂) : fidelity (Λ ρ) (Λ σ) ≥ fidelity ρ σ :=
  sorry

--TODO: Real.arccos ∘ fidelity forms a metric (triangle inequality), the Fubini–Study metric.
--Matches with classical (squared) Bhattacharyya coefficient
--Invariance under unitaries
--Uhlmann's theorem

end MState
