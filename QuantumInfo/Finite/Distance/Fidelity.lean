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
open scoped Matrix ComplexOrder RealInnerProductSpace InnerProductSpace

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] (ρ σ : MState d)

namespace MState

/-- The fidelity of two quantum states. This is the quantum version of the Bhattacharyya
  coefficient. -/
def fidelity (ρ σ : MState d) : ℝ :=
  (σ.M.conj ρ.M.sqrt.mat).sqrt.trace

theorem fidelity_ge_zero : 0 ≤ fidelity ρ σ := by
  apply HermitianMat.trace_nonneg
  apply HermitianMat.sqrt_nonneg

theorem fidelity_le_one : fidelity ρ σ ≤ 1 := by
  unfold fidelity
  rw [HermitianMat.sqrt_eq_cfc_rpow_half, ← HermitianMat.rpow_eq_cfc]
  calc ((σ.M.conj ρ.M.sqrt.mat) ^ (1/2 : ℝ)).trace
      ≤ ((σ.M ^ (2/2 : ℝ)).trace ^ (1/2 : ℝ) *
         (ρ.M.sqrt ^ (2 : ℝ)).trace ^ (1/2 : ℝ)) ^ (2 * (1/2 : ℝ)) :=
        HermitianMat.trace_rpow_conj_le σ.nonneg (HermitianMat.sqrt_nonneg ρ.M)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    _ = 1 := by
        have h1 : (σ.M ^ (2/2 : ℝ)).trace = 1 := by
          rw [show (2:ℝ)/2 = 1 from by norm_num, HermitianMat.rpow_one]; exact σ.tr
        have h2 : (ρ.M.sqrt ^ (2 : ℝ)).trace = 1 := by
          rw [show ρ.M.sqrt = ρ.M ^ (1/2 : ℝ) from by
            rw [HermitianMat.sqrt_eq_cfc_rpow_half, ← HermitianMat.rpow_eq_cfc],
            ← HermitianMat.rpow_mul ρ.nonneg,
            show (1:ℝ)/2 * 2 = 1 from by norm_num, HermitianMat.rpow_one]; exact ρ.tr
        simp [h2]

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

/-- Fidelity can be rewritten as the trace norm of the product of square roots. -/
theorem fidelity_eq_traceNorm_sqrt_mul_sqrt (ρ σ : MState d) :
    fidelity ρ σ = (σ.M.sqrt.mat * ρ.M.sqrt.mat).traceNorm := by
  open MatrixOrder in
  rw [fidelity, HermitianMat.sqrt_eq_cfc_rpow_half, HermitianMat.trace_eq_re_trace,
    Matrix.traceNorm, CFC.sqrt_eq_rpow]
  change RCLike.re (((σ.M.conj ρ.M.sqrt.mat) ^ (1 / 2 : ℝ)).mat.trace) = _
  rw [show ((σ.M.conj ρ.M.sqrt.mat) ^ (1 / 2 : ℝ)).mat =
      ((σ.M.conj ρ.M.sqrt.mat).mat) ^ (1 / 2 : ℝ) by
    rw [HermitianMat.rpow_eq_cfc, HermitianMat.mat_cfc, CFC.rpow_eq_cfc_real (ha := by positivity)]]
  simp [HermitianMat.conj_apply_mat, Matrix.mul_assoc, (HermitianMat.sqrt_sq σ.nonneg).symm]

/-- The fidelity is 1 if and only if the two states are the same. -/
theorem fidelity_eq_one_iff_self : fidelity ρ σ = 1 ↔ ρ = σ := by
  constructor
  · intro h
    let A : Matrix d d ℂ := ρ.M.sqrt.mat
    let B : Matrix d d ℂ := σ.M.sqrt.mat
    let X : Matrix d d ℂ := B * A
    have hX : X.traceNorm = 1 := by
      simpa [X, A, B] using (fidelity_eq_traceNorm_sqrt_mul_sqrt ρ σ).symm.trans h
    obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_tr_U X).left
    have hUeq : RCLike.re ((U.1 * X).trace) = 1 := by
      rw [hU]; simpa using hX
    have hAherm : Matrix.conjTranspose A = A := by simp [A]
    have hBherm : Matrix.conjTranspose B = B := by simp [B]
    have hAeq : ρ.m = Matrix.conjTranspose A * A := by
      simpa [A, hAherm] using (HermitianMat.sqrt_sq ρ.nonneg).symm
    have hBeq : σ.m = Matrix.conjTranspose B * B := by
      simpa [B, hBherm] using (HermitianMat.sqrt_sq σ.nonneg).symm
    have hUB : Matrix.conjTranspose (U.1 * B) * (U.1 * B) = Matrix.conjTranspose B * B := by
      rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      simp [show Matrix.conjTranspose U.1 = star U.1 from rfl, ← Matrix.mul_assoc, U.2.1]
    let z : ℂ := (U.1 * X).trace
    have hz1 : (Matrix.conjTranspose A * (U.1 * B)).trace = z := by
      dsimp [z, X]; rw [hAherm, ← Matrix.mul_assoc, Matrix.trace_mul_cycle, Matrix.trace_mul_comm]
    have hz2 : (Matrix.conjTranspose (U.1 * B) * A).trace = conj z := by
      rw [show Matrix.conjTranspose (U.1 * B) * A =
          Matrix.conjTranspose (Matrix.conjTranspose A * (U.1 * B)) by
        simp [Matrix.conjTranspose_mul, hAherm, hBherm]]
      simpa [hz1] using Matrix.trace_conjTranspose (Matrix.conjTranspose A * (U.1 * B))
    have htraceM : (Matrix.conjTranspose (A - U.1 * B) * (A - U.1 * B)).trace = 0 := by
      have h_expand : (Matrix.conjTranspose (A - U.1 * B) * (A - U.1 * B)).trace =
          (Matrix.conjTranspose A * A).trace - (Matrix.conjTranspose A * (U.1 * B)).trace
            - (Matrix.conjTranspose (U.1 * B) * A).trace
            + (Matrix.conjTranspose (U.1 * B) * (U.1 * B)).trace := by
        simp [sub_eq_add_neg, Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul,
          Matrix.trace_add, Matrix.trace_neg, add_assoc, add_left_comm, add_comm]
      rw [h_expand, hz1, hz2, ← hAeq, ρ.tr', hUB, ← hBeq, σ.tr']
      have : z + conj z = 2 := by rw [RCLike.add_conj, hUeq]; push_cast; ring
      linear_combination -this
    have hAU : A = U.1 * B :=
      sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htraceM)
    exact MState.ext_m <| calc ρ.m = Matrix.conjTranspose A * A := hAeq
      _ = Matrix.conjTranspose (U.1 * B) * (U.1 * B) := by rw [hAU]
      _ = Matrix.conjTranspose B * B := hUB
      _ = σ.m := hBeq.symm
  · rintro rfl; exact fidelity_self_eq_one ρ

/-- The fidelity is a symmetric quantity. -/
theorem fidelity_symm : fidelity ρ σ = fidelity σ ρ := by
  simp only [fidelity]
  have expand : ∀ (a b : MState d), (a.M.conj b.M.sqrt.mat).mat =
      (b.M.sqrt.mat * a.M.sqrt.mat) * (a.M.sqrt.mat * b.M.sqrt.mat) := fun a b => by
    simp [HermitianMat.conj_apply_mat, b.M.sqrt.conjTranspose_mat,
      (HermitianMat.sqrt_sq a.nonneg).symm, Matrix.mul_assoc]
  have h_eig := ((σ.M.conj ρ.M.sqrt.mat).H.eigenvalues_eq_eigenvalues_iff
    (ρ.M.conj σ.M.sqrt.mat).H).mpr (by rw [expand σ ρ, expand ρ σ, Matrix.charpoly_mul_comm])
  show ((σ.M.conj ρ.M.sqrt.mat).cfc Real.sqrt).trace = ((ρ.M.conj σ.M.sqrt.mat).cfc Real.sqrt).trace
  rw [HermitianMat.trace_cfc_eq, HermitianMat.trace_cfc_eq, h_eig]

/-- The fidelity cannot decrease under the application of a channel. -/
theorem fidelity_channel_nondecreasing [DecidableEq d₂] (Λ : CPTPMap d d₂) : fidelity (Λ ρ) (Λ σ) ≥ fidelity ρ σ :=
  sorry

--TODO: Real.arccos ∘ fidelity forms a metric (triangle inequality), the Fubini–Study metric.
--Matches with classical (squared) Bhattacharyya coefficient
--Invariance under unitaries
--Uhlmann's theorem

end MState
