/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import QuantumInfo.Finite.CPTPMap.CPTP

@[expose] public section

/-! # Classical-to-quantum preparation channels

This file defines the CPTP map that prepares a quantum state depending on a classical input.
-/

noncomputable section
universe u

open ComplexOrder

namespace CPTPMap

variable {d : Type u} [Fintype d] [DecidableEq d]

/-- The classical-to-quantum preparation channel associated to a family of output states. -/
def cqPrepare {κ : Type u} [Fintype κ] [DecidableEq κ] (τ : κ → MState d) :
    CPTPMap κ d :=
  let M : Matrix (d × κ) (d × κ) ℂ :=
    (∑ i, HermitianMat.kronecker (τ i).M (MState.ofClassical (.constant i)).M).mat
  CPTP_of_choi_PSD_Tr
    (M := M)
    (by
      change ((∑ i,
        HermitianMat.kronecker (τ i).M (MState.ofClassical (.constant i)).M).mat).PosSemidef
      have hnonneg : 0 ≤
          ∑ i, HermitianMat.kronecker (τ i).M (MState.ofClassical (.constant i)).M :=
        Finset.sum_nonneg fun i _ =>
          HermitianMat.kronecker_nonneg (τ i).nonneg (MState.ofClassical (.constant i)).nonneg
      exact HermitianMat.zero_le_iff.mp hnonneg)
    (by
      let prepMap : MatrixMap κ d ℂ := {
        toFun X := fun b₁ b₂ => ∑ i, X i i * (τ i).m b₁ b₂
        map_add' X Y := by
          ext b₁ b₂
          simp [Matrix.add_apply, Finset.sum_add_distrib, add_mul]
        map_smul' c X := by
          ext b₁ b₂
          simp [Matrix.smul_apply, Finset.mul_sum, mul_assoc] }
      have hchoi : prepMap.choi_matrix = M := by
        ext ⟨b₁, a₁⟩ ⟨b₂, a₂⟩
        simp only [MatrixMap.choi_matrix, prepMap, Matrix.single, M,
          HermitianMat.mat_finset_sum, Matrix.sum_apply]
        refine Finset.sum_congr rfl fun x _ => ?_
        show (if a₁ = x ∧ a₂ = x then 1 else 0) * (τ x).m b₁ b₂ =
          (τ x).m b₁ b₂ *
            (HermitianMat.diagonal ℂ
              (fun x₁ => ((ProbDistribution.constant x) x₁ : ℝ))).mat a₁ a₂
        rw [HermitianMat.diagonal_mat]
        aesop (add simp [Matrix.diagonal, ProbDistribution.constant_eq, Ne.symm])
      rw [← hchoi, ← MatrixMap.IsTracePreserving_iff_trace_choi]
      intro X
      change ∑ x, ∑ i, X i i * (τ i).m x x = X.trace
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.mul_sum, show ∑ x, (τ i).m x x = 1 by
        simpa [Matrix.trace] using (MState.tr' (ρ := τ i))]
      simp [Matrix.diag_apply])

/-- Applying a preparation channel to a classical distribution gives the corresponding mixture. -/
theorem cqPrepare_apply_ofClassical {κ : Type u} [Fintype κ] [DecidableEq κ]
    (τ : κ → MState d) (dist : ProbDistribution κ) :
    (cqPrepare (d := d) τ (MState.ofClassical dist)).m =
      ∑ i, (dist i : ℝ) • (τ i).m := by
  let prepMap : MatrixMap κ d ℂ := {
    toFun X := fun b₁ b₂ => ∑ i, X i i * (τ i).m b₁ b₂
    map_add' X Y := by
      ext b₁ b₂
      simp [Matrix.add_apply, Finset.sum_add_distrib, add_mul]
    map_smul' c X := by
      ext b₁ b₂
      simp [Matrix.smul_apply, Finset.mul_sum, mul_assoc] }
  have hchoi : prepMap.choi_matrix =
      (∑ i, HermitianMat.kronecker (τ i).M (MState.ofClassical (.constant i)).M).mat := by
    ext ⟨b₁, a₁⟩ ⟨b₂, a₂⟩
    simp only [MatrixMap.choi_matrix, prepMap, Matrix.single,
      HermitianMat.mat_finset_sum, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    show (if a₁ = x ∧ a₂ = x then 1 else 0) * (τ x).m b₁ b₂ =
      (τ x).m b₁ b₂ *
        (HermitianMat.diagonal ℂ
          (fun x₁ => ((ProbDistribution.constant x) x₁ : ℝ))).mat a₁ a₂
    rw [HermitianMat.diagonal_mat]
    aesop (add simp [Matrix.diagonal, ProbDistribution.constant_eq, Ne.symm])
  change MatrixMap.of_choi_matrix ((∑ i, HermitianMat.kronecker (τ i).M
      (MState.ofClassical (.constant i)).M).mat) (MState.ofClassical dist).m = _
  rw [← hchoi, MatrixMap.choi_map_inv]
  ext b₁ b₂
  change ∑ i, (Matrix.diagonal fun x => ((dist x : Prob) : ℂ)) i i * (τ i).m b₁ b₂ =
    (∑ i, (dist i : ℝ) • (τ i).m) b₁ b₂
  rw [Matrix.sum_apply]
  simp [Matrix.smul_apply]

end CPTPMap
