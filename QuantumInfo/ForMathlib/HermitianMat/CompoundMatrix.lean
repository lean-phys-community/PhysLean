/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import QuantumInfo.ForMathlib.Majorization
public import QuantumInfo.ForMathlib.HermitianMat.Order

/-! # Compound matrices on `HermitianMat`

This file lifts the compound-matrix construction from
`QuantumInfo.ForMathlib.Majorization` to `HermitianMat`. The compound matrix of
a Hermitian matrix is again Hermitian, and inherits the natural spectral and
positivity properties of the original.
-/

@[expose] public section

open scoped AllOrdered

namespace HermitianMat

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The `k`-th compound matrix of a Hermitian matrix, packaged as a
`HermitianMat`. -/
noncomputable def compoundHermitian (A : HermitianMat d ℂ) (k : ℕ) :
    HermitianMat {S : Finset d // S.card = k} ℂ :=
  ⟨compoundMatrix A.mat k, (compoundMatrix_conjTranspose A.mat k).symm.trans <|
    congrArg (compoundMatrix · k) A.H⟩

/-- The eigenvalues of `compoundHermitian A k` are the products of eigenvalues
of `A` over `k`-subsets, up to an index permutation. -/
lemma compoundHermitian_eigenvalues (A : HermitianMat d ℂ) (k : ℕ) :
    ∃ σ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k},
      (compoundHermitian A k).H.eigenvalues ∘ σ =
        fun S => ∏ i : Fin k, A.H.eigenvalues (S.1.orderEmbOfFin S.2 i) :=
  (compoundHermitian A k).H.eigenvalues_eq_of_unitary_similarity_diagonal
    (U := compoundMatrix (Matrix.IsHermitian.eigenvectorUnitary A.H) k)
    (compoundMatrix_unitary _ (by simp [Matrix.unitaryGroup]) _)
    (by simpa [compoundHermitian, compoundMatrix_mul, compoundMatrix_diagonal, Matrix.mul_assoc,
        Matrix.star_eq_conjTranspose, ← compoundMatrix_conjTranspose] using
      congrArg (fun x => compoundMatrix x k) (Matrix.IsHermitian.spectral_theorem A.H))

/-- `compoundHermitian` preserves positive semidefiniteness. -/
lemma compoundHermitian_nonneg (A : HermitianMat d ℂ) (hA : 0 ≤ A) (k : ℕ) :
    0 ≤ compoundHermitian A k := by
  rw [HermitianMat.zero_le_iff, (compoundHermitian A k).H.posSemidef_iff_eigenvalues_nonneg]
  obtain ⟨σ, hσ⟩ := compoundHermitian_eigenvalues A k
  intro S
  rw [show (compoundHermitian A k).H.eigenvalues S = _ by
    simpa [Function.comp_def] using congrFun hσ (σ.symm S)]
  exact Finset.prod_nonneg fun _ _ => A.eigenvalues_nonneg hA _

/-- `compoundHermitian` distributes over `HermitianMat.conj`: the compound of
`A.conj B` equals the conjugation of `compoundHermitian A k` by `compoundMatrix B k`. -/
lemma compoundHermitian_conj (A : HermitianMat d ℂ) (B : Matrix d d ℂ) (k : ℕ) :
    compoundHermitian (A.conj B) k =
      (compoundHermitian A k).conj (compoundMatrix B k) :=
  Subtype.ext <| by simp [compoundHermitian, HermitianMat.conj_apply_mat, compoundMatrix_mul,
    ← compoundMatrix_conjTranspose, Matrix.mul_assoc]

end HermitianMat
