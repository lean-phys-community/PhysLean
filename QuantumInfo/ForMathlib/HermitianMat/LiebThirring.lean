/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Rpow
import QuantumInfo.ForMathlib.Majorization

/-! # The Araki-Lieb-Thirring inequality

For positive semidefinite `A` and `B` and `0 < r ≤ 1`,
`Tr[Bʳ Aʳ Bʳ] ≤ Tr[(B A B)ʳ]`.

The proof goes through weak log-majorization. Writing `T = Bʳ Aʳ Bʳ` and `P = B A B`, the `k`-th
compound (exterior power) matrices satisfy `Cₖ(T) = Cₖ(B)ʳ Cₖ(A)ʳ Cₖ(B)ʳ` and
`Cₖ(P) = Cₖ(B) Cₖ(A) Cₖ(B)`, and the largest eigenvalue of a compound matrix is the product of the
`k` largest eigenvalues of the original. So the whole inequality reduces to the `k = 1` statement
`λ_max(Bʳ Aʳ Bʳ) ≤ λ_max(B A B)ʳ`, i.e. `HermitianMat.conj_rpow_le_smul_one`: that one is proved by
conjugating `B A B ≤ c • 1` with `B⁻¹` to get `A ≤ c • B⁻²`, applying Loewner-Heinz, and
conjugating back with `Bʳ`.

Along the way this file sets up:
* `HermitianMat.eigMax`, the largest eigenvalue;
* `HermitianMat.compound`, the `k`-th compound matrix of a Hermitian matrix, and its behaviour
  under `conj` and `rpow`.
-/

noncomputable section

open Finset Matrix
open scoped AllOrdered ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

namespace HermitianMat

variable {A B : HermitianMat d ℂ} {c : ℝ}

theorem le_smul_one_iff_eigenvalues_le : A ≤ c • 1 ↔ ∀ i, A.H.eigenvalues i ≤ c := by
  have h : c • (1 : HermitianMat d ℂ) - A = A.cfc (fun x ↦ c - x) := by
    simp [cfc_sub_apply (f := fun _ ↦ c) (g := fun x ↦ x)]
  rw [← sub_nonneg, h, cfc_nonneg_iff]
  simp [sub_nonneg]

/-- The spectral decomposition of a Hermitian matrix, as a `HermitianMat`. -/
theorem eq_conj_diagonal_eigenvalues (A : HermitianMat d ℂ) :
    A = (diagonal ℂ A.H.eigenvalues).conj A.H.eigenvectorUnitary.val := by
  ext1
  rw [conj_apply_mat, diagonal_mat]
  exact A.H.spectral_theorem

/-- For a positive semidefinite matrix, the singular values are a permutation of the
eigenvalues. -/
theorem exists_equiv_singularValues_eq_eigenvalues (hA : 0 ≤ A) :
    ∃ σ : d ≃ d, ∀ i, singularValues A.mat (σ i) = A.H.eigenvalues i := by
  have hU : A.H.eigenvectorUnitary.val.conjTranspose * A.H.eigenvectorUnitary.val = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using A.H.eigenvectorUnitary.2.1
  have hsq : A.matᴴ * A.matᴴᴴ =
      A.H.eigenvectorUnitary.val *
        Matrix.diagonal (fun i ↦ (RCLike.ofReal ((A.H.eigenvalues i) ^ 2) : ℂ)) *
        A.H.eigenvectorUnitary.val.conjTranspose := by
    have hspec : A.mat = A.H.eigenvectorUnitary.val *
        Matrix.diagonal (fun i ↦ (RCLike.ofReal (A.H.eigenvalues i) : ℂ)) *
        A.H.eigenvectorUnitary.val.conjTranspose := A.H.spectral_theorem
    rw [Matrix.conjTranspose_conjTranspose, A.H]
    conv_lhs => rw [hspec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc _ A.H.eigenvectorUnitary.val, hU, Matrix.one_mul,
      ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
    congr! 4 with i
    push_cast
    ring
  obtain ⟨σ, hσ⟩ := Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal
    (isHermitian_mul_conjTranspose_self A.mat.conjTranspose) A.H.eigenvectorUnitary.2 hsq
  refine ⟨σ, fun i ↦ ?_⟩
  have := congrFun hσ i
  simp only [Function.comp_apply] at this
  rw [singularValues, this, Real.sqrt_sq]
  exact (zero_le_iff.mp hA).eigenvalues_nonneg i

/-! ## The largest eigenvalue -/

section eigMax
variable [Nonempty d]

variable (A) in
/-- The largest eigenvalue of a Hermitian matrix. -/
def eigMax : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty A.H.eigenvalues

theorem le_eigMax (i : d) : A.H.eigenvalues i ≤ A.eigMax :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem le_eigMax_smul_one : A ≤ A.eigMax • 1 :=
  le_smul_one_iff_eigenvalues_le.mpr fun i ↦ le_eigMax i

theorem eigMax_le_of_le_smul_one (h : A ≤ c • 1) : A.eigMax ≤ c :=
  Finset.sup'_le _ _ fun i _ ↦ le_smul_one_iff_eigenvalues_le.mp h i

theorem eigMax_nonneg (hA : 0 ≤ A) : 0 ≤ A.eigMax :=
  ((zero_le_iff.mp hA).eigenvalues_nonneg (Classical.arbitrary d)).trans (le_eigMax _)

theorem singularValuesSorted_zero_eq_eigMax (hA : 0 ≤ A) (h : 0 < Fintype.card d) :
    singularValuesSorted A.mat ⟨0, h⟩ = A.eigMax := by
  obtain ⟨σ, hσ⟩ := exists_equiv_singularValues_eq_eigenvalues hA
  rw [singularValuesSorted_zero_eq_sup]
  refine le_antisymm (Finset.sup'_le _ _ fun i _ ↦ ?_) (Finset.sup'_le _ _ fun i _ ↦ ?_)
  · have h' := hσ (σ.symm i)
    rw [Equiv.apply_symm_apply] at h'
    exact h' ▸ le_eigMax _
  · exact hσ i ▸ Finset.le_sup' _ (Finset.mem_univ (σ i))

end eigMax

theorem sum_eigenvalues_rpow_eq_sum_sorted (hA : 0 ≤ A) (p : ℝ) :
    ∑ i, A.H.eigenvalues i ^ p =
      ∑ i : Fin (Fintype.card d), singularValuesSorted A.mat i ^ p := by
  rw [← sum_singularValues_rpow_eq_sum_sorted]
  obtain ⟨σ, hσ⟩ := exists_equiv_singularValues_eq_eigenvalues hA
  exact Fintype.sum_equiv σ _ _ fun i ↦ by rw [hσ]

end HermitianMat

/-! ## Compound matrices of Hermitian matrices -/

section compound

variable (k : ℕ)

/-- The compound matrix of the identity is the identity. -/
lemma compoundMatrix_one : compoundMatrix (1 : Matrix d d ℂ) k = 1 := by
  rw [show (1 : Matrix d d ℂ) = Matrix.diagonal (fun _ ↦ (1 : ℂ)) by simp,
    compoundMatrix_diagonal]
  simp

/-- The compound matrix of a unitary matrix is unitary. -/
lemma compoundMatrix_unitary {U : Matrix d d ℂ} (hU : U ∈ Matrix.unitaryGroup d ℂ) :
    compoundMatrix U k ∈ Matrix.unitaryGroup {S : Finset d // S.card = k} ℂ := by
  have h1 : (compoundMatrix U k)ᴴ * compoundMatrix U k = 1 := by
    rw [← compoundMatrix_conjTranspose, ← compoundMatrix_mul,
      show Uᴴ * U = 1 by simpa [Matrix.star_eq_conjTranspose] using hU.1]
    exact compoundMatrix_one k
  refine ⟨?_, ?_⟩
  · simpa [Matrix.star_eq_conjTranspose] using h1
  · simpa [Matrix.star_eq_conjTranspose] using mul_eq_one_comm.mp h1

namespace HermitianMat

variable {A : HermitianMat d ℂ}

variable (A) in
/-- The `k`-th compound matrix of a Hermitian matrix; it is again Hermitian. -/
def compound : HermitianMat {S : Finset d // S.card = k} ℂ :=
  ⟨compoundMatrix A.mat k, by
    show (compoundMatrix A.mat k)ᴴ = compoundMatrix A.mat k
    rw [← compoundMatrix_conjTranspose, A.H]⟩

@[simp]
theorem compound_mat : (A.compound k).mat = compoundMatrix A.mat k :=
  rfl

theorem compound_conj (M : Matrix d d ℂ) :
    (A.conj M).compound k = (A.compound k).conj (compoundMatrix M k) := by
  ext1
  simp only [compound_mat, conj_apply_mat, compoundMatrix_mul, compoundMatrix_conjTranspose]

theorem compound_diagonal (f : d → ℝ) :
    (diagonal ℂ f).compound k = diagonal ℂ
      (fun S : {S : Finset d // S.card = k} ↦ ∏ i : Fin k, f (S.1.orderEmbOfFin S.2 i)) := by
  ext1
  simp only [compound_mat, diagonal_mat, compoundMatrix_diagonal]
  congr! 4 with S
  push_cast
  rfl

/-- The compound matrix, written out in terms of the spectral decomposition. -/
theorem compound_eq_conj (A : HermitianMat d ℂ) :
    A.compound k = (diagonal ℂ (fun S : {S : Finset d // S.card = k} ↦
      ∏ i : Fin k, A.H.eigenvalues (S.1.orderEmbOfFin S.2 i))).conj
      (compoundMatrix A.H.eigenvectorUnitary.val k) := by
  conv_lhs => rw [A.eq_conj_diagonal_eigenvalues]
  rw [compound_conj, compound_diagonal]

/-- The eigenvalues of `Cₖ(A)` are the `k`-fold products of eigenvalues of `A`. -/
theorem compound_eigenvalues (A : HermitianMat d ℂ) :
    ∃ σ : {S : Finset d // S.card = k} ≃ {S : Finset d // S.card = k},
      (A.compound k).H.eigenvalues ∘ σ =
        fun S ↦ ∏ i : Fin k, A.H.eigenvalues (S.1.orderEmbOfFin S.2 i) := by
  refine Matrix.IsHermitian.eigenvalues_eq_of_unitary_similarity_diagonal _
    (compoundMatrix_unitary k A.H.eigenvectorUnitary.2) ?_
  rw [compound_eq_conj]
  simp [diagonal_mat]

theorem compound_nonneg (hA : 0 ≤ A) : 0 ≤ A.compound k := by
  obtain ⟨σ, hσ⟩ := compound_eigenvalues k A
  rw [zero_le_iff, (A.compound k).H.posSemidef_iff_eigenvalues_nonneg]
  intro S
  have h' := congrFun hσ (σ.symm S)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h'
  exact h' ▸ Finset.prod_nonneg fun i _ ↦ (zero_le_iff.mp hA).eigenvalues_nonneg _

theorem compound_posDef (hA : A.mat.PosDef) : (A.compound k).mat.PosDef := by
  obtain ⟨σ, hσ⟩ := compound_eigenvalues k A
  rw [(A.compound k).H.posDef_iff_eigenvalues_pos]
  intro S
  have h' := congrFun hσ (σ.symm S)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at h'
  exact h' ▸ Finset.prod_pos fun i _ ↦ hA.eigenvalues_pos _

theorem compound_rpow (hA : 0 ≤ A) {s : ℝ} :
    (A ^ s).compound k = (A.compound k) ^ s := by
  have hev : ∀ i, 0 ≤ A.H.eigenvalues i := (zero_le_iff.mp hA).eigenvalues_nonneg
  set CU : Matrix.unitaryGroup {S : Finset d // S.card = k} ℂ :=
    ⟨compoundMatrix A.H.eigenvectorUnitary.val k,
      compoundMatrix_unitary k A.H.eigenvectorUnitary.2⟩ with hCU
  have hAs : A ^ s = (diagonal ℂ (fun i ↦ A.H.eigenvalues i ^ s)).conj
      A.H.eigenvectorUnitary.val := by
    conv_lhs => rw [A.eq_conj_diagonal_eigenvalues]
    rw [rpow_conj_unitary, rpow_diagonal]
  rw [hAs, compound_conj, compound_diagonal, compound_eq_conj,
    show (compoundMatrix A.H.eigenvectorUnitary.val k) = CU.val from rfl,
    rpow_conj_unitary, rpow_diagonal]
  congr! 2
  funext S
  exact Real.finset_prod_rpow _ _ (fun i _ ↦ hev _) s

end HermitianMat
end compound

namespace HermitianMat

/-! ## The `k = 1` operator inequality -/

section core

variable {A B : HermitianMat d ℂ} {c r : ℝ}

theorem conj_real_smul (x : ℝ) (X : HermitianMat d ℂ) (M : Matrix d d ℂ) :
    (x • X).conj M = x • X.conj M := by
  ext1
  simp

theorem smul_rpow (hA : 0 ≤ A) (hc : 0 ≤ c) : (c • A) ^ r = c ^ r • A ^ r := by
  have h1 : c • A = A.cfc (fun x ↦ c * x) := (cfc_const_mul_id A c).symm
  rw [h1, rpow_eq_cfc, ← cfc_comp_apply, rpow_eq_cfc, ← cfc_const_mul]
  exact cfc_congr_of_nonneg hA fun x hx ↦ Real.mul_rpow hc hx

/-- The core operator inequality behind Araki-Lieb-Thirring: if `B A B ≤ c • 1`, then
`Bʳ Aʳ Bʳ ≤ cʳ • 1`, for `0 < r ≤ 1`. -/
theorem conj_rpow_le_smul_one (hA : 0 ≤ A) (hB : B.mat.PosDef) (hc : 0 ≤ c)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (h : A.conj B.mat ≤ c • 1) :
    (A ^ r).conj (B ^ r).mat ≤ c ^ r • 1 := by
  have hB0 : (0 : HermitianMat d ℂ) ≤ B := zero_le_iff.mpr hB.posSemidef
  have hinv1 : (B ^ (-1 : ℝ)).mat * B.mat = 1 := by
    have h1 := rpow_neg_mul_rpow_self hB (1 : ℝ)
    rwa [rpow_one] at h1
  have hone : (1 : HermitianMat d ℂ).conj ((B ^ (-1 : ℝ)).mat) = B ^ (-2 : ℝ) := by
    ext1
    have h2 : ((-1 : ℝ)) + (-1 : ℝ) ≠ 0 := by norm_num
    simp only [conj_apply_mat, mat_one, Matrix.mul_one]
    rw [(B ^ (-1 : ℝ)).H, show (-2 : ℝ) = -1 + -1 by norm_num, mat_rpow_add hB0 h2]
  have hstep1 : A ≤ c • B ^ (-2 : ℝ) := by
    have h3 := conj_mono (M := (B ^ (-1 : ℝ)).mat) h
    rwa [conj_conj, hinv1, conj_one, conj_real_smul, hone] at h3
  have hstep2 : A ^ r ≤ c ^ r • B ^ (-2 * r : ℝ) := by
    have h4 := rpow_le_rpow_of_le hA hstep1 hr0 hr1
    rwa [smul_rpow (rpow_nonneg hB0) hc, ← rpow_mul hB0] at h4
  have hne : r + -2 * r ≠ 0 := by intro hh; linarith
  have hfinal : (B ^ (-2 * r : ℝ)).conj ((B ^ r).mat) = 1 := by
    ext1
    simp only [conj_apply_mat]
    rw [(B ^ r).H, ← mat_rpow_add hB0 hne, show r + -2 * r = -r by ring,
      rpow_neg_mul_rpow_self hB r, mat_one]
  have h5 := conj_mono (M := (B ^ r).mat) hstep2
  rwa [conj_real_smul, hfinal] at h5

end core

/-! ## Araki-Lieb-Thirring -/

section ArakiLiebThirring

variable {A B : HermitianMat d ℂ} {r : ℝ}

/-- The Araki-Lieb-Thirring inequality, for positive definite `B`. -/
theorem lieb_thirring_le_one_of_posDef (hA : 0 ≤ A) (hB : B.mat.PosDef)
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ((A ^ r).conj (B ^ r).mat).trace ≤ ((A.conj B.mat) ^ r).trace := by
  have hB0 : (0 : HermitianMat d ℂ) ≤ B := zero_le_iff.mpr hB.posSemidef
  set T : HermitianMat d ℂ := (A ^ r).conj (B ^ r).mat with hT
  set P : HermitianMat d ℂ := A.conj B.mat with hP
  have hT0 : 0 ≤ T := conj_nonneg _ (rpow_nonneg hA)
  have hP0 : 0 ≤ P := conj_nonneg _ hA
  have hTtr : T.trace = ∑ i : Fin (Fintype.card d), singularValuesSorted T.mat i := by
    rw [← T.sum_eigenvalues_eq_trace]
    simpa using sum_eigenvalues_rpow_eq_sum_sorted hT0 1
  have hPtr : (P ^ r).trace = ∑ i : Fin (Fintype.card d), singularValuesSorted P.mat i ^ r := by
    rw [trace_rpow_eq_sum, sum_eigenvalues_rpow_eq_sum_sorted hP0]
  rw [hTtr, hPtr]
  refine weak_log_maj_sum_le (fun i ↦ singularValuesSorted_nonneg _ i)
    (fun i ↦ Real.rpow_nonneg (singularValuesSorted_nonneg _ i) r)
    (singularValuesSorted_antitone _)
    (rpow_antitone_of_nonneg_antitone (singularValuesSorted_antitone _)
      (fun i ↦ singularValuesSorted_nonneg _ i) hr0) ?_
  intro k hk
  haveI : Nonempty {S : Finset d // S.card = k} := by
    obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset d)) (n := k)
      (by simpa using hk)
    exact ⟨⟨S, hS⟩⟩
  have hxk : ∏ i : Fin k, singularValuesSorted T.mat ⟨i.val, by omega⟩
      = (T.compound k).eigMax := by
    rw [prod_singularValuesSorted_eq_compoundSV T.mat k hk]
    exact singularValuesSorted_zero_eq_eigMax (compound_nonneg k hT0) _
  have hyk : ∏ i : Fin k, singularValuesSorted P.mat ⟨i.val, by omega⟩
      = (P.compound k).eigMax := by
    rw [prod_singularValuesSorted_eq_compoundSV P.mat k hk]
    exact singularValuesSorted_zero_eq_eigMax (compound_nonneg k hP0) _
  have hcompT : T.compound k = ((A.compound k) ^ r).conj (((B.compound k) ^ r).mat) := by
    rw [hT, compound_conj, compound_rpow k hA, ← compound_mat, compound_rpow k hB0]
  have hcompP : P.compound k = (A.compound k).conj ((B.compound k).mat) := by
    rw [hP, compound_conj, compound_mat]
  have hcore : (T.compound k).eigMax ≤ ((P.compound k).eigMax) ^ r := by
    rw [hcompT]
    refine eigMax_le_of_le_smul_one (conj_rpow_le_smul_one (compound_nonneg k hA)
      (compound_posDef k hB) (eigMax_nonneg (compound_nonneg k hP0)) hr0 hr1 ?_)
    rw [← hcompP]
    exact le_eigMax_smul_one
  have hprod : ∏ i : Fin k, (singularValuesSorted P.mat ⟨i.val, by omega⟩) ^ r
      = ((P.compound k).eigMax) ^ r := by
    rw [← hyk]
    exact Real.finset_prod_rpow _ _ (fun i _ ↦ singularValuesSorted_nonneg _ _) r
  rw [hxk, hprod]
  exact hcore

/-- An inequality of Lieb-Thirring type. For 0 < r ≤ 1:
  `Tr[B^r A^r B^r] ≤ Tr[(B A B)^r]`.
-/
theorem lieb_thirring_le_one (hA : 0 ≤ A) (hB : 0 ≤ B) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ((A ^ r).conj (B ^ r).mat).trace ≤ ((A.conj B.mat) ^ r).trace := by
  have hrp : Continuous (fun M : HermitianMat d ℂ ↦ M ^ r) := rpow_const_continuous hr0.le
  have hlin : Continuous (fun ε : ℝ ↦ B + ε • (1 : HermitianMat d ℂ)) := by fun_prop
  set f : ℝ → ℝ := fun ε ↦ ((A ^ r).conj ((B + ε • 1) ^ r).mat).trace
    - ((A.conj (B + ε • 1).mat) ^ r).trace with hf
  have hcont : Continuous f := by
    refine Continuous.sub ?_ ?_
    · exact trace_Continuous.comp ((continuous_conj (A ^ r)).comp
        (continuous_mat.comp (hrp.comp hlin)))
    · exact trace_Continuous.comp (hrp.comp ((continuous_conj A).comp
        (continuous_mat.comp hlin)))
  have hneg : ∀ ε ∈ Set.Ioi (0 : ℝ), f ε ≤ 0 := by
    intro ε hε
    have := lieb_thirring_le_one_of_posDef hA (posDef_add_smul_one hB hε) hr0 hr1
    simp only [hf]
    linarith
  have h0 : f 0 ≤ 0 := by
    refine le_of_tendsto (hcont.continuousWithinAt (s := Set.Ioi (0 : ℝ)) (x := 0)) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using hneg ε hε
  simp only [hf, zero_smul, add_zero] at h0
  linarith

end ArakiLiebThirring

end HermitianMat
