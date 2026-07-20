/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Sqrt
public import QuantumInfo.ForMathlib.HermitianMat.LiebConcavity

@[expose] public section

noncomputable section

variable {d : Type*}
variable [Fintype d] [DecidableEq d]
variable {𝕜 : Type*} [RCLike 𝕜]

open HermitianMat
open scoped InnerProductSpace RealInnerProductSpace Topology

namespace HermitianMat

/--
The trace of cfc(g, A) is invariant under unitary conjugation of A.
Follows from `cfc_conj_unitary` and `trace_conj_unitary`.
-/
lemma trace_cfc_conj_unitary (A : HermitianMat d ℂ) (g : ℝ → ℝ) (U : 𝐔[d]) :
    ((A.conj U.val).cfc g).trace = (A.cfc g).trace := by
  rw [cfc_conj_unitary, trace_conj_unitary]

/--
Peierls inequality: for a convex function g, the sum of g applied to the
diagonal entries of a Hermitian matrix is at most the trace of g(A).
This follows from Jensen's inequality applied to the spectral decomposition.
-/
theorem peierls_inequality (A : HermitianMat d ℂ) (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g) :
    ∑ i, g ((A.mat i i).re) ≤ (A.cfc g).trace := by
  have hdiag : ∀ i, (A.mat i i).re =
      ∑ j, ‖A.H.eigenvectorUnitary.val i j‖ ^ 2 • A.H.eigenvalues j := fun i => by
    have h := congr_arg (fun M => (M.mat i i).re) A.eq_conj_diagonal
    simp only [conj_apply_mat, diagonal_mat, Matrix.mul_apply, Matrix.diagonal_apply] at h
    simpa [Complex.sq_norm, Complex.normSq_apply, mul_comm, mul_left_comm, mul_assoc] using h
  rw [trace_cfc_eq]
  calc ∑ i, g ((A.mat i i).re)
      ≤ ∑ i, ∑ j, ‖A.H.eigenvectorUnitary.val i j‖ ^ 2 • g (A.H.eigenvalues j) :=
        Finset.sum_le_sum fun i _ => (hdiag i).symm ▸ hg.map_sum_le (fun _ _ => by positivity)
          (Matrix.unitary_row_sum_norm_sq _ A.H.eigenvectorUnitary.2.2 i) fun _ _ => trivial
    _ = ∑ j, g (A.H.eigenvalues j) := by
        rw [Finset.sum_comm]
        simp only [← Finset.sum_smul, Matrix.unitaryGroup_row_norm, one_smul]

theorem peierls_inequality_ici (A : HermitianMat d ℂ) (g : ℝ → ℝ) (hg : ConvexOn ℝ (Set.Ici 0) g)
  (hA : 0 ≤ A) :
    ∑ i, g ((A.mat i i).re) ≤ (A.cfc g).trace := by
  have hdiag : ∀ i, (A.mat i i).re =
      ∑ j, ‖A.H.eigenvectorUnitary.val i j‖ ^ 2 • A.H.eigenvalues j := fun i => by
    have h := congr_arg (fun M => (M.mat i i).re) A.eq_conj_diagonal
    simp only [conj_apply_mat, diagonal_mat, Matrix.mul_apply, Matrix.diagonal_apply] at h
    simpa [Complex.sq_norm, Complex.normSq_apply, mul_comm, mul_left_comm, mul_assoc] using h
  rw [trace_cfc_eq]
  calc ∑ i, g ((A.mat i i).re)
      ≤ ∑ i, ∑ j, ‖A.H.eigenvectorUnitary.val i j‖ ^ 2 • g (A.H.eigenvalues j) :=
        Finset.sum_le_sum fun i _ => (hdiag i).symm ▸ hg.map_sum_le (fun _ _ => by positivity)
          (Matrix.unitary_row_sum_norm_sq _ A.H.eigenvectorUnitary.2.2 i)
          fun j _ => A.eigenvalues_nonneg hA j
    _ = ∑ j, g (A.H.eigenvalues j) := by
        rw [Finset.sum_comm]
        simp only [← Finset.sum_smul, Matrix.unitaryGroup_row_norm, one_smul]

/--
Joint convexity of the trace functional: for a convex function g,
the map A ↦ tr(g(A)) is convex on the space of Hermitian matrices.
-/
theorem trace_function_convex_univ (g : ℝ → ℝ) (hg : ConvexOn ℝ Set.univ g) :
    ConvexOn ℝ Set.univ (fun A : HermitianMat d ℂ => (A.cfc g).trace) := by
  refine ⟨convex_univ, fun A _ B _ a b ha hb hab => ?_⟩
  set C : HermitianMat d ℂ := a • A + b • B with hC
  set V : 𝐔[d] := star C.H.eigenvectorUnitary with hV
  have hCd : C.conj V.val = diagonal ℂ C.H.eigenvalues := by
    nth_rewrite 1 [C.eq_conj_diagonal]
    simp [conj_conj, hV, C.H.eigenvectorUnitary.prop.1]
  have key : ∀ i, C.H.eigenvalues i =
      a * ((A.conj V.val).mat i i).re + b * ((B.conj V.val).mat i i).re := fun i => by
    have h := congr_arg (fun M => (M.mat i i).re) hCd
    simp [hC, -mat_apply] at h
    exact_mod_cast h.symm
  calc (C.cfc g).trace = ∑ i, g (C.H.eigenvalues i) := trace_cfc_eq C g
    _ ≤ ∑ i, (a * g (((A.conj V.val).mat i i).re) + b * g (((B.conj V.val).mat i i).re)) :=
        Finset.sum_le_sum fun i _ => (key i).symm ▸ hg.2 trivial trivial ha hb hab
    _ ≤ a * (A.cfc g).trace + b * (B.cfc g).trace := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        gcongr <;> exact (peierls_inequality _ g hg).trans_eq (trace_cfc_conj_unitary _ g V)

open ComplexOrder in
/--
Convexity of trace functions: if `g` is convex on `ℝ₊`, then `A ↦ Tr[g(A)]` is
convex on PSD matrices. -/
theorem trace_function_convex_ici {g : ℝ → ℝ} (hg : ConvexOn ℝ (Set.Ici 0) g) :
    ConvexOn ℝ {A : HermitianMat d ℂ | 0 ≤ A} (fun A => (A.cfc g).trace) := by
  refine ⟨convex_Ici 0, fun A hA B hB a b ha hb hab => ?_⟩
  set C : HermitianMat d ℂ := a • A + b • B with hC
  set V : 𝐔[d] := star C.H.eigenvectorUnitary with hV
  have hd : ∀ X : HermitianMat d ℂ, 0 ≤ X → ∀ i, ((X.conj V.val).mat i i).re ∈ Set.Ici 0 :=
    fun X hX i => (Complex.le_def.mp ((zero_le_iff.mp (conj_nonneg _ hX)).diag_nonneg (i := i))).1
  have hCd : C.conj V.val = diagonal ℂ C.H.eigenvalues := by
    nth_rewrite 1 [C.eq_conj_diagonal]
    simp [conj_conj, hV, C.H.eigenvectorUnitary.prop.1]
  have key : ∀ i, C.H.eigenvalues i =
      a * ((A.conj V.val).mat i i).re + b * ((B.conj V.val).mat i i).re := fun i => by
    have h := congr_arg (fun M => (M.mat i i).re) hCd
    simp [hC, -mat_apply] at h
    exact_mod_cast h.symm
  calc (C.cfc g).trace = ∑ i, g (C.H.eigenvalues i) := trace_cfc_eq C g
    _ ≤ ∑ i, (a * g (((A.conj V.val).mat i i).re) + b * g (((B.conj V.val).mat i i).re)) :=
        Finset.sum_le_sum fun i _ => (key i).symm ▸ hg.2 (hd A hA i) (hd B hB i) ha hb hab
    _ ≤ a * (A.cfc g).trace + b * (B.cfc g).trace := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        gcongr <;> exact (peierls_inequality_ici _ g hg (conj_nonneg _ ‹_›)).trans_eq
          (trace_cfc_conj_unitary _ g V)

-- /-- Strict convexity of trace functions: if `g` is strictly convex on `ℝ₊`, then
-- `A ↦ Tr[g(A)]` is strictly convex on PSD matrices. -/
-- theorem trace_function_strictConvex {g : ℝ → ℝ} (hg : StrictConvexOn ℝ (Set.Ici 0) g)
--     (hg_cont : Continuous g) :
--     StrictConvexOn ℝ {A : HermitianMat d ℂ | 0 ≤ A}
--       (fun A => (A.cfc g).trace) := by
--   not needed right now
