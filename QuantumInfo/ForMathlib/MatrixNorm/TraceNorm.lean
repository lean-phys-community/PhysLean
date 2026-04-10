/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.Isometry

@[expose] public section

open BigOperators
open Classical

namespace Matrix
noncomputable section traceNorm

open scoped ComplexOrder

variable {m n R : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike R]

set_option backward.isDefEq.respectTransparency false in
/-- The trace norm of a matrix: Tr[√(A† A)]. -/
def traceNorm (A : Matrix m n R) : ℝ :=
  open MatrixOrder in
  RCLike.re (CFC.sqrt (Aᴴ * A)).trace

@[simp]
theorem traceNorm_zero : traceNorm (0 : Matrix m n R) = 0 := by
  simp [traceNorm]

/-- The trace norm of the negative is equal to the trace norm. -/
@[simp]
theorem traceNorm_eq_neg_self (A : Matrix m n R) : traceNorm (-A) = traceNorm A := by
  unfold traceNorm
  congr! 3
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg]
  exact neg_neg _


open MatrixOrder Isometry
set_option backward.isDefEq.respectTransparency false in
lemma cfc_sqrt_isometry_conj {A : Matrix n n R} (hA : 0 ≤ A)
  {u : Matrix m n R} (hu₁ : u.Isometry) :
    CFC.sqrt (u * A * uᴴ) = u * CFC.sqrt A * uᴴ := by
    have h_conj (B : Matrix n n R) (hB : 0 ≤ B) : 0 ≤ u * B * uᴴ := by
      rw [Matrix.nonneg_iff_posSemidef] at hB ⊢
      exact hB.mul_mul_conjTranspose_same u
    have hu := h_conj A hA
    have hu' := h_conj (CFC.sqrt A) (CFC.sqrt_nonneg A)
    apply (CFC.sqrt_eq_iff _ _ hu hu').mpr
    . rw [Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, ← Matrix.mul_assoc uᴴ]
      simp [show uᴴ * u = 1 from hu₁]
      rw [← Matrix.mul_assoc, Matrix.mul_assoc u, CFC.sqrt_mul_sqrt_self A hA]

theorem traceNorm_isometry_left [Fintype k] {A : Matrix n m R} {u : Matrix k n R}
  (hu₁ : u.Isometry) : traceNorm (u * A) = traceNorm A := by
  unfold traceNorm
  congr 1
  simp [Matrix.mul_assoc]
  nth_rw 2 [← Matrix.mul_assoc]
  simp [show uᴴ * u = 1 from hu₁]

theorem traceNorm_isometry_right [Fintype k] {A : Matrix n m R} {u : Matrix k m R}
  (hu₁ : u.Isometry) : traceNorm (A * uᴴ) = traceNorm A := by
  unfold traceNorm
  congr 1
  simp [← Matrix.mul_assoc]
  nth_rw 2 [Matrix.mul_assoc]
  have hA := (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  rw [cfc_sqrt_isometry_conj hA hu₁, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp [show uᴴ * u = 1 by exact hu₁]

/-- The trace norm is invariant under isometries u and v, Property 9.1.4 in Wilde -/
theorem traceNorm_isometry_conj {A : Matrix n n R} {u : Matrix m n R}
  (hu : u.Isometry) {v : Matrix m n R} (hv : v.Isometry) :
    traceNorm (u * A * vᴴ) = traceNorm A := by
    rw [traceNorm_isometry_right hv, traceNorm_isometry_left hu]

@[simp]
theorem traceNorm_unitary_conj {A : Matrix n n R} {U : Matrix.unitaryGroup n R} :
  traceNorm (U.val * A * U.valᴴ) = traceNorm A := by
  have hu:= (Matrix.mem_unitaryGroup_iff_isometry U.val).mp U.2
  exact traceNorm_isometry_conj hu.1 hu.1

--More generally sum of abs of singular values.
--Proposition 9.1.1 in Wilde
set_option backward.isDefEq.respectTransparency false in
theorem traceNorm_Hermitian_eq_sum_abs_eigenvalues {A : Matrix n n R} (hA : A.IsHermitian) :
    A.traceNorm = ∑ i, abs (hA.eigenvalues i) := by
  obtain ⟨U, D, hD, hA_eq, h_eig⟩ : ∃ U : Matrix.unitaryGroup n R, ∃ D : Matrix n n R, D.IsDiag ∧ A = U.val * D * U.valᴴ ∧ ∀ i, D i i = hA.eigenvalues i := by
    refine' ⟨hA.eigenvectorUnitary, _, isDiag_diagonal _, hA.spectral_theorem, _⟩
    simp [diagonal]
  nth_rw 1 [hA_eq, traceNorm_unitary_conj]
  unfold traceNorm
  rw [← Matrix.IsDiag.diagonal_diag hD]
  simp [Matrix.diagonal_mul_diagonal, h_eig]
  simp_rw [← sq, ← Real.sqrt_sq_eq_abs, ← Matrix.trace_diagonal]
  set B := ((diagonal fun i => (hA.eigenvalues i : R) ^ 2)) with bD
  rw [CFC.sqrt_eq_real_sqrt B _, bD]
  . rw [cfcₙ_eq_cfc]
    rw_mod_cast [cfc_diagonal (g := fun i => (hA.eigenvalues i) ^2)]
    simp
  . apply Matrix.PosSemidef.nonneg
    rw [Matrix.posSemidef_diagonal_iff]
    exact_mod_cast fun i => sq_nonneg (hA.eigenvalues i)

set_option backward.isDefEq.respectTransparency false in
/-- The trace norm is nonnegative. Property 9.1.1 in Wilde -/
theorem traceNorm_nonneg (A : Matrix m n R) : 0 ≤ A.traceNorm :=
  open MatrixOrder in
  And.left $ RCLike.nonneg_iff.1
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg

set_option backward.isDefEq.respectTransparency false in
/-- The trace norm is zero iff. the matrix is zero. -/
theorem traceNorm_zero_iff (A : Matrix m n R) : A.traceNorm = 0 ↔ A = 0 := by
  open MatrixOrder in
  set B := CFC.sqrt (Aᴴ * A) with hB_de
  have hB_posSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  have hB_hermitian : B.IsHermitian := hB_posSemidef.1
  have hB_pos : B.PosSemidef := ⟨hB_hermitian, hB_posSemidef.2⟩
  constructor
  · intro h
    have h₂ : ∀ i, hB_hermitian.eigenvalues i = 0 := by
      have h_sum : (↑(∑ j, hB_hermitian.eigenvalues j) : R) = 0 := by
        rw [hB_hermitian.sum_eigenvalues_eq_trace, ← hB_hermitian.re_trace_eq_trace]
        unfold traceNorm at h
        norm_cast
      have : ∑ j, hB_hermitian.eigenvalues j = 0 := by exact_mod_cast h_sum
      intro i
      exact Finset.sum_eq_zero_iff_of_nonneg (λ j _ => hB_pos.eigenvalues_nonneg j)
        |>.mp this i (Finset.mem_univ i)
    have h₃ : CFC.sqrt (Aᴴ * A) = 0 := hB_hermitian.eigenvalues_zero_eq_zero h₂
    have h₄ : Aᴴ * A = 0 := by
      simpa [h₃] using (
        CFC.nnrpow_sqrt_two (Aᴴ * A)
        (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self)
      ).symm
    rw [Matrix.conjTranspose_mul_self_eq_zero] at h₄
    exact h₄
  · rintro rfl
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Trace norm is linear under scalar multiplication. Property 9.1.2 in Wilde -/
theorem traceNorm_smul (A : Matrix m n R) (c : R) : (c • A).traceNorm = ‖c‖ * A.traceNorm := by
  have h : (c • A)ᴴ * (c • A) = (‖c‖^2:R) • (Aᴴ * A) := by
    rw [conjTranspose_smul, RCLike.star_def, mul_smul, smul_mul, smul_smul]
    rw [RCLike.mul_conj c]
  rw [traceNorm, h]
  open MatrixOrder in
  have : RCLike.re (trace (‖c‖ • CFC.sqrt (Aᴴ * A))) = ‖c‖ * traceNorm A := by
    simp [RCLike.smul_re]
    apply Or.inl
    rfl
  convert this using 3
  rw [RCLike.real_smul_eq_coe_smul (K := R) ‖c‖]
  by_cases h : c = 0
  · subst c
    simp
  · have hM_pd : (Aᴴ * A).PosSemidef := by apply posSemidef_conjTranspose_mul_self
    set M := (Aᴴ * A)
    rw [sq]
    simp [SemigroupAction.mul_smul]
    apply CFC.sqrt_unique;
    · simp; rw [CFC.sqrt_mul_sqrt_self M hM_pd.nonneg]
    · exact le_trans ( by norm_num ) (
        smul_le_smul_of_nonneg_left ( show 0 ≤ CFC.sqrt M from by exact (CFC.sqrt_nonneg M) ) ( norm_nonneg c ) );

/-- For square matrices, the trace norm is max Tr[U * A] over unitaries U.-/
theorem traceNorm_eq_max_tr_U (A : Matrix n n R) : IsGreatest {x | ∃ (U : unitaryGroup n R), (U.1 * A).trace = x} A.traceNorm := by
  sorry

/-- the trace norm satisfies the triangle inequality (for square matrices). TODO: Prove in general. -/
theorem traceNorm_triangleIneq (A B : Matrix n n R) : (A + B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  obtain ⟨Uab, h₁⟩ := (traceNorm_eq_max_tr_U (A + B)).left
  rw [Matrix.mul_add, Matrix.trace_add] at h₁
  obtain h₂ := (traceNorm_eq_max_tr_U A).right
  obtain h₃ := (traceNorm_eq_max_tr_U B).right
  simp only [upperBounds, Subtype.exists, exists_prop, Set.mem_setOf_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] at h₂ h₃
  replace h₂ := h₂ Uab.1 Uab.2
  replace h₃ := h₃ Uab.1 Uab.2
  rw [← RCLike.ofReal_le_ofReal (K := R)]
  simp only [RCLike.ofReal_add]
  calc _
    _ = _ + _ := h₁.symm
    _ ≤ ↑(traceNorm A) + trace (↑Uab * B) := by simp only [add_le_add_iff_right]; exact h₂
    _ ≤ _ := by simp only [add_le_add_iff_left]; exact h₃

theorem traceNorm_triangleIneq' (A B : Matrix n n R) : (A - B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  rw [sub_eq_add_neg A B, ←traceNorm_eq_neg_self B]
  exact traceNorm_triangleIneq A (-B)

set_option backward.isDefEq.respectTransparency false in
theorem PosSemidef.traceNorm_PSD_eq_trace {A : Matrix m m R} (hA : A.PosSemidef) : A.traceNorm = A.trace := by
  have : Aᴴ * A = A^2 := by rw [hA.1, pow_two]
  open MatrixOrder in
  rw [traceNorm, this, CFC.sqrt_sq A, hA.1.re_trace_eq_trace]

/-- The trace norm is convex. Property 9.1.5 in Wilde -/
theorem traceNorm_convex (M N : Matrix n n R) (l : ℝ) (hl : 0 ≤ l ∧ l ≤ 1) :
  ((l:R) • M + ((1 - l) : R) • N).traceNorm ≤ l * M.traceNorm + (1-l) * N.traceNorm := by
  refine (traceNorm_triangleIneq _ _).trans ?_
  simp_rw [traceNorm_smul]
  nth_rw 1 [← RCLike.ofReal_one]
  simp_rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
  rw [abs_of_nonneg (hl.1), abs_of_nonneg (sub_nonneg.mpr (hl.2))]

end traceNorm

end Matrix
