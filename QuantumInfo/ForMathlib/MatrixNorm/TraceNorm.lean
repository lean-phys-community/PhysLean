/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.Matrix
import QuantumInfo.ForMathlib.Isometry

open BigOperators
open Classical

namespace Matrix
noncomputable section traceNorm

open scoped ComplexOrder

variable {m n R : Type*}
variable [Fintype m] [Fintype n]
variable [RCLike R]

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

open scoped MatrixOrder Isometry
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

/-- The trace norm is nonnegative. Property 9.1.1 in Wilde -/
theorem traceNorm_nonneg (A : Matrix m n R) : 0 ≤ A.traceNorm :=
  open MatrixOrder in
  And.left $ RCLike.nonneg_iff.1
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg

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

/-- For square matrices, the trace norm is the largest value of `Re Tr[U * A]` over unitaries `U`.
The maximum is attained at `U = W⁻¹`, where `A = W√(AᴴA)` is the polar decomposition. -/
theorem traceNorm_eq_max_re_tr_U (A : Matrix n n R) :
    IsGreatest {x : ℝ | ∃ U : unitaryGroup n R, RCLike.re (U.1 * A).trace = x} A.traceNorm := by
  obtain ⟨W, hW, hA⟩ := A.exists_unitary_mul_sqrt_conjTranspose_mul_self
  set P := CFC.sqrt (Aᴴ * A) with hP
  have hPnn : (0 : Matrix n n R) ≤ P := CFC.sqrt_nonneg _
  constructor
  · refine ⟨⟨star W, Unitary.star_mem hW⟩, ?_⟩
    show RCLike.re (star W * A).trace = _
    simp only [traceNorm, ← hP]
    congr 1
    rw [hA, ← mul_assoc, mem_unitaryGroup_iff'.mp hW, one_mul]
  · rintro x ⟨U, rfl⟩
    -- Writing `√(AᴴA) = S * S` and cycling the trace, `Tr[UA] = ∑ᵢ ⟪S eᵢ, U W S eᵢ⟫`, which by
    -- Cauchy-Schwarz is at most `∑ᵢ ‖S eᵢ‖² = Tr[√(AᴴA)]`.
    set S := CFC.sqrt P with hS
    have hSnn : (0 : Matrix n n R) ≤ S := CFC.sqrt_nonneg _
    have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hPnn
    have hSH : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp hSnn).isHermitian
    have hs_adj := adjoint_toEuclideanLin_of_isHermitian hSH
    set V := (U : Matrix n n R) * W with hV
    have hVU : Vᴴ * V = 1 := by
      rw [← star_eq_conjTranspose]
      exact mem_unitaryGroup_iff'.mp (mul_mem U.2 hW)
    have hViso : ∀ y : EuclideanSpace R n, ‖V.toEuclideanLin y‖ = ‖y‖ := by
      intro y
      have := norm_toEuclideanLin_eq_of_conjTranspose_mul_self_eq
        (A := V) (B := (1 : Matrix n n R)) (by simp [hVU]) y
      simpa [toEuclideanLin_one] using this
    set v : n → EuclideanSpace R n := fun i => S.toEuclideanLin (EuclideanSpace.single i 1) with hv
    have htr : (U.1 * A).trace = (S * V * S).trace := by
      rw [hA, hV, ← hSS]
      rw [show U.1 * (W * (S * S)) = (U.1 * W * S) * S by simp [mul_assoc]]
      rw [Matrix.trace_mul_comm]
      congr 1
      simp [mul_assoc]
    have hsum : (S * V * S).trace = ∑ i, inner (𝕜 := R) (v i) (V.toEuclideanLin (v i)) := by
      rw [trace_eq_sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [toEuclideanLin_mul, toEuclideanLin_mul, LinearMap.comp_apply, LinearMap.comp_apply,
        ← LinearMap.adjoint_inner_left, hs_adj]
    have hsumP : (∑ i, ‖v i‖ ^ 2) = A.traceNorm := by
      rw [traceNorm, ← hP, ← hSS, trace_eq_sum_inner, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [toEuclideanLin_mul, LinearMap.comp_apply, ← LinearMap.adjoint_inner_left, hs_adj,
        inner_self_eq_norm_sq_to_K]
      simp [hv]
    rw [htr, hsum, map_sum, ← hsumP]
    refine Finset.sum_le_sum fun i _ => ?_
    calc RCLike.re (inner (𝕜 := R) (v i) (V.toEuclideanLin (v i)))
        ≤ ‖v i‖ * ‖V.toEuclideanLin (v i)‖ := re_inner_le_norm _ _
      _ = ‖v i‖ ^ 2 := by rw [hViso]; ring

/-- The trace norm is invariant under the conjugate transpose (for square matrices). -/
theorem traceNorm_conjTranspose (A : Matrix n n R) : Aᴴ.traceNorm = A.traceNorm := by
  have key : ∀ U : Matrix n n R, RCLike.re (U * Aᴴ).trace = RCLike.re (Uᴴ * A).trace := by
    intro U
    rw [show U * Aᴴ = (A * Uᴴ)ᴴ by simp, Matrix.trace_conjTranspose, Matrix.trace_mul_comm]
    simp
  have hset : {x : ℝ | ∃ U : unitaryGroup n R, RCLike.re (U.1 * Aᴴ).trace = x}
      = {x : ℝ | ∃ U : unitaryGroup n R, RCLike.re (U.1 * A).trace = x} := by
    ext x
    constructor
    · rintro ⟨U, rfl⟩
      exact ⟨⟨star U.1, Unitary.star_mem U.2⟩, (key U.1).symm⟩
    · rintro ⟨U, rfl⟩
      refine ⟨⟨star U.1, Unitary.star_mem U.2⟩, ?_⟩
      rw [key]
      simp [star_eq_conjTranspose]
  exact IsGreatest.unique (hset ▸ traceNorm_eq_max_re_tr_U Aᴴ) (traceNorm_eq_max_re_tr_U A)

/-- The maximizing unitary of `traceNorm_eq_max_re_tr_U`, stated without reference to
`Matrix.unitaryGroup` or to the identity matrix, so that it can be used in contexts carrying a
different `DecidableEq` instance than the classical one in scope here. -/
theorem exists_unitary_re_trace_eq_traceNorm (A : Matrix n n R) :
    ∃ U : Matrix n n R, (∀ X : Matrix n n R, Uᴴ * (U * X) = X) ∧
      RCLike.re (U * A).trace = A.traceNorm := by
  obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U A).left
  refine ⟨U.1, fun X ↦ ?_, hU⟩
  rw [← mul_assoc, ← star_eq_conjTranspose, mem_unitaryGroup_iff'.mp U.2, one_mul]

omit [Fintype m] in
/-- **Cauchy-Schwarz for the trace pairing**: for square matrices, `Re Tr[Pᴴ Q]` is at most the
trace norm of `√(QᴴQ) √(PᴴP)`. Writing the polar decompositions `P = W₁ √(PᴴP)` and
`Q = W₂ √(QᴴQ)` turns the left side into `Re Tr[(W₁ᴴW₂) √(QᴴQ) √(PᴴP)]`, and the right side is the
largest such value by `traceNorm_eq_max_re_tr_U`. -/
theorem re_trace_conjTranspose_mul_le_traceNorm (P Q : Matrix n n R) :
    RCLike.re (Pᴴ * Q).trace ≤ (CFC.sqrt (Qᴴ * Q) * CFC.sqrt (Pᴴ * P)).traceNorm := by
  obtain ⟨W₁, hW₁, hP⟩ := P.exists_unitary_mul_sqrt_conjTranspose_mul_self
  obtain ⟨W₂, hW₂, hQ⟩ := Q.exists_unitary_mul_sqrt_conjTranspose_mul_self
  set S := CFC.sqrt (Pᴴ * P) with hS
  set T := CFC.sqrt (Qᴴ * Q) with hT
  have hSH : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp (hS ▸ CFC.sqrt_nonneg _)).isHermitian
  have key : (Pᴴ * Q).trace = ((star W₁ * W₂) * (T * S)).trace := by
    rw [hP, hQ, Matrix.conjTranspose_mul, hSH, star_eq_conjTranspose,
      show S * W₁ᴴ * (W₂ * T) = S * (W₁ᴴ * W₂ * T) by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    congr 1
    simp [Matrix.mul_assoc]
  rw [key]
  exact (traceNorm_eq_max_re_tr_U (T * S)).2
    ⟨⟨star W₁ * W₂, mul_mem (Unitary.star_mem hW₁) hW₂⟩, rfl⟩

/-- The rectangular version of `re_trace_conjTranspose_mul_le_traceNorm`, obtained by padding `P`
and `Q` out to square matrices along an isometry `E`. -/
theorem re_trace_conjTranspose_mul_le_traceNorm_of_isometry (P Q : Matrix m n R)
    {E : Matrix m n R} (hE : E.Isometry) :
    RCLike.re (Pᴴ * Q).trace ≤ (CFC.sqrt (Qᴴ * Q) * CFC.sqrt (Pᴴ * P)).traceNorm := by
  have hE' : Eᴴ * E = 1 := hE
  have hgram (X Y : Matrix m n R) : (X * Eᴴ)ᴴ * (Y * Eᴴ) = E * (Xᴴ * Y) * Eᴴ := by
    simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have htr : ((P * Eᴴ)ᴴ * (Q * Eᴴ)).trace = (Pᴴ * Q).trace := by
    rw [hgram, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hE', Matrix.one_mul]
  have h := re_trace_conjTranspose_mul_le_traceNorm (P * Eᴴ) (Q * Eᴴ)
  rw [htr, hgram, hgram,
    cfc_sqrt_isometry_conj (Matrix.posSemidef_conjTranspose_mul_self Q).nonneg hE,
    cfc_sqrt_isometry_conj (Matrix.posSemidef_conjTranspose_mul_self P).nonneg hE,
    show E * CFC.sqrt (Qᴴ * Q) * Eᴴ * (E * CFC.sqrt (Pᴴ * P) * Eᴴ)
        = E * (CFC.sqrt (Qᴴ * Q) * CFC.sqrt (Pᴴ * P)) * Eᴴ by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Eᴴ, hE', Matrix.one_mul],
    traceNorm_isometry_conj hE hE] at h
  exact h

/-- An isometry `Matrix m n R` exists whenever `n` embeds into `m`. -/
theorem exists_isometry_of_card_le (h : Fintype.card n ≤ Fintype.card m) :
    ∃ E : Matrix m n R, E.Isometry := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le h
  exact ⟨Matrix.submatrix 1 id f, Matrix.submatrix_one_isometry Function.bijective_id f.injective⟩

/-- The rectangular version of `re_trace_conjTranspose_mul_le_traceNorm`, for matrices with at
least as many rows as columns. -/
theorem re_trace_conjTranspose_mul_le_traceNorm' (P Q : Matrix m n R)
    (h : Fintype.card n ≤ Fintype.card m) :
    RCLike.re (Pᴴ * Q).trace ≤ (CFC.sqrt (Qᴴ * Q) * CFC.sqrt (Pᴴ * P)).traceNorm := by
  obtain ⟨E, hE⟩ := exists_isometry_of_card_le (R := R) h
  exact re_trace_conjTranspose_mul_le_traceNorm_of_isometry P Q hE

/-- the trace norm satisfies the triangle inequality (for square matrices). TODO: Prove in general. -/
theorem traceNorm_triangleIneq (A B : Matrix n n R) : (A + B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  obtain ⟨Uab, h₁⟩ := (traceNorm_eq_max_re_tr_U (A + B)).left
  rw [Matrix.mul_add, Matrix.trace_add, map_add] at h₁
  obtain h₂ := (traceNorm_eq_max_re_tr_U A).right
  obtain h₃ := (traceNorm_eq_max_re_tr_U B).right
  simp only [upperBounds, Subtype.exists, exists_prop, Set.mem_setOf_eq, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂] at h₂ h₃
  replace h₂ := h₂ Uab.1 Uab.2
  replace h₃ := h₃ Uab.1 Uab.2
  calc (A + B).traceNorm
    _ = _ + _ := h₁.symm
    _ ≤ _ := add_le_add h₂ h₃

theorem traceNorm_triangleIneq' (A B : Matrix n n R) : (A - B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  rw [sub_eq_add_neg A B, ←traceNorm_eq_neg_self B]
  exact traceNorm_triangleIneq A (-B)

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
