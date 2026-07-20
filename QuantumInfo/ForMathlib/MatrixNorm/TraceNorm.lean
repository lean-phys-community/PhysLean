/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.Majorization
public import QuantumInfo.ForMathlib.HermitianMat.Unitary
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

/-- The trace norm of a matrix: Tr[√(A† A)]. -/
def traceNorm (A : Matrix m n R) : ℝ :=
  open MatrixOrder in
  RCLike.re (CFC.sqrt (Aᴴ * A)).trace

@[simp]
theorem traceNorm_zero : traceNorm (0 : Matrix m n R) = 0 := by
  simp [traceNorm]

/-- The trace norm of the negative is equal to the trace norm. -/
@[simp]
theorem traceNorm_neg (A : Matrix m n R) : traceNorm (-A) = traceNorm A := by
  simp [traceNorm]


open MatrixOrder Isometry

/-- The trace norm is invariant under left multiplication by an isometry. -/
theorem traceNorm_isometry_left [Fintype k] {A : Matrix n m R} {u : Matrix k n R}
  (hu₁ : u.Isometry) : traceNorm (u * A) = traceNorm A := by
  rw [traceNorm, traceNorm, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ,
    hu₁, Matrix.one_mul]

/-- The trace norm is invariant under right multiplication by the adjoint of an isometry. -/
theorem traceNorm_isometry_right [Fintype k] {A : Matrix n m R} {u : Matrix k m R}
  (hu₁ : u.Isometry) : traceNorm (A * uᴴ) = traceNorm A := by
  have hA := (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have h_conj (B : Matrix m m R) (hB : 0 ≤ B) : 0 ≤ u * B * uᴴ :=
    Matrix.nonneg_iff_posSemidef.mpr
      ((Matrix.nonneg_iff_posSemidef.mp hB).mul_mul_conjTranspose_same u)
  have hsqrt : CFC.sqrt (u * (Aᴴ * A) * uᴴ) = u * CFC.sqrt (Aᴴ * A) * uᴴ := by
    refine (CFC.sqrt_eq_iff _ _ (h_conj _ hA) (h_conj _ (CFC.sqrt_nonneg _))).mpr ?_
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, ← Matrix.mul_assoc uᴴ, hu₁, Matrix.one_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc u, CFC.sqrt_mul_sqrt_self _ hA]
  rw [traceNorm, traceNorm, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    ← Matrix.mul_assoc, Matrix.mul_assoc u, hsqrt, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    hu₁, Matrix.one_mul]

private theorem traceNorm_isometry_conj {A : Matrix n n R} {u : Matrix m n R}
  (hu : u.Isometry) {v : Matrix m n R} (hv : v.Isometry) :
    traceNorm (u * A * vᴴ) = traceNorm A := by
    rw [traceNorm_isometry_right hv, traceNorm_isometry_left hu]

/-- The trace norm is invariant under unitary conjugation. -/
@[simp]
theorem traceNorm_unitary_conj {A : Matrix n n R} {U : Matrix.unitaryGroup n R} :
  traceNorm (U.val * A * U.valᴴ) = traceNorm A := by
  have hu := (Matrix.mem_unitaryGroup_iff_isometry U.val).mp U.2
  exact traceNorm_isometry_conj hu.1 hu.1

/-- For Hermitian matrices, the trace norm is the sum of absolute eigenvalues.

This is Proposition 9.1.1 in Wilde. -/
theorem traceNorm_Hermitian_eq_sum_abs_eigenvalues {A : Matrix n n R} (hA : A.IsHermitian) :
    A.traceNorm = ∑ i, abs (hA.eigenvalues i) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    traceNorm_unitary_conj, traceNorm, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  simp only [Pi.star_apply, Function.comp_apply, RCLike.star_def, RCLike.conj_ofReal,
    ← sq, ← RCLike.ofReal_pow]
  rw [CFC.sqrt_eq_real_sqrt _
      (Matrix.posSemidef_diagonal_iff.mpr fun i => by
        exact_mod_cast sq_nonneg (hA.eigenvalues i)).nonneg,
    cfcₙ_eq_cfc (by fun_prop) (by simp), cfc_diagonal]
  simp [Real.sqrt_sq_eq_abs]

/-- The trace norm is nonnegative. Property 9.1.1 in Wilde. -/
theorem traceNorm_nonneg (A : Matrix m n R) : 0 ≤ A.traceNorm :=
  (RCLike.nonneg_iff.1
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))).trace_nonneg).1

/-- The trace norm is zero iff the matrix is zero. -/
theorem traceNorm_zero_iff (A : Matrix m n R) : A.traceNorm = 0 ↔ A = 0 := by
  have hB := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (Aᴴ * A))
  constructor
  · intro h
    unfold traceNorm at h
    rw [← Matrix.conjTranspose_mul_self_eq_zero (A := A), ← CFC.sqrt_mul_sqrt_self (Aᴴ * A)
        (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
      hB.trace_eq_zero_iff.mp (by rw [← hB.1.re_trace_eq_trace, h, RCLike.ofReal_zero]),
      Matrix.mul_zero]
  · rintro rfl
    simp

/-- The trace norm is homogeneous under scalar multiplication. Property 9.1.2 in Wilde. -/
theorem traceNorm_smul (A : Matrix m n R) (c : R) : (c • A).traceNorm = ‖c‖ * A.traceNorm := by
  have h : (c • A)ᴴ * (c • A) = ‖c‖ ^ 2 • (Aᴴ * A) := by
    rw [conjTranspose_smul, RCLike.star_def, Matrix.mul_smul, smul_mul, smul_smul,
      RCLike.mul_conj c, ← RCLike.ofReal_pow, ← RCLike.real_smul_eq_coe_smul]
  have h2 : CFC.sqrt (‖c‖ ^ 2 • (Aᴴ * A)) = ‖c‖ • CFC.sqrt (Aᴴ * A) :=
    CFC.sqrt_unique
      (by rw [smul_mul_smul_comm, CFC.sqrt_mul_sqrt_self _
        (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self), ← sq])
      (smul_nonneg (norm_nonneg c) (CFC.sqrt_nonneg _))
  rw [traceNorm, h, h2, Matrix.trace_smul, RCLike.smul_re, traceNorm]

section complexTraceNorm

variable [DecidableEq n]

omit [Fintype m] [DecidableEq n] in
private lemma inner_A_mulVec_eq (A : Matrix n n ℂ) (v w : n → ℂ) :
    inner ℂ (WithLp.toLp 2 (A.mulVec v)) (WithLp.toLp 2 (A.mulVec w)) =
      star v ⬝ᵥ ((Aᴴ * A).mulVec w) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm, Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, Matrix.dotProduct_mulVec]

/-- Singular value decomposition for square complex matrices, with singular values expressed as
square roots of the eigenvalues of `Aᴴ * A`. -/
theorem exists_svd_sqrt_eigenvalues (A : Matrix n n ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    ∃ V W : Matrix.unitaryGroup n ℂ,
      A = V.val * Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ)) * W.valᴴ := by
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  let s : n → ℂ := fun i => Real.sqrt (hH.eigenvalues i)
  have hs_ne {i : n} (hi : hH.eigenvalues i ≠ 0) : s i ≠ 0 := by
    simpa [s] using Real.sqrt_ne_zero'.2
      ((Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i).lt_of_ne' hi)
  let u : n → EuclideanSpace ℂ n := fun i =>
    if hi : hH.eigenvalues i ≠ 0 then
      ((s i)⁻¹ • WithLp.toLp 2 (A.mulVec (hH.eigenvectorBasis i).ofLp))
    else 0
  have hu : Orthonormal ℂ ({i | hH.eigenvalues i ≠ 0}.restrict u) := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp [u, s]
    have hi' : hH.eigenvalues i.1 ≠ 0 := i.2
    have hj' : hH.eigenvalues j.1 ≠ 0 := j.2
    simp only [hi', hj', not_false_eq_true, if_true]
    rw [inner_smul_left, inner_smul_right, inner_A_mulVec_eq, hH.mulVec_eigenvectorBasis j.1]
    by_cases hij : i.1 = j.1
    · cases Subtype.ext hij
      simp [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, mul_comm]
      field_simp [show (Real.sqrt (hH.eigenvalues i.1) : ℂ) ≠ 0 by simpa [s] using hs_ne i.2]
      exact_mod_cast (Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i.1)).symm
    · simpa [hij, dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct,
        orthonormal_iff_ite.mp hH.eigenvectorBasis.orthonormal, mul_comm]
        using (show i ≠ j from fun h => hij (congrArg Subtype.val h))
  obtain ⟨b, hb⟩ :=
    hu.exists_orthonormalBasis_extension_of_card_eq (by simp [finrank_euclideanSpace])
  let V : Matrix.unitaryGroup n ℂ := ⟨Matrix.of (fun i j ↦ b j i), by
    simp only [Matrix.mem_unitaryGroup_iff]
    ext i j
    simpa [inner, Matrix.mul_apply, Matrix.one_apply] using
      b.sum_inner_mul_inner (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)⟩
  let W : Matrix.unitaryGroup n ℂ := hH.eigenvectorUnitary
  have hAW : A * W.val = V.val * Matrix.diagonal s := by
    ext i j
    have hleft : (A * W.val) i j = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
      simp [mul_apply, Matrix.mulVec, dotProduct, W, IsHermitian.eigenvectorUnitary_apply]
    by_cases hj : hH.eigenvalues j = 0
    · have hzero : A.mulVec (hH.eigenvectorBasis j).ofLp = 0 :=
        WithLp.toLp_injective 2 <| inner_self_eq_zero.mp <| by
          rw [inner_A_mulVec_eq, hH.mulVec_eigenvectorBasis j, hj]
          simp
      rw [hleft, congrFun hzero i]
      simp [Matrix.mul_apply, Matrix.diagonal, V, s, hj]
    · have hbji : b j i = (s j)⁻¹ * A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        simpa [u, hj] using congrArg (fun x : EuclideanSpace ℂ n => x.ofLp i) (hb j hj)
      have hs_mul : s j * b j i = A.mulVec (hH.eigenvectorBasis j).ofLp i := by
        rw [hbji]; field_simp [hs_ne hj]
      rw [hleft, ← hs_mul]; simp [Matrix.mul_apply, Matrix.diagonal, V, s, mul_comm]
  refine ⟨V, W, ?_⟩
  simpa [W, Matrix.IsHermitian.eigenvectorUnitary, Matrix.mul_assoc] using
    congrArg (fun X => X * W.valᴴ) hAW

open scoped MatrixOrder in
private lemma traceNorm_eq_sum_sqrt_eigenvalues (A : Matrix n n ℂ) :
    let hH : (Aᴴ * A).IsHermitian := by
      simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
    A.traceNorm = ∑ i, Real.sqrt (hH.eigenvalues i) := by
  intro hH
  rw [Matrix.traceNorm, CFC.sqrt_eq_real_sqrt (Aᴴ * A)
    (Matrix.nonneg_iff_posSemidef.mpr A.posSemidef_conjTranspose_mul_self),
    cfcₙ_eq_cfc, Matrix.IsHermitian.cfc_eq hH, Matrix.IsHermitian.cfc]
  simp [Matrix.trace_mul_comm, Matrix.mul_assoc]

omit [DecidableEq n] in
/-- The trace norm of a square complex matrix is the sum of its singular values. -/
theorem traceNorm_eq_sum_singularValues [DecidableEq n] (A : Matrix n n ℂ) :
    A.traceNorm = ∑ i, singularValues A i := by
  rw [traceNorm_eq_sum_sqrt_eigenvalues A]
  exact Finset.sum_congr rfl fun i _ => by simp [singularValues]

omit [DecidableEq n] in
/-- The trace norm of a square complex matrix is the sum of its sorted singular values. -/
theorem traceNorm_eq_sum_singularValuesSorted [DecidableEq n] (A : Matrix n n ℂ) :
    A.traceNorm = ∑ i : Fin (Fintype.card n), singularValuesSorted A i := by
  rw [traceNorm_eq_sum_singularValues]
  simpa using (sum_singularValues_rpow_eq_sum_sorted A (1 : ℝ))

section
open scoped Matrix.Norms.L2Operator

omit [DecidableEq n] in
/-- Every singular value is bounded by the operator norm. -/
theorem singularValues_le_opNorm [DecidableEq n] (A : Matrix n n ℂ) (i : n) :
    singularValues A i ≤ ‖A‖ := by
  letI : Nonempty n := ⟨i⟩
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  have hmem : hH.eigenvalues i ∈ spectrum ℝ (Aᴴ * A) :=
    hH.spectrum_real_eq_range_eigenvalues ▸ Set.mem_range_self i
  have h : hH.eigenvalues i ≤ ‖A‖ * ‖A‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self A]
    simpa [abs_of_nonneg (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)] using
      spectrum.norm_le_norm_of_mem hmem
  simpa [singularValues, Real.sqrt_mul_self (norm_nonneg A)] using Real.sqrt_le_sqrt h

omit [DecidableEq n] in
/-- The trace norm is bounded by the operator norm on the left times the trace norm on the right. -/
theorem traceNorm_mul_le_opNorm_traceNorm [DecidableEq n] (A B : Matrix n n ℂ) :
    (A * B).traceNorm ≤ ‖A‖ * B.traceNorm := by
  classical
  rcases isEmpty_or_nonempty n with h | h
  · simp [Subsingleton.elim A 0, Subsingleton.elim B 0]
  · have hcard : 0 < Fintype.card n := Fintype.card_pos_iff.mpr h
    have hA_bound (i : Fin (Fintype.card n)) : singularValuesSorted A i ≤ ‖A‖ :=
      (singularValuesSorted_antitone A (Fin.zero_le i)).trans <| by
        show singularValuesSorted A ⟨0, hcard⟩ ≤ ‖A‖
        rw [singularValuesSorted_zero_eq_sup A hcard, Finset.sup'_le_iff]
        exact fun j _ => singularValues_le_opNorm A j
    calc
      (A * B).traceNorm ≤ ∑ i, singularValuesSorted A i * singularValuesSorted B i := by
        rw [traceNorm_eq_sum_singularValuesSorted]
        simpa using sum_rpow_singularValues_mul_le A B one_pos
      _ ≤ ∑ i, ‖A‖ * singularValuesSorted B i :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (hA_bound i) (singularValuesSorted_nonneg B i)
      _ = ‖A‖ * B.traceNorm := by
        rw [← Finset.mul_sum, traceNorm_eq_sum_singularValuesSorted]

omit [DecidableEq n] in
/-- The trace norm is invariant under conjugate transpose. -/
theorem traceNorm_conjTranspose (A : Matrix n n ℂ) :
    Aᴴ.traceNorm = A.traceNorm := by
  classical
  have hH : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  obtain ⟨V, W, hA⟩ := Matrix.exists_svd_sqrt_eigenvalues A
  have hiso (U : Matrix.unitaryGroup n ℂ) : U.val.Isometry :=
    ((Matrix.mem_unitaryGroup_iff_isometry U.val).mp U.prop).1
  set D : Matrix n n ℂ :=
    Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hDH : Dᴴ = D := by simp [D, Matrix.diagonal_conjTranspose]
  rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hDH, ← Matrix.mul_assoc,
    traceNorm_isometry_conj (hiso W) (hiso V), traceNorm_isometry_conj (hiso V) (hiso W)]

omit [Fintype m] [RCLike R] [DecidableEq n] in
/-- The trace norm is bounded by trace norm on the left times operator norm on the right. -/
theorem traceNorm_mul_le_traceNorm_opNorm [DecidableEq n] (A B : Matrix n n ℂ) :
    (A * B).traceNorm ≤ A.traceNorm * ‖B‖ := by
  simpa [← Matrix.conjTranspose_mul, Matrix.l2_opNorm_conjTranspose, traceNorm_conjTranspose,
    mul_comm] using Matrix.traceNorm_mul_le_opNorm_traceNorm Bᴴ Aᴴ

omit [Fintype m] [RCLike R] [DecidableEq n] in
/-- Multiplication on both sides by contractions does not increase trace norm. -/
theorem traceNorm_sandwich_le [DecidableEq n] {S M T : Matrix n n ℂ} (hS : ‖S‖ ≤ 1)
    (hT : ‖T‖ ≤ 1) : (S * M * T).traceNorm ≤ M.traceNorm :=
  calc (S * M * T).traceNorm
      ≤ (M * T).traceNorm :=
        le_trans
          (by simpa [Matrix.mul_assoc] using Matrix.traceNorm_mul_le_opNorm_traceNorm S (M * T))
          (by simpa using mul_le_mul_of_nonneg_right hS (Matrix.traceNorm_nonneg (M * T)))
    _ ≤ M.traceNorm :=
        le_trans (traceNorm_mul_le_traceNorm_opNorm M T)
          (by simpa using mul_le_mul_of_nonneg_left hT (Matrix.traceNorm_nonneg M))

end

/-- The absolute value of the trace is bounded by the trace norm. -/
theorem abs_trace_le_traceNorm (A : Matrix n n ℂ) :
    ‖A.trace‖ ≤ A.traceNorm := by
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  obtain ⟨V, W, hA⟩ := exists_svd_sqrt_eigenvalues A
  set D : Matrix n n ℂ := Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  set C : Matrix.unitaryGroup n ℂ := star W * V
  calc
    ‖A.trace‖ = ‖(C.val * D).trace‖ := by
      rw [hA, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
      rfl
    _ ≤ ∑ i, ‖(C.val * D) i i‖ := by
      simpa [Matrix.trace] using norm_sum_le (s := Finset.univ) (f := fun i => (C.val * D) i i)
    _ = ∑ i, ‖C.val i i‖ * Real.sqrt (hH.eigenvalues i) := by
      simp [D, Matrix.mul_apply, Matrix.diagonal, Real.norm_eq_abs, abs_of_nonneg]
    _ ≤ ∑ i, Real.sqrt (hH.eigenvalues i) := by
      exact Finset.sum_le_sum (fun i _ => by
        simpa using mul_le_mul_of_nonneg_right
          (entry_norm_bound_of_unitary C.property i i)
          (Real.sqrt_nonneg _))
    _ = A.traceNorm := by
      simpa [hH] using (traceNorm_eq_sum_sqrt_eigenvalues A).symm

end complexTraceNorm

/-- For square complex matrices, the trace norm is the maximum of `re (Tr[U * A])`
over unitaries `U`. -/
theorem traceNorm_eq_max_re_tr_U (A : Matrix n n ℂ) :
    IsGreatest {x : ℝ | ∃ U : unitaryGroup n ℂ, Complex.re ((U.val * A).trace) = x} A.traceNorm := by
  classical
  let hH : (Aᴴ * A).IsHermitian := by
    simpa using (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose)
  obtain ⟨V, W, hA⟩ := exists_svd_sqrt_eigenvalues A
  have htraceNorm : A.traceNorm = ∑ i, Real.sqrt (hH.eigenvalues i) := by
    simpa [hH] using traceNorm_eq_sum_sqrt_eigenvalues A
  set D : Matrix n n ℂ := Matrix.diagonal (fun i => (Real.sqrt (hH.eigenvalues i) : ℂ))
  have hVu : V.valᴴ * V.val = 1 := (Matrix.mem_unitaryGroup_iff_isometry V.val).mp V.prop |>.1
  have hWu : W.valᴴ * W.val = 1 := (Matrix.mem_unitaryGroup_iff_isometry W.val).mp W.prop |>.1
  refine ⟨⟨W * star V, ?_⟩, ?_⟩
  · calc Complex.re (((W * star V).val * A).trace)
        = Complex.re (D.trace) := by
          rw [hA]; congr 1
          change (W.val * V.valᴴ * (V.val * D * W.valᴴ)).trace = D.trace
          simp [Matrix.mul_assoc, hVu, Matrix.trace_mul_comm, hWu]
      _ = A.traceNorm := by simp [D, Matrix.trace, htraceNorm]
  · rintro _ ⟨U, rfl⟩
    set C : Matrix.unitaryGroup n ℂ := star W * U * V
    rw [show Complex.re ((U.val * A).trace) =
        ∑ i, Real.sqrt (hH.eigenvalues i) * Complex.re (C.val i i) by
      conv_lhs => rw [hA]
      have h1 : (U.val * (V.val * D * W.valᴴ)).trace = (C.val * D).trace := by
        change _ = (W.valᴴ * U.val * V.val * D).trace
        rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
        simp [Matrix.mul_assoc]
      rw [h1]
      simp [D, Matrix.trace, Matrix.mul_apply, Matrix.diagonal, Complex.mul_re, mul_comm],
      htraceNorm]
    have hdiag_le : ∀ i, Complex.re (C.val i i) ≤ 1 := fun i =>
      (Complex.re_le_norm _).trans (entry_norm_bound_of_unitary C.prop i i)
    exact Finset.sum_le_sum fun i _ => by
      nlinarith [hdiag_le i, Real.sqrt_nonneg (hH.eigenvalues i)]

/-- The trace norm satisfies the triangle inequality for square complex matrices. -/
theorem traceNorm_add_le (A B : Matrix n n ℂ) : (A + B).traceNorm ≤ A.traceNorm + B.traceNorm := by
  obtain ⟨Uab, h₁⟩ := (traceNorm_eq_max_re_tr_U (A + B)).left
  rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re] at h₁
  exact h₁ ▸ add_le_add ((traceNorm_eq_max_re_tr_U A).2 ⟨Uab, rfl⟩)
    ((traceNorm_eq_max_re_tr_U B).2 ⟨Uab, rfl⟩)

/-- A positive semidefinite matrix has trace norm equal to its trace. -/
theorem PosSemidef.traceNorm_eq_trace {A : Matrix m m R} (hA : A.PosSemidef) :
    A.traceNorm = A.trace := by
  rw [traceNorm, hA.1, ← pow_two, CFC.sqrt_sq A, hA.1.re_trace_eq_trace]

/-- The trace norm is convex. Property 9.1.5 in Wilde. -/
theorem traceNorm_convex (M N : Matrix n n ℂ) (l : ℝ) (hl : 0 ≤ l ∧ l ≤ 1) :
  ((l:ℂ) • M + ((1 - l) : ℂ) • N).traceNorm ≤ l * M.traceNorm + (1-l) * N.traceNorm := by
  refine (traceNorm_add_le _ _).trans ?_
  rw [traceNorm_smul, traceNorm_smul, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hl.1,
    Real.norm_of_nonneg (sub_nonneg.mpr hl.2)]

end traceNorm

end Matrix
