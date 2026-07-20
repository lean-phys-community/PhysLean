/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.ForMathlib.HermitianMat.Sqrt

/-!
Quantities of quantum _relative entropy_, namely the (standard) quantum relative
entropy, and generalizations such as sandwiched Rényi relative entropy.
-/

@[expose] public section

noncomputable section

variable {d d₁ d₂ d₃ m n : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype m] [Fintype n]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] [DecidableEq m] [DecidableEq n]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}


open scoped InnerProductSpace RealInnerProductSpace Kronecker Matrix

/-
The operator norm of a matrix is the operator norm of the linear map it represents, with respect to the Euclidean norm.
-/
/-- The operator norm of a matrix, with respect to the Euclidean norm (l2 norm) on the domain and codomain. -/
noncomputable def Matrix.opNorm (A : Matrix m n 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)‖

/-
An isometry preserves the Euclidean norm.
-/
theorem Matrix.isometry_preserves_norm (A : Matrix n m 𝕜) (hA : A.Isometry) (x : EuclideanSpace 𝕜 m) :
    ‖Matrix.toEuclideanLin A x‖ = ‖x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← inner_self_eq_norm_sq (𝕜 := 𝕜),
    ← inner_self_eq_norm_sq (𝕜 := 𝕜), ← LinearMap.adjoint_inner_left,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  rw [Matrix.Isometry] at hA
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec, hA]

/-
The operator norm of an isometry is 1 (assuming the domain is non-empty).
-/
theorem Matrix.opNorm_isometry [Nonempty m] (A : Matrix n m 𝕜) (hA : A.Isometry) : Matrix.opNorm A = 1 := by
  exact LinearIsometry.norm_toContinuousLinearMap
    ⟨Matrix.toEuclideanLin A, Matrix.isometry_preserves_norm A hA⟩

variable (d₁ d₂) in
/-- The matrix representation of the map $v \mapsto v \otimes \sum_k |k\rangle|k\rangle$.
    The output index is `(d1 \times d2) \times d2`. -/
def map_to_tensor_MES : Matrix ((d₁ × d₂) × d₂) d₁ ℂ :=
  Matrix.of fun ((i, j), k) l => if i = l ∧ j = k then 1 else 0

theorem map_to_tensor_MES_prop (A : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) :
    (map_to_tensor_MES d₁ d₂).conjTranspose * (Matrix.kronecker A (1 : Matrix d₂ d₂ ℂ)) * (map_to_tensor_MES d₁ d₂) =
    A.traceRight := by
  ext i j
  simp [map_to_tensor_MES, Matrix.mul_apply, Matrix.traceRight, Fintype.sum_prod_type,
    Matrix.one_apply, ite_and, apply_ite (starRingEnd ℂ)]

/-- The isometry V_rho from the paper. -/
noncomputable def V_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix ((dA × dB) × dB) dA ℂ :=
  let ρA_inv_sqrt := ρAB.traceRight⁻¹.sqrt
  let ρAB_sqrt := ρAB.sqrt
  let I_B := (1 : Matrix dB dB ℂ)
  let term1 := ρAB_sqrt.mat ⊗ₖ I_B
  let term2 := map_to_tensor_MES dA dB
  term1 * term2 * ρA_inv_sqrt.mat

open scoped MatrixOrder ComplexOrder

/-- The isometry V_sigma from the paper. -/
noncomputable def V_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dB × (dB × dC)) dC ℂ :=
  (V_rho (σBC.reindex (Equiv.prodComm dB dC))).reindex
    ((Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _)))
    (Equiv.refl _)

/--
V_rho^H * V_rho simplifies to sandwiching the traceRight by the inverse square root.
-/
lemma V_rho_conj_mul_self_eq (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    let ρA := ρAB.traceRight
    let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
    (V_rho ρAB)ᴴ * (V_rho ρAB) = ρA_inv_sqrt * ρAB.traceRight.mat * ρA_inv_sqrt := by
  have h1 : (ρAB.sqrt.mat ⊗ₖ (1 : Matrix dB dB ℂ))ᴴ * (ρAB.sqrt.mat ⊗ₖ (1 : Matrix dB dB ℂ)) =
      ρAB.mat ⊗ₖ (1 : Matrix dB dB ℂ) := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
      Matrix.one_mul, HermitianMat.conjTranspose_mat,
      HermitianMat.sqrt_sq (HermitianMat.zero_le_iff.mpr hρ.posSemidef)]
  simp only [V_rho, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((ρAB.sqrt.mat ⊗ₖ (1 : Matrix dB dB ℂ))ᴴ), h1]
  simp only [HermitianMat.conjTranspose_mat, HermitianMat.traceRight_mat,
    ← map_to_tensor_MES_prop, ← Matrix.mul_assoc]
  rfl

/--
The partial trace (left) of a positive definite matrix is positive definite.
-/
lemma PosDef_traceRight [Nonempty dB] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceRight.mat.PosDef := by
  have _ := ‹DecidableEq dA›
  have hsd := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hA.posSemidef).2
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨A.traceRight.H, fun x hx => ?_⟩
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  have key : star x ⬝ᵥ A.traceRight.mat *ᵥ x =
      ∑ i : dB, star (fun (p : dA × dB) => if i = p.2 then x p.1 else 0) ⬝ᵥ
        A.mat *ᵥ (fun p => if i = p.2 then x p.1 else 0) := by
    simp_rw [HermitianMat.traceRight_mat, Matrix.traceRight, Matrix.dotProduct_mulVec]
    simpa [dotProduct, Matrix.vecMul_eq_sum, ite_apply, Fintype.sum_prod_type,
      Finset.mul_sum, Finset.sum_mul, apply_ite] using Finset.sum_comm_cycle
  rw [key]
  refine Finset.sum_pos' (fun i _ => hsd _) ⟨Classical.arbitrary dB, Finset.mem_univ _,
    (Matrix.posDef_iff_dotProduct_mulVec.mp hA).2 fun h => hj ?_⟩
  simpa using congr_fun h (j, Classical.arbitrary dB)

lemma PosDef_traceLeft [Nonempty dA] (A : HermitianMat (dA × dB) ℂ) (hA : A.mat.PosDef) :
    A.traceLeft.mat.PosDef := by
  exact PosDef_traceRight (A.reindex (Equiv.prodComm _ _)) (hA.reindex _)

/--
V_rho is an isometry.
-/
theorem V_rho_isometry [Nonempty dB] (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    (V_rho ρAB)ᴴ * (V_rho ρAB) = 1 := by
  rw [← HermitianMat.sqrt_inv_mul_self_mul_sqrt_inv_eq_one (PosDef_traceRight ρAB hρ)]
  exact V_rho_conj_mul_self_eq ρAB hρ

/--
V_sigma is an isometry.
-/
theorem V_sigma_isometry [Nonempty dB] (σBC : HermitianMat (dB × dC) ℂ) (hσ : σBC.mat.PosDef) :
    (V_sigma σBC).conjTranspose * (V_sigma σBC) = 1 := by
  rw [V_sigma, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    V_rho_isometry (σBC.reindex (Equiv.prodComm dB dC))
      (by rw [HermitianMat.mat_reindex]; exact hσ.reindex _)]
  simp

/-
Definition of W_mat with correct reindexing.
-/
open HermitianMat
open scoped MatrixOrder

variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC]

/-- The operator W from the paper, defined as a matrix product. -/
noncomputable def W_mat (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) : Matrix ((dA × dB) × dC) ((dA × dB) × dC) ℂ :=
  let ρA := ρAB.traceRight
  let σC := σBC.traceLeft
  let ρAB_sqrt := (ρAB.sqrt : Matrix (dA × dB) (dA × dB) ℂ)
  let σC_inv_sqrt := (σC⁻¹.sqrt : Matrix dC dC ℂ)
  let ρA_inv_sqrt := (ρA⁻¹.sqrt : Matrix dA dA ℂ)
  let σBC_sqrt := (σBC.sqrt : Matrix (dB × dC) (dB × dC) ℂ)

  let term1 := ρAB_sqrt ⊗ₖ σC_inv_sqrt
  let term2 := ρA_inv_sqrt ⊗ₖ σBC_sqrt
  let term2_reindexed := term2.reindex (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm

  term1 * term2_reindexed

/--
The operator norm of a matrix product is at most the product of the operator norms.
-/
theorem Matrix.opNorm_mul_le {l m n 𝕜 : Type*} [Fintype l] [Fintype m] [Fintype n]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [RCLike 𝕜]
    (A : Matrix l m 𝕜) (B : Matrix m n 𝕜) :
    Matrix.opNorm (A * B) ≤ Matrix.opNorm A * Matrix.opNorm B := by
  have h_comp : Matrix.toEuclideanLin (A * B) = Matrix.toEuclideanLin A ∘ₗ Matrix.toEuclideanLin B := by
    ext; simp [toEuclideanLin]
  simp only [Matrix.opNorm, h_comp]
  exact ContinuousLinearMap.opNorm_comp_le (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin B))

theorem Matrix.opNorm_reindex_proven {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n] [Fintype p]
    [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]
    (e : m ≃ l) (f : n ≃ p) (A : Matrix m n 𝕜) :
    Matrix.opNorm (A.reindex e f) = Matrix.opNorm A := by
  refine' le_antisymm _ _;
  · refine' csInf_le _ _;
    · exact ⟨ 0, fun c hc => hc.1 ⟩;
    · refine' ⟨ norm_nonneg _, fun x => _ ⟩;
      convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( Matrix.toEuclideanLin A ) ) (WithLp.toLp 2 ( fun i => x ( f i ) )) using 1;
      · simp [ Matrix.toEuclideanLin, EuclideanSpace.norm_eq ];
        rw [ ← Equiv.sum_comp e.symm ] ; aesop;
      · simp [ EuclideanSpace.norm_eq, Matrix.opNorm ];
        exact Or.inl ( by rw [ ← Equiv.sum_comp f ] );
  · refine' ContinuousLinearMap.opNorm_le_bound _ _ fun a => _;
    · exact ContinuousLinearMap.opNorm_nonneg _;
    · convert ContinuousLinearMap.le_opNorm ( LinearMap.toContinuousLinearMap ( toEuclideanLin ( Matrix.reindex e f A ) ) ) (WithLp.toLp 2 ( fun i => a ( f.symm i ) )) using 1;
      · simp [ EuclideanSpace.norm_eq, Matrix.toEuclideanLin ];
        rw [ ← Equiv.sum_comp e.symm ]
        simp [ Matrix.mulVec, dotProduct ] ;
      · congr! 2;
        simp [ EuclideanSpace.norm_eq]
        conv_lhs => rw [ ← Equiv.sum_comp f.symm ] ;

/--
Define U_rho as the Kronecker product of V_rho and the identity.
-/
noncomputable def U_rho (ρAB : HermitianMat (dA × dB) ℂ) : Matrix (((dA × dB) × dB) × dC) (dA × dC) ℂ :=
  Matrix.kronecker (V_rho ρAB) (1 : Matrix dC dC ℂ)

/--
Define U_sigma as the Kronecker product of the identity and V_sigma.
-/
noncomputable def U_sigma (σBC : HermitianMat (dB × dC) ℂ) : Matrix (dA × (dB × (dB × dC))) (dA × dC) ℂ :=
  Matrix.kronecker (1 : Matrix dA dA ℂ) (V_sigma σBC)

/--
The operator norm of the conjugate transpose is equal to the operator norm.
-/
theorem Matrix.opNorm_conjTranspose_eq_opNorm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m n 𝕜) :
    Matrix.opNorm Aᴴ = Matrix.opNorm A := by
  unfold Matrix.opNorm
  rw [← ContinuousLinearMap.adjoint.norm_map (toEuclideanLin A).toContinuousLinearMap,
    toEuclideanLin_conjTranspose_eq_adjoint]
  rfl

theorem isometry_mul_conjTranspose_le_one {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (V : Matrix m n ℂ) (hV : V.conjTranspose * V = 1) :
    V * V.conjTranspose ≤ 1 := by
  have h2 : (1 - V * Vᴴ)ᴴ * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
    simp [sub_mul, mul_sub, ← Matrix.mul_assoc]
    simp [Matrix.mul_assoc, hV]
  exact Matrix.le_iff.mpr (h2 ▸ Matrix.posSemidef_conjTranspose_mul_self _)

/-
If `A†A = I` and `B†B = I` (both isometries into the same space), then `||(A†B)|| ≤ 1`,
  equivalently `(A†B)†(A†B) ≤ I`.
-/
theorem conjTranspose_isometry_mul_isometry_le_one {m n k : Type*}
    [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k]
    (A : Matrix k m ℂ) (B : Matrix k n ℂ)
    (hA : A.conjTranspose * A = 1) (hB : B.conjTranspose * B = 1) :
    (A.conjTranspose * B).conjTranspose * (A.conjTranspose * B) ≤ 1 := by
  simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, hB] using
    Matrix.PosSemidef.conjTranspose_mul_mul_mono B (isometry_mul_conjTranspose_le_one A hA)

/-! ### Helper lemmas for operator_ineq_SSA -/

/- Reindexing preserves the HermitianMat ordering. -/
theorem HermitianMat.reindex_le_reindex_iff {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (e : d ≃ d₂) (A B : HermitianMat d ℂ) :
    A.reindex e ≤ B.reindex e ↔ A ≤ B := by
  constructor <;> intro h <;> rw [HermitianMat.le_iff] at * <;> aesop;

/- Inverse of a Kronecker product of HermitianMat. -/
theorem HermitianMat.inv_kronecker {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] [Nonempty m] [Nonempty n]
    (A : HermitianMat m ℂ) (B : HermitianMat n ℂ)
    [A.NonSingular] [B.NonSingular] :
    (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ := by
  refine HermitianMat.ext (Matrix.inv_eq_right_inv ?_)
  rw [HermitianMat.kronecker_mat, HermitianMat.kronecker_mat, HermitianMat.mat_inv,
    HermitianMat.mat_inv, ← Matrix.mul_kronecker_mul, Matrix.mul_inv_of_invertible,
    Matrix.mul_inv_of_invertible, Matrix.one_kronecker_one]

/- Inverse of a reindexed HermitianMat. -/
theorem HermitianMat.inv_reindex {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (A : HermitianMat d ℂ) (e : d ≃ d₂) :
    (A.reindex e)⁻¹ = A⁻¹.reindex e := by
  ext1
  simp

/- Kronecker of PosDef matrices is PosDef. -/
theorem HermitianMat.PosDef_kronecker {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (A : HermitianMat m ℂ) (B : HermitianMat n ℂ)
    (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    (A ⊗ₖ B).mat.PosDef :=
  Matrix.PosDef.kron hA hB

/- Reindex of PosDef is PosDef. -/
theorem HermitianMat.PosDef_reindex {d d₂ : Type*} [Fintype d] [DecidableEq d]
    [Fintype d₂] [DecidableEq d₂] (A : HermitianMat d ℂ) (e : d ≃ d₂)
    (hA : A.mat.PosDef) :
    (A.reindex e).mat.PosDef := by
  convert! hA.reindex e

/-- The sandwich matrix S used in the proof of intermediate_ineq.
  This is derived from W_mat_sq_le_one by algebraic manipulation (conjugation and simplification). -/
private noncomputable def S_mat (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) :
    Matrix ((dA × dB) × dC) ((dA × dB) × dC) ℂ :=
  (ρAB.traceRight⁻¹.sqrt.mat ⊗ₖ σBC.sqrt.mat).reindex
    (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm

/- W†W = S * (ρ_AB ⊗ σ_C⁻¹) * S, i.e. W†W equals the conj of LHS by S.
This follows from: W = (ρAB^½ ⊗ σC^{-½}) * S, so W†W = S† * (ρAB^½ ⊗ σC^{-½})† * (ρAB^½ ⊗ σC^{-½}) * S
= S * (ρAB ⊗ σC⁻¹) * S (using sqrt_sq and Hermiticity of S).
-/
private lemma W_mat_sq_eq_conj [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    (W_mat ρAB σBC)ᴴ * (W_mat ρAB σBC) =
      S_mat ρAB σBC * (ρAB ⊗ₖ (σBC.traceLeft)⁻¹).mat * S_mat ρAB σBC := by
  have hσC : (σBC.traceLeft⁻¹).mat.PosDef := (PosDef_traceLeft σBC hσ).inv
  have hT : (ρAB.sqrt.mat ⊗ₖ σBC.traceLeft⁻¹.sqrt.mat)ᴴ * (ρAB.sqrt.mat ⊗ₖ σBC.traceLeft⁻¹.sqrt.mat)
      = (ρAB ⊗ₖ σBC.traceLeft⁻¹).mat := by
    rw [Matrix.conjTranspose_kronecker, HermitianMat.conjTranspose_mat,
      HermitianMat.conjTranspose_mat, ← Matrix.mul_kronecker_mul,
      HermitianMat.sqrt_sq (zero_le_iff.mpr hρ.posSemidef),
      HermitianMat.sqrt_sq (zero_le_iff.mpr hσC.posSemidef), HermitianMat.kronecker_mat]
  simp only [W_mat, S_mat, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((ρAB.sqrt.mat ⊗ₖ σBC.traceLeft⁻¹.sqrt.mat)ᴴ), hT]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker,
    HermitianMat.conjTranspose_mat]

/- **Step 2**: S * (ρ_A ⊗ σ_BC⁻¹).reindex * S = I.
This follows from (ρ_A^{-½} * ρ_A * ρ_A^{-½}) ⊗ (σ_BC^½ * σ_BC⁻¹ * σ_BC^½) = I ⊗ I = I.
-/
private lemma S_mat_conj_rhs_eq_one [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    S_mat ρAB σBC * ((ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm).mat *
      S_mat ρAB σBC = 1 := by
  have h1 : ρAB.traceRight⁻¹.sqrt.mat * ρAB.traceRight.mat * ρAB.traceRight⁻¹.sqrt.mat = 1 :=
    sqrt_inv_mul_self_mul_sqrt_inv_eq_one (PosDef_traceRight ρAB hρ)
  have hinv : σBC⁻¹⁻¹ = σBC := by
    haveI := nonSingular_of_posDef hσ
    exact HermitianMat.ext (Matrix.inv_inv_of_invertible _)
  have h2 : σBC.sqrt.mat * σBC⁻¹.mat * σBC.sqrt.mat = 1 := by
    have := sqrt_inv_mul_self_mul_sqrt_inv_eq_one (A := σBC⁻¹) hσ.inv
    rwa [hinv] at this
  simp only [S_mat, HermitianMat.mat_reindex, HermitianMat.kronecker_mat, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, h1, h2,
    Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

/- Key factorization: W_mat = (F ⊗ I_C) * (I_A ⊗ G).reindex, where
  F = ρAB.sqrt * (ρA⁻¹.sqrt ⊗ I_B) and G = (I_B ⊗ σC⁻¹.sqrt) * σBC.sqrt.
  This expresses W as a "contraction over the shared B index". -/
private lemma W_mat_eq_factored
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) :
    W_mat ρAB σBC =
      let F := ρAB.sqrt.mat * (ρAB.traceRight⁻¹.sqrt.mat ⊗ₖ (1 : Matrix dB dB ℂ))
      let G := ((1 : Matrix dB dB ℂ) ⊗ₖ σBC.traceLeft⁻¹.sqrt.mat) * σBC.sqrt.mat
      (F ⊗ₖ (1 : Matrix dC dC ℂ)) *
        ((1 : Matrix dA dA ℂ) ⊗ₖ G).reindex
          (Equiv.prodAssoc dA dB dC).symm (Equiv.prodAssoc dA dB dC).symm := by
  ext ⟨⟨a, b⟩, c⟩ ⟨⟨a', b'⟩, c'⟩
  simp [W_mat, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm.trans
    (Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring)

/- Connection between F and V_rho via the MES:
(F ⊗ I_B) * MES = V_rho, where F = ρAB.sqrt * (ρA⁻¹.sqrt ⊗ I_B).-/
private lemma F_tensor_MES_eq_V_rho
    (ρAB : HermitianMat (dA × dB) ℂ) :
    let F := ρAB.sqrt.mat * (ρAB.traceRight⁻¹.sqrt.mat ⊗ₖ (1 : Matrix dB dB ℂ))
    (F ⊗ₖ (1 : Matrix dB dB ℂ)) * map_to_tensor_MES dA dB = V_rho ρAB := by
  ext ⟨i, j⟩ k
  simp [V_rho, map_to_tensor_MES, Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type,
    ite_and]

section Wmat_calculation

variable {dA dB dC : Type*} [Fintype dA] [Fintype dB] [Fintype dC]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC]

abbrev BigIdx (dA dB dC : Type*) := ((dA × dB) × dB) × (dB × dC)
abbrev SmallIdx (dA dB dC : Type*) := (dA × dB) × dC
abbrev MidIdx (dA dB dC : Type*) := (dA × dB) × (dB × (dB × dC))

/-- The associator equivalence (no swap needed).
    Maps (((dA×dB)×dB)×(dB×dC)) to ((dA×dB)×(dB×(dB×dC))). -/
private def assoc_equiv (dA dB dC : Type*) :
    BigIdx dA dB dC ≃ MidIdx dA dB dC :=
  Equiv.prodAssoc (dA × dB) dB (dB × dC)

variable (dA dB dC) in
private def T₁_mat (ρAB : HermitianMat (dA × dB) ℂ) :
    Matrix (BigIdx dA dB dC) (SmallIdx dA dB dC) ℂ :=
  (V_rho ρAB ⊗ₖ (1 : Matrix (dB × dC) (dB × dC) ℂ)).reindex
    (Equiv.refl _) (Equiv.prodAssoc dA dB dC).symm

variable (dA dB dC) in
private def T₂_mat (σBC : HermitianMat (dB × dC) ℂ) :
    Matrix (SmallIdx dA dB dC) (MidIdx dA dB dC) ℂ :=
  (1 : Matrix (dA × dB) (dA × dB) ℂ) ⊗ₖ (V_sigma σBC)ᴴ

private def PERM_mat (dA dB dC : Type*) [Fintype dA] [Fintype dB] [Fintype dC]
    [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] :
    Matrix (MidIdx dA dB dC) (BigIdx dA dB dC) ℂ :=
  (1 : Matrix (BigIdx dA dB dC) (BigIdx dA dB dC) ℂ).reindex
    (assoc_equiv dA dB dC) (Equiv.refl _)

private lemma T₁_isometry [Nonempty dB]
    (ρAB : HermitianMat (dA × dB) ℂ) (hρ : ρAB.mat.PosDef) :
    (T₁_mat dA dB dC ρAB)ᴴ * (T₁_mat dA dB dC ρAB) = 1 := by
  have h_kron : (V_rho ρAB ⊗ₖ (1 : Matrix (dB × dC) (dB × dC) ℂ))ᴴ *
      (V_rho ρAB ⊗ₖ (1 : Matrix (dB × dC) (dB × dC) ℂ)) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
      Matrix.one_mul, V_rho_isometry ρAB hρ, Matrix.one_kronecker_one]
  rw [T₁_mat, Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    h_kron, Matrix.submatrix_one_equiv]

set_option maxHeartbeats 400000 in
private lemma T₂_sq_le_one [Nonempty dB]
    (σBC : HermitianMat (dB × dC) ℂ) (hσ : σBC.mat.PosDef) :
    (T₂_mat dA dB dC σBC)ᴴ * (T₂_mat dA dB dC σBC) ≤ 1 := by
  have h1 : ((1 : Matrix (dA × dB) (dA × dB) ℂ) ⊗ₖ V_sigma σBC)ᴴ *
      ((1 : Matrix (dA × dB) (dA × dB) ℂ) ⊗ₖ V_sigma σBC) = 1 := by
    rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
      Matrix.one_mul, V_sigma_isometry σBC hσ, Matrix.one_kronecker_one]
  have h2 := isometry_mul_conjTranspose_le_one _ h1
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one] at h2
  rw [T₂_mat, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.conjTranspose_conjTranspose]
  exact h2

private lemma PERM_isometry : (PERM_mat dA dB dC)ᴴ * PERM_mat dA dB dC = 1 := by
  simp [PERM_mat]

/-- Element-wise identity: W_mat = ∑_{b*} V_rho * V_sigma†.
    This is the key computation from Eq. (6) of Lin-Kim-Hsieh. -/
private lemma W_mat_entry (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (i j : SmallIdx dA dB dC) :
    W_mat ρAB σBC i j =
      ∑ b_star : dB,
        V_rho ρAB ((i.1, b_star)) j.1.1 *
        (V_sigma σBC)ᴴ i.2 (b_star, (j.1.2, j.2)) := by
  obtain ⟨⟨a, b⟩, c⟩ := i
  obtain ⟨⟨a', b'⟩, c'⟩ := j
  have h1 : (σBC.reindex (Equiv.prodComm dB dC)).traceRight = σBC.traceLeft := rfl
  have h2 : (σBC.reindex (Equiv.prodComm dB dC)).sqrt = σBC.sqrt.reindex (Equiv.prodComm dB dC) :=
    σBC.cfc_reindex Real.sqrt (Equiv.prodComm dB dC)
  have hs1 : ∀ (p q : dB × dC), star (σBC.sqrt p q) = σBC.sqrt q p := fun p q =>
    CStarMatrix.star_apply_of_isSelfAdjoint σBC.sqrt.2
  have hs2 : ∀ (p q : dC), star (σBC.traceLeft⁻¹.sqrt p q) = σBC.traceLeft⁻¹.sqrt q p := fun p q =>
    CStarMatrix.star_apply_of_isSelfAdjoint σBC.traceLeft⁻¹.sqrt.2
  simp [W_mat, V_sigma, V_rho, h1, h2, map_to_tensor_MES, Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ite_and, Finset.mul_sum, Finset.sum_mul]
  simp only [starRingEnd_apply, hs1, hs2]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_comm.trans
    (Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => by ring)

/-- Element-wise identity: RHS = ∑_{b*} V_rho * V_sigma†. -/
private lemma RHS_entry (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (i j : SmallIdx dA dB dC) :
    (T₂_mat dA dB dC σBC * PERM_mat dA dB dC * T₁_mat dA dB dC ρAB) i j =
      ∑ b_star : dB,
        V_rho ρAB ((i.1, b_star)) j.1.1 *
        (V_sigma σBC)ᴴ i.2 (b_star, (j.1.2, j.2)) := by
  obtain ⟨⟨a, b⟩, c⟩ := i
  obtain ⟨⟨a', b'⟩, c'⟩ := j
  simp [T₂_mat, T₁_mat, PERM_mat, assoc_equiv, Matrix.mul_apply, Matrix.one_apply,
    Fintype.sum_prod_type, ite_and, Finset.mul_sum, mul_comm]

private lemma W_mat_eq_three_factors [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ) :
    W_mat ρAB σBC =
      T₂_mat dA dB dC σBC * PERM_mat dA dB dC * T₁_mat dA dB dC ρAB := by
  ext i j
  rw [W_mat_entry, RHS_entry]

/-- Core inequality: W†W ≤ I.
This is the key step, following from the isometry argument:
V_rho ⊗ I_C and I_A ⊗ V_sigma are isometries, their cross product has norm ≤ 1,
and the result can be related to W_mat through the MES computation (Eq. 6 in Lin-Kim-Hsieh). -/
theorem W_mat_sq_le_one [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    (W_mat ρAB σBC)ᴴ * (W_mat ρAB σBC) ≤ 1 := by
  rw [W_mat_eq_three_factors]
  have h1 : (PERM_mat dA dB dC)ᴴ * ((T₂_mat dA dB dC σBC)ᴴ * (T₂_mat dA dB dC σBC)) *
      PERM_mat dA dB dC ≤ 1 := by
    simpa [PERM_isometry] using Matrix.PosSemidef.conjTranspose_mul_mul_mono
      (PERM_mat dA dB dC) (T₂_sq_le_one (dA := dA) σBC hσ)
  simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc, T₁_isometry _ hρ] using
    Matrix.PosSemidef.conjTranspose_mul_mul_mono (T₁_mat dA dB dC ρAB) h1

end Wmat_calculation

/- S_mat is invertible (since ρ_A and σ_BC are positive definite). -/
private lemma S_mat_isUnit [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    IsUnit (S_mat ρAB σBC) := by
  have h1 := (sqrt_posDef (A := ρAB.traceRight⁻¹) (PosDef_traceRight ρAB hρ).inv).det_pos.ne'
  have h2 := (sqrt_posDef hσ).det_pos.ne'
  simp [S_mat, Matrix.isUnit_iff_isUnit_det, Matrix.det_kronecker, isUnit_iff_ne_zero, h1, h2]

/-- The intermediate operator inequality: ρ_AB ⊗ σ_C⁻¹ ≤ (ρ_A ⊗ σ_BC⁻¹).reindex(assoc⁻¹).
  This is derived from W_mat_sq_le_one by algebraic manipulation (conjugation and simplification). -/
theorem intermediate_ineq [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    ρAB ⊗ₖ (σBC.traceLeft)⁻¹ ≤
      (ρAB.traceRight ⊗ₖ σBC⁻¹).reindex (Equiv.prodAssoc dA dB dC).symm := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (S_mat_isUnit ρAB σBC hρ hσ)
  have hi1 : (S_mat ρAB σBC)⁻¹ * S_mat ρAB σBC = 1 := Matrix.nonsing_inv_mul _ hdet
  have hi2 : S_mat ρAB σBC * (S_mat ρAB σBC)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have key : ∀ M : Matrix ((dA × dB) × dC) ((dA × dB) × dC) ℂ,
      (S_mat ρAB σBC)⁻¹ * (S_mat ρAB σBC * M * S_mat ρAB σBC) * (S_mat ρAB σBC)⁻¹ = M :=
    fun M => by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, hi2, Matrix.mul_one, ← Matrix.mul_assoc, hi1,
        Matrix.one_mul]
  have hSH : (S_mat ρAB σBC)ᴴ = S_mat ρAB σBC := by
    simp [S_mat, Matrix.conjTranspose_submatrix, Matrix.conjTranspose_kronecker]
  have h := W_mat_sq_le_one ρAB σBC hρ hσ
  rw [W_mat_sq_eq_conj ρAB σBC hρ hσ, ← S_mat_conj_rhs_eq_one ρAB σBC hρ hσ] at h
  have h2 := Matrix.PosSemidef.mul_mul_conjTranspose_same (Matrix.le_iff.mp h) (S_mat ρAB σBC)⁻¹
  rw [Matrix.conjTranspose_nonsing_inv, hSH, Matrix.mul_sub, Matrix.sub_mul, key, key] at h2
  rw [HermitianMat.le_iff]
  simpa using h2

open HermitianMat in
/-- **Operator extension of SSA** (Main result of Lin-Kim-Hsieh).
  For positive definite ρ_AB and σ_BC:
  `ρ_A⁻¹ ⊗ σ_BC ≤ ρ_AB⁻¹ ⊗ σ_C`
  where ρ_A = Tr_B(ρ_AB) and σ_C = Tr_B(σ_BC), and the RHS is reindexed
  via the associator `(dA × dB) × dC ≃ dA × (dB × dC)`. -/
theorem operator_ineq_SSA [Nonempty dA] [Nonempty dB] [Nonempty dC]
    (ρAB : HermitianMat (dA × dB) ℂ) (σBC : HermitianMat (dB × dC) ℂ)
    (hρ : ρAB.mat.PosDef) (hσ : σBC.mat.PosDef) :
    ρAB.traceRight⁻¹ ⊗ₖ σBC ≤
      (ρAB⁻¹ ⊗ₖ σBC.traceLeft).reindex (Equiv.prodAssoc dA dB dC) := by
  have hρA := PosDef_traceRight ρAB hρ
  have hσC := PosDef_traceLeft σBC hσ
  haveI := nonSingular_of_posDef hρ
  haveI := nonSingular_of_posDef hσ
  haveI := nonSingular_of_posDef hρA
  haveI := nonSingular_of_posDef hσC
  have hbc : σBC⁻¹⁻¹ = σBC := HermitianMat.ext (Matrix.inv_inv_of_invertible _)
  have hc : σBC.traceLeft⁻¹⁻¹ = σBC.traceLeft := HermitianMat.ext (Matrix.inv_inv_of_invertible _)
  have h := HermitianMat.inv_antitone
    (HermitianMat.PosDef_kronecker ρAB σBC.traceLeft⁻¹ hρ hσC.inv)
    (intermediate_ineq ρAB σBC hρ hσ)
  rw [HermitianMat.inv_reindex, HermitianMat.inv_kronecker, HermitianMat.inv_kronecker,
    hbc, hc] at h
  simpa using (HermitianMat.reindex_le_reindex_iff (Equiv.prodAssoc dA dB dC) _ _).mpr h

open scoped InnerProductSpace RealInnerProductSpace

/-! ### Weak monotonicity and SSA proof infrastructure -/
section SSA_proof

omit [DecidableEq d₁] in
open HermitianMat in
private lemma inner_kron_one_eq_inner_traceRight
    (A : HermitianMat d₁ ℂ) (M : HermitianMat (d₁ × d₂) ℂ) :
    ⟪A ⊗ₖ (1 : HermitianMat d₂ ℂ), M⟫ = ⟪A, M.traceRight⟫ := by
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace, Matrix.trace_mul_comm,
    HermitianMat.kronecker_mat, HermitianMat.mat_one, Matrix.trace_mul_kron_one_right,
    ← HermitianMat.traceRight_mat, Matrix.trace_mul_comm]

omit [DecidableEq d₂] in
open HermitianMat in
private lemma inner_one_kron_eq_inner_traceLeft
    (B : HermitianMat d₂ ℂ) (M : HermitianMat (d₁ × d₂) ℂ) :
    ⟪(1 : HermitianMat d₁ ℂ) ⊗ₖ B, M⟫ = ⟪B, M.traceLeft⟫ := by
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace, Matrix.trace_mul_comm,
    HermitianMat.kronecker_mat, HermitianMat.mat_one, Matrix.trace_mul_one_kron_right,
    ← HermitianMat.traceLeft_mat, Matrix.trace_mul_comm]

open HermitianMat in
private lemma hermitianMat_log_inv_eq_neg
    (A : HermitianMat d₁ ℂ) [A.NonSingular] : A⁻¹.log = -A.log := by
  rw [← HermitianMat.cfc_inv (A := A), HermitianMat.log, ← HermitianMat.cfc_comp,
    HermitianMat.log, ← HermitianMat.cfc_neg]
  exact congrArg A.cfc (funext fun x => Real.log_inv x)

private lemma PosDef_assoc'_traceRight
    (ρ : MState (d₁ × d₂ × d₃)) (hρ : ρ.M.mat.PosDef) :
    ρ.assoc'.traceRight.M.mat.PosDef := by
  have _ := ρ.nonempty |> nonempty_prod.mp |>.right |> nonempty_prod.mp |>.right
  apply PosDef_traceRight
  convert! hρ.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm

private lemma wm_inner_lhs [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) :
    ⟪(-ρ.assoc'.traceRight.M.traceRight.log) ⊗ₖ (1 : HermitianMat (d₂ × d₃) ℂ) +
     (1 : HermitianMat d₁ ℂ) ⊗ₖ ρ.traceLeft.M.log, ρ.M⟫ =
    Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft := by
  have h12 : ρ.assoc'.traceRight.M.traceRight = ρ.traceRight.M := by
    rw [← MState.traceRight_M, MState.traceRight_right_assoc']
  rw [h12, inner_add_left, inner_kron_one_eq_inner_traceRight, inner_one_kron_eq_inner_traceLeft,
    Sᵥₙ_eq_neg_trace_log, Sᵥₙ_eq_neg_trace_log, inner_neg_left, ← MState.traceRight_M,
    ← MState.traceLeft_M]
  ring

private lemma wm_inner_rhs [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) :
    ⟪((-ρ.assoc'.traceRight.M.log) ⊗ₖ (1 : HermitianMat d₃ ℂ) +
     (1 : HermitianMat (d₁ × d₂) ℂ) ⊗ₖ ρ.traceLeft.M.traceLeft.log).reindex
      (Equiv.prodAssoc d₁ d₂ d₃), ρ.M⟫ =
    Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft := by
  rw [HermitianMat.reindex_inner,
    show ρ.M.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm = ρ.assoc'.M from rfl,
    inner_add_left, inner_kron_one_eq_inner_traceRight, inner_one_kron_eq_inner_traceLeft]
  simp [Sᵥₙ_eq_neg_trace_log, ← MState.traceRight_M, ← MState.traceLeft_M, inner_neg_left]

/-- Weak monotonicity (form 2) for positive definite states:
    S(ρ₁₂) + S(ρ₂₃) ≥ S(ρ₁) + S(ρ₃).
    Proved by applying operator_ineq_SSA, taking log, then inner product with ρ. -/
private lemma Sᵥₙ_wm_pd [Nonempty d₁] [Nonempty d₂] [Nonempty d₃]
    (ρ : MState (d₁ × d₂ × d₃)) (hρ : ρ.M.mat.PosDef) :
    Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft ≤
    Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft := by
  -- Set up marginals and their PD properties
  have h₁₂ := PosDef_assoc'_traceRight ρ hρ
  have h₂₃ := PosDef_traceLeft ρ.M hρ
  haveI : ρ.assoc'.traceRight.M.NonSingular := nonSingular_of_posDef h₁₂
  haveI : ρ.traceLeft.M.NonSingular := nonSingular_of_posDef h₂₃
  haveI : ρ.assoc'.traceRight.M.traceRight.NonSingular :=
    nonSingular_of_posDef (PosDef_traceRight _ h₁₂)
  haveI : ρ.traceLeft.M.traceLeft.NonSingular :=
    nonSingular_of_posDef (PosDef_traceLeft _ h₂₃)
  -- Step 1: Operator inequality
  have h_op := operator_ineq_SSA ρ.assoc'.traceRight.M ρ.traceLeft.M h₁₂ h₂₃
  -- Step 2: Take log
  have h_lhs_pd : (ρ.assoc'.traceRight.M.traceRight⁻¹ ⊗ₖ ρ.traceLeft.M).mat.PosDef :=
    HermitianMat.PosDef_kronecker _ _ (PosDef_traceRight _ h₁₂).inv h₂₃
  have h_log := HermitianMat.log_mono h_lhs_pd h_op
  -- Step 3: Simplify logs
  rw [HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  rw [HermitianMat.reindex_log, HermitianMat.log_kron, hermitianMat_log_inv_eq_neg] at h_log
  -- Step 4: Take inner product with ρ.M (≥ 0)
  have h_inner := HermitianMat.inner_mono ρ.nonneg h_log
  -- Step 5: Use commutativity to match wm_inner_lhs/rhs forms
  rw [HermitianMat.inner_comm, HermitianMat.inner_comm ρ.M] at h_inner
  rw [wm_inner_lhs ρ, wm_inner_rhs ρ] at h_inner
  linarith

set_option backward.isDefEq.respectTransparency false in
private lemma MState.approx_by_pd
    (ρ : MState d₁) :
    ∃ (ρn : ℕ → MState d₁), (∀ n, (ρn n).M.mat.PosDef) ∧
      Filter.Tendsto ρn Filter.atTop (nhds ρ) := by
  have h_ne1 := ρ.nonempty
  set εn : ℕ → ℝ := fun n => 1 / (n + 2)
  have hε0 : ∀ n, 0 < εn n := fun n => by positivity
  set ρn : ℕ → MState d₁ := fun n => Mixable.mix ⟨εn n, by
    exact ⟨(hε0 n).le, by rw [div_le_iff₀] <;> linarith⟩⟩ (MState.uniform) ρ
  refine ⟨ρn, fun n => MState.PosDef_mix_of_ne_zero MState.uniform_posDef _
    (ne_of_apply_ne Subtype.val (hε0 n).ne'), ?_⟩
  have hε : Filter.Tendsto εn Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have h1 : Filter.Tendsto (fun n => 1 - εn n) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hε
  have h_conv := (hε.smul_const (MState.uniform (d := d₁)).M).add (h1.smul_const ρ.M)
  simp only [zero_smul, zero_add, one_smul] at h_conv
  rw [tendsto_iff_dist_tendsto_zero] at *
  convert h_conv using 1
  ext n
  simp [ρn, Mixable.mix]
  congr! 1

set_option backward.isDefEq.respectTransparency false in
@[fun_prop]
private lemma MState.traceLeft_continuous :
    Continuous (MState.traceLeft : MState (d₁ × d₂) → MState d₂) := by
  have h1 : Continuous (fun ρ : Matrix (d₁ × d₂) (d₁ × d₂) ℂ => ρ.traceLeft) :=
    continuous_pi fun _ => continuous_pi fun _ => continuous_finsetSum _ fun _ _ =>
      (continuous_apply _).comp (continuous_apply _)
  have h_cont : Continuous
      (HermitianMat.traceLeft : HermitianMat (d₁ × d₂) ℂ → HermitianMat d₂ ℂ) :=
    Continuous.subtype_mk (h1.comp continuous_subtype_val) _
  exact continuous_induced_rng.mpr (by continuity)

@[fun_prop]
private lemma MState.traceRight_continuous :
    Continuous (MState.traceRight : MState (d₁ × d₂) → MState d₁) := by
  have h1 : Continuous (fun ρ : Matrix (d₁ × d₂) (d₁ × d₂) ℂ => ρ.traceRight) :=
    continuous_pi fun _ => continuous_pi fun _ => continuous_finsetSum _ fun _ _ =>
      (continuous_apply _).comp (continuous_apply _)
  have h_cont : Continuous
      (HermitianMat.traceRight : HermitianMat (d₁ × d₂) ℂ → HermitianMat d₁ ℂ) :=
    Continuous.subtype_mk (h1.comp continuous_subtype_val) _
  exact continuous_induced_rng.mpr (by continuity)

@[fun_prop]
private lemma MState.assoc'_continuous :
    Continuous (MState.assoc' : MState (d₁ × d₂ × d₃) → MState ((d₁ × d₂) × d₃)) := by
  apply continuous_induced_rng.mpr;
  -- The reindex function is continuous because it is a composition of continuous functions (permutations).
  have h_reindex_cont : Continuous (fun ρ : HermitianMat (d₁ × d₂ × d₃) ℂ => ρ.reindex (Equiv.prodAssoc d₁ d₂ d₃).symm) := by
    apply continuous_induced_rng.mpr;
    fun_prop (disch := norm_num);
  convert! h_reindex_cont.comp _ using 2;
  exact Continuous_HermitianMat

/-- Weak monotonicity, version with partial traces. -/
lemma Sᵥₙ_wm (ρ : MState (d₁ × d₂ × d₃)) :
    Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft.traceLeft ≤
    Sᵥₙ ρ.assoc'.traceRight + Sᵥₙ ρ.traceLeft := by
  have h_ne123 := ρ.nonempty
  have ⟨_, hn23⟩ := nonempty_prod.mp h_ne123
  have ⟨_, _⟩ := nonempty_prod.mp hn23
  obtain ⟨ρn, hρn_pos, hρn⟩ := MState.approx_by_pd ρ
  have hc1 : Continuous fun σ : MState (d₁ × d₂ × d₃) =>
      Sᵥₙ σ.traceRight + Sᵥₙ σ.traceLeft.traceLeft := by fun_prop
  have hc2 : Continuous fun σ : MState (d₁ × d₂ × d₃) =>
      Sᵥₙ σ.assoc'.traceRight + Sᵥₙ σ.traceLeft := by fun_prop
  exact le_of_tendsto_of_tendsto' ((hc1.tendsto ρ).comp hρn) ((hc2.tendsto ρ).comp hρn)
    fun n => Sᵥₙ_wm_pd _ (hρn_pos n)

/-- Permutation to relabel (A×B×C)×R as A×(B×C×R). -/
private def perm_A_BCR' (dA dB dC : Type*) :
    (dA × dB × dC) × (dA × dB × dC) ≃ dA × (dB × dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (a, (b,c,r))
  invFun x := let (a, (b,c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The BCR state: trace out A from the purification of ρ_ABC. -/
private def ρBCR (ρ : MState (dA × dB × dC)) : MState (dB × dC × (dA × dB × dC)) :=
  ((MState.pure ρ.purify).relabel (perm_A_BCR' dA dB dC).symm).traceLeft

private lemma S_BC_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).assoc'.traceRight = Sᵥₙ ρ.traceLeft := by
  -- By definition of ρBCR, we know that its BC-marginal is equal to the BC-marginal of ρ.
  have h_marginal : (ρBCR ρ).assoc'.traceRight = ρ.traceLeft := by
    unfold ρBCR MState.traceLeft MState.traceRight MState.assoc';
    simp [ MState.assoc, MState.SWAP, MState.relabel, MState.pure, perm_A_BCR' ];
    unfold reindex HermitianMat.traceLeft HermitianMat.traceRight; ext
    simp
    simp [ Matrix.traceLeft, Matrix.traceRight, Matrix.submatrix ];
    have := ρ.purify_spec;
    replace this := congr_arg ( fun x => x.M.val ) this ; simp_all [ MState.traceRight, MState.pure ];
    simp [ ← this, Matrix.traceRight, Matrix.vecMulVec ];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
  rw [h_marginal]

/-- Equivalence to relabel the purification as (dA × dB) × (dC × R). -/
private def perm_AB_CR' (dA dB dC : Type*) :
    (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dB) × (dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,b), (c,r))
  invFun x := let ((a,b), (c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

set_option backward.isDefEq.respectTransparency false in
/- The CR-marginal of ρBCR equals the traceLeft of the AB|CR-relabeled purification. -/
private lemma BCR_traceLeft_eq_purify_traceLeft (ρ : MState (dA × dB × dC)) :
    (ρBCR ρ).traceLeft =
    ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceLeft := by
  convert MState.ext ?_;
  convert MState.ext ?_;
  any_goals exact ρ.traceLeft.traceLeft;
  · simp [ MState.traceLeft, MState.relabel, perm_AB_CR' ];
    simp [ MState.traceLeft, MState.relabel, ρBCR ];
    unfold HermitianMat.traceLeft
    simp only [mat_reindex, MState.mat_M, Matrix.reindex_apply, mat_mk, Equiv.coe_fn_symm_mk]
    unfold Matrix.traceLeft
    simp
    congr! 2
    ext i₁ j₁
    rw [ ← Finset.sum_product' ]
    simp [ perm_A_BCR' ]
    exact Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) ( by simp ) ( by simp ) ( by simp ) ( by simp );
  · rfl

/- The traceRight of the AB|CR-relabeled purification has same entropy as ρ.assoc'.traceRight. -/
private lemma purify_AB_traceRight_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceRight =
    Sᵥₙ ρ.assoc'.traceRight := by
  have h_traceRight : ((MState.pure ρ.purify).relabel (perm_AB_CR' dA dB dC).symm).traceRight = ρ.assoc'.traceRight := by
    have h_traceRight : (MState.pure ρ.purify).traceRight = ρ := by
      exact MState.purify_spec ρ;
    convert congr_arg ( fun m => m.assoc'.traceRight ) h_traceRight using 1;
    ext i j; simp [ MState.traceRight, MState.assoc' ] ;
    simp [ HermitianMat.traceRight, MState.SWAP, MState.assoc ];
    simp [ Matrix.traceRight, Matrix.submatrix ];
    congr! 2;
    ext i j; simp [ perm_AB_CR' ] ;
    exact Fintype.sum_prod_type _
  rw [h_traceRight]

/-- The CR-marginal of ρBCR has the same entropy as the AB-marginal of ρ. -/
private lemma S_CR_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceLeft = Sᵥₙ ρ.assoc'.traceRight := by
  rw [BCR_traceLeft_eq_purify_traceLeft]
  rw [Sᵥₙ_pure_complement ρ.purify (perm_AB_CR' dA dB dC).symm]
  exact purify_AB_traceRight_eq ρ

private lemma S_B_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceRight = Sᵥₙ ρ.traceLeft.traceRight := by
  unfold ρBCR;
  unfold MState.traceLeft MState.traceRight MState.relabel MState.pure;
  simp [ HermitianMat.traceLeft, HermitianMat.traceRight, perm_A_BCR' ];
  unfold Matrix.traceLeft Matrix.traceRight; simp [Matrix.vecMulVec ] ;
  -- By definition of purification, we know that ρ.purify is a purification of ρ.m.
  have h_purify : ∀ (i j : dA × dB × dC), ρ.m i j = ∑ r : dA × dB × dC, ρ.purify (i, r) * (starRingEnd ℂ) (ρ.purify (j, r)) := by
    intro i j
    have := ρ.purify_spec;
    replace this := congr_arg ( fun m => m.M i j ) this
    simp_all [MState.traceRight]
    exact this.symm
  simp only [Finset.sum_sigma', h_purify];
  congr! 3;
  ext i₂ j₂
  simp
  ring_nf
  refine' Finset.sum_bij ( fun x _ => ⟨ x.fst.1, x.snd, x.fst.2 ⟩ ) _ _ _ _ <;> simp
  · grind
  · grind

private lemma S_R_of_BCR_eq (ρ : MState (dA × dB × dC)) :
    Sᵥₙ (ρBCR ρ).traceLeft.traceLeft = Sᵥₙ ρ := by
  have h_trace : (ρBCR ρ).traceLeft.traceLeft = (MState.pure ρ.purify).traceLeft := by
    unfold ρBCR MState.traceLeft;
    ext i j;
    simp [ HermitianMat.traceLeft];
    simp [ perm_A_BCR', Matrix.traceLeft ];
    simp [ Finset.sum_sigma' ];
    refine' Finset.sum_bij ( fun x _ => ( x.snd.snd, x.snd.fst, x.fst ) ) _ _ _ _ <;> simp
    grind;
  convert Sᵥₙ_of_partial_eq ρ.purify using 1;
  · rw [h_trace];
  · rw [ ρ.purify_spec ]

/-- Strong subadditivity on a tripartite system -/
theorem Sᵥₙ_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.traceRight;
    let ρ₂₃ := ρ₁₂₃.traceLeft;
    let ρ₂ := ρ₁₂₃.traceLeft.traceRight;
    Sᵥₙ ρ₁₂₃ + Sᵥₙ ρ₂ ≤ Sᵥₙ ρ₁₂ + Sᵥₙ ρ₂₃ := by
  have _ := ρ₁₂₃.nonempty |> nonempty_prod.mp |>.right |> nonempty_prod.mp |>.right
  -- Apply weak monotonicity to ρBCR, then substitute purification identities
  have h_wm := Sᵥₙ_wm (ρBCR ρ₁₂₃)
  rw [S_BC_of_BCR_eq, S_CR_of_BCR_eq, S_B_of_BCR_eq, S_R_of_BCR_eq] at h_wm
  linarith

/-- "Ordinary" subadditivity of von Neumann entropy -/
theorem Sᵥₙ_subadditivity (ρ : MState (d₁ × d₂)) :
    Sᵥₙ ρ ≤ Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft := by
  have := Sᵥₙ_strong_subadditivity (ρ.relabel (d₂ := d₁ × Unit × d₂)
    ⟨fun x ↦ (x.1, x.2.2), fun x ↦ (x.1, ⟨(), x.2⟩), fun x ↦ by simp, fun x ↦ by simp⟩)
  simp [Sᵥₙ_relabel] at this
  convert this using 1
  congr 1
  · convert Sᵥₙ_relabel _ (Equiv.prodPUnit _).symm
    exact rfl
  · convert Sᵥₙ_relabel _ (Equiv.punitProd _).symm
    exact rfl

/-- Triangle inequality for pure tripartite states: S(A) ≤ S(B) + S(C). -/
theorem Sᵥₙ_pure_tripartite_triangle (ψ : Ket ((d₁ × d₂) × d₃)) :
    Sᵥₙ (MState.pure ψ).traceRight.traceRight ≤
    Sᵥₙ (MState.pure ψ).traceRight.traceLeft + Sᵥₙ (MState.pure ψ).traceLeft := by
  have h_subadd := Sᵥₙ_subadditivity (MState.pure ψ).assoc.traceLeft
  obtain ⟨ψ', hψ'⟩ : ∃ ψ', (MState.pure ψ).assoc = _ :=
    MState.relabel_pure_exists ψ _
  grind [Sᵥₙ_of_partial_eq, MState.traceLeft_left_assoc,
    MState.traceLeft_right_assoc, MState.traceRight_assoc]

/-- One direction of the Araki-Lieb triangle inequality: S(A) ≤ S(B) + S(AB). -/
theorem Sᵥₙ_triangle_ineq_one_way (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.traceRight ≤ Sᵥₙ ρ.traceLeft + Sᵥₙ ρ := by
  have := Sᵥₙ_pure_tripartite_triangle ρ.purify
  have := Sᵥₙ_of_partial_eq ρ.purify
  aesop

/-- Araki-Lieb triangle inequality on von Neumann entropy -/
theorem Sᵥₙ_triangle_subaddivity (ρ : MState (d₁ × d₂)) :
    abs (Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft) ≤ Sᵥₙ ρ := by
  rw [abs_sub_le_iff]
  constructor
  · have := Sᵥₙ_triangle_ineq_one_way ρ
    grind only
  · have := Sᵥₙ_triangle_ineq_one_way ρ.SWAP
    grind only [Sᵥₙ_triangle_ineq_one_way, Sᵥₙ_of_SWAP_eq, MState.traceRight_SWAP,
      MState.traceLeft_SWAP]

/-- Weak monotonicity of quantum conditional entropy: S(A|B) + S(A|C) ≥ 0. -/
theorem Sᵥₙ_weak_monotonicity (ρ : MState (dA × dB × dC)) :
    let ρAB := ρ.assoc'.traceRight
    let ρAC := ρ.SWAP.assoc.traceLeft.SWAP
    0 ≤ qConditionalEnt ρAB + qConditionalEnt ρAC := by
  simp only [qConditionalEnt, MState.traceRight_left_assoc', Sᵥₙ_of_SWAP_eq]
  rw [add_sub, sub_add_eq_add_sub, le_sub_iff_add_le, le_sub_iff_add_le, zero_add]
  nth_rw 2 [add_comm]
  have := Sᵥₙ_wm ρ.SWAP.assoc.SWAP.assoc
  simp_all only [MState.traceRight_assoc, MState.traceRight_SWAP, MState.traceLeft_right_assoc,
    MState.traceLeft_left_assoc, MState.traceLeft_SWAP, MState.assoc'_assoc, ge_iff_le]
  exact this

/-- Strong subadditivity, stated in terms of conditional entropies.
  Also called the data processing inequality. H(A|BC) ≤ H(A|B). -/
theorem qConditionalEnt_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qConditionalEnt ρ₁₂₃ ≤ qConditionalEnt ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qConditionalEnt, MState.traceRight_left_assoc']
  linarith

/-- Strong subadditivity, stated in terms of quantum mutual information.
  I(A;BC) ≥ I(A;B). -/
theorem qMutualInfo_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qMutualInfo ρ₁₂₃ ≥ qMutualInfo ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qMutualInfo, MState.traceRight_left_assoc', MState.traceRight_right_assoc']
  linarith

/-- The quantum conditional mutual information `QCMI` is nonnegative. -/
theorem qcmi_nonneg (ρ : MState (dA × dB × dC)) :
    0 ≤ qcmi ρ := by
  simp [qcmi, qConditionalEnt]
  have := Sᵥₙ_strong_subadditivity ρ
  linarith

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dA. -/
theorem qcmi_le_2_log_dim (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dA) := by
  have := Sᵥₙ_subadditivity ρ.assoc'.traceRight
  have := abs_le.mp (Sᵥₙ_triangle_subaddivity ρ)
  grind [qcmi, qConditionalEnt, Sᵥₙ_nonneg, Sᵥₙ_le_log_d]

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dC. -/
theorem qcmi_le_2_log_dim' (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dC) := by
  have h_araki_lieb_assoc' : Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft ≤ Sᵥₙ ρ := by
    apply le_of_abs_le
    rw [← ρ.traceLeft_assoc', ← Sᵥₙ_of_assoc'_eq ρ]
    exact Sᵥₙ_triangle_subaddivity ρ.assoc'
  have := Sᵥₙ_subadditivity ρ.traceLeft
  grind [qcmi, qConditionalEnt, Sᵥₙ_le_log_d, MState.traceRight_left_assoc']

/- The chain rule for quantum conditional mutual information:
`I(A₁A₂ : C | B) = I(A₁:C|B) + I(A₂:C|BA₁)`.

It should be something like this, but it's hard to track the indices correctly:
theorem qcmi_chain_rule (ρ : MState ((dA₁ × dA₂) × dB × dC)) :
    let ρA₁BC := ρ.assoc.SWAP.assoc.traceLeft.SWAP;
    let ρA₂BA₁C : MState (dA₂ × (dA₁ × dB) × dC) :=
      ((CPTPMap.id ⊗ₖ CPTPMap.assoc').compose (CPTPMap.assoc.compose (CPTPMap.SWAP ⊗ₖ CPTPMap.id))) ρ;
    qcmi ρ = qcmi ρA₁BC + qcmi ρA₂BA₁C
     := by
  admit
-/
