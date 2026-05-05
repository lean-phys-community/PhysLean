/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Rpow
import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LiebAndoTrace
import Mathlib

/-! ## Bridge lemmas: HermitianMat ↔ L (EuclideanSpace ℂ d)

We use `Matrix.toEuclideanCLM` (a `≃⋆ₐ[ℂ]`) to bridge between `Matrix d d ℂ`
and bounded operators on `EuclideanSpace ℂ d`. This allows us to apply
the Lieb–Ando trace inequalities proved in `LiebAndoTrace.lean` to
`HermitianMat` trace functionals.
-/

variable {d : Type*} [Fintype d] [DecidableEq d]

namespace HermitianMatBridge

open LiebAndoTrace GeneralizedPerspectiveFunction

/-- Abbreviation for the star algebra isomorphism. -/
noncomputable abbrev Φ : Matrix d d ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)

/-- `Φ` is continuous (as a linear map between finite-dimensional spaces). -/
lemma Φ_continuous : Continuous (⇑Φ : Matrix d d ℂ → _) :=
  (Φ (d := d)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

/-- `Φ` maps Hermitian matrices to self-adjoint operators. -/
lemma Φ_isSelfAdjoint (A : HermitianMat d ℂ) :
    IsSelfAdjoint (Φ A.mat) := by
  rw [isSelfAdjoint_iff, ← map_star (Φ (d := d))]
  congr 1; exact A.conjTranspose_mat

/-
`Φ` preserves nonneg: PSD HermitianMat maps to nonneg operators.
-/
lemma Φ_nonneg (A : HermitianMat d ℂ) (hA : 0 ≤ A) :
    (0 : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) ≤ Φ A.mat := by
  refine' { .. };
  · convert Φ_isSelfAdjoint A using 1;
    simp +decide [ IsSelfAdjoint, LinearMap.IsSymmetric ];
    simp +decide [ ContinuousLinearMap.ext_iff, ContinuousLinearMap.star_eq_adjoint ];
    grind +suggestions;
  · intro x;
    have h_inner : ∀ x : EuclideanSpace ℂ d, 0 ≤ Complex.re (inner ℂ x (Φ A.mat x)) := by
      intro x;
      have h_inner : 0 ≤ Complex.re (∑ i, ∑ j, star (x i) * A.mat i j * x j) := by
        have := hA.2;
        specialize this ( Finsupp.equivFunOnFinite.symm x.ofLp ) ; simp_all +decide [ Finsupp.sum_fintype ];
        simp_all +decide [ Complex.le_def, Complex.ext_iff ];
      convert h_inner using 1;
      simp +decide [ inner, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
      simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm, Finset.sum_add_distrib ];
      simp +decide [ mul_add, mul_sub, Finset.mul_sum _ _ _, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc, mul_comm, mul_left_comm, Finset.sum_mul ];
      ring;
    convert h_inner x using 1;
    simp +decide [ ContinuousLinearMap.reApplyInnerSelf ];
    rw [ ← inner_conj_symm, Complex.conj_re ]

open ComplexOrder in
/-- `Φ` maps PosDef HermitianMat to pdSet. -/
lemma Φ_mem_pdSet [Nonempty d] (A : HermitianMat d ℂ) (hA : A.mat.PosDef) :
    Φ A.mat ∈ pdSet (ℋ := EuclideanSpace ℂ d) := by
  have h_spectrum : spectrum ℝ (Φ A.mat) = spectrum ℝ A.mat := by
    ext x;
    simp +decide [ spectrum.mem_iff, Matrix.PosDef ];
    rw [ show ( algebraMap ℝ ( EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d ) ) x = Φ ( algebraMap ℝ ( Matrix d d ℂ ) x ) from ?_, show ( algebraMap ℝ ( Matrix d d ℂ ) ) x = x • 1 from ?_ ];
    · simp +decide [ ← map_sub, ← map_smul ];
    · simp +decide [ Algebra.smul_def ];
    · ext; simp [Φ];
      simp +decide [ Algebra.algebraMap_eq_smul_one, Matrix.mulVec, dotProduct ];
      simp +decide [ Matrix.one_apply, Finset.sum_ite_eq ];
  refine' ⟨ Φ_isSelfAdjoint A, h_spectrum.symm ▸ _ ⟩;
  exact?

/-- `Φ` commutes with CFC for Hermitian matrices. -/
lemma Φ_cfc (A : HermitianMat d ℂ) (f : ℝ → ℝ) :
    Φ (cfc f A.mat) = cfc f (Φ A.mat) := by
  exact StarAlgHomClass.map_cfc Φ f A.mat (hφ := Φ_continuous)
    (ha := A.H.isSelfAdjoint)

/-- `Φ` commutes with rpow for PSD matrices. -/
lemma Φ_rpow (A : HermitianMat d ℂ) (hA : 0 ≤ A) (r : ℝ) :
    Φ (A ^ r).mat = (Φ A.mat) ^ r := by
  rw [HermitianMat.rpow_eq_cfc, HermitianMat.mat_cfc]
  rw [Φ_cfc, CFC.rpow_eq_cfc_real (ha := Φ_nonneg A hA)]

/-
The `traceRe` on `L ℋ` agrees with `HermitianMat.trace` through `Φ`.
-/
lemma traceRe_Φ (A : HermitianMat d ℂ) :
    traceRe (Φ A.mat) = A.trace := by
  convert congr_arg Complex.re ?_;
  convert LinearMap.trace_eq_matrix_trace _ _;
  any_goals exact Pi.basisFun ℂ d;
  all_goals try infer_instance;
  constructor <;> intro h;
  · exact?;
  · convert h _;
    rotate_right;
    exact Matrix.toLin ( Pi.basisFun ℂ d ) ( Pi.basisFun ℂ d ) A.mat;
    · convert LinearMap.trace_conj' _ _;
    · exact?

set_option maxHeartbeats 800000 in
/-- General trace bridge: the operator trace of Φ(M) equals the matrix trace of M,
for any matrix M (not just Hermitian). -/
lemma trace_Φ_eq (M : Matrix d d ℂ) :
    (LinearMap.trace ℂ (EuclideanSpace ℂ d)) (Φ M).toLinearMap = M.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun d ℂ).toBasis]
  congr 1
  ext i j
  simp [Φ, Matrix.toEuclideanCLM, EuclideanSpace.basisFun]

/-- `traceRe(Φ(M)) = re(Tr[M])` for any matrix M. -/
lemma traceRe_Φ_general (M : Matrix d d ℂ) :
    traceRe (Φ M) = Complex.re M.trace := by
  simp [traceRe, trace_Φ_eq]

end HermitianMatBridge
