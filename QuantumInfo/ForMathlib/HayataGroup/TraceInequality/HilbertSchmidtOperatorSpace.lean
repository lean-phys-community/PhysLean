/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzTheorem
public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.GeneralizedPerspectiveFunction

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace HilbertSchmidtOperatorSpace

open LownerHeinzTheorem

universe u

noncomputable section

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ]

/-- The canonical finite index used for Hilbert-Schmidt coordinates. -/
abbrev HSIndex (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  Fin (Module.finrank ℂ ℋ)

/-- The standard orthonormal basis on a finite-dimensional Hilbert space. -/
noncomputable abbrev hsOrthonormalBasis :
    OrthonormalBasis (HSIndex ℋ) ℂ ℋ :=
  stdOrthonormalBasis ℂ ℋ

/-- Coordinate space for Hilbert-Schmidt operators. -/
abbrev HSCoords (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  EuclideanSpace ℂ (HSIndex ℋ × HSIndex ℋ)

/-- The underlying coordinate function space for Hilbert-Schmidt operators. -/
abbrev HSCoordFun (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  HSIndex ℋ × HSIndex ℋ → ℂ

/-- The operator space `L ℋ`, viewed later with the Hilbert-Schmidt structure. -/
def HSOp (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  L ℋ

instance : AddCommGroup (HSOp ℋ) := by
  delta HSOp
  infer_instance

set_option synthInstance.maxHeartbeats 200000 in
instance : Module ℂ (HSOp ℋ) := by
  show Module ℂ (ℋ →L[ℂ] ℋ)
  infer_instance

instance : Star (HSOp ℋ) := by
  delta HSOp
  infer_instance

instance : Mul (HSOp ℋ) := by
  delta HSOp
  infer_instance

instance : One (HSOp ℋ) := by
  delta HSOp
  infer_instance

instance : Inhabited (HSOp ℋ) := by
  delta HSOp
  infer_instance

instance : Zero (HSOp ℋ) := by
  delta HSOp
  infer_instance

set_option synthInstance.maxHeartbeats 200000 in
instance : FiniteDimensional ℂ (HSOp ℋ) := by
  show FiniteDimensional ℂ (ℋ →L[ℂ] ℋ)
  infer_instance

noncomputable def hsCoordsLinearEquiv :
    HSCoords ℋ ≃ₗ[ℂ] (HSCoordFun ℋ) := by
  simpa [HSCoords, HSCoordFun] using
    (WithLp.linearEquiv (2 : ENNReal) ℂ (HSCoordFun ℋ))

def matrixToFun :
    Matrix (HSIndex ℋ) (HSIndex ℋ) ℂ ≃ₗ[ℂ] HSCoordFun ℋ where
  toFun M p := M p.1 p.2
  invFun f i j := f (i, j)
  map_add' M N := by rfl
  map_smul' c M := by rfl
  left_inv M := by rfl
  right_inv f := by rfl

noncomputable def matrixToCoords :
    Matrix (HSIndex ℋ) (HSIndex ℋ) ℂ ≃ₗ[ℂ] HSCoords ℋ :=
  (matrixToFun (ℋ := ℋ)).trans hsCoordsLinearEquiv.symm

/-- Forget continuity and identify continuous linear operators with linear endomorphisms. -/
noncomputable def hsLinearMapEquiv :
    HSOp ℋ ≃ₗ[ℂ] (ℋ →ₗ[ℂ] ℋ) :=
  LinearMap.toContinuousLinearMap.symm

/-- Hilbert-Schmidt coordinates on `L ℋ`. -/
noncomputable def toHSCoordsLinearEquiv :
    HSOp ℋ ≃ₗ[ℂ] HSCoords ℋ :=
  (hsLinearMapEquiv (ℋ := ℋ)).trans <|
    (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      (hsOrthonormalBasis (ℋ := ℋ)).toBasis).trans <|
      matrixToCoords (ℋ := ℋ)

omit [CompleteSpace ℋ] in
@[simp] lemma toHSCoordsLinearEquiv_apply_apply
    (T : HSOp ℋ) (i j : HSIndex ℋ) :
    toHSCoordsLinearEquiv (ℋ := ℋ) T (i, j) =
      LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
        (hsOrthonormalBasis (ℋ := ℋ)).toBasis
        ((hsLinearMapEquiv (ℋ := ℋ)) T) i j := rfl

instance : NormedAddCommGroup (HSOp ℋ) :=
  NormedAddCommGroup.induced (HSOp ℋ) (HSCoords ℋ)
    (toHSCoordsLinearEquiv (ℋ := ℋ)) (toHSCoordsLinearEquiv (ℋ := ℋ)).injective

instance : NormedSpace ℂ (HSOp ℋ) :=
  NormedSpace.induced ℂ (HSOp ℋ) (HSCoords ℋ) (toHSCoordsLinearEquiv (ℋ := ℋ))

instance : Inner ℂ (HSOp ℋ) where
  inner T S := inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T) (toHSCoordsLinearEquiv (ℋ := ℋ) S)

instance : InnerProductSpace ℂ (HSOp ℋ) where
  norm_sq_eq_re_inner T :=
    (inner_self_eq_norm_sq (𝕜 := ℂ) (toHSCoordsLinearEquiv (ℋ := ℋ) T)).symm
  conj_inner_symm T S :=
    inner_conj_symm (toHSCoordsLinearEquiv (ℋ := ℋ) T) (toHSCoordsLinearEquiv (ℋ := ℋ) S)
  add_left T S R := by
    show inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) (T + S)) (toHSCoordsLinearEquiv (ℋ := ℋ) R) = _
    rw [map_add, inner_add_left]
    rfl
  smul_left T S z := by
    show inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) (z • T)) (toHSCoordsLinearEquiv (ℋ := ℋ) S) = _
    rw [map_smul, inner_smul_left]
    rfl

/-- Hilbert-Schmidt coordinates as a linear isometry. -/
noncomputable def toHSCoordsLinearIsometryEquiv :
    HSOp ℋ ≃ₗᵢ[ℂ] HSCoords ℋ :=
  LinearEquiv.isometryOfInner (toHSCoordsLinearEquiv (ℋ := ℋ)) fun _ _ => rfl

instance : CompleteSpace (HSOp ℋ) :=
  (toHSCoordsLinearIsometryEquiv (ℋ := ℋ)).toIsometryEquiv.completeSpace

instance : ContinuousSMul ℂ (HSOp ℋ) :=
  (toHSCoordsLinearIsometryEquiv (ℋ := ℋ)).isometry.isUniformInducing.isInducing.continuousSMul
    continuous_id fun {c x} => map_smul (toHSCoordsLinearEquiv (ℋ := ℋ)) c x

/-- Reinterpret an operator as an element of the Hilbert-Schmidt operator space. -/
abbrev ofOp (T : L ℋ) : HSOp ℋ := T

/-- Forget the Hilbert-Schmidt structure and recover the underlying operator. -/
abbrev toOp (T : HSOp ℋ) : L ℋ := T

/-- Left multiplication on the Hilbert-Schmidt operator space. -/
noncomputable def leftMulHS (A : L ℋ) : HSOp ℋ →L[ℂ] HSOp ℋ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => ofOp (A * toOp T)
      map_add' := fun T S => mul_add A (toOp T) (toOp S)
      map_smul' := fun z T => mul_smul_comm z A (toOp T) }

/-- Right multiplication on the Hilbert-Schmidt operator space. -/
noncomputable def rightMulHS (B : L ℋ) : HSOp ℋ →L[ℂ] HSOp ℋ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => ofOp (toOp T * B)
      map_add' := fun T S => add_mul (toOp T) (toOp S) B
      map_smul' := fun z T => smul_mul_assoc z (toOp T) B }

omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_apply (A : L ℋ) (T : HSOp ℋ) :
    toOp (leftMulHS (ℋ := ℋ) A T) = A * toOp T := rfl

omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_apply (B : L ℋ) (T : HSOp ℋ) :
    toOp (rightMulHS (ℋ := ℋ) B T) = toOp T * B := rfl

omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_mul (A B : L ℋ) :
    leftMulHS (ℋ := ℋ) (A * B) = leftMulHS (ℋ := ℋ) A * leftMulHS (ℋ := ℋ) B := by
  ext T
  simp [mul_assoc]

omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_mul (A B : L ℋ) :
    rightMulHS (ℋ := ℋ) (A * B) = rightMulHS (ℋ := ℋ) B * rightMulHS (ℋ := ℋ) A := by
  ext T
  simp [mul_assoc]

omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_one :
    leftMulHS (ℋ := ℋ) (1 : L ℋ) = (1 : L (HSOp ℋ)) := by
  ext T
  simp

omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_one :
    rightMulHS (ℋ := ℋ) (1 : L ℋ) = (1 : L (HSOp ℋ)) := by
  ext T
  simp

omit [CompleteSpace ℋ] in
lemma leftMulHS_rightMulHS_commute (A B : L ℋ) :
    Commute (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) := by
  ext T
  simp [mul_assoc]

omit [CompleteSpace ℋ] in
private lemma hsInner_eq_pairSum (X Y : L ℋ) :
    inner ℂ (ofOp X) (ofOp Y) =
      ∑ p : HSIndex ℋ × HSIndex ℋ,
        LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
          (hsOrthonormalBasis (ℋ := ℋ)).toBasis Y.toLinearMap p.1 p.2 *
        star
          (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis X.toLinearMap p.1 p.2) := by
  change inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp X))
      (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp Y)) = _
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  rfl

private lemma trace_star_mul_eq_pairSum (X Y : L ℋ) :
    LinearMap.trace ℂ ℋ ((star X * Y).toLinearMap) =
      ∑ p : HSIndex ℋ × HSIndex ℋ,
        LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
          (hsOrthonormalBasis (ℋ := ℋ)).toBasis Y.toLinearMap p.1 p.2 *
        star
          (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis X.toLinearMap p.1 p.2) := by
  let b := hsOrthonormalBasis (ℋ := ℋ)
  rw [LinearMap.trace_eq_sum_inner ((star X * Y).toLinearMap) b, Fintype.sum_prod_type,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc
    inner ℂ (b i) (((star X * Y).toLinearMap) (b i)) = inner ℂ (X (b i)) (Y (b i)) := by
      simpa [ContinuousLinearMap.star_eq_adjoint] using
        ContinuousLinearMap.adjoint_inner_right (A := X) (x := b i) (y := Y (b i))
    _ = ∑ j : HSIndex ℋ, inner ℂ (X (b i)) (b j) * inner ℂ (b j) (Y (b i)) :=
      (OrthonormalBasis.sum_inner_mul_inner b (X (b i)) (Y (b i))).symm
    _ = _ := Finset.sum_congr rfl fun j _ => by
      simp [b, LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply, mul_comm]

lemma hsInner_eq_trace (X Y : L ℋ) :
    inner ℂ (ofOp X) (ofOp Y) = LinearMap.trace ℂ ℋ ((star X * Y).toLinearMap) :=
  (hsInner_eq_pairSum X Y).trans (trace_star_mul_eq_pairSum X Y).symm

lemma re_hsInner_eq_traceRe (X Y : L ℋ) :
    Complex.re (inner ℂ (ofOp X) (ofOp Y)) =
      Complex.re (LinearMap.trace ℂ ℋ ((star X * Y).toLinearMap)) :=
  congrArg Complex.re (hsInner_eq_trace X Y)

@[simp] lemma leftMulHS_star (A : L ℋ) :
    star (leftMulHS (ℋ := ℋ) A) = leftMulHS (ℋ := ℋ) (star A) := by
  rw [eq_comm, ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun X Y => ?_
  change inner ℂ (ofOp ((star A) * toOp X)) (ofOp (toOp Y)) =
    inner ℂ (ofOp (toOp X)) (ofOp (A * toOp Y))
  rw [hsInner_eq_trace, hsInner_eq_trace]
  simp [mul_assoc]

omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_real_smul_one (r : ℝ) :
    leftMulHS (ℋ := ℋ) (r • (1 : L ℋ)) = r • (1 : L (HSOp ℋ)) := by
  ext T
  change ofOp ((r • (1 : L ℋ)) * toOp T) = ofOp (r • toOp T)
  simp [Algebra.smul_def]

omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_real_smul_one (r : ℝ) :
    rightMulHS (ℋ := ℋ) (r • (1 : L ℋ)) = r • (1 : L (HSOp ℋ)) := by
  ext T
  change ofOp (toOp T * (r • (1 : L ℋ))) = ofOp (r • toOp T)
  simp [Algebra.smul_def, Algebra.commutes (R := ℝ) (A := L ℋ) r (toOp T)]

lemma leftMulHS_nonneg {A : L ℋ} (hA0 : 0 ≤ A) :
    0 ≤ leftMulHS (ℋ := ℋ) A := by
  rw [StarOrderedRing.nonneg_iff] at hA0
  induction hA0 using AddSubmonoid.closure_induction with
  | mem a ha =>
    obtain ⟨s, rfl⟩ := ha
    simpa using star_mul_self_nonneg (leftMulHS (ℋ := ℋ) s)
  | zero =>
    exact le_of_eq (ContinuousLinearMap.ext fun T => congrArg ofOp (zero_mul (toOp T)).symm)
  | add a b _ _ ha hb =>
    have hadd : leftMulHS (ℋ := ℋ) (a + b) = leftMulHS (ℋ := ℋ) a + leftMulHS (ℋ := ℋ) b :=
      ContinuousLinearMap.ext fun T => congrArg ofOp (add_mul a b (toOp T))
    exact hadd ▸ add_nonneg ha hb

lemma leftMulHS_le_leftMulHS {A B : L ℋ} (hAB : A ≤ B) :
    leftMulHS (ℋ := ℋ) A ≤ leftMulHS (ℋ := ℋ) B := by
  have hsub : leftMulHS (ℋ := ℋ) B - leftMulHS (ℋ := ℋ) A = leftMulHS (ℋ := ℋ) (B - A) :=
    ContinuousLinearMap.ext fun T => congrArg ofOp (sub_mul B A (toOp T)).symm
  exact sub_nonneg.mp (hsub ▸ leftMulHS_nonneg (ℋ := ℋ) (sub_nonneg.mpr hAB))

lemma leftMulHS_pdSet [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    {A : L ℋ} (hA : A ∈ GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ)) :
    leftMulHS (ℋ := ℋ) A ∈ GeneralizedPerspectiveFunction.pdSet (ℋ := HSOp ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  have hleft_sa : IsSelfAdjoint (leftMulHS (ℋ := ℋ) A) := by
    simp [IsSelfAdjoint, hA_sa.star_eq]
  letI : Nontrivial (HSOp ℋ) := inferInstanceAs (Nontrivial (L ℋ))
  refine ⟨hleft_sa, ?_⟩
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 hA_spec
    with ⟨r, hr, hrA⟩
  refine (CFC.exists_pos_algebraMap_le_iff
    (A := L (HSOp ℋ)) (a := leftMulHS (ℋ := ℋ) A) (ha := hleft_sa)).1 ⟨r, hr, ?_⟩
  simpa [Algebra.algebraMap_eq_smul_one, leftMulHS_real_smul_one (r := r)] using
    leftMulHS_le_leftMulHS (ℋ := ℋ) hrA

@[simp] lemma rightMulHS_star (A : L ℋ) :
    star (rightMulHS (ℋ := ℋ) A) = rightMulHS (ℋ := ℋ) (star A) := by
  rw [eq_comm, ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun X Y => ?_
  change inner ℂ (ofOp (toOp X * star A)) (ofOp (toOp Y)) =
    inner ℂ (ofOp (toOp X)) (ofOp (toOp Y * A))
  rw [hsInner_eq_trace, hsInner_eq_trace, star_mul, star_star, mul_assoc]
  symm
  simpa [mul_assoc] using
    (LinearMap.trace_mul_cycle (R := ℂ) (M := ℋ)
      (f := (star (toOp X)).toLinearMap) (g := (toOp Y).toLinearMap) (h := A.toLinearMap))

/-- Left multiplication as a real `⋆`-algebra homomorphism on the Hilbert-Schmidt operator space. -/
noncomputable def leftMulHSStarAlgHom : L ℋ →⋆ₐ[ℝ] L (HSOp ℋ) where
  toFun := leftMulHS (ℋ := ℋ)
  map_one' := leftMulHS_one (ℋ := ℋ)
  map_mul' := leftMulHS_mul (ℋ := ℋ)
  map_zero' := ContinuousLinearMap.ext fun T => congrArg ofOp (zero_mul (toOp T))
  map_add' A B := ContinuousLinearMap.ext fun T => congrArg ofOp (add_mul A B (toOp T))
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := by simp

/-- Right multiplication as a real `⋆`-algebra homomorphism out of the opposite algebra. -/
noncomputable def rightMulHSStarAlgHom : (L ℋ)ᵐᵒᵖ →⋆ₐ[ℝ] L (HSOp ℋ) where
  toFun := fun A => rightMulHS (ℋ := ℋ) (MulOpposite.unop A)
  map_one' := by simp
  map_mul' A B := rightMulHS_mul (ℋ := ℋ) (MulOpposite.unop B) (MulOpposite.unop A)
  map_zero' := ContinuousLinearMap.ext fun T => congrArg ofOp (mul_zero (toOp T))
  map_add' A B := ContinuousLinearMap.ext fun T =>
    congrArg ofOp (mul_add (toOp T) (MulOpposite.unop A) (MulOpposite.unop B))
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := by simp

@[simp] theorem rightMulHSStarAlgHom_apply (A : (L ℋ)ᵐᵒᵖ) :
    rightMulHSStarAlgHom (ℋ := ℋ) A = rightMulHS (ℋ := ℋ) (MulOpposite.unop A) :=
  rfl

/-- The `⋆`-algebra hom sending `A` to `op (star A)`. On selfadjoint operators this is just `op`. -/
noncomputable def opStarHSStarAlgHom : L ℋ →⋆ₐ[ℝ] (L ℋ)ᵐᵒᵖ where
  toFun := fun A => MulOpposite.op (star A)
  map_one' := by simp
  map_mul' A B := by simp [star_mul]
  map_zero' := by simp
  map_add' A B := by simp
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]
  map_star' A := by simp

private noncomputable def opStarHSAlgEquiv : L ℋ ≃ₐ[ℝ] (L ℋ)ᵐᵒᵖ where
  toFun A := MulOpposite.op (star A)
  invFun A := star (MulOpposite.unop A)
  left_inv A := by simp
  right_inv A := by simp
  map_mul' A B := by simp [star_mul]
  map_add' A B := by simp
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one]

omit [FiniteDimensional ℂ ℋ] in
lemma op_isSelfAdjoint (A : L ℋ) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (MulOpposite.op A : (L ℋ)ᵐᵒᵖ) :=
  congrArg MulOpposite.op hA.star_eq

private noncomputable def opStarHSLinearMap : L ℋ →ₗ[ℝ] (L ℋ)ᵐᵒᵖ where
  toFun := fun A => MulOpposite.op (star A)
  map_add' A B := by simp
  map_smul' r A := map_smul (opStarHSStarAlgHom (ℋ := ℋ)) r A

private noncomputable def leftMulHSLinearMap : L ℋ →ₗ[ℝ] L (HSOp ℋ) where
  toFun := leftMulHS (ℋ := ℋ)
  map_add' A B := map_add (leftMulHSStarAlgHom (ℋ := ℋ)) A B
  map_smul' r A := map_smul (leftMulHSStarAlgHom (ℋ := ℋ)) r A

private noncomputable def rightMulHSLinearMap : (L ℋ)ᵐᵒᵖ →ₗ[ℝ] L (HSOp ℋ) where
  toFun := fun A => rightMulHS (ℋ := ℋ) (MulOpposite.unop A)
  map_add' A B := map_add (rightMulHSStarAlgHom (ℋ := ℋ)) A B
  map_smul' r A := map_smul (rightMulHSStarAlgHom (ℋ := ℋ)) r A

omit [FiniteDimensional ℂ ℋ] in
lemma spectrum_op_eq [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    (A : L ℋ) (hA : IsSelfAdjoint A) :
    spectrum ℝ (MulOpposite.op A : (L ℋ)ᵐᵒᵖ) = spectrum ℝ A := by
  simpa [opStarHSAlgEquiv, hA.star_eq, (op_isSelfAdjoint A hA).star_eq] using
    AlgEquiv.spectrum_eq (opStarHSAlgEquiv (ℋ := ℋ)) A

lemma cfc_op_eq_op_cfc [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ ((L ℋ)ᵐᵒᵖ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    (f : ℝ → ℝ) (A : L ℋ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    cfc (R := ℝ) (A := (L ℋ)ᵐᵒᵖ) (p := IsSelfAdjoint) f (MulOpposite.op A) =
      MulOpposite.op (cfcR f A) := by
  have hmap := StarAlgHom.map_cfc (φ := opStarHSStarAlgHom (ℋ := ℋ)) (f := f) (a := A)
    (hf := hf)
    (hφ := LinearMap.continuous_of_finiteDimensional (opStarHSLinearMap (ℋ := ℋ)))
    (ha := hA) (hφa := hA.map (opStarHSStarAlgHom (ℋ := ℋ)))
  simpa [opStarHSStarAlgHom, cfcR, hA.star_eq, (op_isSelfAdjoint A hA).star_eq,
    (IsSelfAdjoint.cfc (f := f) (a := A)).star_eq,
    (op_isSelfAdjoint _ (IsSelfAdjoint.cfc (f := f) (a := A))).star_eq] using hmap.symm

lemma leftMulHS_cfcR [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    (f : ℝ → ℝ) (A : L ℋ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    leftMulHS (ℋ := ℋ) (cfcR f A) =
      cfcR (ℋ := HSOp ℋ) f (leftMulHS (ℋ := ℋ) A) := by
  exact StarAlgHom.map_cfc (φ := leftMulHSStarAlgHom (ℋ := ℋ)) (f := f) (a := A) (hf := hf)
    (hφ := LinearMap.continuous_of_finiteDimensional (leftMulHSLinearMap (ℋ := ℋ)))
    (ha := hA) (hφa := hA.map (leftMulHSStarAlgHom (ℋ := ℋ)))

lemma rightMulHS_cfcR [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ ((L ℋ)ᵐᵒᵖ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    (f : ℝ → ℝ) (A : L ℋ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    rightMulHS (ℋ := ℋ) (cfcR f A) =
      cfcR (ℋ := HSOp ℋ) f (rightMulHS (ℋ := ℋ) A) := by
  have hopA : IsSelfAdjoint (MulOpposite.op A : (L ℋ)ᵐᵒᵖ) := op_isSelfAdjoint (A := A) hA
  have hmap := StarAlgHom.map_cfc (φ := rightMulHSStarAlgHom (ℋ := ℋ)) (f := f)
    (a := MulOpposite.op A) (hf := by simpa [spectrum_op_eq (A := A) hA] using hf)
    (hφ := LinearMap.continuous_of_finiteDimensional (rightMulHSLinearMap (ℋ := ℋ)))
    (ha := hopA) (hφa := hopA.map (rightMulHSStarAlgHom (ℋ := ℋ)))
  simpa [cfcR, rightMulHSStarAlgHom, cfc_op_eq_op_cfc (ℋ := ℋ) f A hA hf] using hmap

end

end HilbertSchmidtOperatorSpace
