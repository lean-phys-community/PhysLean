/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.OperatorGeometricMean
public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.HilbertSchmidtOperatorSpace
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.JointEigenspace
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

namespace LiebAndoTrace

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction
open HilbertSchmidtOperatorSpace
open OperatorGeometricMean
open Module.End Polynomial

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [FiniteDimensional ℂ ℋ] [Nontrivial ℋ]

set_option synthInstance.maxHeartbeats 80000 in
noncomputable local instance : NonnegSpectrumClass ℝ ((L ℋ)ᵐᵒᵖ) := inferInstance

set_option synthInstance.maxHeartbeats 80000 in
noncomputable local instance :
    IsometricContinuousFunctionalCalculus ℂ ((L ℋ)ᵐᵒᵖ) IsStarNormal := inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 80000 in
noncomputable instance instCFCRealSelfAdjointMop :
    ContinuousFunctionalCalculus ℝ ((L ℋ)ᵐᵒᵖ) IsSelfAdjoint := inferInstance

/-- The real part of the finite-dimensional trace on bounded operators. -/
noncomputable def traceRe (T : L ℋ) : ℝ :=
  Complex.re (LinearMap.trace ℂ ℋ T.toLinearMap)

/-- Trace functional appearing in Lieb's concavity theorem. -/
noncomputable def liebTraceMap (s : ℝ) (K : L ℋ) (A B : L ℋ) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ s * star K * B ^ (1 - s) * K)

/-- Trace functional appearing in Lieb's extension theorem. -/
noncomputable def liebExtensionTraceMap (q p : ℝ) (K : L ℋ) (A B : L ℋ) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ q * star K * B ^ p * K)

/-- Trace functional appearing in Corollary 1.3. -/
noncomputable def liebCorollaryTraceMap (q r : ℝ) (K : L ℋ) (A B : L ℋ) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ q * star K * B ^ (1 - r) * K)

/-- Trace functional appearing in Ando's convexity theorem. -/
noncomputable def andoTraceMap (q r : ℝ) (K : L ℋ) (A B : L ℋ) : ℝ :=
  traceRe (ℋ := ℋ) (A ^ q * star K * B ^ (-r) * K)

omit [Nontrivial ℋ] [CompleteSpace ℋ] in
private lemma rightMulHS_real_smul_one (r : ℝ) :
    rightMulHS (ℋ := ℋ) (r • (1 : L ℋ)) = r • (1 : L (HSOp ℋ)) := by
  exact HilbertSchmidtOperatorSpace.rightMulHS_real_smul_one r

omit [Nontrivial ℋ] in
private lemma rightMulHS_nonneg {A : L ℋ} (hA0 : 0 ≤ A) :
    0 ≤ rightMulHS (ℋ := ℋ) A := by
  calc (0 : L (HSOp ℋ))
      ≤ star (rightMulHS (ℋ := ℋ) (CFC.sqrt A)) * rightMulHS (ℋ := ℋ) (CFC.sqrt A) :=
        star_mul_self_nonneg _
    _ = rightMulHS (ℋ := ℋ) A := by
        rw [rightMulHS_star, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq,
          ← rightMulHS_mul, CFC.sqrt_mul_sqrt_self A hA0]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
private lemma rightMulHS_le_rightMulHS {A B : L ℋ} (hAB : A ≤ B) :
    rightMulHS (ℋ := ℋ) A ≤ rightMulHS (ℋ := ℋ) B := by
  have hsub :
      rightMulHS (ℋ := ℋ) B - rightMulHS (ℋ := ℋ) A = rightMulHS (ℋ := ℋ) (B - A) := by
    ext T
    exact congrArg ofOp (mul_sub (toOp T) B A).symm
  exact sub_nonneg.mp (by simpa [hsub] using rightMulHS_nonneg (ℋ := ℋ) (sub_nonneg.mpr hAB))

private lemma rightMulHS_pdSet {A : L ℋ} (hA : A ∈ pdSet (ℋ := ℋ)) :
    rightMulHS (ℋ := ℋ) A ∈ pdSet (ℋ := HSOp ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  have hright_sa : IsSelfAdjoint (rightMulHS (ℋ := ℋ) A) := by
    simp [isSelfAdjoint_iff, hA_sa.star_eq]
  letI : Nontrivial (HSOp ℋ) := inferInstanceAs (Nontrivial (L ℋ))
  letI : Nontrivial (L (HSOp ℋ)) := inferInstance
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 hA_spec
    with ⟨r, hr, hrA⟩
  refine ⟨hright_sa, (CFC.exists_pos_algebraMap_le_iff
    (a := rightMulHS (ℋ := ℋ) A) (ha := hright_sa)).1 ⟨r, hr, ?_⟩⟩
  simpa [Algebra.algebraMap_eq_smul_one, rightMulHS_real_smul_one (ℋ := ℋ) (r := r)] using
    rightMulHS_le_rightMulHS (ℋ := ℋ) hrA

private noncomputable def phiK (K : L ℋ) (T : L (HSOp ℋ)) : ℝ :=
  Complex.re (inner ℂ (ofOp (star K)) (T (ofOp (star K))))

omit [Nontrivial ℋ] in
private lemma phiK_nonneg (K : L ℋ) {T : L (HSOp ℋ)} (hT : 0 ≤ T) :
    0 ≤ phiK (ℋ := ℋ) K T := by
  simpa [phiK] using
    ((ContinuousLinearMap.nonneg_iff_isPositive T).1 hT).re_inner_nonneg_right (ofOp (star K))

omit [Nontrivial ℋ] in
private lemma phiK_add (K : L ℋ) (T S : L (HSOp ℋ)) :
    phiK (ℋ := ℋ) K (T + S) = phiK (ℋ := ℋ) K T + phiK (ℋ := ℋ) K S := by
  simp [phiK, inner_add_right, Complex.add_re]

omit [Nontrivial ℋ] in
private lemma phiK_smul (K : L ℋ) (r : ℝ) (T : L (HSOp ℋ)) :
    phiK (ℋ := ℋ) K (r • T) = r * phiK (ℋ := ℋ) K T := by
  simp only [phiK, show (r • T) (ofOp (star K)) = (r : ℂ) • T (ofOp (star K)) from rfl,
    inner_smul_right]
  simp

omit [Nontrivial ℋ] in
private lemma phiK_mono (K : L ℋ) {T S : L (HSOp ℋ)} (hTS : T ≤ S) :
    phiK (ℋ := ℋ) K T ≤ phiK (ℋ := ℋ) K S := by
  have h := phiK_nonneg (ℋ := ℋ) K (sub_nonneg.mpr hTS)
  rw [sub_eq_add_neg, ← neg_one_smul ℝ T, phiK_add, phiK_smul] at h
  linarith

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
private lemma leftMulHS_rankOne (A : L ℋ) (x y : ℋ) :
    leftMulHS (ℋ := ℋ) A (ofOp (InnerProductSpace.rankOne ℂ x y)) =
      ofOp (InnerProductSpace.rankOne ℂ (A x) y) :=
  InnerProductSpace.comp_rankOne (𝕜 := ℂ) (x := x) (y := y) (f := A)

omit [Nontrivial ℋ] in
private lemma rightMulHS_rankOne (B : L ℋ) (x y : ℋ) :
    rightMulHS (ℋ := ℋ) B (ofOp (InnerProductSpace.rankOne ℂ x y)) =
      ofOp (InnerProductSpace.rankOne ℂ x ((star B) y)) :=
  InnerProductSpace.rankOne_comp (𝕜 := ℂ) (x := x) (y := y) (f := B)

private lemma re_inner_nonneg_of_nonneg
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : 𝓚 →L[ℂ] 𝓚} (hT : 0 ≤ T) :
    ∀ x : 𝓚, 0 ≤ Complex.re (inner ℂ x (T x)) := by
  intro x
  simpa using ((ContinuousLinearMap.nonneg_iff_isPositive T).1 hT).re_inner_nonneg_right x

private lemma aeval_apply_of_mem_eigenspace_realpoly
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚]
    {T : 𝓚 →L[ℂ] 𝓚} {r : ℝ} {x : 𝓚}
    (hx : x ∈ eigenspace T.toLinearMap (r : ℂ)) (p : ℝ[X]) :
    Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
      ((p.map (algebraMap ℝ ℂ)).eval (r : ℂ)) • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hmap :
      Polynomial.aeval T (p.map (algebraMap ℝ ℂ)) x =
        Polynomial.aeval T.toLinearMap (p.map (algebraMap ℝ ℂ)) x := by
    simpa using congrArg (fun F : 𝓚 →ₗ[ℂ] 𝓚 => F x)
      (Polynomial.map_aeval_eq_aeval_map (φ := RingHom.id ℂ)
        (ψ := ContinuousLinearMap.toLinearMapRingHom) (h := by ext z; rfl)
        (p := p.map (algebraMap ℝ ℂ)) (a := T))
  rw [hmap]
  simpa using Module.End.aeval_apply_of_hasEigenvector (p := p.map (algebraMap ℝ ℂ)) ⟨hx, hx0⟩

-- The interpolation-based `cfcR`-on-eigenspace lemma is elaboration-heavy.
set_option maxHeartbeats 400000 in
private lemma cfcR_apply_of_mem_eigenspace_real
    {𝓚 : Type*} [NormedAddCommGroup 𝓚] [InnerProductSpace ℂ 𝓚] [CompleteSpace 𝓚]
    [FiniteDimensional ℂ 𝓚]
    [ContinuousFunctionalCalculus ℝ (L 𝓚) IsSelfAdjoint]
    (f : ℝ → ℝ) {T : L 𝓚} (hT : IsSelfAdjoint T) {r : ℝ} {x : 𝓚}
    (hx : x ∈ eigenspace T.toLinearMap (r : ℂ)) :
    cfcR (ℋ := 𝓚) f T x = (f r : ℂ) • x := by
  haveI : IsScalarTower ℝ ℂ (L 𝓚) := RestrictScalars.isScalarTower ℝ ℂ (L 𝓚)
  classical
  by_cases hx0 : x = 0
  · simp [hx0]
  have hspecCfin : Set.Finite (spectrum ℂ T) := by
    change Set.Finite (spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) T.toLinearMap))
    simpa using Module.End.finite_spectrum (K := ℂ) (V := 𝓚) T.toLinearMap
  have hspecRfin : Set.Finite (spectrum ℝ T) := by
    rw [← spectrum.preimage_algebraMap ℂ]
    exact hspecCfin.preimage (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn
  let s : Finset ℝ := hspecRfin.toFinset
  let q : ℝ[X] := Lagrange.interpolate s id fun y ↦ f y
  have hq_spec : (spectrum ℝ T).EqOn f q.eval := fun y hy =>
    (Lagrange.eval_interpolate_at_node (v := id) (r := fun z ↦ f z)
      (fun _ _ _ _ h => h) (by simpa [s] using hy)).symm
  have hcfc : cfcR (ℋ := 𝓚) f T = cfcR (ℋ := 𝓚) q.eval T := by
    simpa [cfcR] using (cfc_congr (a := T) (f := f) (g := q.eval) hq_spec)
  have hpoly : cfcR (ℋ := 𝓚) q.eval T = Polynomial.aeval T q := by
    simpa [cfcR] using (cfc_polynomial (p := IsSelfAdjoint) (q := q) (a := T) hT)
  have hxv : Module.End.HasEigenvector T.toLinearMap (r : ℂ) x := ⟨hx, hx0⟩
  have hr_specC : (r : ℂ) ∈ spectrum ℂ T :=
    by
      change (r : ℂ) ∈ spectrum ℂ ((Module.End.toContinuousLinearMap 𝓚) T.toLinearMap)
      simpa using (Module.End.hasEigenvalue_of_hasEigenvector hxv).mem_spectrum
  have hr_spec : r ∈ spectrum ℝ T := spectrum.of_algebraMap_mem ℂ hr_specC
  calc
    cfcR (ℋ := 𝓚) f T x = Polynomial.aeval T q x := by rw [hcfc, hpoly]
    _ = Polynomial.aeval T (q.map (algebraMap ℝ ℂ)) x := by simp
    _ = ((q.map (algebraMap ℝ ℂ)).eval (r : ℂ)) • x := by
      simpa using aeval_apply_of_mem_eigenspace_realpoly hx q
    _ = (f r : ℂ) • x := by
      congr 1
      rw [Polynomial.eval_map_algebraMap]
      simpa [hq_spec hr_spec] using
        Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval (A := ℂ) (x := r) (p := q)

-- This proof is isolated because the joint eigenspace decomposition is heartbeat-heavy.
set_option maxHeartbeats 800000 in
private lemma hmiddle_leftMul_rightMul
    {s : ℝ} {A B : L ℋ}
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ)) :
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
        (cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B)) =
      leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hA0 : 0 ≤ A :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A hA_sa).2 fun x hx => (hA_spec hx).le
  have hB0 : 0 ≤ B :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B hB_sa).2 fun x hx => (hB_spec hx).le
  have hright_negHalf :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((-1 : ℝ) / 2)) := by
    rw [← rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) B hB_sa fun x hx =>
      (Real.continuousAt_rpow_const x _ (Or.inl (hB_spec hx).ne')).continuousWithinAt]
    congr 1
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (-1 : ℝ) / 2) (ha := hB0)).symm
  have hBunit : IsUnit B :=
    spectrum.isUnit_of_zero_notMem (R := ℝ) fun h0 => lt_irrefl 0 (Set.mem_Ioi.mp (hB_spec h0))
  have hBnegOne :
      B ^ ((-1 : ℝ) / 2) * B ^ ((-1 : ℝ) / 2) = B ^ (-1 : ℝ) := by
    rw [← CFC.rpow_add hBunit]
    norm_num
  have hmid_prod :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) *
          leftMulHS (ℋ := ℋ) A *
          cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) := by
    rw [hright_negHalf, (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ ((-1 : ℝ) / 2))).eq.symm,
      mul_assoc, ← rightMulHS_mul, hBnegOne]
  rw [hmid_prod]
  let T0 : HSOp ℋ →ₗ[ℂ] HSOp ℋ := (leftMulHS (ℋ := ℋ) A).toLinearMap
  let T1 : HSOp ℋ →ₗ[ℂ] HSOp ℋ := (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))).toLinearMap
  let lhs : L (HSOp ℋ) :=
    cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
      (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)))
  let rhs : L (HSOp ℋ) :=
    leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))
  let D : L (HSOp ℋ) := lhs - rhs
  have hleft_sa : IsSelfAdjoint (leftMulHS (ℋ := ℋ) A) :=
    IsSelfAdjoint.of_nonneg (leftMulHS_nonneg (ℋ := ℋ) hA0)
  have hT0_symm : T0.IsSymmetric := by
    simpa [T0] using ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hleft_sa
  have hBinv0 : 0 ≤ B ^ (-1 : ℝ) := by simp
  have hBinv_sa : IsSelfAdjoint (B ^ (-1 : ℝ)) := IsSelfAdjoint.of_nonneg hBinv0
  have hBinv_unit : IsUnit (B ^ (-1 : ℝ)) := by
    rcases hBunit with ⟨u, rfl⟩
    simp [CFC.rpow_neg_one_eq_inv u (by simpa using hB0)]
  have hright_sa : IsSelfAdjoint (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) :=
    IsSelfAdjoint.of_nonneg (rightMulHS_nonneg (ℋ := ℋ) hBinv0)
  have hT1_symm : T1.IsSymmetric := by
    simpa [T1] using ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hright_sa
  have hcomm : Commute T0 T1 :=
    congrArg ContinuousLinearMap.toLinearMap
      (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ (-1 : ℝ))).eq
  have hleft_pow :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s) (leftMulHS (ℋ := ℋ) A) =
        leftMulHS (ℋ := ℋ) (A ^ s) := by
    rw [← leftMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) A hA_sa fun x hx =>
      (Real.continuousAt_rpow_const x s (Or.inl (hA_spec hx).ne')).continuousWithinAt]
    congr 1
    simpa [cfcR] using (CFC.rpow_eq_cfc_real (A := L ℋ) (a := A) (y := s) (ha := hA0)).symm
  have hright_pow :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ s)
          (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) =
        rightMulHS (ℋ := ℋ) (B ^ (-s)) := by
    rw [← rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ)) hBinv_sa fun x hx =>
      (Real.continuousAt_rpow_const x s (Or.inl fun hx0 =>
        spectrum.zero_notMem (R := ℝ) hBinv_unit (hx0 ▸ hx))).continuousWithinAt]
    congr 1
    calc
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ s) (B ^ (-1 : ℝ)) = (B ^ (-1 : ℝ)) ^ s := by
        simpa [cfcR] using
          (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B ^ (-1 : ℝ)) (y := s) (ha := hBinv0)).symm
      _ = B ^ (-s) := by
        simpa using CFC.rpow_rpow B (-1 : ℝ) s (by norm_num) (hBunit.isStrictlyPositive hB0)
  have hprod0 :
      0 ≤ leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) :=
    (leftMulHS_rightMulHS_commute (ℋ := ℋ) A (B ^ (-1 : ℝ))).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) hA0) (rightMulHS_nonneg (ℋ := ℋ) hBinv0)
  have hprod_sa :
      IsSelfAdjoint
        (leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) :=
    IsSelfAdjoint.of_nonneg hprod0
  have htop : (⨆ α, ⨆ β, eigenspace T0 α ⊓ eigenspace T1 β) = ⊤ :=
    hT0_symm.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hT1_symm hcomm
  have hjoint_ker :
      ∀ α β,
        eigenspace T0 α ⊓ eigenspace T1 β ≤ LinearMap.ker D.toLinearMap := by
    rintro α β x ⟨hx0, hx1⟩
    rw [LinearMap.mem_ker]
    by_cases hxzero : x = 0
    · simp [D, hxzero]
    have hαeq : α = (α.re : ℂ) :=
      (RCLike.conj_eq_iff_re.mp (hT0_symm.conj_eigenvalue_eq_self
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx0, hxzero⟩))).symm
    have hβeq : β = (β.re : ℂ) :=
      (RCLike.conj_eq_iff_re.mp (hT1_symm.conj_eigenvalue_eq_self
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx1, hxzero⟩))).symm
    have hx0r : x ∈ eigenspace T0 (α.re : ℂ) := by
      rwa [hαeq] at hx0
    have hx1r : x ∈ eigenspace T1 (β.re : ℂ) := by
      rwa [hβeq] at hx1
    have hαnonneg : 0 ≤ α.re :=
      eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx0r, hxzero⟩) fun y => by
          simpa [T0] using re_inner_nonneg_of_nonneg (leftMulHS_nonneg (ℋ := ℋ) hA0) y
    have hβnonneg : 0 ≤ β.re :=
      eigenvalue_nonneg_of_nonneg
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨hx1r, hxzero⟩) fun y => by
          simpa [T1] using re_inner_nonneg_of_nonneg (rightMulHS_nonneg (ℋ := ℋ) hBinv0) y
    have hxprod :
        x ∈ eigenspace
          ((leftMulHS (ℋ := ℋ) A * rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))).toLinearMap)
          (((α.re * β.re : ℝ) : ℂ)) := by
      rw [Module.End.mem_eigenspace_iff]
      show leftMulHS (ℋ := ℋ) A (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) x) =
        (((α.re * β.re : ℝ) : ℂ)) • x
      rw [show rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ)) x = (β.re : ℂ) • x from
          Module.End.mem_eigenspace_iff.mp hx1r, ContinuousLinearMap.map_smul,
        show leftMulHS (ℋ := ℋ) A x = (α.re : ℂ) • x from Module.End.mem_eigenspace_iff.mp hx0r,
        smul_smul, ← Complex.ofReal_mul, mul_comm β.re α.re]
    have hlhsx :
        lhs x = ((((α.re * β.re : ℝ) ^ s : ℝ) : ℂ) • x) := by
      simpa [lhs] using
        cfcR_apply_of_mem_eigenspace_real (f := fun t : ℝ ↦ t ^ s) hprod_sa hxprod
    have hrhsx :
        rhs x = ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x) := by
      change (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B ^ (-s))) x =
        ((((α.re ^ s) * (β.re ^ s) : ℝ) : ℂ) • x)
      have hleftx :
          cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s) (leftMulHS (ℋ := ℋ) A) x =
            (((α.re ^ s : ℝ) : ℂ) • x) := by
        simpa using cfcR_apply_of_mem_eigenspace_real (f := fun t : ℝ ↦ t ^ s) hleft_sa hx0r
      have hrightx :
          cfcR (ℋ := HSOp ℋ) (fun t : ℝ ↦ t ^ s)
              (rightMulHS (ℋ := ℋ) (B ^ (-1 : ℝ))) x =
            (((β.re ^ s : ℝ) : ℂ) • x) := by
        simpa using cfcR_apply_of_mem_eigenspace_real (f := fun t : ℝ ↦ t ^ s) hright_sa hx1r
      rw [← hleft_pow, ← hright_pow, mul_apply_eq_comp, hrightx,
        ContinuousLinearMap.map_smul, hleftx, smul_smul, ← Complex.ofReal_mul,
        mul_comm (β.re ^ s) (α.re ^ s)]
    have hscal :
        (((α.re * β.re : ℝ) ^ s : ℝ) : ℂ) =
          ((((α.re ^ s) * (β.re ^ s) : ℝ)) : ℂ) :=
      congrArg Complex.ofReal (Real.mul_rpow hαnonneg hβnonneg)
    simpa [D] using
      sub_eq_zero.mpr (hlhsx.trans (hscal ▸ hrhsx.symm))
  have hker_top : LinearMap.ker D.toLinearMap = ⊤ :=
    top_unique (htop ▸ iSup_le fun α => iSup_le fun β => hjoint_ker α β)
  have hDzero : D = 0 := ContinuousLinearMap.coe_injective (LinearMap.ker_eq_top.mp hker_top)
  simpa [D, lhs, rhs, sub_eq_zero] using hDzero

-- The bridge lemma expands a large `HSOp`-valued generalized perspective term.
set_option maxHeartbeats 800000 in
private lemma phiK_operatorPowerMean_eq_liebTraceMap
    {s : ℝ} (K A B : L ℋ) (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ)) :
    phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B)) =
      liebTraceMap (ℋ := ℋ) s K A B := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  have hB0 : 0 ≤ B :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B hB_sa).2 fun x hx => (hB_spec hx).le
  have hright_half :
      cfcR (ℋ := HSOp ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (rightMulHS (ℋ := ℋ) B) =
        rightMulHS (ℋ := ℋ) (B ^ ((1 : ℝ) / 2)) := by
    rw [← rightMulHS_cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) B hB_sa fun x hx =>
      (Real.continuousAt_rpow_const x _ (Or.inr (by positivity))).continuousWithinAt]
    congr 1
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := L ℋ) (a := B) (y := (1 : ℝ) / 2) (ha := hB0)).symm
  have hBunit : IsUnit B :=
    spectrum.isUnit_of_zero_notMem (R := ℝ) fun h0 => lt_irrefl 0 (Set.mem_Ioi.mp (hB_spec h0))
  have hBpow :
      B ^ ((2 : ℝ)⁻¹) * (B ^ (-s) * B ^ ((2 : ℝ)⁻¹)) = B ^ (1 - s) := by
    rw [← CFC.rpow_add hBunit, ← CFC.rpow_add hBunit]
    ring_nf
  have happly :
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) (ofOp (star K)) =
        ofOp (A ^ s * star K * B ^ (1 - s)) := by
    rw [OperatorGeometricMean.operatorPowerMean, GeneralizedPerspective,
      GeneralizedPerspectiveFunction.hSqrt, GeneralizedPerspectiveFunction.hInvSqrt]
    simp only [Real.rpow_one]
    rw [hmiddle_leftMul_rightMul (ℋ := ℋ) (s := s) ⟨hA_sa, hA_spec⟩ ⟨hB_sa, hB_spec⟩,
      hright_half]
    simp [mul_assoc, hBpow]
  calc
    phiK (ℋ := ℋ) K
        (operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B))
      = Complex.re
          (inner ℂ (ofOp (star K))
            (ofOp (A ^ s * star K * B ^ (1 - s)))) := by
            simp [phiK, happly]
    _ = traceRe (ℋ := ℋ) (A ^ s * star K * B ^ (1 - s) * K) := by
          rw [re_hsInner_eq_traceRe, traceRe]
          simpa [mul_assoc] using congrArg Complex.re
            (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) K.toLinearMap
              ((A ^ s * star K * B ^ (1 - s)).toLinearMap))
    _ = liebTraceMap (ℋ := ℋ) s K A B := rfl

omit [FiniteDimensional ℂ ℋ] in
/-- Convex combinations preserve `pdSet` (strict positivity). -/
lemma pdSet_convexCombo {A B : L ℋ} {t : ℝ}
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB : B ∈ pdSet (ℋ := ℋ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • A + t • B) ∈ pdSet (ℋ := ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  rcases hB with ⟨hB_sa, hB_spec⟩
  set C : L ℋ := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA_sa |>.add ((IsSelfAdjoint.all t).smul hB_sa)
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 hA_spec with
    ⟨rA, hrA, hrA_le⟩
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := B) (ha := hB_sa)).2 hB_spec with
    ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    rcases eq_or_lt_of_le ht1 with h | h
    · simpa [rC, h] using hrB
    · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) hrA) (mul_nonneg ht0 hrB.le)
  have hrC_le : algebraMap ℝ (L ℋ) rC ≤ C := by
    have hLHS :
        (1 - t) • algebraMap ℝ (L ℋ) rA + t • algebraMap ℝ (L ℋ) rB =
          algebraMap ℝ (L ℋ) rC := by
      simp [rC, Algebra.smul_def]
    simpa [C, hLHS] using
      add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1))
        (smul_le_smul_of_nonneg_left hrB_le ht0)
  exact ⟨hC, (CFC.exists_pos_algebraMap_le_iff (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩⟩

omit [Nontrivial ℋ] in
private lemma phiK_leftMul_rightMul_eq_traceRe (K C D : L ℋ) :
    phiK (ℋ := ℋ) K
        (leftMulHS (ℋ := ℋ) C * rightMulHS (ℋ := ℋ) D) =
      traceRe (ℋ := ℋ) (C * star K * D * K) := by
  have happly : (leftMulHS (ℋ := ℋ) C * rightMulHS (ℋ := ℋ) D) (ofOp (star K)) =
      ofOp (C * star K * D) := by
    simp [mul_assoc]
  simp only [phiK, happly]
  rw [re_hsInner_eq_traceRe, traceRe]
  simpa [mul_assoc] using congrArg Complex.re
    (LinearMap.trace_mul_comm (R := ℂ) (M := ℋ) K.toLinearMap ((C * star K * D).toLinearMap))

omit [FiniteDimensional ℂ ℋ] in
set_option maxHeartbeats 400000 in
private lemma pdSet_rpow_of_mem_Icc_zero_one
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {A : L ℋ} (hA : A ∈ pdSet (ℋ := ℋ)) :
    A ^ p ∈ pdSet (ℋ := ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  have hA0 : 0 ≤ A :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A hA_sa).2 fun x hx => (hA_spec hx).le
  have hApow0 : 0 ≤ A ^ p := by simp
  have hApow_sa : IsSelfAdjoint (A ^ p) := IsSelfAdjoint.of_nonneg hApow0
  rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 hA_spec with
    ⟨r, hr, hrA⟩
  refine ⟨hApow_sa, ?_⟩
  have hr0 : 0 ≤ algebraMap ℝ (L ℋ) r := by
    simpa [Algebra.algebraMap_eq_smul_one] using smul_nonneg hr.le (show (0 : L ℋ) ≤ 1 by simp)
  have hmono :=
    power_Icc_zero_one_operatorMonotoneOn_Ici (ℋ := ℋ) p hp hA0 hr0 hrA
      (fun x hx => Set.mem_Ici.mpr (hA_spec hx).le) fun x hx =>
        spectrum_nonneg_of_nonneg hr0 hx
  have hApow :
      cfcR (ℋ := ℋ) (fun x : ℝ ↦ x ^ p) A = A ^ p := by
    simpa [cfcR, LownerHeinzCore.cfcR] using
      (CFC.rpow_eq_cfc_real (A := L ℋ) (a := A) (y := p) (ha := hA0)).symm
  have hscalar :
      (algebraMap ℝ (L ℋ) r) ^ p = algebraMap ℝ (L ℋ) (r ^ p) := by
    rw [CFC.rpow_eq_cfc_real (A := L ℋ) (a := algebraMap ℝ (L ℋ) r) (y := p) (ha := hr0)]
    simp
  have hbound : algebraMap ℝ (L ℋ) (r ^ p) ≤ A ^ p := by
    simpa [hscalar, hApow] using hmono
  exact (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A ^ p) (ha := hApow_sa)).1
    ⟨r ^ p, Real.rpow_pos_of_pos hr p, hbound⟩

omit [Nontrivial ℋ] in
set_option maxHeartbeats 400000 in
private lemma liebTraceMap_mono_right
    {s : ℝ} (hs : 1 - s ∈ Set.Icc (0 : ℝ) 1)
    (K A B₁ B₂ : L ℋ)
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ))
    (hB : B₁ ≤ B₂) :
    liebTraceMap (ℋ := ℋ) s K A B₁ ≤ liebTraceMap (ℋ := ℋ) s K A B₂ := by
  rcases hA with ⟨-, -⟩
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  have hB₁0 : 0 ≤ B₁ := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ hB₁_sa).2
    fun x hx => (hB₁_spec hx).le
  have hB₂0 : 0 ≤ B₂ := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ hB₂_sa).2
    fun x hx => (hB₂_spec hx).le
  have hcfc :=
    power_Icc_zero_one_operatorMonotoneOn_Ici (ℋ := ℋ) (1 - s) hs hB₂0 hB₁0 hB
      (fun x hx => Set.mem_Ici.mpr (hB₂_spec hx).le) fun x hx =>
        Set.mem_Ici.mpr (hB₁_spec hx).le
  have hpow :
      B₁ ^ (1 - s) ≤ B₂ ^ (1 - s) := by
    simpa [cfcR, LownerHeinzCore.cfcR,
      CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₁) (y := 1 - s) (ha := hB₁0),
      CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₂) (y := 1 - s) (ha := hB₂0)] using hcfc
  have hApow0 : 0 ≤ A ^ s := by simp
  have hdiff0 : 0 ≤ B₂ ^ (1 - s) - B₁ ^ (1 - s) := sub_nonneg.mpr hpow
  have hprod0 :
      0 ≤ leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s)) :=
    (leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s) (B₂ ^ (1 - s) - B₁ ^ (1 - s))).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) hApow0) (rightMulHS_nonneg (ℋ := ℋ) hdiff0)
  have hsplit :
      leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s)) -
          leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s)) := by
    ext T
    show (A ^ s * (toOp T * (B₂ ^ (1 - s) - B₁ ^ (1 - s))) : L ℋ) =
      A ^ s * (toOp T * B₂ ^ (1 - s)) - A ^ s * (toOp T * B₁ ^ (1 - s))
    simp [mul_sub]
  have hrewrite :
      phiK (ℋ := ℋ) K
          (leftMulHS (ℋ := ℋ) (A ^ s) *
            rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s) - B₁ ^ (1 - s))) =
        liebTraceMap (ℋ := ℋ) s K A B₂ - liebTraceMap (ℋ := ℋ) s K A B₁ := by
    rw [hsplit, sub_eq_add_neg, ← neg_one_smul ℝ
        (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s))),
      phiK_add, phiK_smul]
    simp [phiK_leftMul_rightMul_eq_traceRe, liebTraceMap, mul_assoc, sub_eq_add_neg]
  linarith [hrewrite ▸ phiK_nonneg (ℋ := ℋ) K hprod0]

omit [Nontrivial ℋ] in
set_option maxHeartbeats 400000 in
private lemma liebTraceMap_antitone_right
    {s : ℝ} (hs : 1 - s ∈ Set.Icc (-1 : ℝ) 0)
    (K A B₁ B₂ : L ℋ)
    (hA : A ∈ pdSet (ℋ := ℋ)) (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ))
    (hB : B₁ ≤ B₂) :
    liebTraceMap (ℋ := ℋ) s K A B₂ ≤ liebTraceMap (ℋ := ℋ) s K A B₁ := by
  rcases hA with ⟨-, -⟩
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  have hB₁0 : 0 ≤ B₁ := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ hB₁_sa).2
    fun x hx => (hB₁_spec hx).le
  have hB₂0 : 0 ≤ B₂ := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ hB₂_sa).2
    fun x hx => (hB₂_spec hx).le
  have hcfc :=
    power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi (ℋ := ℋ) (1 - s) hs hB₂0 hB₁0 hB
      (fun x hx => hB₂_spec hx) fun x hx => hB₁_spec hx
  have hpow :
      B₂ ^ (1 - s) ≤ B₁ ^ (1 - s) := by
    have hnegpow : -(B₁ ^ (1 - s)) ≤ -(B₂ ^ (1 - s)) := by
      simpa [cfcR, LownerHeinzCore.cfcR, cfc_neg,
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₁) (y := 1 - s) (ha := hB₁0),
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₂) (y := 1 - s) (ha := hB₂0)] using hcfc
    simpa using neg_le_neg_iff.mp hnegpow
  have hApow0 : 0 ≤ A ^ s := by simp
  have hdiff0 : 0 ≤ B₁ ^ (1 - s) - B₂ ^ (1 - s) := sub_nonneg.mpr hpow
  have hprod0 :
      0 ≤ leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s)) :=
    (leftMulHS_rightMulHS_commute (ℋ := ℋ) (A ^ s) (B₁ ^ (1 - s) - B₂ ^ (1 - s))).mul_nonneg
      (leftMulHS_nonneg (ℋ := ℋ) hApow0) (rightMulHS_nonneg (ℋ := ℋ) hdiff0)
  have hsplit :
      leftMulHS (ℋ := ℋ) (A ^ s) *
          rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s)) =
        leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s)) -
          leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s)) := by
    ext T
    show (A ^ s * (toOp T * (B₁ ^ (1 - s) - B₂ ^ (1 - s))) : L ℋ) =
      A ^ s * (toOp T * B₁ ^ (1 - s)) - A ^ s * (toOp T * B₂ ^ (1 - s))
    simp [mul_sub]
  have hrewrite :
      phiK (ℋ := ℋ) K
          (leftMulHS (ℋ := ℋ) (A ^ s) *
            rightMulHS (ℋ := ℋ) (B₁ ^ (1 - s) - B₂ ^ (1 - s))) =
        liebTraceMap (ℋ := ℋ) s K A B₁ - liebTraceMap (ℋ := ℋ) s K A B₂ := by
    rw [hsplit, sub_eq_add_neg, ← neg_one_smul ℝ
        (leftMulHS (ℋ := ℋ) (A ^ s) * rightMulHS (ℋ := ℋ) (B₂ ^ (1 - s))),
      phiK_add, phiK_smul]
    simp [phiK_leftMul_rightMul_eq_traceRe, liebTraceMap, mul_assoc, sub_eq_add_neg]
  linarith [hrewrite ▸ phiK_nonneg (ℋ := ℋ) K hprod0]

private lemma phiK_weightedSum_operatorPowerMean_eq
    {s θ : ℝ} (K A₁ A₂ B₁ B₂ : L ℋ)
    (hA₁ : A₁ ∈ pdSet (ℋ := ℋ)) (hA₂ : A₂ ∈ pdSet (ℋ := ℋ))
    (hB₁ : B₁ ∈ pdSet (ℋ := ℋ)) (hB₂ : B₂ ∈ pdSet (ℋ := ℋ)) :
    phiK (ℋ := ℋ) K
        ((1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
          θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂)) =
      (1 - θ) • liebTraceMap (ℋ := ℋ) s K A₁ B₁ +
        θ • liebTraceMap (ℋ := ℋ) s K A₂ B₂ := by
  rw [phiK_add, phiK_smul, phiK_smul,
    phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) K A₁ B₁ hA₁ hB₁,
    phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) K A₂ B₂ hA₂ hB₂]
  simp [smul_eq_mul]

-- The `HSOp`-valued `operatorPowerMean` terms are large enough that the skeleton itself is expensive.
theorem liebTrace_jointlyConcaveOn_pdSet
    {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (K : L ℋ) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
        leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    show ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : L ℋ) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
        rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    show ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : L ℋ) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo := pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo := pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  letI : Nontrivial (HSOp ℋ) := inferInstanceAs (Nontrivial (L ℋ))
  letI : Nontrivial (L (HSOp ℋ)) := inferInstance
  have hconc :
      (1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
        θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂) ≤
        operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
          (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂)) := by
    simpa [hleft_combo, hright_combo] using
      operatorPowerMean_jointlyConcaveOn_pdSet (ℋ := HSOp ℋ) (α := s) (β := 1)
        ⟨le_of_lt hs0, hs1.le⟩ ⟨by norm_num, by norm_num⟩
        (leftMulHS_pdSet (ℋ := ℋ) hA₁) (leftMulHS_pdSet (ℋ := ℋ) hA₂)
        (rightMulHS_pdSet (ℋ := ℋ) hB₁) (rightMulHS_pdSet (ℋ := ℋ) hB₂) hθ0 hθ1
  have hphi_mono := phiK_mono (ℋ := ℋ) K hconc
  rw [phiK_weightedSum_operatorPowerMean_eq (ℋ := ℋ) (s := s) (θ := θ) K A₁ A₂ B₁ B₂
      hA₁ hA₂ hB₁ hB₂] at hphi_mono
  rw [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo] at hphi_mono
  simpa [add_comm, add_left_comm, add_assoc] using hphi_mono

theorem liebTrace_jointlyConvexOn_pdSet
    {s : ℝ} (hs1 : 1 ≤ s) (hs2 : s ≤ 2) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebTraceMap (ℋ := ℋ) s K) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hleft_combo :
      (1 - θ) • leftMulHS (ℋ := ℋ) A₁ + θ • leftMulHS (ℋ := ℋ) A₂ =
        leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂) := by
    ext T
    show ((1 - θ) • (A₁ * toOp T) + θ • (A₂ * toOp T) : L ℋ) =
      ((1 - θ) • A₁ + θ • A₂) * toOp T
    rw [add_mul, smul_mul_assoc, smul_mul_assoc]
  have hright_combo :
      (1 - θ) • rightMulHS (ℋ := ℋ) B₁ + θ • rightMulHS (ℋ := ℋ) B₂ =
        rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂) := by
    ext T
    show ((1 - θ) • (toOp T * B₁) + θ • (toOp T * B₂) : L ℋ) =
      toOp T * ((1 - θ) • B₁ + θ • B₂)
    rw [mul_add, mul_smul_comm, mul_smul_comm]
  have hA_combo := pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo := pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  letI : Nontrivial (HSOp ℋ) := inferInstanceAs (Nontrivial (L ℋ))
  letI : Nontrivial (L (HSOp ℋ)) := inferInstance
  have hconv :
      operatorPowerMean (ℋ := HSOp ℋ) s 1
          (leftMulHS (ℋ := ℋ) ((1 - θ) • A₁ + θ • A₂))
          (rightMulHS (ℋ := ℋ) ((1 - θ) • B₁ + θ • B₂)) ≤
        (1 - θ) • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₁) (rightMulHS (ℋ := ℋ) B₁) +
          θ • operatorPowerMean (ℋ := HSOp ℋ) s 1
            (leftMulHS (ℋ := ℋ) A₂) (rightMulHS (ℋ := ℋ) B₂) := by
    simpa [hleft_combo, hright_combo] using
      operatorPowerMean_jointlyConvexOn_pdSet (ℋ := HSOp ℋ) (α := s) (β := 1)
        ⟨hs1, hs2⟩ ⟨by norm_num, by norm_num⟩
        (leftMulHS_pdSet (ℋ := ℋ) hA₁) (leftMulHS_pdSet (ℋ := ℋ) hA₂)
        (rightMulHS_pdSet (ℋ := ℋ) hB₁) (rightMulHS_pdSet (ℋ := ℋ) hB₂) hθ0 hθ1
  have hphi_mono := phiK_mono (ℋ := ℋ) K hconv
  rw [phiK_operatorPowerMean_eq_liebTraceMap (ℋ := ℋ) (s := s) K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • B₁ + θ • B₂) hA_combo hB_combo] at hphi_mono
  rw [phiK_weightedSum_operatorPowerMean_eq (ℋ := ℋ) (s := s) (θ := θ) K A₁ A₂ B₁ B₂
      hA₁ hA₂ hB₁ hB₂] at hphi_mono
  simpa [add_comm, add_left_comm, add_assoc] using hphi_mono

set_option maxHeartbeats 600000 in
theorem liebExtensionTrace_jointlyConcaveOn_pdSet
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : p + q ≤ 1) (K : L ℋ) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebExtensionTraceMap (ℋ := ℋ) q p K) := by
  have hq1 : q < 1 := by linarith
  let β : ℝ := p / (1 - q)
  have h1q : 0 < 1 - q := by linarith
  have hβ0 : 0 ≤ β := div_nonneg hp.le h1q.le
  have hβ1 : β ≤ 1 := (div_le_one h1q).mpr (by linarith)
  have hβ : β ∈ Set.Icc (0 : ℝ) 1 := ⟨hβ0, hβ1⟩
  have hβmul : β * (1 - q) = p := div_mul_cancel₀ p h1q.ne'
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hA_combo := pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
  have hB_combo := pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
  have hB₁β : B₁ ^ β ∈ pdSet (ℋ := ℋ) :=
    pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₁
  have hB₂β : B₂ ^ β ∈ pdSet (ℋ := ℋ) :=
    pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₂
  have hB_comboβ :
      (((1 - θ) • B₁ + θ • B₂) ^ β) ∈ pdSet (ℋ := ℋ) :=
    pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB_combo
  have hBpow_combo := pdSet_convexCombo (ℋ := ℋ) hB₁β hB₂β hθ0 hθ1
  rcases id hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases id hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  rcases id hB_combo with ⟨hB_combo_sa, hB_combo_spec⟩
  have hB₁0 : 0 ≤ B₁ := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ hB₁_sa).2
    fun x hx => (hB₁_spec hx).le
  have hB₂0 : 0 ≤ B₂ := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ hB₂_sa).2
    fun x hx => (hB₂_spec hx).le
  have hBcombo0 : 0 ≤ ((1 - θ) • B₁ + θ • B₂) :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hB_combo_sa).2
      fun x hx => (hB_combo_spec hx).le
  have hpow_conc :=
    power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := ℋ) β hβ hB₁_sa hB₂_sa hθ0 hθ1
      (fun x hx => Set.mem_Ici.mpr (hB₁_spec hx).le) fun x hx =>
        Set.mem_Ici.mpr (hB₂_spec hx).le
  have hBpow_le :
      (1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β) ≤
        ((1 - θ) • B₁ + θ • B₂) ^ β := by
    have hBcombo0' : 0 ≤ θ • B₂ + (1 - θ) • B₁ := by
      simpa [add_comm, add_left_comm, add_assoc] using hBcombo0
    have hneg :
        -(((1 - θ) • B₁ + θ • B₂) ^ β) ≤
          -((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β)) := by
      simpa [cfcR, LownerHeinzCore.cfcR, cfc_neg, smul_neg, neg_add,
        add_comm, add_left_comm, add_assoc,
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₁) (y := β) (ha := hB₁0),
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₂) (y := β) (ha := hB₂0),
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := θ • B₂ + (1 - θ) • B₁) (y := β) (ha := hBcombo0'),
        CFC.rpow_eq_cfc_real (A := L ℋ) (a := ((1 - θ) • B₁ + θ • B₂)) (y := β) (ha := hBcombo0)]
        using hpow_conc
    exact neg_le_neg_iff.mp hneg
  have hsmono : 1 - q ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hmono := liebTraceMap_mono_right (ℋ := ℋ) (s := q) hsmono K ((1 - θ) • A₁ + θ • A₂)
    ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β)) (((1 - θ) • B₁ + θ • B₂) ^ β)
    hA_combo hBpow_combo hB_comboβ hBpow_le
  have hconc :=
    liebTrace_jointlyConcaveOn_pdSet (ℋ := ℋ) hq hq1 K hA₁ hA₂ hB₁β hB₂β hθ0 hθ1
  have hpow_rewrite :
      ∀ {A B : L ℋ}, B ∈ pdSet (ℋ := ℋ) →
        liebTraceMap (ℋ := ℋ) q K A (B ^ β) =
          liebExtensionTraceMap (ℋ := ℋ) q p K A B := by
    intro A B hB
    rcases hB with ⟨hB_sa, hB_spec⟩
    have hB0 : 0 ≤ B := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B hB_sa).2
      fun x hx => (hB_spec hx).le
    have hpow : (B ^ β) ^ (1 - q) = B ^ p := by
      rw [CFC.rpow_rpow_of_exponent_nonneg (A := L ℋ) B β (1 - q) hβ0 (by linarith) hB0, hβmul]
    simp [liebTraceMap, liebExtensionTraceMap, hpow, mul_assoc]
  simpa [hpow_rewrite hB₁, hpow_rewrite hB₂, hpow_rewrite hB_combo] using le_trans hconc hmono

set_option maxHeartbeats 600000 in
theorem andoTrace_jointlyConvexOn_pdSet
    {q r : ℝ} (hq1 : 1 ≤ q) (hq2 : q ≤ 2) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hqr : 1 ≤ q - r) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (andoTraceMap (ℋ := ℋ) q r K) := by
  by_cases hqeq : q = 1
  · have hrz : r = 0 := by linarith
    subst hqeq
    subst hrz
    convert (liebTrace_jointlyConvexOn_pdSet (s := 1) (by norm_num) (by norm_num) K) using 1
    ext A B
    simp [andoTraceMap, liebTraceMap]
  · have hqgt : 1 < q := lt_of_le_of_ne hq1 (Ne.symm hqeq)
    let β : ℝ := r / (q - 1)
    have hq1pos : 0 < q - 1 := by linarith
    have hβ0 : 0 ≤ β := div_nonneg hr0 hq1pos.le
    have hβ1 : β ≤ 1 := (div_le_one hq1pos).mpr (by linarith)
    have hβ : β ∈ Set.Icc (0 : ℝ) 1 := ⟨hβ0, hβ1⟩
    have hβmul : β * (1 - q) = -r := by
      rw [show (1 : ℝ) - q = -(q - 1) by ring, mul_neg, div_mul_cancel₀ r hq1pos.ne']
    intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
    have hA_combo := pdSet_convexCombo (ℋ := ℋ) hA₁ hA₂ hθ0 hθ1
    have hB_combo := pdSet_convexCombo (ℋ := ℋ) hB₁ hB₂ hθ0 hθ1
    have hB₁β : B₁ ^ β ∈ pdSet (ℋ := ℋ) :=
      pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₁
    have hB₂β : B₂ ^ β ∈ pdSet (ℋ := ℋ) :=
      pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB₂
    have hB_comboβ :
        (((1 - θ) • B₁ + θ • B₂) ^ β) ∈ pdSet (ℋ := ℋ) :=
      pdSet_rpow_of_mem_Icc_zero_one (ℋ := ℋ) hβ hB_combo
    have hBpow_combo := pdSet_convexCombo (ℋ := ℋ) hB₁β hB₂β hθ0 hθ1
    rcases id hB₁ with ⟨hB₁_sa, hB₁_spec⟩
    rcases id hB₂ with ⟨hB₂_sa, hB₂_spec⟩
    rcases id hB_combo with ⟨hB_combo_sa, hB_combo_spec⟩
    have hB₁0 : 0 ≤ B₁ := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₁ hB₁_sa).2
      fun x hx => (hB₁_spec hx).le
    have hB₂0 : 0 ≤ B₂ := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B₂ hB₂_sa).2
      fun x hx => (hB₂_spec hx).le
    have hBcombo0 : 0 ≤ ((1 - θ) • B₁ + θ • B₂) :=
      (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hB_combo_sa).2
        fun x hx => (hB_combo_spec hx).le
    have hpow_conc :=
      power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := ℋ) β hβ hB₁_sa hB₂_sa hθ0 hθ1
        (fun x hx => Set.mem_Ici.mpr (hB₁_spec hx).le) fun x hx =>
          Set.mem_Ici.mpr (hB₂_spec hx).le
    have hBcombo0' : 0 ≤ θ • B₂ + (1 - θ) • B₁ := by
      simpa [add_comm, add_left_comm, add_assoc] using hBcombo0
    have hBpow_le :
        (1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β) ≤
          ((1 - θ) • B₁ + θ • B₂) ^ β := by
      have hneg :
          -(((1 - θ) • B₁ + θ • B₂) ^ β) ≤
            -((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β)) := by
        simpa [cfcR, LownerHeinzCore.cfcR, cfc_neg, smul_neg, neg_add,
          add_comm, add_left_comm, add_assoc,
          CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₁) (y := β) (ha := hB₁0),
          CFC.rpow_eq_cfc_real (A := L ℋ) (a := B₂) (y := β) (ha := hB₂0),
          CFC.rpow_eq_cfc_real (A := L ℋ) (a := θ • B₂ + (1 - θ) • B₁) (y := β) (ha := hBcombo0'),
          CFC.rpow_eq_cfc_real (A := L ℋ) (a := ((1 - θ) • B₁ + θ • B₂)) (y := β) (ha := hBcombo0)]
          using hpow_conc
      exact neg_le_neg_iff.mp hneg
    have hsanti : 1 - q ∈ Set.Icc (-1 : ℝ) 0 := ⟨by linarith, by linarith⟩
    have hmono := liebTraceMap_antitone_right (ℋ := ℋ) (s := q) hsanti K
      ((1 - θ) • A₁ + θ • A₂) ((1 - θ) • (B₁ ^ β) + θ • (B₂ ^ β))
      (((1 - θ) • B₁ + θ • B₂) ^ β) hA_combo hBpow_combo hB_comboβ hBpow_le
    have hconv :=
      liebTrace_jointlyConvexOn_pdSet (ℋ := ℋ) hq1 hq2 K hA₁ hA₂ hB₁β hB₂β hθ0 hθ1
    have hpow_rewrite :
        ∀ {A B : L ℋ}, B ∈ pdSet (ℋ := ℋ) →
          liebTraceMap (ℋ := ℋ) q K A (B ^ β) =
            andoTraceMap (ℋ := ℋ) q r K A B := by
      intro A B hB
      rcases hB with ⟨hB_sa, hB_spec⟩
      have hB0 : 0 ≤ B := (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B hB_sa).2
        fun x hx => (hB_spec hx).le
      have hBunit : IsUnit B := spectrum.isUnit_of_zero_notMem (R := ℝ) fun h0 =>
        lt_irrefl 0 (Set.mem_Ioi.mp (hB_spec h0))
      have hpow :
          (B ^ β) ^ (1 - q) = B ^ (-r) := by
        by_cases hβzero : β = 0
        · have hrz : r = 0 := by
            rw [hβzero] at hβmul
            linarith
          have hBzero : B ^ (0 : ℝ) = (1 : L ℋ) := by
            simpa using CFC.rpow_zero (a := B)
          simp [hβzero, hrz, hBzero, CFC.one_rpow]
        · calc
            (B ^ β) ^ (1 - q) = B ^ (β * (1 - q)) := by
                simpa [mul_comm] using
                  (CFC.rpow_rpow B β (1 - q) hβzero (hBunit.isStrictlyPositive hB0))
            _ = B ^ (-r) := by rw [hβmul]
      simp [liebTraceMap, andoTraceMap, hpow, mul_assoc]
    simpa [hpow_rewrite hB₁, hpow_rewrite hB₂, hpow_rewrite hB_combo] using le_trans hmono hconv

theorem liebCorollaryTrace_jointlyConvexOn_pdSet
    {q r : ℝ} (hr1 : 1 < r) (hrq : r ≤ q) (hq2 : q ≤ 2) (K : L ℋ) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (liebCorollaryTraceMap (ℋ := ℋ) q r K) := by
  have hq1 : 1 ≤ q := by linarith
  have hr0 : 0 ≤ r - 1 := by linarith
  have hr1' : r - 1 ≤ 1 := by linarith
  have hqr' : 1 ≤ q - (r - 1) := by linarith
  convert
    (andoTrace_jointlyConvexOn_pdSet (ℋ := ℋ) (q := q) (r := r - 1)
      hq1 hq2 hr0 hr1' hqr' K) using 1
  ext A B
  simp [liebCorollaryTraceMap, andoTraceMap]

end LiebAndoTrace
