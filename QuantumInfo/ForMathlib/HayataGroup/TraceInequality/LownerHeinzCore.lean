/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/

module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
## 構造（Core / Wrapper）

このファイルは Löwner–Heinz まわりの議論を、**一般の C★代数 `𝓐`** 上で再利用できるように
Core として切り出したものです。

- `section Pure`：`cfcR` と `OperatorMonotone(On)` / `OperatorConvexOn` などの **定義**（軽い層）
- `section Spectrum`：`NonnegSpectrumClass` などを仮定して、主要定理群を置く **重い層**
- `namespace LownerHeinzCore.Spectral`：`spectralOrder` を **`local instance`** として閉じ込めた wrapper

`spectralOrder` を Core 本体に混ぜず、wrapper 側で局所化することで、他モジュールへの順序変更が
漏れないようにしています。また `NonnegSpectrumClass` は必要な層で明示し、場当たりの `infer_instance`
散布を避けています。
-/

namespace LownerHeinzCore

universe u v

open CFC

section Pure

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]

noncomputable abbrev cfcR (f : ℝ → ℝ) (A : 𝓐) : 𝓐 :=
  cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f A

/-- Fixed-space operator monotonicity on the ambient algebra `𝓐`. -/
def OperatorMonotone (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄, 0 ≤ A → 0 ≤ B → B ≤ A → cfcR f B ≤ cfcR f A

/-- Fixed-space operator monotonicity on `s` for the ambient algebra `𝓐`. -/
def OperatorMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄,
    0 ≤ A → 0 ≤ B → B ≤ A →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f B ≤ cfcR f A

/-- Fixed-space operator antitonicity on the ambient algebra `𝓐`. -/
def OperatorAntitone (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄, 0 ≤ A → 0 ≤ B → B ≤ A →
    cfcR f A ≤ cfcR f B

/-- Fixed-space operator antitonicity on `s` for the ambient algebra `𝓐`. -/
def OperatorAntitoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄,
    0 ≤ A → 0 ≤ B → B ≤ A →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f A ≤ cfcR f B

/-- Fixed-space operator convexity on the ambient algebra `𝓐`. -/
def OperatorConvex (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄ ⦃t : ℝ⦄, 0 ≤ t → t ≤ 1 →
    cfcR f ((1 - t) • A + t • B)
      ≤ (1 - t) • cfcR f A + t • cfcR f B

/-- Fixed-space operator convexity on `s` for the ambient algebra `𝓐`. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄ ⦃t : ℝ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    0 ≤ t → t ≤ 1 →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f ((1 - t) • A + t • B)
      ≤ (1 - t) • cfcR f A + t • cfcR f B

/-- Fixed-space operator concavity on the ambient algebra `𝓐`. -/
def OperatorConcave (f : ℝ → ℝ) : Prop :=
  OperatorConvex (𝓐 := 𝓐) (fun x => - f x)

/-- Fixed-space operator concavity on `s` for the ambient algebra `𝓐`. -/
def OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorConvexOn (𝓐 := 𝓐) (s : Set ℝ) (fun x => - f x)

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator monotonicity over all ambient algebras in universe `u`. -/
def OperatorMonotoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorMonotone (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator monotonicity on `s` over all ambient algebras in universe `u`. -/
def OperatorMonotoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorMonotoneOn (𝓐 := 𝓑) s f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator antitonicity over all ambient algebras in universe `u`. -/
def OperatorAntitoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorAntitone (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator antitonicity on `s` over all ambient algebras in universe `u`. -/
def OperatorAntitoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorAntitoneOn (𝓐 := 𝓑) s f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator convexity over all ambient algebras in universe `u`. -/
def OperatorConvexAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorConvex (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator convexity on `s` over all ambient algebras in universe `u`. -/
def OperatorConvexOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorConvexOn (𝓐 := 𝓑) s f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator concavity over all ambient algebras in universe `u`. -/
def OperatorConcaveAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorConcave (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator concavity on `s` over all ambient algebras in universe `u`. -/
def OperatorConcaveOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorConcaveOn (𝓐 := 𝓑) s f

end Pure

section Spectrum

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]
variable [NonnegSpectrumClass ℝ 𝓐]

omit [Nontrivial (𝓐)] [NonnegSpectrumClass ℝ 𝓐] in
lemma conjugate_isPositive {X T : 𝓐} (hX : 0 ≤ X) (hT : IsSelfAdjoint T) :
    0 ≤ T * X * T := by
  simpa using hT.conjugate_nonneg hX

omit [Nontrivial 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
theorem one_div_operatorAntitoneOn_Ioi :
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  dsimp [OperatorAntitoneOn]
  intro A B A_nonneg B_nonneg BA As Bs
  let f : ℝ → ℝ := fun x ↦ x
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg A_nonneg
  have hB_sa : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg B_nonneg
  have hA_ne0 : ∀ x ∈ spectrum ℝ A, f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (As hx)
  have hB_ne0 : ∀ x ∈ spectrum ℝ B, f x ≠ 0 := by
    intro x hx
    exact ne_of_gt (Bs hx)
  let uA : (𝓐)ˣ :=
    cfcUnits (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f A hA_ne0 (ha := hA_sa)
  let uB : (𝓐)ˣ :=
    cfcUnits (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f B hB_ne0 (ha := hB_sa)
  have huA_val : (uA : 𝓐) = A := by
    simp [uA, cfcUnits, f, cfc_id' (R := ℝ) (a := A) (ha := hA_sa)]
  have huB_val : (uB : 𝓐) = B := by
    simp [uB, cfcUnits, f, cfc_id' (R := ℝ) (a := B) (ha := hB_sa)]
  have huB_nonneg : 0 ≤ (uB : 𝓐) := by
    simpa [huB_val] using B_nonneg
  have hub_le_hua : (uB : 𝓐) ≤ (uA : 𝓐) := by
    simpa [huA_val, huB_val] using BA
  have hinv : (↑uA⁻¹ : 𝓐) ≤ (↑uB⁻¹ : 𝓐) := by
    simpa using
      (CStarAlgebra.inv_le_inv (A := 𝓐) (a := uB) (b := uA) huB_nonneg hub_le_hua)
  -- convert the inverse inequality back to the desired `cfcR` inequality
  simpa [uA, uB, cfcUnits, cfcR, f, one_div] using hinv

private lemma spectrum_convexCombo_Ioi {A B : 𝓐} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) := by
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have hApos : ∃ r > 0, algebraMap ℝ (𝓐) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := A) (ha := hA)).2 ?_
    intro x hx
    exact As hx
  have hBpos : ∃ r > 0, algebraMap ℝ (𝓐) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := B) (ha := hB)).2 ?_
    intro x hx
    exact Bs hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by simpa [sub_eq_zero] using (sub_eq_zero.mp h1t).symm
      subst ht'
      simpa [rC, h1t] using hrB
    · simpa [rC] using add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne' (sub_nonneg.mpr ht1) (by simpa using h1t)) hrA) (mul_nonneg ht0 (le_of_lt hrB))
  have hrC_le : algebraMap ℝ (𝓐) rC ≤ C := by
    have hsum : (1 - t) • algebraMap ℝ (𝓐) rA + t • algebraMap ℝ (𝓐) rB ≤ C := by
      simpa [C] using add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1)) (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (𝓐) rA + t • algebraMap ℝ (𝓐) rB =
          algebraMap ℝ (𝓐) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  intro x hx
  simpa [C] using (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx

omit [Nontrivial (𝓐)] in
omit [NonnegSpectrumClass ℝ 𝓐] in
private lemma posSemidef_block_one_inv {A : 𝓐} (hA : IsSelfAdjoint A)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    Matrix.PosSemidef
      (!![A, 1; 1, cfcR (fun x : ℝ ↦ x⁻¹) A] : Matrix (Fin 2) (Fin 2) 𝓐) := by
  -- Gram matrix construction using `A^{1/2}` and `A^{-1/2}`
  set sqrtA : 𝓐 := cfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) A
  set invSqrtA : 𝓐 := cfcR (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) A
  set v : Fin 2 → 𝓐 := fun i => if i = 0 then sqrtA else invSqrtA
  have posV : Matrix.PosSemidef (Matrix.vecMulVec v (star v)) := by
    simpa using (Matrix.posSemidef_vecMulVec_self_star (R := 𝓐) v)
  have hsqrtA : IsSelfAdjoint sqrtA := by
    dsimp [sqrtA, cfcR]
    exact cfc_predicate _ _
  have hinvSqrtA : IsSelfAdjoint invSqrtA := by
    dsimp [invSqrtA, cfcR]
    exact cfc_predicate _ _
  have hcont_sqrt : ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ A) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt (As hx)))).continuousWithinAt
  have hcont_invSqrt : ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ A) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt (As hx)))).continuousWithinAt
  have sqrtA_mul_invSqrtA : sqrtA * invSqrtA = (1 : 𝓐) := by
    dsimp [sqrtA, invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_sqrt hcont_invSqrt, ← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((1 : ℝ) / 2 + (-1) / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
  have invSqrtA_mul_sqrtA : invSqrtA * sqrtA = (1 : 𝓐) := by
    dsimp [sqrtA, invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_invSqrt hcont_sqrt, ← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((-1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
  have invSqrtA_mul_invSqrtA : invSqrtA * invSqrtA = cfcR (fun x : ℝ ↦ x ^ (-1 : ℝ)) A := by
    dsimp [invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_invSqrt hcont_invSqrt]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((-1 : ℝ) / 2 + (-1 : ℝ) / 2 : ℝ) = -1 from by ring]
  have sqrtA_mul_sqrtA : sqrtA * sqrtA = A := by
    dsimp [sqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_sqrt hcont_sqrt]
    calc
      cfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) A =
          cfcR (fun x : ℝ ↦ x) A := by
            apply cfc_congr
            intro x hx
            dsimp only
            rw [← Real.rpow_add (As hx), show ((1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 1 from by ring, Real.rpow_one]
      _ = A := cfc_id' (R := ℝ) (a := A) (ha := hA)
  have invA_eq : cfcR (fun x : ℝ ↦ x ^ (-1 : ℝ)) A = cfcR (fun x : ℝ ↦ x⁻¹) A := by
    dsimp [cfcR]
    apply cfc_congr
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt (As hx)
    simpa [hxne] using (Real.rpow_neg_one x)
  have hEq : Matrix.vecMulVec v (star v) = (!![A, 1; 1, cfcR (fun x : ℝ ↦ x⁻¹) A] :
      Matrix (Fin 2) (Fin 2) (𝓐)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_apply, v, hsqrtA.star_eq, hinvSqrtA.star_eq, sqrtA_mul_sqrtA,
        sqrtA_mul_invSqrtA, invSqrtA_mul_sqrtA, invSqrtA_mul_invSqrtA, invA_eq]
  simpa [hEq] using posV

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma schur_conj_eq_diagonal {C D invC : 𝓐} (hInvC_sa : IsSelfAdjoint invC)
    (invC_mul_C : invC * C = (1 : 𝓐)) (C_mul_invC : C * invC = (1 : 𝓐)) :
    star (!![(1 : 𝓐), -invC; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓐))
        * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐))
        * (!![(1 : 𝓐), -invC; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓐))
      = Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC) := by
  set U : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), -invC; 0, 1]
  have hstarU : star U = !![(1 : 𝓐), 0; -invC, 1] := by
    dsimp [U]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hInvC_sa.star_eq]
  have hP :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) =
        !![C, 1; -invC * C + 1, -invC + D] := by
    simp [hstarU, U]
  have hQ :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U =
        !![C, 0; 0, D - invC] := by
    have hstep :
        star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U =
          (!![C, 1; -invC * C + 1, -invC + D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U := by
      simpa [mul_assoc] using congrArg (fun X => X * U) hP
    dsimp [U] at hstep ⊢
    simp [hstep, C_mul_invC, invC_mul_C, sub_eq_add_neg, add_comm]
  have hdiag :
      (Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC)) =
        (!![C, 0; 0, D - invC] : Matrix (Fin 2) (Fin 2) (𝓐)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  simpa [hdiag] using hQ

theorem one_div_operatorConvexOn_Ioi :
  OperatorConvexOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  dsimp [OperatorConvexOn]
  intro A B t hA hB ht0 ht1 As Bs
  -- rewrite `1/x` as `x⁻¹`
  simp only [one_div]
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have specC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using
      spectrum_convexCombo_Ioi  (A := A) (B := B) (t := t) hA hB ht0 ht1 As Bs
  set invA : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) A
  set invB : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) B
  set invC : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) C
  set D : 𝓐 := (1 - t) • invA + t • invB
  let M_A : Matrix (Fin 2) (Fin 2) (𝓐) := !![A, 1; 1, invA]
  let M_B : Matrix (Fin 2) (Fin 2) (𝓐) := !![B, 1; 1, invB]
  let M : Matrix (Fin 2) (Fin 2) (𝓐) := (1 - t) • M_A + t • M_B
  have posA : Matrix.PosSemidef M_A := by
    simpa [M_A, invA] using posSemidef_block_one_inv  (A := A) hA As
  have posB : Matrix.PosSemidef M_B := by
    simpa [M_B, invB] using posSemidef_block_one_inv  (A := B) hB Bs
  have posM : Matrix.PosSemidef M := by
    simpa [M] using Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul (x := M_A) (a := (1 - t)) posA (sub_nonneg.mpr ht1))
      (Matrix.PosSemidef.smul (x := M_B) (a := t) posB ht0)
  have hM : M = !![C, 1; 1, D] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [M, M_A, M_B, C]
    · have h1 : (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = (1 : 𝓐) := by
        calc
          (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = ((1 - t) + t) • (1 : 𝓐) := by
            simpa using (add_smul (1 - t) t (1 : 𝓐)).symm
          _ = (1 : 𝓐) := by simp [sub_add_cancel]
      simp [M, M_A, M_B, h1]
    · have h1 : (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = (1 : 𝓐) := by
        calc
          (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = ((1 - t) + t) • (1 : 𝓐) := by
            simpa using (add_smul (1 - t) t (1 : 𝓐)).symm
          _ = (1 : 𝓐) := by simp [sub_add_cancel]
      simp [M, M_A, M_B, h1]
    · simp [M, M_A, M_B, D]
  let U : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), -invC; 0, 1]
  have hU : IsUnit U := by
    let V : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), invC; 0, 1]
    refine ⟨⟨U, V, ?_, ?_⟩, rfl⟩
    · dsimp [U, V]
      simp [Matrix.one_fin_two]
    · dsimp [U, V]
      simp [Matrix.one_fin_two]
  have hconj :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U
        = Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC) := by
    have hInvC_sa : IsSelfAdjoint invC := by
      dsimp [invC, cfcR]
      exact cfc_predicate _ _
    have hcont_inv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (spectrum ℝ C) :=
      fun x hx => (continuousAt_inv₀ (ne_of_gt (specC hx))).continuousWithinAt
    have invC_mul_C : invC * C = (1 : 𝓐) := by
      dsimp [invC, cfcR]
      have hmul :
          cfcR (fun x : ℝ ↦ x⁻¹) C * C =
            cfcR (fun x : ℝ ↦ x⁻¹ * x) C := by
        simpa [cfc_id' (R := ℝ) (a := C) (ha := hC)] using
          (cfc_mul (fun x : ℝ ↦ x⁻¹) (fun x : ℝ ↦ x) C hcont_inv continuousOn_id).symm
      rw [hmul, ← cfc_const_one ℝ C]
      apply cfc_congr
      intro x hx
      have hxne : x ≠ 0 := ne_of_gt (specC hx)
      simp [hxne]
    have C_mul_invC : C * invC = (1 : 𝓐) := by
      dsimp [invC, cfcR]
      have hmul :
          C * cfcR (fun x : ℝ ↦ x⁻¹) C =
            cfcR (fun x : ℝ ↦ x * x⁻¹) C := by
        simpa [cfc_id' (R := ℝ) (a := C) (ha := hC)] using
          (cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x⁻¹) C continuousOn_id hcont_inv).symm
      rw [hmul, ← cfc_const_one ℝ C]
      apply cfc_congr
      intro x hx
      have hxne : x ≠ 0 := ne_of_gt (specC hx)
      simp [hxne]
    simpa [U] using
      schur_conj_eq_diagonal  (C := C) (D := D) (invC := invC)
        hInvC_sa invC_mul_C C_mul_invC
  have posDiag :
      Matrix.PosSemidef (Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC)) := by
    have posConj : Matrix.PosSemidef (star U * M * U) := by
      simpa [Matrix.star_eq_conjTranspose] using (posM.conjTranspose_mul_mul_same U)
    have posConj' :
        Matrix.PosSemidef
          (star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) 𝓐) * U) := by
      -- rewrite the middle block matrix as `M`
      rw [← hM]
      exact posConj
    -- rewrite the goal using the computed conjugation
    rw [← hconj]
    exact posConj'
  have hinvC : invC ≤ D := by
    have hDinvC : 0 ≤ D - invC := by
      simpa using
        (Matrix.posSemidef_diagonal_iff (R := 𝓐)
          (d := fun i : Fin 2 => if i = 0 then C else D - invC)).1 posDiag (1 : Fin 2)
    exact le_of_sub_nonneg hDinvC
  exact hinvC

omit [Nontrivial (𝓐)] [NonnegSpectrumClass ℝ 𝓐] in
theorem one_div_add_t_operatorAntitoneOn_Ici : ∀ (t : ℝ), 0 < t →
  OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  dsimp [OperatorAntitoneOn]
  intro A B A_nonneg B_nonneg BA As Bs
  let f : ℝ → ℝ := fun x => x + t
  have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg A_nonneg
  have hB_sa : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg B_nonneg
  have hA_ne0 : ∀ x ∈ spectrum ℝ A, f x ≠ 0 := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := by
      simpa [Set.Ici] using (As hx)
    exact ne_of_gt (add_pos_of_nonneg_of_pos hx0 ht)
  have hB_ne0 : ∀ x ∈ spectrum ℝ B, f x ≠ 0 := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := by
      simpa [Set.Ici] using (Bs hx)
    exact ne_of_gt (add_pos_of_nonneg_of_pos hx0 ht)
  let uA : (𝓐)ˣ :=
    cfcUnits (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f A hA_ne0 (ha := hA_sa)
  let uB : (𝓐)ˣ :=
    cfcUnits (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f B hB_ne0 (ha := hB_sa)
  have huA_val : (uA : 𝓐) = A + algebraMap ℝ (𝓐) t := by
    -- unfold `uA` to a `cfc` statement and use `cfc_add_const` + `cfc_id'`
    simp [uA, cfcUnits, f]
    simpa [cfc_id' (R := ℝ) (a := A) (ha := hA_sa)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := A) (ha := hA_sa))
  have huB_val : (uB : 𝓐) = B + algebraMap ℝ (𝓐) t := by
    -- unfold `uB` to a `cfc` statement and use `cfc_add_const` + `cfc_id'`
    simp [uB, cfcUnits, f]
    simpa [cfc_id' (R := ℝ) (a := B) (ha := hB_sa)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := B) (ha := hB_sa))
  have huB_nonneg : 0 ≤ (uB : 𝓐) := by
    -- unfold `uB` and use pointwise nonnegativity on the spectrum
    simp only [uB, cfcUnits, f]
    refine cfc_nonneg (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := B) ?_
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := by
      simpa [Set.Ici] using (Bs hx)
    exact le_of_lt (add_pos_of_nonneg_of_pos hx0 ht)
  have hub_le_hua : (uB : 𝓐) ≤ (uA : 𝓐) := by
    simpa [huA_val, huB_val, add_assoc, add_left_comm, add_comm] using add_le_add_right BA (algebraMap ℝ (𝓐) t)
  have hinv : (↑uA⁻¹ : 𝓐) ≤ (↑uB⁻¹ : 𝓐) := by
    simpa using
      (CStarAlgebra.inv_le_inv (A := 𝓐) (a := uB) (b := uA) huB_nonneg hub_le_hua)
  -- convert the inverse inequality back to the desired `cfcR` inequality
  simpa [uA, uB, cfcUnits, cfcR, f, one_div] using hinv

-- Reduces to `one_div_operatorConvexOn_Ioi` and is also elaboration-heavy.
theorem one_div_add_t_operatorConvexOn_Ici : ∀ (t : ℝ), 0 < t →
  OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  /-
  It follows from one_div_operatorConvexOn_Ioi
  -/
  intro t ht
  dsimp [OperatorConvexOn]
  intro A B θ hA hB hθ0 hθ1 As Bs
  -- rewrite `1 / (x + t)` as `(x + t)⁻¹` for `simp`/`cfc` lemmas
  simp only [one_div]
  -- Reduce to operator convexity of `x ↦ x⁻¹` on `Ioi 0` by shifting by `t`.
  set C : 𝓐 := (1 - θ) • A + θ • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - θ)).smul hA |>.add ((IsSelfAdjoint.all θ).smul hB)
  set shift : ℝ → ℝ := fun x ↦ x + t
  set T : 𝓐 := algebraMap ℝ (𝓐) t
  have hT : IsSelfAdjoint T := by
    simpa [T] using (IsSelfAdjoint.algebraMap (A := 𝓐) (r := t)
      (hr := IsSelfAdjoint.all (t : ℝ)))
  have A_nonneg : 0 ≤ A := by
    have h0 : 0 ≤ cfcR (fun x : ℝ ↦ x) A := by
      dsimp [cfcR]
      apply cfc_nonneg
      intro x hx
      simpa [Set.Ici] using (As hx)
    simpa [cfcR, cfc_id' (R := ℝ) (a := A) (ha := hA)] using h0
  have B_nonneg : 0 ≤ B := by
    have h0 : 0 ≤ cfcR (fun x : ℝ ↦ x) B := by
      dsimp [cfcR]
      apply cfc_nonneg
      intro x hx
      simpa [Set.Ici] using (Bs hx)
    simpa [cfcR, cfc_id' (R := ℝ) (a := B) (ha := hB)] using h0
  have C_nonneg : 0 ≤ C := by
    simpa [C] using add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) A_nonneg) (smul_nonneg hθ0 B_nonneg)
  have hA_shift : cfcR shift A = A + T := by
    dsimp [cfcR, shift, T]
    simpa [cfc_id' (R := ℝ) (a := A) (ha := hA)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := A) (ha := hA))
  have hB_shift : cfcR shift B = B + T := by
    dsimp [cfcR, shift, T]
    simpa [cfc_id' (R := ℝ) (a := B) (ha := hB)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := B) (ha := hB))
  have hC_shift : cfcR shift C = C + T := by
    dsimp [cfcR, shift, T]
    simpa [cfc_id' (R := ℝ) (a := C) (ha := hC)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := C) (ha := hC))
  set A1 : 𝓐 := A + T
  set B1 : 𝓐 := B + T
  set C1 : 𝓐 := (1 - θ) • A1 + θ • B1
  have hA1_sa : IsSelfAdjoint A1 := by
    subst A1
    exact hA.add hT
  have hB1_sa : IsSelfAdjoint B1 := by
    subst B1
    exact hB.add hT
  have specA1 : spectrum ℝ A1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hs : spectrum ℝ (cfc shift A) = shift '' spectrum ℝ A := by
      simpa [shift] using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := A)
          (f := shift) (ha := hA))
    have hx' : x ∈ shift '' spectrum ℝ A := by
      have hx0 : x ∈ spectrum ℝ (cfc shift A) := by
        have hval : cfc shift A = A1 := by
          simpa [cfcR, shift, A1] using hA_shift
        simpa [hval] using hx
      simpa [hs] using hx0
    rcases hx' with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := by
      simpa [Set.Ici] using (As hy)
    simpa [Set.Ioi] using (add_pos_of_nonneg_of_pos hy0 ht)
  have specB1 : spectrum ℝ B1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hs : spectrum ℝ (cfc shift B) = shift '' spectrum ℝ B := by
      simpa [shift] using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := B)
          (f := shift) (ha := hB))
    have hx' : x ∈ shift '' spectrum ℝ B := by
      have hx0 : x ∈ spectrum ℝ (cfc shift B) := by
        have hval : cfc shift B = B1 := by
          simpa [cfcR, shift, B1] using hB_shift
        simpa [hval] using hx
      simpa [hs] using hx0
    rcases hx' with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := by
      simpa [Set.Ici] using (Bs hy)
    simpa [Set.Ioi] using (add_pos_of_nonneg_of_pos hy0 ht)
  have hC1 : C1 = C + T := by
    subst A1 B1 C1
    simp [C, add_assoc, add_left_comm, add_comm, smul_add]
  have hshift_ne0_A : ∀ x ∈ spectrum ℝ A, shift x ≠ 0 := by
    intro x hx
    have hx0 : 0 ≤ x := by
      simpa [Set.Ici] using (As hx)
    exact ne_of_gt (by simpa [shift] using (add_pos_of_nonneg_of_pos hx0 ht))
  have hshift_ne0_B : ∀ x ∈ spectrum ℝ B, shift x ≠ 0 := by
    intro x hx
    have hx0 : 0 ≤ x := by
      simpa [Set.Ici] using (Bs hx)
    exact ne_of_gt (by simpa [shift] using (add_pos_of_nonneg_of_pos hx0 ht))
  have hshift_ne0_C : ∀ x ∈ spectrum ℝ C, shift x ≠ 0 :=
    fun x hx ↦ ne_of_gt (by simpa [shift] using (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg C_nonneg hx) ht))
  have hA_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) A = Ring.inverse A1 := by
    have h' : cfc (fun x : ℝ ↦ (shift x)⁻¹) A = Ring.inverse (cfc shift A) := by
      simpa [shift] using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := shift) (a := A) hshift_ne0_A (ha := hA))
    have hval : cfc shift A = A1 := by
      simpa [cfcR, shift, A1] using hA_shift
    simpa [cfcR, shift, hval] using h'
  have hB_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) B = Ring.inverse B1 := by
    have h' : cfc (fun x : ℝ ↦ (shift x)⁻¹) B = Ring.inverse (cfc shift B) := by
      simpa [shift] using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := shift) (a := B) hshift_ne0_B (ha := hB))
    have hval : cfc shift B = B1 := by
      simpa [cfcR, shift, B1] using hB_shift
    simpa [cfcR, shift, hval] using h'
  have hC_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) C = Ring.inverse (C + T) := by
    have h' : cfc (fun x : ℝ ↦ (shift x)⁻¹) C = Ring.inverse (cfc shift C) := by
      simpa [shift] using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := shift) (a := C) hshift_ne0_C (ha := hC))
    have hval : cfc shift C = C + T := by
      simpa [cfcR, shift] using hC_shift
    simpa [cfcR, shift, hval] using h'
  have hA1_inv : cfcR (fun x : ℝ ↦ x⁻¹) A1 = Ring.inverse A1 := by
    dsimp [cfcR]
    simpa [cfc_id' (R := ℝ) (a := A1) (ha := hA1_sa)] using
      (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
        (a := A1) (fun x hx ↦ ne_of_gt (specA1 hx)) (ha := hA1_sa))
  have hB1_inv : cfcR (fun x : ℝ ↦ x⁻¹) B1 = Ring.inverse B1 := by
    dsimp [cfcR]
    simpa [cfc_id' (R := ℝ) (a := B1) (ha := hB1_sa)] using
      (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
        (a := B1) (fun x hx ↦ ne_of_gt (specB1 hx)) (ha := hB1_sa))
  have hA_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) A = cfcR (fun x : ℝ ↦ x⁻¹) A1 := by
    simp [hA_inv, hA1_inv]
  have hB_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) B = cfcR (fun x : ℝ ↦ x⁻¹) B1 := by
    simp [hB_inv, hB1_inv]
  have specC1 : spectrum ℝ C1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hs : spectrum ℝ (cfc shift C) = shift '' spectrum ℝ C := by
      simpa [shift] using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := C)
          (f := shift) (ha := hC))
    have hx' : x ∈ shift '' spectrum ℝ C := by
      have hx0 : x ∈ spectrum ℝ (cfc shift C) := by
        have hval : cfc shift C = C + T := by
          simpa [cfcR, shift] using hC_shift
        have hval' : cfc shift C = C1 := by
          simpa [hC1] using hval
        simpa [hval'] using hx
      simpa [hs] using hx0
    rcases hx' with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := spectrum_nonneg_of_nonneg C_nonneg hy
    have : 0 < y + t := add_pos_of_nonneg_of_pos hy0 ht
    simpa [Set.Ioi] using this
  have hC1_ne0 : ∀ x ∈ spectrum ℝ C1, (x : ℝ) ≠ 0 := fun x hx ↦ ne_of_gt (specC1 hx)
  have hC1_sa : IsSelfAdjoint C1 := by
    simpa [hC1] using (hC.add hT)
  have hC1_inv : cfcR (fun x : ℝ ↦ x⁻¹) C1 = Ring.inverse C1 := by
    dsimp [cfcR]
    simpa [cfc_id' (R := ℝ) (a := C1) (ha := hC1_sa)] using
      (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
        (a := C1) hC1_ne0 (ha := hC1_sa))
  have hC_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) C = cfcR (fun x : ℝ ↦ x⁻¹) C1 := by
    calc
      cfcR (fun x : ℝ ↦ (x + t)⁻¹) C
          = Ring.inverse (C + T) := hC_inv
      _ = Ring.inverse C1 := by simp [hC1]
      _ = cfcR (fun x : ℝ ↦ x⁻¹) C1 := by simpa using hC1_inv.symm
  have hconv :
      cfcR (fun x : ℝ ↦ x⁻¹) C1
        ≤ (1 - θ) • cfcR (fun x : ℝ ↦ x⁻¹) A1
          + θ • cfcR (fun x : ℝ ↦ x⁻¹) B1 := by
    simpa [one_div] using
      (one_div_operatorConvexOn_Ioi  (A := A1) (B := B1) (t := θ)
        hA1_sa hB1_sa hθ0 hθ1 specA1 specB1)
  -- conclude by rewriting everything to the shifted `1/x` convexity statement
  simpa [C, hC_eq, hA_eq, hB_eq] using hconv

omit [Nontrivial (𝓐)] [NonnegSpectrumClass ℝ 𝓐] in
theorem ratio_add_t_operatorMonotoneOn_Ici : ∀ (t : ℝ), 0 < t →
  OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  intro t ht
  dsimp [OperatorMonotoneOn]
  intro A B hA0 hB0 hBA hspA hspB
  let invfun : ℝ → ℝ := fun x : ℝ ↦ 1 / (x + t)
  have hmono_core :
      (1 : 𝓐) - t • cfcR invfun B ≤ (1 : 𝓐) - t • cfcR invfun A := by
    have h1 : t • cfcR invfun A ≤ t • cfcR invfun B :=
      smul_le_smul_of_nonneg_left
        ((one_div_add_t_operatorAntitoneOn_Ici  t ht) hA0 hB0 hBA hspA hspB) (le_of_lt ht)
    exact sub_le_sub_left h1 (1 : 𝓐)
  have hrepr (T : 𝓐) (hT0 : 0 ≤ T) (hspT : spectrum ℝ T ⊆ Set.Ici (0 : ℝ)) :
      cfcR (fun x : ℝ ↦ x / (x + t)) T = (1 : 𝓐) - t • cfcR invfun T := by
    have hT_sa : IsSelfAdjoint T := IsSelfAdjoint.of_nonneg hT0
    have hEqT :
        (spectrum ℝ T).EqOn (fun x : ℝ ↦ x / (x + t)) (fun x : ℝ ↦ 1 - t * invfun x) := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := by
        simpa [Set.Ici] using (hspT hx)
      simp [invfun]
      field_simp [ne_of_gt (add_pos_of_nonneg_of_pos hx0 ht)]
      ring
    have hT_ne0 : ∀ x ∈ spectrum ℝ T, x + t ≠ 0 := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := by
        simpa [Set.Ici] using (hspT hx)
      exact ne_of_gt (add_pos_of_nonneg_of_pos hx0 ht)
    have hT_cont : ContinuousOn invfun (spectrum ℝ T) := by
      have h1 : ContinuousOn (fun x : ℝ ↦ x + t) (spectrum ℝ T) :=
        continuousOn_id.add continuousOn_const
      have h2 : ContinuousOn (fun x : ℝ ↦ (x + t)⁻¹) (spectrum ℝ T) := h1.inv₀ hT_ne0
      simpa [invfun, one_div] using h2
    dsimp [cfcR]
    have hcongr :
        cfcR (fun x : ℝ ↦ x / (x + t)) T =
          cfcR (fun x : ℝ ↦ 1 - t * invfun x) T :=
      cfc_congr hEqT
    have hsub :
        cfcR (fun x : ℝ ↦ 1 - t * invfun x) T =
          cfcR (fun _ : ℝ ↦ (1 : ℝ)) T -
            cfcR (fun x : ℝ ↦ t * invfun x) T := by
      simpa using
        (cfc_sub (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun x : ℝ ↦ t * invfun x) (a := T)
          (hf := continuousOn_const) (hg := continuousOn_const.mul hT_cont))
    have hone :
        cfcR (fun _ : ℝ ↦ (1 : ℝ)) T = (1 : 𝓐) := by
      simpa using
        (cfc_const_one (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := T) (ha := hT_sa))
    have hmul :
        cfcR (fun x : ℝ ↦ t * invfun x) T =
          t • cfcR invfun T := by
      simpa using
        (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t) (f := invfun) (a := T)
          (hf := hT_cont))
    calc
      cfcR (fun x : ℝ ↦ x / (x + t)) T =
          cfcR (fun x : ℝ ↦ 1 - t * invfun x) T := hcongr
      _ =
          cfcR (fun _ : ℝ ↦ (1 : ℝ)) T -
            cfcR (fun x : ℝ ↦ t * invfun x) T := hsub
      _ = (1 : 𝓐) - t • cfcR invfun T := by
        rw [hone, hmul]
  calc
    cfcR (fun x : ℝ ↦ x / (x + t)) B
        = (1 : 𝓐) - t • cfcR invfun B := by
          simpa using hrepr B hB0 hspB
    _ ≤ (1 : 𝓐) - t • cfcR invfun A := hmono_core
    _ = cfcR (fun x : ℝ ↦ x / (x + t)) A := by
      simpa using (hrepr A hA0 hspA).symm

theorem ratio_add_t_operatorConcaveOn_Ici : ∀ (t : ℝ), 0 < t →
  OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
    intro t ht
    dsimp [OperatorConcaveOn, OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
    -- main input: operator convexity of `x ↦ 1 / (x + t)` on `Set.Ici 0`
    have hconv_inv :
        cfcR (fun x : ℝ ↦ 1 / (x + t)) ((1 - u) • A + u • B)
          ≤ (1 - u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
            + u • cfcR (fun x : ℝ ↦ 1 / (x + t)) B := by
      simpa using (one_div_add_t_operatorConvexOn_Ici  t ht) (A := A)
        (B := B) (t := u) hA hB hu0 hu1 As Bs
    -- rewrite `-(x/(x+t))` as `(-1) + t/(x+t)` under functional calculus
    have hcalc (T : 𝓐) (hT : IsSelfAdjoint T) (Ts : spectrum ℝ T ⊆ Set.Ici (0 : ℝ)) :
        cfcR (fun x : ℝ ↦ - (x / (x + t))) T
          = algebraMap ℝ (𝓐) (-1 : ℝ)
            + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) T := by
      let invfun : ℝ → ℝ := fun x ↦ 1 / (x + t)
      have hne0 : ∀ x ∈ spectrum ℝ T, x + t ≠ 0 := by
        intro x hx
        have hx0 : (0 : ℝ) ≤ x := by
          simpa [Set.Ici] using (Ts hx)
        exact ne_of_gt (add_pos_of_nonneg_of_pos hx0 ht)
      have hcont : ContinuousOn invfun (spectrum ℝ T) := by
        have h1 : ContinuousOn (fun x : ℝ ↦ x + t) (spectrum ℝ T) :=
          continuousOn_id.add continuousOn_const
        have h2 : ContinuousOn (fun x : ℝ ↦ (x + t)⁻¹) (spectrum ℝ T) := h1.inv₀ hne0
        simpa [invfun, one_div] using h2
      dsimp [cfcR]
      have hcongr :
          cfcR (fun x : ℝ ↦ - (x / (x + t))) T
            = cfcR
                (fun x : ℝ ↦ (-1 : ℝ) + t * invfun x) T := by
        apply cfc_congr
        intro x hx
        have hx0 : (0 : ℝ) ≤ x := by
          simpa [Set.Ici] using (Ts hx)
        have :
            - (x / (x + t)) = (-1 : ℝ) + t * (1 / (x + t)) := by
          field_simp [ne_of_gt (add_pos_of_nonneg_of_pos hx0 ht)]
          ring_nf
        simpa [invfun] using this
      calc
        cfcR (fun x : ℝ ↦ - (x / (x + t))) T
            = cfcR
                (fun x : ℝ ↦ (-1 : ℝ) + t * invfun x) T := hcongr
        _ = algebraMap ℝ (𝓐) (-1 : ℝ)
              + cfcR (fun x : ℝ ↦ t * invfun x) T := by
            simpa using
              (cfc_const_add (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := (-1 : ℝ))
                (f := fun x : ℝ ↦ t * invfun x) (a := T)
                (hf := continuousOn_const.mul hcont) (ha := hT))
        _ = algebraMap ℝ (𝓐) (-1 : ℝ)
              + t • cfcR invfun T := by
            simp [cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) t invfun T
              (hf := hcont)]
        _ = algebraMap ℝ (𝓐) (-1 : ℝ)
              + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) T := by
            simp [invfun]
    set AB : 𝓐 := (1 - u) • A + u • B
    have hAB : IsSelfAdjoint AB := by
      dsimp [AB]
      simpa using
        (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) hA).add
          (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) hB)
    -- apply operator convexity of `-(x/(x+t))`
    have hL :
        cfcR (fun x : ℝ ↦ - (x / (x + t))) AB
          ≤ (1 - u) • cfcR (fun x : ℝ ↦ - (x / (x + t))) A
            + u • cfcR (fun x : ℝ ↦ - (x / (x + t))) B := by
      -- expand both sides using `hcalc`, then use `hconv_inv`
      -- (filled in the next step)
      set C : 𝓐 := algebraMap ℝ (𝓐) (-1 : ℝ)
      have nonneg_of_spectrum_subset_Ici0 {T : 𝓐} (hT : IsSelfAdjoint T)
          (Ts : spectrum ℝ T ⊆ Set.Ici (0 : ℝ)) : 0 ≤ T := by
        have h' : algebraMap ℝ (𝓐) (0 : ℝ) ≤ T :=
          (algebraMap_le_iff_le_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
              (r := (0 : ℝ)) (a := T) (ha := hT)).2 (by
              intro x hx
              simpa [Set.Ici] using (Ts hx))
        simpa using h'
      have hA0 : 0 ≤ A :=
        nonneg_of_spectrum_subset_Ici0 (T := A) hA As
      have hB0 : 0 ≤ B :=
        nonneg_of_spectrum_subset_Ici0 (T := B) hB Bs
      have hAB0 : 0 ≤ AB := by
        dsimp [AB]
        exact add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
      have ABs : spectrum ℝ AB ⊆ Set.Ici (0 : ℝ) := by
        intro x hx
        have hx0 : (0 : ℝ) ≤ x :=
          spectrum_nonneg_of_nonneg (𝕜 := ℝ) (A := 𝓐) (a := AB) hAB0 hx
        simpa [Set.Ici] using hx0
      have hscale :
          t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
            ≤ (t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
              + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B := by
        have hconv_inv_AB :
            cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤ (1 - u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                + u • cfcR (fun x : ℝ ↦ 1 / (x + t)) B := by
          simpa [AB] using hconv_inv
        have hscale0 :
            t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤ t •
                  ((1 - u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + u • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) :=
          smul_le_smul_of_nonneg_left hconv_inv_AB (le_of_lt ht)
        calc
          t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤ t •
                  ((1 - u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + u • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := hscale0
          _ =
              (t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B := by
            simp [smul_add, smul_smul]
      have hconst : (1 - u) • C + u • C = C := by
        simpa [add_smul, sub_add_cancel] using (add_smul (1 - u) u C).symm
      have hmain :
          C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
            ≤ (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
              + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
        have h' :
            C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤ C
                + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                  + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
          exact add_le_add_right hscale C
        have hR :
            C
                + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                  + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)
              =
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
          have hR' :
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                  + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)
                =
                ((1 - u) • C + u • C)
                  + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
            calc
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                  + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)
                  =
                  (1 - u) • C
                    + (1 - u) • (t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                    + (u • C + u • (t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)) := by
                    simp [smul_add, add_assoc, add_left_comm, add_comm]
              _ =
                  (1 - u) • C
                    + (t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + (u • C + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
                    simp [smul_smul, mul_comm, add_assoc, add_left_comm, add_comm]
              _ =
                  ((1 - u) • C + u • C)
                    + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                      + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
                    abel
          calc
            C
                + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                  + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B)
                =
                ((1 - u) • C + u • C)
                  + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                    + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
                  simp [hconst, add_comm]
            _ =
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := by
                  simpa using hR'.symm
        calc
          C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) AB
              ≤
              C
                + ((t * (1 - u)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) A
                  + (t * u) • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := h'
          _ =
              (1 - u) • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) A)
                + u • (C + t • cfcR (fun x : ℝ ↦ 1 / (x + t)) B) := hR
      dsimp [C] at hmain
      rw [hcalc AB hAB ABs, hcalc A hA As, hcalc B hB Bs]
      exact hmain
    simpa [AB] using hL

omit [Nontrivial (𝓐)] in
theorem power_Icc_zero_one_operatorMonotoneOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
  OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  dsimp [OperatorMonotoneOn]
  intro A B hA0 hB0 hBA hspA hspB
  have hA : cfcR (fun x : ℝ ↦ x ^ p) A = A ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := A) (y := p) (ha := hA0)).symm
  have hB : cfcR (fun x : ℝ ↦ x ^ p) B = B ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := B) (y := p) (ha := hB0)).symm
  simpa [hA, hB] using (CFC.rpow_le_rpow (A := 𝓐) hp hBA)

omit [Nontrivial (𝓐)] in
omit [StarOrderedRing 𝓐] in
private lemma cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1)
    {t : ℝ} (htpos : 0 < t) (X : 𝓐) (hX0 : 0 ≤ X) :
    cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
      (t ^ ((q : ℝ) - 1)) • cfcR (fun x : ℝ => x / (x + t)) X := by
  have hq_real : ((q : ℝ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨(NNReal.coe_pos).2 hq.1, (NNReal.coe_lt_coe).2 hq.2⟩
  let ratio : ℝ → ℝ := fun x => x / (x + t)
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hcont_ratio : ContinuousOn ratio (spectrum ℝ X) :=
    continuousOn_id.div (continuousOn_id.add continuousOn_const) (fun x hx ↦ ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hX0 hx) htpos))
  have hcfcₙ : cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
      cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X := by
    have hqs : quasispectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := quasispectrum_nonneg_of_nonneg X hX0 x hx
      simpa [Set.Ici] using hx0
    have hf : ContinuousOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (quasispectrum ℝ X) :=
      (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real htpos).mono hqs
    simpa using
      (cfcₙ_eq_cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := Real.rpowIntegrand₀₁ (q : ℝ) t) (a := X) (hf := hf) (hf0 := by simp))
  have hEq :
      (spectrum ℝ X).EqOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (fun x : ℝ ↦ r * ratio x) := by
    intro x hx
    simp [r, ratio, Real.rpowIntegrand₀₁_eq_pow_div hq_real (le_of_lt htpos) (spectrum_nonneg_of_nonneg hX0 hx),
      add_comm, mul_div_assoc]
  have hcfc_congr :
      cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
        cfcR (fun x : ℝ ↦ r * ratio x) X :=
    cfc_congr hEq
  have hcfc_mul :
      cfcR (fun x : ℝ ↦ r * ratio x) X =
        r • cfcR ratio X := by
    simpa using
      (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := r) (f := ratio) (a := X)
        (hf := hcont_ratio))
  have hmain :
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X = r • cfcR ratio X := by
    calc
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
          cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X := by
            simpa using hcfcₙ
      _ = cfcR (fun x : ℝ ↦ r * ratio x) X := hcfc_congr
      _ = r • cfcR ratio X := hcfc_mul
      _ = r • cfcR ratio X := by simp [cfcR]
  simpa [r, ratio] using hmain

private lemma cfcR_ratio_weighted_le {t : ℝ} (htpos : 0 < t) {A B : 𝓐} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • cfcR (fun x : ℝ => x / (x + t)) A + b • cfcR (fun x : ℝ => x / (x + t)) B
      ≤ cfcR (fun x : ℝ => x / (x + t)) (a • A + b • B) := by
  have ha1 : a = 1 - b := by linarith [hab]
  have hb1 : b ≤ 1 := by linarith [ha, hab]
  have hspec (X : 𝓐) (hX0 : 0 ≤ X) : spectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := spectrum_nonneg_of_nonneg hX0 hx
    simpa [Set.Ici] using hx0
  have hOp := ratio_add_t_operatorConcaveOn_Ici (𝓐 := 𝓐) t htpos
  have hneg :=
    (by
      dsimp [OperatorConcaveOn, OperatorConvexOn] at hOp
      have := hOp (A := A) (B := B) (t := b) (IsSelfAdjoint.of_nonneg hA0) (IsSelfAdjoint.of_nonneg hB0)
        hb hb1 (hspec A hA0) (hspec B hB0)
      exact this)
  have hneg' :
      cfcR (fun x : ℝ ↦ - (x / (x + t))) ((1 - b) • A + b • B)
        ≤ (1 - b) • cfcR (fun x : ℝ ↦ - (x / (x + t))) A
          + b • cfcR (fun x : ℝ ↦ - (x / (x + t))) B := hneg
  have hneg'' :
      -cfcR (fun x : ℝ => x / (x + t)) ((1 - b) • A + b • B)
        ≤ -((1 - b) • cfcR (fun x : ℝ => x / (x + t)) A + b • cfcR (fun x : ℝ => x / (x + t)) B) := by
    have h' :
        -cfcR (fun x : ℝ => x / (x + t)) ((1 - b) • A + b • B)
          ≤ -(b • cfcR (fun x : ℝ => x / (x + t)) B + (1 - b) • cfcR (fun x : ℝ => x / (x + t)) A) := by
      simpa [cfcR, cfc_neg, smul_neg, neg_add] using hneg'
    simpa [add_comm, add_left_comm, add_assoc] using h'
  simpa [ha1, add_comm, add_left_comm, add_assoc] using neg_le_neg_iff.mp hneg''

private lemma concaveOn_cfcₙ_rpowIntegrand₀₁ {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1)
    {t : ℝ} (htpos : 0 < t) :
    ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 => cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A) := by
  have hq_real : ((q : ℝ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · exact (NNReal.coe_pos).2 hq.1
    · exact (NNReal.coe_lt_coe).2 hq.2
  refine ⟨convex_Ici (𝕜 := ℝ) (0 : 𝓐), ?_⟩
  intro A hA B hB a b ha hb hab
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hB0 : 0 ≤ B := by simpa [Set.Ici] using hB
  have hAB0 : 0 ≤ a • A + b • B := add_nonneg (smul_nonneg ha hA0) (smul_nonneg hb hB0)
  let ratio : ℝ → ℝ := fun x => x / (x + t)
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg (le_of_lt htpos) _
  have hrepr (X : 𝓐) (hX0 : 0 ≤ X) :
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X = r • cfcR ratio X := by
    simpa [r, ratio] using cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio  (q := q) hq htpos X hX0
  have hratio :
      a • cfcR ratio A + b • cfcR ratio B ≤ cfcR ratio (a • A + b • B) := by
    -- use the separate lemma to keep heartbeats per-declaration small
    -- (`ratio` is a local abbreviation here)
    simpa [ratio] using cfcR_ratio_weighted_le  (t := t) htpos (A := A) (B := B) hA0 hB0 ha hb hab
  have hscaled : r • (a • cfcR ratio A + b • cfcR ratio B) ≤ r • cfcR ratio (a • A + b • B) :=
    smul_le_smul_of_nonneg_left hratio hr_nonneg
  have hL :
      a • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A + b • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) B =
        r • (a • cfcR ratio A + b • cfcR ratio B) := by
    simp [hrepr A hA0, hrepr B hB0, smul_add, smul_smul, mul_comm]
  have hR :
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) (a • A + b • B) = r • cfcR ratio (a • A + b • B) := by
    simp [hrepr (a • A + b • B) hAB0]
  calc
    a • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A + b • cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) B
        = r • (a • cfcR ratio A + b • cfcR ratio B) := hL
    _ ≤ r • cfcR ratio (a • A + b • B) := hscaled
    _ = cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) (a • A + b • B) := hR.symm

private lemma concaveOn_nnrpow_Ioo {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1) :
    ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ q) := by
  -- integral representation for `a ↦ a ^ q`
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ (A := 𝓐) hq
  let ν : MeasureTheory.Measure ℝ := μ.restrict (Set.Ioi (0 : ℝ))
  let F : ℝ → 𝓐 → 𝓐 := fun t A => cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A
  have hF_int : ∀ A ∈ Set.Ici (0 : 𝓐), MeasureTheory.Integrable (fun t => F t A) ν := by
    intro A hA
    simpa [F, ν, MeasureTheory.IntegrableOn] using (hμ A hA).1
  have hF_conc :
      ∀ᵐ t ∂ν, ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 => F t A) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    simpa [F] using (concaveOn_cfcₙ_rpowIntegrand₀₁  (q := q) hq ht)
  have hconc_int :
      ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ ∫ t, F t A ∂ν) :=
    MeasureTheory.integral_concaveOn_of_integrand_ae
      (μ := ν) (s := Set.Ici (0 : 𝓐)) (f := fun t A => F t A)
      (convex_Ici (𝕜 := ℝ) (0 : 𝓐)) hF_conc hF_int
  -- identify the integral with `A ^ q` on `Ici 0`
  refine hconc_int.congr ?_
  intro A hA
  -- `A ^ q` is the set integral of the integrand on `Ioi 0`
  have hEq : A ^ q = ∫ t, F t A ∂ν := by
    simpa [F, ν] using (hμ A hA).2
  simp [hEq]

private lemma concaveOn_rpow_Ioo {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ p) := by
  -- reduce to the `ℝ≥0` exponent case
  let q : NNReal := ⟨p, le_of_lt hp.1⟩
  have hq0 : (0 : NNReal) < q := by
    have : (0 : ℝ) < (q : ℝ) := by
      exact hp.1
    exact (NNReal.coe_pos).1 this
  have hq1 : q < (1 : NNReal) := by
    have : (q : ℝ) < (1 : ℝ) := by
      exact hp.2
    exact (NNReal.coe_lt_coe).1 (by simpa using this)
  have hq : q ∈ Set.Ioo (0 : NNReal) 1 := ⟨hq0, hq1⟩
  -- main lemma: concavity for `a ↦ a ^ q`
  have hconc : ConcaveOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ q) :=
    concaveOn_nnrpow_Ioo  hq
  -- transport concavity from `A ^ q` to `A ^ p`
  refine hconc.congr ?_
  intro A hA
  -- `A ^ q = A ^ (q : ℝ)`, and `(q : ℝ) = p`
  exact (CFC.nnrpow_eq_rpow (A := 𝓐) (a := A) (x := q) hq0)

theorem power_Icc_zero_one_operatorConcaveOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
  OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  by_cases hp0 : p = 0
  · subst hp0
    dsimp [OperatorConcaveOn, OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hC : IsSelfAdjoint ((1 - u) • A + u • B) := by
      simpa using (IsSelfAdjoint.all (1 - u)).smul hA |>.add ((IsSelfAdjoint.all u).smul hB)
    have hfun : (fun x : ℝ ↦ - (x ^ (0 : ℝ))) = (fun _ : ℝ ↦ (-1 : ℝ)) := by
      funext x
      simp
    have hconst (T : 𝓐) (hT : IsSelfAdjoint T) :
        cfcR (fun _ : ℝ ↦ (-1 : ℝ)) T = (-1 : 𝓐) := by
      simpa [cfcR] using
        (cfc_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (-1 : ℝ) T hT)
    rw [hfun]
    rw [hconst _ hC, hconst _ hA, hconst _ hB]
    have hR : (1 - u) • (-1 : 𝓐) + u • (-1 : 𝓐) = (-1 : 𝓐) := by
      calc
        (1 - u) • (-1 : 𝓐) + u • (-1 : 𝓐) = ((1 - u) + u) • (-1 : 𝓐) := by
          simpa [add_smul] using (add_smul (1 - u) u (-1 : 𝓐)).symm
        _ = (1 : ℝ) • (-1 : 𝓐) := by simp
        _ = (-1 : 𝓐) := by simp
    simp
  by_cases hp1 : p = 1
  · subst hp1
    dsimp [OperatorConcaveOn, OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hC : IsSelfAdjoint ((1 - u) • A + u • B) := by
      simpa using (IsSelfAdjoint.all (1 - u)).smul hA |>.add ((IsSelfAdjoint.all u).smul hB)
    have hfun : (fun x : ℝ ↦ - (x ^ (1 : ℝ))) = (fun x : ℝ ↦ -x) := by
      funext x
      simp
    have hneg (T : 𝓐) (hT : IsSelfAdjoint T) :
        cfcR (fun x : ℝ ↦ -x) T = -T := by
      simpa [cfcR] using (cfc_neg_id (R := ℝ) (p := IsSelfAdjoint) (a := T) hT)
    rw [hfun]
    rw [hneg _ hC, hneg _ hA, hneg _ hB]
    -- both sides are `-((1-u)•A + u•B)`
    simp [add_comm, sub_eq_add_neg]
  have hp01 : p ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have : 0 ≤ p := hp.1
      exact lt_of_le_of_ne this (Ne.symm hp0)
    · have : p ≤ 1 := hp.2
      exact lt_of_le_of_ne this hp1
  dsimp [OperatorConcaveOn, OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  have hA0 : 0 ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := As hx
    simpa [Set.Ici] using this
  have hB0 : 0 ≤ B := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := Bs hx
    simpa [Set.Ici] using this
  have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
  have hC0 : 0 ≤ (1 - u) • A + u • B :=
    add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
  set C : 𝓐 := (1 - u) • A + u • B
  have hC_mem : C ∈ Set.Ici (0 : 𝓐) := by
    simpa [C, Set.Ici] using hC0
  have hA_mem : A ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hA0
  have hB_mem : B ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hB0
  have hconcC : (1 - u) • (A ^ p) + u • (B ^ p) ≤ C ^ p := by
    have hab : (1 - u) + u = (1 : ℝ) := by ring
    simpa [C] using (concaveOn_rpow_Ioo  hp01).2 hA_mem hB_mem hu0' hu0 hab
  have hcalc (T : 𝓐) (hT0 : 0 ≤ T) :
      cfcR (fun x : ℝ ↦ x ^ p) T = T ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := T) (y := p) (ha := hT0)).symm
  have hconcC' :
      (1 - u) • cfcR (fun x : ℝ ↦ x ^ p) A + u • cfcR (fun x : ℝ ↦ x ^ p) B
        ≤ cfcR (fun x : ℝ ↦ x ^ p) C := by
    simpa [hcalc A hA0, hcalc B hB0, hcalc C hC0, C] using hconcC
  -- convert concavity into convexity of `x ↦ -x^p`
  simpa [cfcR, cfc_neg, smul_neg, neg_add, add_assoc, add_left_comm, add_comm] using neg_le_neg hconcC'

private lemma sq_mul_div_add (x t : ℝ) (hxt : x + t ≠ 0) :
    (x * x) / (x + t) = x - t + (t * t) / (x + t) := by
  field_simp [hxt]
  ring

private lemma convexOn_cfcR_one_div_add_t (t : ℝ) (htpos : 0 < t) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
  have hs : Convex ℝ (Set.Ici (0 : 𝓐)) := convex_Ici (𝕜 := ℝ) (0 : 𝓐)
  refine ⟨hs, ?_⟩
  intro A hA B hB a b ha hb hab
  have ha1 : a = 1 - b := by linarith [hab]
  have hb1 : b ≤ 1 := by linarith [ha, hab]
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hB0 : 0 ≤ B := by simpa [Set.Ici] using hB
  have hspec (X : 𝓐) (hX0 : 0 ≤ X) : spectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := spectrum_nonneg_of_nonneg hX0 hx
    simpa [Set.Ici] using hx0
  have hOp := one_div_add_t_operatorConvexOn_Ici (𝓐 := 𝓐) t htpos
  dsimp [OperatorConvexOn] at hOp
  simpa [one_div, ha1] using
    hOp (A := A) (B := B) (t := b) (IsSelfAdjoint.of_nonneg hA0) (IsSelfAdjoint.of_nonneg hB0) hb hb1 (hspec A hA0) (hspec B hB0)

omit [Nontrivial (𝓐)] in
private lemma G_eqOn_rpowIntegrand₀₁_mul {q : NNReal} (hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (htpos : 0 < t) :
    (Set.Ici (0 : 𝓐)).EqOn
      (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X)
      (fun X : 𝓐 ↦ (t ^ ((q : ℝ) - 1)) •
        (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X)) := by
  intro X hX
  have hX0 : 0 ≤ X := by simpa [Set.Ici] using hX
  have hX_sa : IsSelfAdjoint X := IsSelfAdjoint.of_nonneg hX0
  have hqs : quasispectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := quasispectrum_nonneg_of_nonneg X hX0 x hx
    simpa [Set.Ici] using hx0
  have hf_int : ContinuousOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (quasispectrum ℝ X) :=
    (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real htpos).mono hqs
  have hf :
      ContinuousOn (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) (quasispectrum ℝ X) :=
    continuousOn_id.mul hf_int
  have hcfcₙ :
      cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X =
        cfcR
          (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X := by
    simpa using
      (cfcₙ_eq_cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) (a := X)
        (hf := hf) (hf0 := by simp))
  have hEq :
      (spectrum ℝ X).EqOn (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x)
        (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) * (x - t + (t ^ (2 : ℕ)) / (x + t))) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := spectrum_nonneg_of_nonneg hX0 hx
    have ht0 : (0 : ℝ) ≤ t := le_of_lt htpos
    have hxt : x + t ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos hx0 htpos)
    have hdiv : (x * x) / (x + t) = x - t + (t * t) / (x + t) := sq_mul_div_add x t hxt
    have hrepr0 :
        x * Real.rpowIntegrand₀₁ (q : ℝ) t x = (t ^ ((q : ℝ) - 1)) * ((x * x) / (x + t)) := by
      rw [Real.rpowIntegrand₀₁_eq_pow_div hq_real ht0 hx0]
      rw [mul_div_assoc']
      have hnum : x * (t ^ ((q : ℝ) - 1) * x) = t ^ ((q : ℝ) - 1) * (x * x) := by ring
      rw [hnum, mul_div_assoc]
      simp [add_comm]
    simp [hrepr0, hdiv, pow_two, mul_comm]
  have hcfc_congr :
      cfcR
          (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X
        =
        cfcR
          (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) * (x - t + (t ^ (2 : ℕ)) / (x + t))) X :=
    cfc_congr hEq
  have hne : ∀ x ∈ spectrum ℝ X, x + t ≠ 0 := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := spectrum_nonneg_of_nonneg hX0 hx
    exact ne_of_gt (add_pos_of_nonneg_of_pos hx0 htpos)
  have hcont_one_div : ContinuousOn (fun x : ℝ ↦ 1 / (x + t)) (spectrum ℝ X) := by
    have hden : ContinuousOn (fun x : ℝ ↦ x + t) (spectrum ℝ X) :=
      continuousOn_id.add continuousOn_const
    exact continuousOn_const.div hden hne
  have hcont_inner :
      ContinuousOn (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) (spectrum ℝ X) := by
    have hden : ContinuousOn (fun x : ℝ ↦ x + t) (spectrum ℝ X) :=
      continuousOn_id.add continuousOn_const
    have hdiv : ContinuousOn (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) (spectrum ℝ X) :=
      continuousOn_const.div hden hne
    have hsub : ContinuousOn (fun x : ℝ ↦ x - t) (spectrum ℝ X) :=
      continuousOn_id.sub continuousOn_const
    exact hsub.add hdiv
  have hcfc_scale :
      cfcR
          (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) * (x - t + (t ^ (2 : ℕ)) / (x + t))) X
        =
        (t ^ ((q : ℝ) - 1)) • cfcR
          (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) X := by
    simpa using
      (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := (t ^ ((q : ℝ) - 1)))
        (f := fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) (a := X)
        (hf := hcont_inner))
  have hcfc_inner :
      cfcR
          (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) X
        =
        X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X := by
    have hconst :
        cfcR (fun _ : ℝ ↦ t) X =
          algebraMap ℝ (𝓐) t := by
      simpa using (cfc_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t) (a := X) hX_sa)
    have hid :
        cfcR (fun x : ℝ ↦ x) X = X := by
      simpa using (cfc_id' (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := X) (ha := hX_sa))
    have hpow :
        cfcR
            (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) X
          =
          (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X := by
      have :
          cfcR
              (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) X
            =
            cfcR
              (fun x : ℝ ↦ (t ^ (2 : ℕ)) * (1 / (x + t))) X := by
        refine cfc_congr ?_
        intro x hx
        simp [div_eq_mul_inv, mul_comm]
      rw [this]
      simpa [cfcR] using
        (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (r := (t ^ (2 : ℕ))) (f := fun x : ℝ ↦ 1 / (x + t)) (a := X) (hf := hcont_one_div))
    calc
      cfcR
          (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) X
          =
          cfcR (fun x : ℝ ↦ x - t) X
            + cfcR (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) X := by
            simpa using
              (cfc_add (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
                (f := fun x : ℝ ↦ x - t) (g := fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) (a := X))
      _ =
          (cfcR (fun x : ℝ ↦ x) X
            - cfcR (fun _ : ℝ ↦ t) X)
            + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X := by
            simpa [hpow] using
              (congrArg (fun z => z + cfcR
                (fun x : ℝ ↦ (t ^ (2 : ℕ)) / (x + t)) X)
                (cfc_sub (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
                  (f := fun x : ℝ ↦ x) (g := fun _ : ℝ ↦ t) (a := X)))
      _ = X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X := by
          simp [hid, hconst, sub_eq_add_neg, add_comm]
  -- finish
  calc
    cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X
        =
        cfcR
          (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X := hcfcₙ
    _ =
        cfcR
          (fun x : ℝ ↦ (t ^ ((q : ℝ) - 1)) * (x - t + (t ^ (2 : ℕ)) / (x + t))) X := hcfc_congr
    _ =
        (t ^ ((q : ℝ) - 1)) • cfcR
          (fun x : ℝ ↦ x - t + (t ^ (2 : ℕ)) / (x + t)) X := hcfc_scale
    _ = (t ^ ((q : ℝ) - 1)) •
        (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
        simp [hcfc_inner, smul_add, smul_smul, mul_comm]

private lemma convexOn_G_rpowIntegrand₀₁_mul {q : NNReal} (hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (htpos : 0 < t) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐))
      (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X) := by
  -- use `EqOn` to replace the integrand by a structured convex expression
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hr_nonneg : 0 ≤ r :=
    Real.rpow_nonneg (le_of_lt htpos) _
  have hs : Convex ℝ (Set.Ici (0 : 𝓐)) := convex_Ici (𝕜 := ℝ) (0 : 𝓐)
  have h_aff : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ X - algebraMap ℝ (𝓐) t) := by
    have hid : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ X) := by
      exact convexOn_id (𝕜 := ℝ) (s := Set.Ici (0 : 𝓐)) hs
    have hconst : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun _ : 𝓐 ↦ -algebraMap ℝ (𝓐) t) :=
      convexOn_const (-algebraMap ℝ (𝓐) t) hs
    simp_all [sub_eq_add_neg]
    exact hid.add hconst
  have h_one_div : ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ cfcR (fun x : ℝ ↦ 1 / (x + t)) X) :=
    convexOn_cfcR_one_div_add_t  t htpos
  have h_inner : ConvexOn ℝ (Set.Ici (0 : 𝓐))
      (fun X : 𝓐 ↦ X - algebraMap ℝ 𝓐 t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) := by
    have hterm :
        ConvexOn ℝ (Set.Ici (0 : 𝓐))
          (fun X : 𝓐 ↦ (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X) :=
      (h_one_div.smul (sq_nonneg t))
    exact h_aff.add hterm
  have h_rhs :
      ConvexOn ℝ (Set.Ici (0 : 𝓐))
        (fun X : 𝓐 ↦ r •
          (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X)) :=
    h_inner.smul hr_nonneg
  -- transfer convexity back to the `cfcₙ` expression
  refine h_rhs.congr ?_
  intro X hX
  have : (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X) X
      =
      (fun X : 𝓐 ↦ r •
        (X - algebraMap ℝ (𝓐) t + (t ^ (2 : ℕ)) • cfcR (fun x : ℝ ↦ 1 / (x + t)) X)) X := by
    simpa [r] using G_eqOn_rpowIntegrand₀₁_mul  hq_real t htpos hX
  simpa using this.symm

omit [Nontrivial (𝓐)] in
private lemma ae_cfcₙ_mul_id_rpowIntegrand₀₁_restrict_Ioi {q : NNReal} (hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    (μ : MeasureTheory.Measure ℝ) (A : 𝓐) (hA0 : 0 ≤ A) :
    ∀ᵐ t ∂(μ.restrict (Set.Ioi (0 : ℝ))),
      cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) A =
        A * cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have hqs : quasispectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := quasispectrum_nonneg_of_nonneg A hA0 x hx
    simpa [Set.Ici] using hx0
  have hg : ContinuousOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (quasispectrum ℝ A) :=
    (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real ht).mono hqs
  have hG_mul :
      cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) A
        =
        cfcₙ (fun x : ℝ ↦ x) A * cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A := by
    simpa using
      (cfcₙ_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := fun x : ℝ ↦ x) (g := Real.rpowIntegrand₀₁ (q : ℝ) t) (a := A)
        (hf := continuousOn_id) (hf0 := by simp) (hg := hg) (hg0 := by simp))
  have hA_id : cfcₙ (fun x : ℝ ↦ x) A = A := by
    simpa using (cfcₙ_id' (R := ℝ) (a := A) (ha := IsSelfAdjoint.of_nonneg hA0))
  simp [hA_id, hG_mul]

private lemma convexOn_nnrpow_Ioo_one_add {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ ((1 : NNReal) + q)) := by
  -- real exponent in `(0,1)`
  have hq_real : (q : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · exact (NNReal.coe_pos).2 hq.1
    · exact (NNReal.coe_lt_coe).2 hq.2
  -- integral representation for `a ↦ a ^ q`
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ (A := 𝓐) hq
  let ν : MeasureTheory.Measure ℝ := μ.restrict (Set.Ioi (0 : ℝ))
  let F0 : ℝ → 𝓐 → 𝓐 := fun t A => cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) A
  let G : ℝ → 𝓐 → 𝓐 := fun t A =>
    cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) A
  have hF0_int : ∀ A ∈ Set.Ici (0 : 𝓐), MeasureTheory.Integrable (fun t => F0 t A) ν := by
    intro A hA
    simpa [F0, ν, MeasureTheory.IntegrableOn] using (hμ A hA).1
  have hG_int : ∀ A ∈ Set.Ici (0 : 𝓐), MeasureTheory.Integrable (fun t => G t A) ν := by
    intro A hA
    have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
    have hAF : MeasureTheory.Integrable (fun t => A * F0 t A) ν := by
      -- left multiplication by a constant is a continuous linear map
      have hF : MeasureTheory.Integrable (fun t => F0 t A) ν := hF0_int A hA
      simpa [ContinuousLinearMap.mul_apply'] using
        (ContinuousLinearMap.mul ℝ (𝓐) A).integrable_comp hF
    have hG_mul_ae : ∀ᵐ t ∂ν, G t A = A * F0 t A := by
      simpa [ν, G, F0] using
        ae_cfcₙ_mul_id_rpowIntegrand₀₁_restrict_Ioi  (q := q) hq_real μ A hA0
    exact hAF.congr (hG_mul_ae.mono fun _ ht => ht.symm)
  have hG_conv :
      ∀ᵐ t ∂ν, ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 => G t A) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hconv :
        ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun X : 𝓐 ↦ cfcₙ (fun x : ℝ ↦ x * Real.rpowIntegrand₀₁ (q : ℝ) t x) X) :=
      convexOn_G_rpowIntegrand₀₁_mul  hq_real t ht
    simpa [G] using hconv
  have hconv_int :
      ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ ∫ t, G t A ∂ν) :=
    MeasureTheory.integral_convexOn_of_integrand_ae
      (μ := ν) (s := Set.Ici (0 : 𝓐)) (f := fun t A => G t A)
      (convex_Ici (𝕜 := ℝ) (0 : 𝓐)) hG_conv hG_int
  -- identify the integral with `A ^ (1 + q)` on `Ici 0`
  refine hconv_int.congr ?_
  intro A hA
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hq0 : (0 : NNReal) < q := hq.1
  have hpow :
      A ^ ((1 : NNReal) + q) = A * (A ^ q) := by
    have h1 : A ^ ((1 : NNReal) + q) = A ^ (1 : NNReal) * A ^ q := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (CFC.nnrpow_add (A := 𝓐) (a := A) (x := (1 : NNReal)) (y := q) zero_lt_one hq0)
    simpa [CFC.nnrpow_one (A := 𝓐) A hA0] using h1
  have hEq_q : A ^ q = ∫ t, F0 t A ∂ν := by
    simpa [F0, ν] using (hμ A hA).2
  have hEq_mul :
      A * (∫ t, F0 t A ∂ν) = ∫ t, A * F0 t A ∂ν := by
    have h :
        (∫ t, (ContinuousLinearMap.mul ℝ (𝓐) A) (F0 t A) ∂ν)
          =
          (ContinuousLinearMap.mul ℝ (𝓐) A) (∫ t, F0 t A ∂ν) :=
      (ContinuousLinearMap.mul ℝ (𝓐) A).integral_comp_comm (μ := ν) (φ_int := hF0_int A hA)
    exact h.symm
  have hEq :
      A ^ ((1 : NNReal) + q) = ∫ t, G t A ∂ν := by
    calc
      A ^ ((1 : NNReal) + q) = A * (A ^ q) := hpow
      _ = A * (∫ t, F0 t A ∂ν) := by simp [hEq_q]
      _ = ∫ t, A * F0 t A ∂ν := hEq_mul
      _ = ∫ t, G t A ∂ν := by
        have hG_mul_ae : ∀ᵐ t ∂ν, A * F0 t A = G t A := by
          have h' : ∀ᵐ t ∂ν, G t A = A * F0 t A := by
            simpa [ν, G, F0] using
              ae_cfcₙ_mul_id_rpowIntegrand₀₁_restrict_Ioi  (q := q) hq_real μ A hA0
          exact h'.mono (fun _ ht => ht.symm)
        simpa using (MeasureTheory.integral_congr_ae hG_mul_ae)
  simp [hEq]

private lemma convexOn_rpow_Ioo_one_two {p : ℝ} (hp : p ∈ Set.Ioo (1 : ℝ) 2) :
    ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ p) := by
  -- reduce to the `ℝ≥0` exponent case with `p = 1 + q`, `q ∈ (0,1)`
  let q : NNReal := ⟨p - 1, sub_nonneg.mpr (le_of_lt hp.1)⟩
  have hq0 : (0 : NNReal) < q := by
    have : (0 : ℝ) < (q : ℝ) := by
      exact_mod_cast sub_pos.mpr hp.1
    exact (NNReal.coe_pos).1 this
  have hq1 : q < (1 : NNReal) := by
    have : (q : ℝ) < (1 : ℝ) := by
      have : p - 1 < (1 : ℝ) := by linarith [hp.2]
      exact this
    exact (NNReal.coe_lt_coe).1 (by simpa using this)
  have hq : q ∈ Set.Ioo (0 : NNReal) 1 := ⟨hq0, hq1⟩
  have hconv :
      ConvexOn ℝ (Set.Ici (0 : 𝓐)) (fun A : 𝓐 ↦ A ^ ((1 : NNReal) + q)) :=
    convexOn_nnrpow_Ioo_one_add  hq
  refine hconv.congr ?_
  intro A hA
  have hA0 : 0 ≤ A := by simpa [Set.Ici] using hA
  have hq0' : (0 : NNReal) < (1 : NNReal) + q :=
    add_pos_of_pos_of_nonneg zero_lt_one (le_of_lt hq0)
  -- `A ^ (1 + q) = A ^ p`
  have hEq :
      A ^ ((1 : NNReal) + q) = A ^ (((1 : NNReal) + q : NNReal) : ℝ) := by
    simpa using (CFC.nnrpow_eq_rpow (A := 𝓐) (a := A) (x := (1 : NNReal) + q) hq0')
  -- simplify the real exponent `(1 + q : ℝ)` into `p`
  have hreal : (((1 : NNReal) + q : NNReal) : ℝ) = p := by
    have : (1 : ℝ) + (p - 1) = p := by ring
    norm_cast
  simp [hEq, hreal]

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma cfcR_mul_self (T : 𝓐) (hT : IsSelfAdjoint T) :
    cfcR (fun x : ℝ ↦ x * x) T = T * T := by
  dsimp [cfcR]
  calc
    cfcR (fun x : ℝ ↦ x * x) T =
        cfcR (fun x : ℝ ↦ x) T * cfcR (fun x : ℝ ↦ x) T := by
      simpa using
        (cfc_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
          (f := fun x : ℝ ↦ x) (g := fun x : ℝ ↦ x) (a := T))
    _ = T * T := by
      simp [cfc_id' (R := ℝ) (a := T) (ha := hT)]

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma sub_mul_sub (A B : 𝓐) :
    (A - B) * (A - B) = A * A - A * B - B * A + B * B := by
  calc
    (A - B) * (A - B) = (A * A - B * A) - (A * B - B * B) := by
      simp [mul_sub, sub_mul]
    _ = A * A - A * B - B * A + B * B := by
      abel

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma smul_sub_mul_sub (α : ℝ) (A B : 𝓐) :
    α • (A * A - A * B - B * A + B * B) =
      α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B) := by
  rw [smul_add, smul_sub, smul_sub]

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma square_convexity_diff_rhs (A B : 𝓐) (u : ℝ) :
    (u * (1 - u)) • ((A - B) * (A - B)) =
      (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
        + (u * (1 - u)) • (B * B) := by
  let α : ℝ := u * (1 - u)
  have hsmul : α • ((A - B) * (A - B)) = α • (A * A - A * B - B * A + B * B) := by
    rw [sub_mul_sub  A B]
  have hα :
      α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B)
        =
        (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
          + (u * (1 - u)) • (B * B) := by
    simp [α]
  calc
    (u * (1 - u)) • ((A - B) * (A - B)) = α • ((A - B) * (A - B)) := by simp [α]
    _ = α • (A * A - A * B - B * A + B * B) := hsmul
    _ = α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B) :=
      smul_sub_mul_sub  (α := α) A B
    _ = (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
          + (u * (1 - u)) • (B * B) := by
      simp [hα]

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma square_convexity_diff_hL (A B : 𝓐) (u : ℝ) :
    (1 - u) • (A * A) + u • (B * B) -
        (((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
          + (u * (1 - u)) • (B * A) + (u * u) • (B * B)) =
      (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
        + (u * (1 - u)) • (B * B) := by
  let α : ℝ := u * (1 - u)
  have hα1 : (1 - u) - (1 - u) * (1 - u) = α := by
    simp [α]
    ring
  have hα2 : u - u * u = α := by
    simp [α]
    ring
  have hα3 : (1 - u) * u = α := by
    simp [α]
    ring
  have hAA : (1 - u) • (A * A) - ((1 - u) * (1 - u)) • (A * A) = α • (A * A) := by
    have : (1 - u) • (A * A) - ((1 - u) * (1 - u)) • (A * A) =
        ((1 - u) - (1 - u) * (1 - u)) • (A * A) := by
      simpa using (sub_smul (1 - u) ((1 - u) * (1 - u)) (A * A)).symm
    simp [this, hα1]
  have hBB : u • (B * B) - (u * u) • (B * B) = α • (B * B) := by
    have : u • (B * B) - (u * u) • (B * B) = (u - u * u) • (B * B) := by
      simpa using (sub_smul u (u * u) (B * B)).symm
    simp [this, hα2]
  have hAB : ((1 - u) * u) • (A * B) = α • (A * B) := by simp [hα3]
  have hBA : (u * (1 - u)) • (B * A) = α • (B * A) := by rfl
  have hL :
      (1 - u) • (A * A) + u • (B * B) -
          (((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
            + (u * (1 - u)) • (B * A) + (u * u) • (B * B)) =
        α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B) := by
    have hL0 :
        (1 - u) • (A * A) + u • (B * B) -
            (((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
              + (u * (1 - u)) • (B * A) + (u * u) • (B * B)) =
          ((1 - u) • (A * A) - ((1 - u) * (1 - u)) • (A * A)
              + (u • (B * B) - (u * u) • (B * B)))
            - ((1 - u) * u) • (A * B) - (u * (1 - u)) • (B * A) := by
      abel
    have hL1 :
        ((1 - u) • (A * A) - ((1 - u) * (1 - u)) • (A * A)
              + (u • (B * B) - (u * u) • (B * B)))
            - ((1 - u) * u) • (A * B) - (u * (1 - u)) • (B * A)
          = α • (A * A) - α • (A * B) - α • (B * A) + α • (B * B) := by
      simp_rw [hAA, hBB, hAB, hBA]
      abel
    simpa [hL0] using hL1
  simpa [α] using hL

-- This lemma is purely algebraic, so we drop analytical/finite-dimensional assumptions here.
omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma square_convexity_diff_hCC_sum (A B : 𝓐) (u : ℝ) :
    ((1 - u) • A) * ((1 - u) • A)
      + ((1 - u) • A) * (u • B)
      + (u • B) * ((1 - u) • A)
      + (u • B) * (u • B) =
      ((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
        + (u * (1 - u)) • (B * A) + (u * u) • (B * B) := by
  have hAA' :
      ((1 - u) • A) * ((1 - u) • A) = ((1 - u) * (1 - u)) • (A * A) := by
    calc
      ((1 - u) • A) * ((1 - u) • A) = (1 - u) • (A * ((1 - u) • A)) := by
        exact Algebra.smul_mul_assoc (R := ℝ) (A := 𝓐) (1 - u) A ((1 - u) • A)
      _ = (1 - u) • ((1 - u) • (A * A)) := by
        rw [Algebra.mul_smul_comm]
      _ = ((1 - u) * (1 - u)) • (A * A) := by
        simp [smul_smul]
  have hAB' :
      ((1 - u) • A) * (u • B) = ((1 - u) * u) • (A * B) := by
    calc
      ((1 - u) • A) * (u • B) = (1 - u) • (A * (u • B)) := by
        exact Algebra.smul_mul_assoc (R := ℝ) (A := 𝓐) (1 - u) A (u • B)
      _ = (1 - u) • (u • (A * B)) := by
        rw [Algebra.mul_smul_comm]
      _ = ((1 - u) * u) • (A * B) := by
        simp [smul_smul]
  have hBA' :
      (u • B) * ((1 - u) • A) = (u * (1 - u)) • (B * A) := by
    calc
      (u • B) * ((1 - u) • A) = u • (B * ((1 - u) • A)) := by
        exact Algebra.smul_mul_assoc (R := ℝ) (A := 𝓐) u B ((1 - u) • A)
      _ = u • ((1 - u) • (B * A)) := by
        simp [Algebra.mul_smul_comm]
      _ = (u * (1 - u)) • (B * A) := by
        simpa using (smul_smul u (1 - u) (B * A))
  have hBB' :
      (u • B) * (u • B) = (u * u) • (B * B) := by
    calc
      (u • B) * (u • B) = u • (B * (u • B)) := by
        exact Algebra.smul_mul_assoc (R := ℝ) (A := 𝓐) u B (u • B)
      _ = u • (u • (B * B)) := by
        simp [Algebra.mul_smul_comm]
      _ = (u * u) • (B * B) := by
        simp [smul_smul]
  rw [hAA', hAB', hBA', hBB']

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
private lemma square_convexity_diff_hCC (A B : 𝓐) (u : ℝ) :
    ((1 - u) • A + u • B) * ((1 - u) • A + u • B) =
      ((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
        + (u * (1 - u)) • (B * A) + (u * u) • (B * B) := by
  have hexpand :
      ((1 - u) • A + u • B) * ((1 - u) • A + u • B) =
        ((1 - u) • A) * ((1 - u) • A)
          + ((1 - u) • A) * (u • B)
          + (u • B) * ((1 - u) • A)
          + (u • B) * (u • B) := by
    set X : 𝓐 := (1 - u) • A
    set Y : 𝓐 := u • B
    have hXY : (1 - u) • A + u • B = X + Y := by simp [X, Y]
    calc
      ((1 - u) • A + u • B) * ((1 - u) • A + u • B) = (X + Y) * (X + Y) := by
        simp [hXY]
      _ = X * (X + Y) + Y * (X + Y) := by
        simp [add_mul]
      _ = (X * X + X * Y) + (Y * X + Y * Y) := by
        simp [mul_add, add_assoc]
      _ = X * X + X * Y + Y * X + Y * Y := by
        abel
      _ = ((1 - u) • A) * ((1 - u) • A)
            + ((1 - u) • A) * (u • B)
            + (u • B) * ((1 - u) • A)
            + (u • B) * (u • B) := by
        simp [X, Y]
  exact hexpand.trans (square_convexity_diff_hCC_sum  A B u)

omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] [Nontrivial (𝓐)] in
private lemma square_convexity_diff (A B : 𝓐) (u : ℝ) :
    (1 - u) • (A * A) + u • (B * B)
        - ((1 - u) • A + u • B) * ((1 - u) • A + u • B)
      =
      (u * (1 - u)) • ((A - B) * (A - B)) := by
  rw [square_convexity_diff_hCC  A B u]
  have hL' :
      (1 - u) • (A * A) + u • (B * B) -
          (((1 - u) * (1 - u)) • (A * A) + ((1 - u) * u) • (A * B)
            + (u * (1 - u)) • (B * A) + (u * u) • (B * B)) =
        (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
          + (u * (1 - u)) • (B * B) :=
    square_convexity_diff_hL  A B u
  have hR :
      (u * (1 - u)) • ((A - B) * (A - B)) =
        (u * (1 - u)) • (A * A) - (u * (1 - u)) • (A * B) - (u * (1 - u)) • (B * A)
          + (u * (1 - u)) • (B * B) :=
    square_convexity_diff_rhs  A B u
  exact hL'.trans hR.symm

omit [Nontrivial (𝓐)] in
private lemma operatorConvexOn_pow_two_Ici :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x ^ (2 : ℝ)) := by
  dsimp [OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  have hA0 : 0 ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := As hx
    simpa [Set.Ici] using this
  have hB0 : 0 ≤ B := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := Bs hx
    simpa [Set.Ici] using this
  have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
  set C : 𝓐 := (1 - u) • A + u • B
  have hC0 : 0 ≤ C :=
    add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
  have hsq : 0 ≤ (A - B) * (A - B) := by
    have h1 : (0 : 𝓐) ≤ (1 : 𝓐) := (zero_le_one : (0 : 𝓐) ≤ 1)
    have hT : IsSelfAdjoint (A - B) := by simpa using hA.sub hB
    simpa [mul_assoc] using conjugate_isPositive  (X := (1 : 𝓐)) (T := (A - B)) h1 hT
  have hub : 0 ≤ u * (1 - u) := mul_nonneg hu0 hu0'
  have hdiff :
      (1 - u) • (A * A) + u • (B * B) - C * C
        = (u * (1 - u)) • ((A - B) * (A - B)) := by
    simpa [C] using (square_convexity_diff  A B u)
  have hnonneg : 0 ≤ (1 - u) • (A * A) + u • (B * B) - C * C := by
    have hscale : 0 ≤ (u * (1 - u)) • ((A - B) * (A - B)) := smul_nonneg hub hsq
    simpa [hdiff] using hscale
  have hmain : C * C ≤ (1 - u) • (A * A) + u • (B * B) :=
    (sub_nonneg).1 hnonneg
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - u)).smul hA |>.add ((IsSelfAdjoint.all u).smul hB)
  -- rewrite the goal via `cfcR (x ↦ x^2) T = T*T`
  have hfun : (fun x : ℝ ↦ x ^ (2 : ℝ)) = (fun x : ℝ ↦ x * x) := by
    funext x
    simp [pow_two]
  rw [hfun]
  simpa [C, cfcR_mul_self  C hC, cfcR_mul_self  A hA, cfcR_mul_self  B hB] using hmain

theorem power_Icc_one_two_operatorConvexOn_Ici : ∀ p ∈ Set.Icc (1 : ℝ) 2,
  OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  by_cases hp1 : p = 1
  · subst hp1
    dsimp [OperatorConvexOn]
    intro A B u hA hB hu0 hu1 As Bs
    have hC : IsSelfAdjoint ((1 - u) • A + u • B) := by
      simpa using (IsSelfAdjoint.all (1 - u)).smul hA |>.add ((IsSelfAdjoint.all u).smul hB)
    have hfun : (fun x : ℝ ↦ x ^ (1 : ℝ)) = (fun x : ℝ ↦ x) := by
      funext x
      simp
    rw [hfun]
    simp [cfcR, cfc_id' (R := ℝ) (a := ((1 - u) • A + u • B)) (ha := hC),
      cfc_id' (R := ℝ) (a := A) (ha := hA), cfc_id' (R := ℝ) (a := B) (ha := hB)]
  by_cases hp2 : p = 2
  · subst hp2
    simpa using operatorConvexOn_pow_two_Ici
  have hp12 : p ∈ Set.Ioo (1 : ℝ) 2 := by
    refine ⟨?_, ?_⟩
    · have : 1 ≤ p := hp.1
      exact lt_of_le_of_ne this (Ne.symm hp1)
    · have : p ≤ 2 := hp.2
      exact lt_of_le_of_ne this hp2
  dsimp [OperatorConvexOn]
  intro A B u hA hB hu0 hu1 As Bs
  have hA0 : 0 ≤ A := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := As hx
    simpa [Set.Ici] using this
  have hB0 : 0 ≤ B := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 ?_
    intro x hx
    have : x ∈ Set.Ici (0 : ℝ) := Bs hx
    simpa [Set.Ici] using this
  have hu0' : 0 ≤ (1 - u) := sub_nonneg.mpr hu1
  set C : 𝓐 := (1 - u) • A + u • B
  have hC0 : 0 ≤ C :=
    add_nonneg (smul_nonneg hu0' hA0) (smul_nonneg hu0 hB0)
  have hC_mem : C ∈ Set.Ici (0 : 𝓐) := by
    simpa [C, Set.Ici] using hC0
  have hA_mem : A ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hA0
  have hB_mem : B ∈ Set.Ici (0 : 𝓐) := by simpa [Set.Ici] using hB0
  have hab : (1 - u) + u = (1 : ℝ) := by ring
  have hconvC : (C ^ p) ≤ (1 - u) • (A ^ p) + u • (B ^ p) := by
    simpa [C] using
      (convexOn_rpow_Ioo_one_two  hp12).2 hA_mem hB_mem hu0' hu0 hab
  have hcalc (T : 𝓐) (hT0 : 0 ≤ T) :
      cfcR (fun x : ℝ ↦ x ^ p) T = T ^ p := by
    simpa [cfcR] using
      (CFC.rpow_eq_cfc_real (A := 𝓐) (a := T) (y := p) (ha := hT0)).symm
  -- rewrite the convexity inequality through `cfcR`
  simpa [hcalc A hA0, hcalc B hB0, hcalc C hC0, C] using hconvC

-- Paper statement (Löwner–Heinz): for `p ∈ [-1,0]`, `f(t) = -t^p` is operator monotone and concave
-- on `(0,∞)`.
omit [Nontrivial 𝓐] in
theorem power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  dsimp [OperatorMonotoneOn]
  intro A B hA0 hB0 hBA hspA hspB
  let q : ℝ := -p
  have hq : q ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [q]
      exact neg_nonneg.mpr hp.2
    · dsimp [q]
      simpa using (neg_le_neg hp.1)
  have hBAq : cfcR  (fun x : ℝ ↦ x ^ q) B ≤ cfcR  (fun x : ℝ ↦ x ^ q) A := by
    have hspA' : spectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspA hx
      simpa [Set.Ici] using (le_of_lt hx0)
    have hspB' : spectrum ℝ B ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspB hx
      simpa [Set.Ici] using (le_of_lt hx0)
    exact (power_Icc_zero_one_operatorMonotoneOn_Ici  q hq (A := A) (B := B) hA0 hB0 hBA hspA' hspB')
  let Aq : 𝓐 := cfcR  (fun x : ℝ ↦ x ^ q) A
  let Bq : 𝓐 := cfcR  (fun x : ℝ ↦ x ^ q) B
  have hAq0 : 0 ≤ Aq := by
    dsimp [Aq, cfcR]
    refine cfc_nonneg ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspA hx
    exact le_of_lt (Real.rpow_pos_of_pos hx0 _)
  have hBq0 : 0 ≤ Bq := by
    dsimp [Bq, cfcR]
    refine cfc_nonneg ?_
    intro x hx
    have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspB hx
    exact le_of_lt (Real.rpow_pos_of_pos hx0 _)
  have hspAq : spectrum ℝ Aq ⊆ Set.Ioi (0 : ℝ) := by
    have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA0
    have hcontA : ContinuousOn (fun x : ℝ ↦ x ^ q) (spectrum ℝ A) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspA hx
      exact (Real.continuousAt_rpow_const x q (Or.inl (ne_of_gt hx0))).continuousWithinAt
    have hspec :
        spectrum ℝ Aq = (fun x : ℝ ↦ x ^ q) '' spectrum ℝ A := by
      dsimp [Aq, cfcR]
      simpa using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x ^ q)
          (a := A) (ha := hA_sa) (hf := hcontA))
    intro y hy
    have hy' : y ∈ (fun x : ℝ ↦ x ^ q) '' spectrum ℝ A := by simpa [hspec] using hy
    rcases hy' with ⟨x, hx, rfl⟩
    have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspA hx
    simpa [Set.Ioi] using (Real.rpow_pos_of_pos hx0 q)
  have hspBq : spectrum ℝ Bq ⊆ Set.Ioi (0 : ℝ) := by
    have hB_sa : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg hB0
    have hcontB : ContinuousOn (fun x : ℝ ↦ x ^ q) (spectrum ℝ B) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspB hx
      exact (Real.continuousAt_rpow_const x q (Or.inl (ne_of_gt hx0))).continuousWithinAt
    have hspec :
        spectrum ℝ Bq = (fun x : ℝ ↦ x ^ q) '' spectrum ℝ B := by
      dsimp [Bq, cfcR]
      simpa using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x ^ q)
          (a := B) (ha := hB_sa) (hf := hcontB))
    intro y hy
    have hy' : y ∈ (fun x : ℝ ↦ x ^ q) '' spectrum ℝ B := by simpa [hspec] using hy
    rcases hy' with ⟨x, hx, rfl⟩
    have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspB hx
    simpa [Set.Ioi] using (Real.rpow_pos_of_pos hx0 q)
  have h_inv :
      cfcR  (fun x : ℝ ↦ 1 / x) Aq ≤ cfcR  (fun x : ℝ ↦ 1 / x) Bq := by
    have hanti := one_div_operatorAntitoneOn_Ioi (𝓐 := 𝓐)
    dsimp [OperatorAntitoneOn] at hanti
    have hBAq' : Bq ≤ Aq := by simpa [Aq, Bq] using hBAq
    exact hanti (A := Aq) (B := Bq) hAq0 hBq0 hBAq' hspAq hspBq
  have hcompA :
      cfcR  (fun x : ℝ ↦ 1 / x) Aq = cfcR  (fun x : ℝ ↦ x ^ p) A := by
    have hA_sa : IsSelfAdjoint A := IsSelfAdjoint.of_nonneg hA0
    have hcontA : ContinuousOn (fun x : ℝ ↦ x ^ q) (spectrum ℝ A) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspA hx
      exact (Real.continuousAt_rpow_const x q (Or.inl (ne_of_gt hx0))).continuousWithinAt
    have hs : (fun x : ℝ ↦ x ^ q) '' spectrum ℝ A ⊆ ({0}ᶜ : Set ℝ) := by
      rintro y ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspA hx
      simpa [Set.mem_compl_singleton_iff] using (ne_of_gt (Real.rpow_pos_of_pos hx0 q))
    have hg : ContinuousOn (fun y : ℝ ↦ 1 / y) ((fun x : ℝ ↦ x ^ q) '' spectrum ℝ A) := by
      have hg' : ContinuousOn (fun y : ℝ ↦ y⁻¹) ({0}ᶜ : Set ℝ) := continuousOn_inv₀
      simpa [one_div] using (hg'.mono hs)
    have hcomp :
        cfcR  (fun y : ℝ ↦ 1 / y) (cfcR  (fun x : ℝ ↦ x ^ q) A) =
          cfcR  (fun x : ℝ ↦ 1 / (x ^ q)) A := by
      dsimp [cfcR]
      simpa [Function.comp] using
        (cfc_comp' (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (g := fun y : ℝ ↦ 1 / y)
          (f := fun x : ℝ ↦ x ^ q) (a := A) (hg := hg) (hf := hcontA) (ha := hA_sa)).symm
    have hL :
        cfcR  (fun x : ℝ ↦ 1 / x) Aq =
          cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ q) A) := by
      simp [Aq, one_div]
    rw [hL]
    have hcomp' :
        cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ q) A) =
          cfcR  (fun x : ℝ ↦ (x ^ q)⁻¹) A := by
      simpa [one_div] using hcomp
    rw [hcomp']
    dsimp [cfcR]
    apply cfc_congr
    intro x hx
    have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspA hx
    calc
      (x ^ q)⁻¹ = x ^ (-q) := by simpa using (Real.rpow_neg (le_of_lt hx0) q).symm
      _ = x ^ p := by simp [q]
  have hcompB :
      cfcR  (fun x : ℝ ↦ 1 / x) Bq = cfcR  (fun x : ℝ ↦ x ^ p) B := by
    have hB_sa : IsSelfAdjoint B := IsSelfAdjoint.of_nonneg hB0
    have hcontB : ContinuousOn (fun x : ℝ ↦ x ^ q) (spectrum ℝ B) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspB hx
      exact (Real.continuousAt_rpow_const x q (Or.inl (ne_of_gt hx0))).continuousWithinAt
    have hs : (fun x : ℝ ↦ x ^ q) '' spectrum ℝ B ⊆ ({0}ᶜ : Set ℝ) := by
      rintro y ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspB hx
      simpa [Set.mem_compl_singleton_iff] using (ne_of_gt (Real.rpow_pos_of_pos hx0 q))
    have hg : ContinuousOn (fun y : ℝ ↦ 1 / y) ((fun x : ℝ ↦ x ^ q) '' spectrum ℝ B) := by
      have hg' : ContinuousOn (fun y : ℝ ↦ y⁻¹) ({0}ᶜ : Set ℝ) := continuousOn_inv₀
      simpa [one_div] using (hg'.mono hs)
    have hcomp :
        cfcR  (fun y : ℝ ↦ 1 / y) (cfcR  (fun x : ℝ ↦ x ^ q) B) =
          cfcR  (fun x : ℝ ↦ 1 / (x ^ q)) B := by
      dsimp [cfcR]
      simpa [Function.comp] using
        (cfc_comp' (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (g := fun y : ℝ ↦ 1 / y)
          (f := fun x : ℝ ↦ x ^ q) (a := B) (hg := hg) (hf := hcontB) (ha := hB_sa)).symm
    have hL :
        cfcR  (fun x : ℝ ↦ 1 / x) Bq =
          cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ q) B) := by
      simp [Bq, one_div]
    rw [hL]
    have hcomp' :
        cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ q) B) =
          cfcR  (fun x : ℝ ↦ (x ^ q)⁻¹) B := by
      simpa [one_div] using hcomp
    rw [hcomp']
    dsimp [cfcR]
    apply cfc_congr
    intro x hx
    have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using hspB hx
    calc
      (x ^ q)⁻¹ = x ^ (-q) := by simpa using (Real.rpow_neg (le_of_lt hx0) q).symm
      _ = x ^ p := by simp [q]
  have hanti : cfcR  (fun x : ℝ ↦ x ^ p) A ≤ cfcR  (fun x : ℝ ↦ x ^ p) B := by
    calc
      cfcR  (fun x : ℝ ↦ x ^ p) A =
          cfcR  (fun x : ℝ ↦ 1 / x) Aq := by
            simpa using hcompA.symm
      _ ≤ cfcR  (fun x : ℝ ↦ 1 / x) Bq := h_inv
      _ = cfcR  (fun x : ℝ ↦ x ^ p) B := by
            simpa using hcompB
  have hneg : -cfcR  (fun x : ℝ ↦ x ^ p) B ≤ -cfcR  (fun x : ℝ ↦ x ^ p) A :=
    neg_le_neg hanti
  have hnegA :
      cfcR  (fun x : ℝ ↦ -(x ^ p)) A = -cfcR  (fun x : ℝ ↦ x ^ p) A := by
    simp [cfcR, cfc_neg]
  have hnegB :
      cfcR  (fun x : ℝ ↦ -(x ^ p)) B = -cfcR  (fun x : ℝ ↦ x ^ p) B := by
    simp [cfcR, cfc_neg]
  simpa [hnegA, hnegB] using hneg

theorem power_Icc_neg_one_zero_neg_operatorConcaveOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  -- `OperatorConcaveOn` for `-(x^p)` is `OperatorConvexOn` for `x^p`.
  dsimp [OperatorConcaveOn, OperatorConvexOn]
  intro A B t hA hB ht0 ht1 As Bs
  -- main parameters
  let r : ℝ := -p
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [r]
      exact neg_nonneg.mpr hp.2
    · dsimp [r]
      simpa using (neg_le_neg hp.1)
  -- convex combination
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have Cs : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using
      spectrum_convexCombo_Ioi  (A := A) (B := B) (t := t) hA hB ht0 ht1 As Bs
  -- r-th powers
  let Ar : 𝓐 := cfcR  (fun x : ℝ ↦ x ^ r) A
  let Br : 𝓐 := cfcR  (fun x : ℝ ↦ x ^ r) B
  let Cr : 𝓐 := cfcR  (fun x : ℝ ↦ x ^ r) C
  let Dr : 𝓐 := (1 - t) • Ar + t • Br
  have h_conc : Dr ≤ Cr := by
    have As0 : spectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using As hx
      simpa [Set.Ici] using (le_of_lt hx0)
    have Bs0 : spectrum ℝ B ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Bs hx
      simpa [Set.Ici] using (le_of_lt hx0)
    have hconc := power_Icc_zero_one_operatorConcaveOn_Ici (𝓐 := 𝓐) r hr
    dsimp [OperatorConcaveOn, OperatorConvexOn] at hconc
    have h1 :
        (-Cr) ≤ (1 - t) • (-Ar) + t • (-Br) := by
      simpa [C, Ar, Br, Cr, cfcR, cfc_neg] using
        hconc (A := A) (B := B) (t := t) hA hB ht0 ht1 As0 Bs0
    have h2 : (1 - t) • (-Ar) + t • (-Br) = -Dr := by
      simp [Dr, smul_neg, add_comm]
    have h3 : (-Cr) ≤ (-Dr) := by
      calc
        (-Cr) ≤ (1 - t) • (-Ar) + t • (-Br) := h1
        _ = (-Dr) := h2
    simpa [Dr, add_comm, add_left_comm, add_assoc] using (neg_le_neg_iff).1 h3
  -- invert and use antitonicity/convexity of `x ↦ 1/x`
  have h_inv1 :
      cfcR  (fun x : ℝ ↦ 1 / x) Cr ≤ cfcR  (fun x : ℝ ↦ 1 / x) Dr := by
    have hCr0 : 0 ≤ Cr := by
      dsimp [Cr, cfcR]
      refine cfc_nonneg ?_
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Cs hx
      exact le_of_lt (Real.rpow_pos_of_pos hx0 r)
    have hAr0 : 0 ≤ Ar := by
      dsimp [Ar, cfcR]
      refine cfc_nonneg ?_
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using As hx
      exact le_of_lt (Real.rpow_pos_of_pos hx0 r)
    have hBr0 : 0 ≤ Br := by
      dsimp [Br, cfcR]
      refine cfc_nonneg ?_
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Bs hx
      exact le_of_lt (Real.rpow_pos_of_pos hx0 r)
    have hDr0 : 0 ≤ Dr := by
      dsimp [Dr]
      exact add_nonneg (smul_nonneg (sub_nonneg.mpr ht1) hAr0) (smul_nonneg ht0 hBr0)
    have hCr_sa : IsSelfAdjoint Cr := by
      dsimp [Cr, cfcR]
      exact cfc_predicate _ _
    have hAr_sa : IsSelfAdjoint Ar := by
      dsimp [Ar, cfcR]
      exact cfc_predicate _ _
    have hBr_sa : IsSelfAdjoint Br := by
      dsimp [Br, cfcR]
      exact cfc_predicate _ _
    have hspCr : spectrum ℝ Cr ⊆ Set.Ioi (0 : ℝ) := by
      have hcontC : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ C) := by
        intro x hx
        have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Cs hx
        exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx0))).continuousWithinAt
      have hspec :
          spectrum ℝ Cr = (fun x : ℝ ↦ x ^ r) '' spectrum ℝ C := by
        dsimp [Cr, cfcR]
        simpa using
          (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x ^ r)
            (a := C) (ha := hC) (hf := hcontC))
      intro y hy
      have hy' : y ∈ (fun x : ℝ ↦ x ^ r) '' spectrum ℝ C := by simpa [hspec] using hy
      rcases hy' with ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Cs hx
      simpa [Set.Ioi] using (Real.rpow_pos_of_pos hx0 r)
    have hspAr : spectrum ℝ Ar ⊆ Set.Ioi (0 : ℝ) := by
      have hcontA : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ A) := by
        intro x hx
        have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using As hx
        exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx0))).continuousWithinAt
      have hspec :
          spectrum ℝ Ar = (fun x : ℝ ↦ x ^ r) '' spectrum ℝ A := by
        dsimp [Ar, cfcR]
        simpa using
          (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x ^ r)
            (a := A) (ha := hA) (hf := hcontA))
      intro y hy
      have hy' : y ∈ (fun x : ℝ ↦ x ^ r) '' spectrum ℝ A := by simpa [hspec] using hy
      rcases hy' with ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using As hx
      simpa [Set.Ioi] using (Real.rpow_pos_of_pos hx0 r)
    have hspBr : spectrum ℝ Br ⊆ Set.Ioi (0 : ℝ) := by
      have hcontB : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ B) := by
        intro x hx
        have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Bs hx
        exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx0))).continuousWithinAt
      have hspec :
          spectrum ℝ Br = (fun x : ℝ ↦ x ^ r) '' spectrum ℝ B := by
        dsimp [Br, cfcR]
        simpa using
          (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x ^ r)
            (a := B) (ha := hB) (hf := hcontB))
      intro y hy
      have hy' : y ∈ (fun x : ℝ ↦ x ^ r) '' spectrum ℝ B := by simpa [hspec] using hy
      rcases hy' with ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Bs hx
      simpa [Set.Ioi] using (Real.rpow_pos_of_pos hx0 r)
    have hspDr : spectrum ℝ Dr ⊆ Set.Ioi (0 : ℝ) := by
      simpa [Dr] using
        spectrum_convexCombo_Ioi  (A := Ar) (B := Br) (t := t) hAr_sa hBr_sa ht0 ht1 hspAr hspBr
    have hanti := one_div_operatorAntitoneOn_Ioi (𝓐 := 𝓐)
    dsimp [OperatorAntitoneOn] at hanti
    exact hanti (A := Cr) (B := Dr) hCr0 hDr0 h_conc hspCr hspDr
  have h_inv2 :
      cfcR  (fun x : ℝ ↦ 1 / x) Dr
        ≤ (1 - t) • cfcR  (fun x : ℝ ↦ 1 / x) Ar
          + t • cfcR  (fun x : ℝ ↦ 1 / x) Br := by
    have hAr_sa : IsSelfAdjoint Ar := by
      dsimp [Ar, cfcR]
      exact cfc_predicate _ _
    have hBr_sa : IsSelfAdjoint Br := by
      dsimp [Br, cfcR]
      exact cfc_predicate _ _
    have hspAr : spectrum ℝ Ar ⊆ Set.Ioi (0 : ℝ) := by
      have hcontA : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ A) := by
        intro x hx
        have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using As hx
        exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx0))).continuousWithinAt
      have hspec :
          spectrum ℝ Ar = (fun x : ℝ ↦ x ^ r) '' spectrum ℝ A := by
        dsimp [Ar, cfcR]
        simpa using
          (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x ^ r)
            (a := A) (ha := hA) (hf := hcontA))
      intro y hy
      have hy' : y ∈ (fun x : ℝ ↦ x ^ r) '' spectrum ℝ A := by simpa [hspec] using hy
      rcases hy' with ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using As hx
      simpa [Set.Ioi] using (Real.rpow_pos_of_pos hx0 r)
    have hspBr : spectrum ℝ Br ⊆ Set.Ioi (0 : ℝ) := by
      have hcontB : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ B) := by
        intro x hx
        have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Bs hx
        exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx0))).continuousWithinAt
      have hspec :
          spectrum ℝ Br = (fun x : ℝ ↦ x ^ r) '' spectrum ℝ B := by
        dsimp [Br, cfcR]
        simpa using
          (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x ^ r)
            (a := B) (ha := hB) (hf := hcontB))
      intro y hy
      have hy' : y ∈ (fun x : ℝ ↦ x ^ r) '' spectrum ℝ B := by simpa [hspec] using hy
      rcases hy' with ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Bs hx
      simpa [Set.Ioi] using (Real.rpow_pos_of_pos hx0 r)
    have hconv := one_div_operatorConvexOn_Ioi (𝓐 := 𝓐)
    dsimp [OperatorConvexOn] at hconv
    simpa [Dr] using
      hconv (A := Ar) (B := Br) (t := t) hAr_sa hBr_sa ht0 ht1 hspAr hspBr
  -- rewrite `1/(X^r)` into `X^p`
  have hcompA :
      cfcR  (fun x : ℝ ↦ 1 / x) Ar = cfcR  (fun x : ℝ ↦ x ^ p) A := by
    have hcontA : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ A) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using As hx
      exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx0))).continuousWithinAt
    have hs : (fun x : ℝ ↦ x ^ r) '' spectrum ℝ A ⊆ ({0}ᶜ : Set ℝ) := by
      rintro y ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using As hx
      simpa [Set.mem_compl_singleton_iff] using (ne_of_gt (Real.rpow_pos_of_pos hx0 r))
    have hg : ContinuousOn (fun y : ℝ ↦ 1 / y) ((fun x : ℝ ↦ x ^ r) '' spectrum ℝ A) := by
      have hg' : ContinuousOn (fun y : ℝ ↦ y⁻¹) ({0}ᶜ : Set ℝ) := continuousOn_inv₀
      simpa [one_div] using (hg'.mono hs)
    have hcomp :
        cfcR  (fun y : ℝ ↦ 1 / y) (cfcR  (fun x : ℝ ↦ x ^ r) A) =
          cfcR  (fun x : ℝ ↦ 1 / (x ^ r)) A := by
      dsimp [cfcR]
      simpa [Function.comp] using
        (cfc_comp' (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (g := fun y : ℝ ↦ 1 / y)
          (f := fun x : ℝ ↦ x ^ r) (a := A) (hg := hg) (hf := hcontA) (ha := hA)).symm
    have hL :
        cfcR  (fun x : ℝ ↦ 1 / x) Ar =
          cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ r) A) := by
      simp [Ar, one_div]
    rw [hL]
    have hcomp' :
        cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ r) A) =
          cfcR  (fun x : ℝ ↦ (x ^ r)⁻¹) A := by
      simpa [one_div] using hcomp
    rw [hcomp']
    dsimp [cfcR]
    apply cfc_congr
    intro x hx
    have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using As hx
    calc
      (x ^ r)⁻¹ = x ^ (-r) := by
        simpa using (Real.rpow_neg (le_of_lt hx0) r).symm
      _ = x ^ p := by simp [r]
  have hcompB :
      cfcR  (fun x : ℝ ↦ 1 / x) Br = cfcR  (fun x : ℝ ↦ x ^ p) B := by
    have hcontB : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ B) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Bs hx
      exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx0))).continuousWithinAt
    have hs : (fun x : ℝ ↦ x ^ r) '' spectrum ℝ B ⊆ ({0}ᶜ : Set ℝ) := by
      rintro y ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Bs hx
      simpa [Set.mem_compl_singleton_iff] using (ne_of_gt (Real.rpow_pos_of_pos hx0 r))
    have hg : ContinuousOn (fun y : ℝ ↦ 1 / y) ((fun x : ℝ ↦ x ^ r) '' spectrum ℝ B) := by
      have hg' : ContinuousOn (fun y : ℝ ↦ y⁻¹) ({0}ᶜ : Set ℝ) := continuousOn_inv₀
      simpa [one_div] using (hg'.mono hs)
    have hcomp :
        cfcR  (fun y : ℝ ↦ 1 / y) (cfcR  (fun x : ℝ ↦ x ^ r) B) =
          cfcR  (fun x : ℝ ↦ 1 / (x ^ r)) B := by
      dsimp [cfcR]
      simpa [Function.comp] using
        (cfc_comp' (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (g := fun y : ℝ ↦ 1 / y)
          (f := fun x : ℝ ↦ x ^ r) (a := B) (hg := hg) (hf := hcontB) (ha := hB)).symm
    have hL :
        cfcR  (fun x : ℝ ↦ 1 / x) Br =
          cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ r) B) := by
      simp [Br, one_div]
    rw [hL]
    have hcomp' :
        cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ r) B) =
          cfcR  (fun x : ℝ ↦ (x ^ r)⁻¹) B := by
      simpa [one_div] using hcomp
    rw [hcomp']
    dsimp [cfcR]
    apply cfc_congr
    intro x hx
    have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Bs hx
    calc
      (x ^ r)⁻¹ = x ^ (-r) := by
        simpa using (Real.rpow_neg (le_of_lt hx0) r).symm
      _ = x ^ p := by simp [r]
  have hcompC :
      cfcR  (fun x : ℝ ↦ 1 / x) Cr = cfcR  (fun x : ℝ ↦ x ^ p) C := by
    have hcontC : ContinuousOn (fun x : ℝ ↦ x ^ r) (spectrum ℝ C) := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Cs hx
      exact (Real.continuousAt_rpow_const x r (Or.inl (ne_of_gt hx0))).continuousWithinAt
    have hs : (fun x : ℝ ↦ x ^ r) '' spectrum ℝ C ⊆ ({0}ᶜ : Set ℝ) := by
      rintro y ⟨x, hx, rfl⟩
      have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Cs hx
      simpa [Set.mem_compl_singleton_iff] using (ne_of_gt (Real.rpow_pos_of_pos hx0 r))
    have hg : ContinuousOn (fun y : ℝ ↦ 1 / y) ((fun x : ℝ ↦ x ^ r) '' spectrum ℝ C) := by
      have hg' : ContinuousOn (fun y : ℝ ↦ y⁻¹) ({0}ᶜ : Set ℝ) := continuousOn_inv₀
      simpa [one_div] using (hg'.mono hs)
    have hcomp :
        cfcR  (fun y : ℝ ↦ 1 / y) (cfcR  (fun x : ℝ ↦ x ^ r) C) =
          cfcR  (fun x : ℝ ↦ 1 / (x ^ r)) C := by
      dsimp [cfcR]
      simpa [Function.comp] using
        (cfc_comp' (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (g := fun y : ℝ ↦ 1 / y)
          (f := fun x : ℝ ↦ x ^ r) (a := C) (hg := hg) (hf := hcontC) (ha := hC)).symm
    have hL :
        cfcR  (fun x : ℝ ↦ 1 / x) Cr =
          cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ r) C) := by
      simp [Cr, one_div]
    rw [hL]
    have hcomp' :
        cfcR  (fun y : ℝ ↦ y⁻¹) (cfcR  (fun x : ℝ ↦ x ^ r) C) =
          cfcR  (fun x : ℝ ↦ (x ^ r)⁻¹) C := by
      simpa [one_div] using hcomp
    rw [hcomp']
    dsimp [cfcR]
    apply cfc_congr
    intro x hx
    have hx0 : (0 : ℝ) < x := by simpa [Set.Ioi] using Cs hx
    calc
      (x ^ r)⁻¹ = x ^ (-r) := by
        simpa using (Real.rpow_neg (le_of_lt hx0) r).symm
      _ = x ^ p := by simp [r]
  -- finish
  have hmain :
      cfcR  (fun x : ℝ ↦ x ^ p) C
        ≤ (1 - t) • cfcR  (fun x : ℝ ↦ x ^ p) A
          + t • cfcR  (fun x : ℝ ↦ x ^ p) B := by
    have hchain :
        cfcR  (fun x : ℝ ↦ 1 / x) Cr
          ≤ (1 - t) • cfcR  (fun x : ℝ ↦ 1 / x) Ar
            + t • cfcR  (fun x : ℝ ↦ 1 / x) Br :=
      le_trans h_inv1 h_inv2
    -- convert via `hcomp*`
    have hcompA' : cfcR  (fun x : ℝ ↦ x⁻¹) Ar = cfcR  (fun x : ℝ ↦ x ^ p) A := by
      simpa [one_div] using hcompA
    have hcompB' : cfcR  (fun x : ℝ ↦ x⁻¹) Br = cfcR  (fun x : ℝ ↦ x ^ p) B := by
      simpa [one_div] using hcompB
    have hcompC' : cfcR  (fun x : ℝ ↦ x⁻¹) Cr = cfcR  (fun x : ℝ ↦ x ^ p) C := by
      simpa [one_div] using hcompC
    have hchain' :
        cfcR  (fun x : ℝ ↦ x⁻¹) Cr
          ≤ (1 - t) • cfcR  (fun x : ℝ ↦ x⁻¹) Ar
            + t • cfcR  (fun x : ℝ ↦ x⁻¹) Br := by
      simpa [one_div] using hchain
    simpa [hcompA', hcompB', hcompC'] using hchain'
  simpa [C] using hmain

end Spectrum

namespace Spectral

variable {𝓐 : Type u} [CStarAlgebra 𝓐]
variable [Nontrivial 𝓐]

section

-- Confine `spectralOrder` to this wrapper namespace.
-- We use local instances so the order change does not leak outside.
noncomputable local instance : PartialOrder 𝓐 := CStarAlgebra.spectralOrder 𝓐
noncomputable local instance : StarOrderedRing 𝓐 := CStarAlgebra.spectralOrderedRing 𝓐
noncomputable local instance : NonnegSpectrumClass ℝ 𝓐 := inferInstance

-- Wrappers: expose the main theorems under spectral order without duplicating proofs.

omit [Nontrivial 𝓐] in
theorem one_div_operatorAntitoneOn_Ioi :
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  simpa using (LownerHeinzCore.one_div_operatorAntitoneOn_Ioi (𝓐 := 𝓐))

theorem one_div_operatorConvexOn_Ioi :
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  simpa using (LownerHeinzCore.one_div_operatorConvexOn_Ioi (𝓐 := 𝓐))

omit [Nontrivial 𝓐] in
theorem one_div_add_t_operatorAntitoneOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorAntitoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  simpa using (LownerHeinzCore.one_div_add_t_operatorAntitoneOn_Ici (𝓐 := 𝓐) t ht)

theorem one_div_add_t_operatorConvexOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  intro t ht
  simpa using (LownerHeinzCore.one_div_add_t_operatorConvexOn_Ici (𝓐 := 𝓐) t ht)

omit [Nontrivial 𝓐] in
theorem ratio_add_t_operatorMonotoneOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  intro t ht
  simpa using (LownerHeinzCore.ratio_add_t_operatorMonotoneOn_Ici (𝓐 := 𝓐) t ht)

theorem ratio_add_t_operatorConcaveOn_Ici : ∀ (t : ℝ), 0 < t →
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ x / (x + t)) := by
  intro t ht
  simpa using (LownerHeinzCore.ratio_add_t_operatorConcaveOn_Ici (𝓐 := 𝓐) t ht)

omit [Nontrivial 𝓐] in
theorem power_Icc_zero_one_operatorMonotoneOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using (LownerHeinzCore.power_Icc_zero_one_operatorMonotoneOn_Ici (𝓐 := 𝓐) p hp)

theorem power_Icc_zero_one_operatorConcaveOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using (LownerHeinzCore.power_Icc_zero_one_operatorConcaveOn_Ici (𝓐 := 𝓐) p hp)

theorem power_Icc_one_two_operatorConvexOn_Ici : ∀ p ∈ Set.Icc (1 : ℝ) 2,
    OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp
  simpa using (LownerHeinzCore.power_Icc_one_two_operatorConvexOn_Ici (𝓐 := 𝓐) p hp)

omit [Nontrivial 𝓐] in
theorem power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorMonotoneOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  simpa using (LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorMonotoneOn_Ioi (𝓐 := 𝓐) p hp)

theorem power_Icc_neg_one_zero_neg_operatorConcaveOn_Ioi : ∀ p ∈ Set.Icc (-1 : ℝ) 0,
    OperatorConcaveOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x ↦ -(x ^ p)) := by
  intro p hp
  simpa using (LownerHeinzCore.power_Icc_neg_one_zero_neg_operatorConcaveOn_Ioi (𝓐 := 𝓐) p hp)

end

end Spectral

end LownerHeinzCore
