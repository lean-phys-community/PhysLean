/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.BlockDiagonal
public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzTheorem
public import Mathlib.Analysis.CStarAlgebra.Unitary.Span

@[expose] public section

namespace JensenOperatorInequalityScratch

universe u

open LownerHeinzTheorem
open JensenOperatorInequality

section Theorem252

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

set_option synthInstance.maxHeartbeats 400000 in
noncomputable local instance : ContinuousFunctionalCalculus ℂ (L ℋ × L ℋ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
set_option synthInstance.maxHeartbeats 400000 in
noncomputable local instance : ContinuousFunctionalCalculus ℝ (L ℋ × L ℋ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
set_option synthInstance.maxHeartbeats 400000 in
noncomputable local instance : NonnegSpectrumClass ℝ (L (HSum ℋ)) := inferInstance

/-- Local copy of condition (iv) for fast iteration on `(iv) → (v)`. -/
def CondIV (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A X : L ℋ⦄, IsSelfAdjoint A → spectrum ℝ A ⊆ Set.Ici (0 : ℝ) → ‖X‖ ≤ 1 →
    cfcR (ℋ := ℋ) f (star X * A * X) ≤ star X * cfcR (ℋ := ℋ) f A * X

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/--
Uniform version of Condition (iv), with the Hilbert space arbitrary in the same universe.
This scratch copy follows the same `...All` naming convention as the main Jensen file.
-/
def CondIVAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    CondIV (ℋ := K) f

/-- Local copy of condition (v) for fast iteration on `(iv) → (v)`. -/
def CondV (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B X Y : L ℋ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) → spectrum ℝ B ⊆ Set.Ici (0 : ℝ) →
    star X * X + star Y * Y ≤ (1 : L ℋ) →
    cfcR (ℋ := ℋ) f (star X * A * X + star Y * B * Y) ≤
      star X * cfcR (ℋ := ℋ) f A * X + star Y * cfcR (ℋ := ℋ) f B * Y

omit [CompleteSpace ℋ] in
/-- `L (HSum ℋ)` is nontrivial once `L ℋ` is. -/
private theorem nontrivial_hsumL : Nontrivial (L (HSum ℋ)) := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ℋ
  refine ⟨blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0, 0, fun h0 => sub_ne_zero.mpr hxy ?_⟩
  have hz : blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0 (hsumIncl ℋ 0 (x - y)) = 0 := by
    simp [h0]
  simpa [blockDiagonal] using congrArg (fun z : HSum ℋ => hsumProj ℋ 0 z) hz

omit [Nontrivial ℋ] in
private lemma blockDiagonal_selfAdjoint {A B : L ℋ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (blockDiagonal (ℋ := ℋ) A B) := by
  rw [isSelfAdjoint_iff, blockDiagonal_star, hA.star_eq, hB.star_eq]

omit [Nontrivial ℋ] [CompleteSpace ℋ] in
private lemma blockDiagonal_eq_blockOp (A B : L ℋ) :
    blockDiagonal (ℋ := ℋ) A B = blockOp (ℋ := ℋ) A 0 0 B := by
  ext z i
  fin_cases i <;> simp [blockDiagonal, blockOp]

-- Multiplication of generic block operators is elaboration-heavy even in the scratch file.
omit [CompleteSpace ℋ] [Nontrivial ℋ] in
set_option maxHeartbeats 400000 in
-- The generic `blockOp` product expands into large block normal forms.
private lemma blockOp_mul (A00 A01 A10 A11 B00 B01 B10 B11 : L ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 * blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ)
        (A00 * B00 + A01 * B10)
        (A00 * B01 + A01 * B11)
        (A10 * B00 + A11 * B10)
        (A10 * B01 + A11 * B11) := by
  refine blockOp_ext (ℋ := ℋ) ?_ ?_ <;> intro z <;>
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
omit [Nontrivial ℋ] in
private lemma cfcR_blockDiagonal (f : ℝ → ℝ)
    (A B : L ℋ) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hcont : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B)) :
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B) =
      blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
  let φ : (L ℋ × L ℋ) →⋆ₐ[ℝ] L (HSum ℋ) := blockDiagonalHom (ℋ := ℋ)
  have hφ : Continuous φ := by
    change Continuous (fun p : L ℋ × L ℋ =>
      hsumIncl ℋ 0 ∘L p.1 ∘L hsumProj ℋ 0 + hsumIncl ℋ 1 ∘L p.2 ∘L hsumProj ℋ 1)
    fun_prop
  have hpair : IsSelfAdjoint (A, B) := by
    change star (A, B) = (A, B)
    ext <;> simp [hA.star_eq, hB.star_eq]
  have hpair' : IsSelfAdjoint (φ (A, B)) := hpair.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := (A, B))
    (hf := by simpa [Prod.spectrum_eq] using hcont)
    (hφ := hφ) (ha := hpair) (hφa := hpair')
  have hprod :
      cfc (R := ℝ) (A := L ℋ × L ℋ) (p := IsSelfAdjoint) f (A, B) =
        (cfcR (ℋ := ℋ) f A, cfcR (ℋ := ℋ) f B) := by
    simpa [cfcR] using
      (cfc_map_prod (R := ℝ) (S := ℝ)
        (A := L ℋ) (B := L ℋ)
        (pab := IsSelfAdjoint) (pa := IsSelfAdjoint) (pb := IsSelfAdjoint)
        f A B
        (hf := hcont)
        (hab := hpair) (ha := hA) (hb := hB))
  calc
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B)
        = cfc (R := ℝ) (A := L (HSum ℋ)) (p := IsSelfAdjoint) f (φ (A, B)) := by
            simp [cfcR, φ]
    _ = φ (cfc (R := ℝ) (A := L ℋ × L ℋ) (p := IsSelfAdjoint) f (A, B)) := by
            simpa using hmap.symm
    _ = φ (cfcR (ℋ := ℋ) f A, cfcR (ℋ := ℋ) f B) := by
            rw [hprod]
    _ = blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
            simp [φ, blockDiagonalHom]

omit [Nontrivial ℋ] in
private lemma blockDiagonal_le_left {A0 A1 B0 B1 : L ℋ}
    (h : blockDiagonal (ℋ := ℋ) A0 A1 ≤ blockDiagonal (ℋ := ℋ) B0 B1) :
    A0 ≤ B0 := by
  have hnonneg : 0 ≤ blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1) := by
    have hsub :
        blockDiagonal (ℋ := ℋ) B0 B1 - blockDiagonal (ℋ := ℋ) A0 A1 =
          blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_ <;> intro z <;> simp [sub_eq_add_neg]
    exact hsub ▸ sub_nonneg.mpr h
  have hpos :
      (blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1)).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 hnonneg
  have hleftPos : (B0 - A0).IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    simpa [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply] using
      (ContinuousLinearMap.isPositive_iff_complex _).1 hpos (hsumIncl ℋ 0 x)
  exact sub_nonneg.mp ((ContinuousLinearMap.nonneg_iff_isPositive _).2 hleftPos)

-- Scratch theorem for fast feedback while formalizing Theorem 2.5.2 `(iv) → (v)`.
-- This file intentionally avoids importing the heavy `(i) → (iv)` proof.
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3000000 in
-- The block-matrix reduction creates large normalization goals in this scratch file.
theorem theorem_2_5_2_iv_imp_v {f : ℝ → ℝ} (hiv : CondIVAll.{u} f)
    (hcont : ContinuousOn f Set.univ) :
    CondV (ℋ := ℋ) f := by
  intro A B X Y hA hB hAs hBs hXY
  have hA0 : (0 : L ℋ) ≤ A :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 fun _ hx => hAs hx
  have hB0 : (0 : L ℋ) ≤ B :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 fun _ hx => hBs hx
  let Atilde : L (HSum ℋ) := blockDiagonal (ℋ := ℋ) A B
  let Xtilde : L (HSum ℋ) := blockOp (ℋ := ℋ) X 0 Y 0
  letI : Nontrivial (L (HSum ℋ)) := nontrivial_hsumL (ℋ := ℋ)
  have hAtilde_sa : IsSelfAdjoint Atilde := blockDiagonal_selfAdjoint (ℋ := ℋ) hA hB
  have hAtilde0 : (0 : L (HSum ℋ)) ≤ Atilde := blockDiagonal_nonneg (ℋ := ℋ) hA0 hB0
  have hAtilde_spec : spectrum ℝ Atilde ⊆ Set.Ici (0 : ℝ) := by
    exact (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) Atilde (ha := hAtilde_sa)).1 hAtilde0
  have hstar : star Xtilde = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 := by simp [Xtilde]
  have hXb : Xtilde = blockOp (ℋ := ℋ) X 0 Y 0 := rfl
  have hAb : Atilde = blockOp (ℋ := ℋ) A 0 0 B := blockDiagonal_eq_blockOp (ℋ := ℋ) A B
  have hXtilde_star_mul :
      star Xtilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 := by
    rw [hstar, hXb, blockOp_mul, blockDiagonal_eq_blockOp]
    simp
  have hXtilde_star_mul_le : star Xtilde * Xtilde ≤ (1 : L (HSum ℋ)) := by
    have hsub :
        (1 : L (HSum ℋ)) - blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 =
          blockDiagonal (ℋ := ℋ) (1 - (star X * X + star Y * Y)) (1 : L ℋ) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_ <;> intro z <;> simp [sub_eq_add_neg]
    rw [hXtilde_star_mul, ← sub_nonneg, hsub]
    exact blockDiagonal_nonneg (ℋ := ℋ) (sub_nonneg.mpr hXY) zero_le_one
  have hXtilde_star_mul_nonneg : (0 : L (HSum ℋ)) ≤ star Xtilde * Xtilde := by
    simp
  have hXtilde_norm : ‖Xtilde‖ ≤ 1 := by
    have hnormSq' : ‖Xtilde‖ * ‖Xtilde‖ ≤ 1 := by
      simpa [CStarRing.norm_star_mul_self] using
        (CStarAlgebra.norm_le_one_iff_of_nonneg _ hXtilde_star_mul_nonneg).2 hXtilde_star_mul_le
    nlinarith [norm_nonneg Xtilde]
  have hiv_hsum : CondIV (ℋ := HSum ℋ) f := @hiv (HSum ℋ) _ _ _ _
  have hcore := hiv_hsum (A := Atilde) (X := Xtilde) hAtilde_sa hAtilde_spec hXtilde_norm
  have hsum_sa : IsSelfAdjoint (star X * A * X + star Y * B * Y) :=
    (hA.conjugate' X).add (hB.conjugate' Y)
  have hmul_block :
      star Xtilde * Atilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * A * X + star Y * B * Y) 0 := by
    rw [hstar, hAb, hXb, blockOp_mul, blockOp_mul, blockDiagonal_eq_blockOp]
    congr 1 <;> simp [mul_assoc]
  have hAtilde_cfc :
      cfcR (ℋ := HSum ℋ) f Atilde =
        blockDiagonal (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) :=
    cfcR_blockDiagonal (ℋ := ℋ) (f := f) A B hA hB (hcont.mono (Set.subset_univ _))
  have hright_block :
      star Xtilde * cfcR (ℋ := HSum ℋ) f Atilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * cfcR f A * X + star Y * cfcR f B * Y) 0 := by
    rw [hAtilde_cfc, hstar, hXb, blockDiagonal_eq_blockOp, blockOp_mul, blockOp_mul,
      blockDiagonal_eq_blockOp]
    congr 1 <;> simp [mul_assoc]
  have hleft_block :
      cfcR (ℋ := HSum ℋ) f (star Xtilde * Atilde * Xtilde) =
        blockDiagonal (cfcR f (star X * A * X + star Y * B * Y)) (cfcR f 0) := by
    rw [hmul_block]
    simpa using
      cfcR_blockDiagonal (ℋ := ℋ) (f := f) (star X * A * X + star Y * B * Y) 0 hsum_sa (by simp)
        (hcont.mono (Set.subset_univ _))
  rw [hleft_block, hright_block] at hcore
  exact blockDiagonal_le_left (ℋ := ℋ) hcore

end Theorem252

end JensenOperatorInequalityScratch
