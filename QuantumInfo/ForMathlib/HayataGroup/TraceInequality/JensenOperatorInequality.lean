/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.JensenOperatorInequalityIImpIV

@[expose] public section

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

section Theorem252

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

set_option synthInstance.maxHeartbeats 400000 in
-- IsStarNormal CFC is only a theorem in Mathlib; CStarAlgebra chain through WithLp is deep.
noncomputable local instance : ContinuousFunctionalCalculus ℂ (L ℋ × L ℋ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
set_option synthInstance.maxHeartbeats 400000 in
-- IsSelfAdjoint CFC for the product type, derived from IsStarNormal above.
noncomputable local instance : ContinuousFunctionalCalculus ℝ (L ℋ × L ℋ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
set_option synthInstance.maxHeartbeats 400000 in
-- CStarAlgebra → NonnegSpectrumClass chain through WithLp is too deep for default heartbeats.
noncomputable local instance : NonnegSpectrumClass ℝ (L (HSum ℋ)) := inferInstance
set_option synthInstance.maxHeartbeats 400000 in
-- Module ℝ for L (HSum ℋ) requires deep WithLp / CStarAlgebra chain.
noncomputable local instance : Module ℝ (L (HSum ℋ)) := inferInstance

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
/--
Uniform version of Condition (iv), with the Hilbert space arbitrary in the same universe.
This is the theorem-level uniform counterpart to the operator-level `...All` predicates.
-/
def CondIVAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    CondIV (ℋ := K) f

omit [CompleteSpace ℋ] in
/-- `L (HSum ℋ)` is nontrivial once `L ℋ` is. -/
private theorem nontrivial_hsumL_wrap [Nontrivial ℋ] : Nontrivial (L (HSum ℋ)) :=
  inferInstance

private lemma blockDiagonal_selfAdjoint_wrap {A B : L ℋ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (blockDiagonal (ℋ := ℋ) A B) := by
  rw [isSelfAdjoint_iff, blockDiagonal_star, hA.star_eq, hB.star_eq]

omit [CompleteSpace ℋ] in
private lemma blockDiagonal_eq_blockOp_wrap (A B : L ℋ) :
    blockDiagonal (ℋ := ℋ) A B = blockOp (ℋ := ℋ) A 0 0 B := by
  ext z i
  fin_cases i <;> simp [blockDiagonal, blockOp]

-- Multiplication of generic block operators is elaboration-heavy even in the wrapper.
set_option maxHeartbeats 400000 in
-- The generic `blockOp` product expands into large block normal forms.
omit [CompleteSpace ℋ] in
private lemma blockOp_mul_wrap (A00 A01 A10 A11 B00 B01 B10 B11 : L ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 * blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ)
        (A00 * B00 + A01 * B10)
        (A00 * B01 + A01 * B11)
        (A10 * B00 + A11 * B10)
        (A10 * B01 + A11 * B11) := by
  refine blockOp_ext (ℋ := ℋ) ?_ ?_ <;> intro z <;>
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]

private lemma cfcR_blockDiagonal_wrap (f : ℝ → ℝ)
    (A B : L ℋ) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hcont : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B)) :
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B) =
      blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
  let φ : (L ℋ × L ℋ) →⋆ₐ[ℝ] L (HSum ℋ) := blockDiagonalHom (ℋ := ℋ)
  have hφ : Continuous φ := by
    change Continuous (fun p : L ℋ × L ℋ =>
      hsumIncl ℋ 0 ∘L p.1 ∘L hsumProj ℋ 0 + hsumIncl ℋ 1 ∘L p.2 ∘L hsumProj ℋ 1)
    fun_prop
  have hpair : IsSelfAdjoint (A, B) := Prod.ext hA.star_eq hB.star_eq
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := (A, B))
    (hf := by simpa [Prod.spectrum_eq] using hcont)
    (hφ := hφ) (ha := hpair) (hφa := hpair.map φ)
  have hprod :
      cfc (R := ℝ) (A := L ℋ × L ℋ) (p := IsSelfAdjoint) f (A, B) =
        (cfcR (ℋ := ℋ) f A, cfcR (ℋ := ℋ) f B) := by
    simpa [cfcR] using cfc_map_prod (S := ℝ) f A B hcont hpair hA hB
  simpa [cfcR, φ] using hmap.symm.trans (congrArg φ hprod)

private lemma continuousOn_union_of_subset_Ici_wrap {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ))) {s t : Set ℝ}
    (hs : s ⊆ Set.Ici (0 : ℝ)) (ht : t ⊆ Set.Ici (0 : ℝ)) :
    ContinuousOn f (s ∪ t) :=
  hcont.mono (Set.union_subset hs ht)

private lemma spectrum_Ici_of_nonneg_wrap {A : L ℋ} (hA0 : (0 : L ℋ) ≤ A) :
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) :=
  (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := .of_nonneg hA0)).1 hA0

variable [Nontrivial ℋ]

omit [CompleteSpace ℋ] in
private lemma spectrum_zero_subset_Ici_wrap :
    spectrum ℝ (0 : L ℋ) ⊆ Set.Ici (0 : ℝ) := by
  simp [spectrum.zero_eq]

omit [Nontrivial ℋ] in
private lemma blockDiagonal_le_left_wrap {A0 A1 B0 B1 : L ℋ}
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

-- Theorem 2.5.2 `(iv) → (v)`.
set_option maxHeartbeats 3000000 in
-- Block-matrix normalization in this wrapper needs a larger local heartbeat budget.
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
  letI : Nontrivial (L (HSum ℋ)) := nontrivial_hsumL_wrap (ℋ := ℋ)
  have hAtilde_sa : IsSelfAdjoint Atilde := blockDiagonal_selfAdjoint_wrap (ℋ := ℋ) hA hB
  have hAtilde0 : (0 : L (HSum ℋ)) ≤ Atilde := blockDiagonal_nonneg (ℋ := ℋ) hA0 hB0
  have hAtilde_spec : spectrum ℝ Atilde ⊆ Set.Ici (0 : ℝ) :=
    spectrum_Ici_of_nonneg_wrap (ℋ := HSum ℋ) hAtilde0
  have hstar : star Xtilde = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 := by simp [Xtilde]
  have hXb : Xtilde = blockOp (ℋ := ℋ) X 0 Y 0 := rfl
  have hAb : Atilde = blockOp (ℋ := ℋ) A 0 0 B := blockDiagonal_eq_blockOp_wrap (ℋ := ℋ) A B
  have hXtilde_star_mul :
      star Xtilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 := by
    rw [hstar, hXb, blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    simp
  have hXtilde_star_mul_le : star Xtilde * Xtilde ≤ (1 : L (HSum ℋ)) := by
    have hsub :
        (1 : L (HSum ℋ)) - blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 =
          blockDiagonal (ℋ := ℋ) (1 - (star X * X + star Y * Y)) (1 : L ℋ) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_ <;> intro z <;> simp [sub_eq_add_neg]
    rw [hXtilde_star_mul, ← sub_nonneg, hsub]
    exact blockDiagonal_nonneg (ℋ := ℋ) (sub_nonneg.mpr hXY) zero_le_one
  have hXtilde_norm : ‖Xtilde‖ ≤ 1 := by
    have hnormSq' : ‖Xtilde‖ * ‖Xtilde‖ ≤ 1 := by
      simpa [CStarRing.norm_star_mul_self] using
        (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg Xtilde)).2
          hXtilde_star_mul_le
    nlinarith [norm_nonneg Xtilde]
  have hcore := @hiv (HSum ℋ) _ _ _ _ Atilde Xtilde hAtilde_sa hAtilde_spec hXtilde_norm
  have hsum_sa : IsSelfAdjoint (star X * A * X + star Y * B * Y) :=
    (hA.conjugate' X).add (hB.conjugate' Y)
  have hmul_block :
      star Xtilde * Atilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * A * X + star Y * B * Y) 0 := by
    rw [hstar, hAb, hXb, blockOp_mul_wrap, blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    congr 1 <;> simp [mul_assoc]
  have hAtilde_cfc :
      cfcR (ℋ := HSum ℋ) f Atilde =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) :=
    cfcR_blockDiagonal_wrap (ℋ := ℋ) (f := f) A B hA hB (hcont.mono (Set.subset_univ _))
  have hright_block :
      star Xtilde * cfcR (ℋ := HSum ℋ) f Atilde * Xtilde =
        blockDiagonal (star X * cfcR (ℋ := ℋ) f A * X + star Y * cfcR (ℋ := ℋ) f B * Y) 0 := by
    rw [hAtilde_cfc, hstar, hXb, blockDiagonal_eq_blockOp_wrap, blockOp_mul_wrap,
      blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    congr 1 <;> simp [mul_assoc]
  have hleft_block :
      cfcR (ℋ := HSum ℋ) f (star Xtilde * Atilde * Xtilde) =
        blockDiagonal (cfcR f (star X * A * X + star Y * B * Y)) (cfcR f 0) := by
    rw [hmul_block]
    simpa using
      cfcR_blockDiagonal_wrap f (star X * A * X + star Y * B * Y) 0 hsum_sa (by simp)
        (hcont.mono (Set.subset_univ _))
  rw [hleft_block, hright_block] at hcore
  exact blockDiagonal_le_left_wrap (ℋ := ℋ) hcore

/-- Uniform consequence of Theorem 2.5.2: `(i) → (v)` via `(iv)`. -/
theorem theorem_2_5_2_i_all_imp_v {f : ℝ → ℝ} (hf : CondIAll.{u} f) :
    CondV (ℋ := ℋ) f := by
  refine theorem_2_5_2_iv_imp_v (ℋ := ℋ) ?_
    (operatorConvex_continuousOn_univ (ℋ := ℋ) hf.1)
  intro K _ _ _ _
  exact theorem_2_5_2_i_all_imp_iv (ℋ := K) (f := f) hf

-- Uniform localized consequence of Theorem 2.5.2: `(i) → (v)` on `Set.Ici 0`.
set_option maxHeartbeats 3000000 in
-- The localized wrapper repeats the same block-operator normalization as
-- `theorem_2_5_2_iv_imp_v`.
theorem theorem_2_5_2_i_ici_all_imp_v {f : ℝ → ℝ}
    (hf : CondIciAll.{u} f) :
    CondV (ℋ := ℋ) f := by
  have hcontIci := hf.2.1
  intro A B X Y hA hB hAs hBs hXY
  have hA0 : (0 : L ℋ) ≤ A :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 fun _ hx => hAs hx
  have hB0 : (0 : L ℋ) ≤ B :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 fun _ hx => hBs hx
  let Atilde : L (HSum ℋ) := blockDiagonal (ℋ := ℋ) A B
  let Xtilde : L (HSum ℋ) := blockOp (ℋ := ℋ) X 0 Y 0
  letI : Nontrivial (L (HSum ℋ)) := nontrivial_hsumL_wrap (ℋ := ℋ)
  have hAtilde_sa : IsSelfAdjoint Atilde := blockDiagonal_selfAdjoint_wrap (ℋ := ℋ) hA hB
  have hAtilde0 : (0 : L (HSum ℋ)) ≤ Atilde := blockDiagonal_nonneg (ℋ := ℋ) hA0 hB0
  have hAtilde_spec : spectrum ℝ Atilde ⊆ Set.Ici (0 : ℝ) :=
    spectrum_Ici_of_nonneg_wrap (ℋ := HSum ℋ) hAtilde0
  have hstar : star Xtilde = blockOp (ℋ := ℋ) (star X) (star Y) 0 0 := by simp [Xtilde]
  have hXb : Xtilde = blockOp (ℋ := ℋ) X 0 Y 0 := rfl
  have hAb : Atilde = blockOp (ℋ := ℋ) A 0 0 B := blockDiagonal_eq_blockOp_wrap (ℋ := ℋ) A B
  have hXtilde_star_mul :
      star Xtilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 := by
    rw [hstar, hXb, blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    simp
  have hXtilde_star_mul_le : star Xtilde * Xtilde ≤ (1 : L (HSum ℋ)) := by
    have hsub :
        (1 : L (HSum ℋ)) - blockDiagonal (ℋ := ℋ) (star X * X + star Y * Y) 0 =
          blockDiagonal (ℋ := ℋ) (1 - (star X * X + star Y * Y)) (1 : L ℋ) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_ <;> intro z <;> simp [sub_eq_add_neg]
    rw [hXtilde_star_mul, ← sub_nonneg, hsub]
    exact blockDiagonal_nonneg (ℋ := ℋ) (sub_nonneg.mpr hXY) zero_le_one
  have hXtilde_norm : ‖Xtilde‖ ≤ 1 := by
    have hnormSq' : ‖Xtilde‖ * ‖Xtilde‖ ≤ 1 := by
      simpa [CStarRing.norm_star_mul_self] using
        (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg Xtilde)).2
          hXtilde_star_mul_le
    nlinarith [norm_nonneg Xtilde]
  have hcore := theorem_2_5_2_i_ici_all_imp_iv (ℋ := HSum ℋ) (f := f) hf
    (A := Atilde) (X := Xtilde) hAtilde_sa hAtilde_spec hXtilde_norm
  have hsum_nonneg : (0 : L ℋ) ≤ star X * A * X + star Y * B * Y :=
    add_nonneg (star_left_conjugate_nonneg hA0 X) (star_left_conjugate_nonneg hB0 Y)
  have hsum_sa : IsSelfAdjoint (star X * A * X + star Y * B * Y) :=
    IsSelfAdjoint.of_nonneg hsum_nonneg
  have hmul_block :
      star Xtilde * Atilde * Xtilde =
        blockDiagonal (ℋ := ℋ) (star X * A * X + star Y * B * Y) 0 := by
    rw [hstar, hAb, hXb, blockOp_mul_wrap, blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    congr 1 <;> simp [mul_assoc]
  have hAtilde_cfc :
      cfcR (ℋ := HSum ℋ) f Atilde =
        blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) :=
    cfcR_blockDiagonal_wrap (ℋ := ℋ) (f := f) A B hA hB
      (continuousOn_union_of_subset_Ici_wrap (f := f) hcontIci hAs hBs)
  have hright_block :
      star Xtilde * cfcR (ℋ := HSum ℋ) f Atilde * Xtilde =
        blockDiagonal (ℋ := ℋ)
          (star X * cfcR (ℋ := ℋ) f A * X + star Y * cfcR (ℋ := ℋ) f B * Y) 0 := by
    rw [hAtilde_cfc, hstar, hXb, blockDiagonal_eq_blockOp_wrap,
      blockOp_mul_wrap, blockOp_mul_wrap, blockDiagonal_eq_blockOp_wrap]
    congr 1 <;> simp [mul_assoc]
  have hsum_spec : spectrum ℝ (star X * A * X + star Y * B * Y) ⊆ Set.Ici (0 : ℝ) :=
    spectrum_Ici_of_nonneg_wrap (ℋ := ℋ) hsum_nonneg
  have hleft_block :
      cfcR (ℋ := HSum ℋ) f (star Xtilde * Atilde * Xtilde) =
        blockDiagonal (cfcR f (star X * A * X + star Y * B * Y)) (cfcR f 0) := by
    rw [hmul_block]
    simpa using
      cfcR_blockDiagonal_wrap f (star X * A * X + star Y * B * Y) 0 hsum_sa (by simp)
        (continuousOn_union_of_subset_Ici_wrap hcontIci hsum_spec spectrum_zero_subset_Ici_wrap)
  rw [hleft_block, hright_block] at hcore
  exact blockDiagonal_le_left_wrap (ℋ := ℋ) hcore

end Theorem252

end JensenOperatorInequality
