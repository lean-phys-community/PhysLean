/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzTheorem

@[expose] public section

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- A two-fold Hilbert sum used for the block-operator proof of Jensen's inequality. -/
abbrev HSum (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  PiLp 2 (fun _ : Fin 2 => ℋ)

noncomputable def hsumEquiv (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] :
    HSum ℋ ≃L[ℂ] (Fin 2 → ℋ) :=
  PiLp.continuousLinearEquiv (p := (2 : ENNReal)) (𝕜 := ℂ) (β := fun _ : Fin 2 => ℋ)

noncomputable def hsumProj (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (i : Fin 2) : HSum ℋ →L[ℂ] ℋ :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℋ) i) ∘L
    (hsumEquiv ℋ).toContinuousLinearMap

noncomputable def hsumIncl (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    (i : Fin 2) : ℋ →L[ℂ] HSum ℋ :=
  (hsumEquiv ℋ).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.single ℂ (fun _ : Fin 2 => ℋ) i)

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_hsumIncl_apply (i j : Fin 2) (x : ℋ) :
    hsumProj ℋ i (hsumIncl ℋ j x) = if i = j then x else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hsumProj, hsumIncl, hsumEquiv]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem inner_hsumIncl_hsumIncl (i j : Fin 2) (x y : ℋ) :
    inner ℂ (hsumIncl ℋ i x) (hsumIncl ℋ j y) = if i = j then inner ℂ x y else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hsumIncl, hsumEquiv, PiLp.inner_apply]

omit [Nontrivial ℋ] in
@[simp] theorem hsumIncl_adjoint (i : Fin 2) :
    (hsumIncl ℋ i).adjoint = hsumProj ℋ i := by
  fin_cases i
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  · ext x
    refine ext_inner_right ℂ fun y => ?_
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]

omit [Nontrivial ℋ] in
@[simp] theorem hsumProj_adjoint (i : Fin 2) :
    (hsumProj ℋ i).adjoint = hsumIncl ℋ i := by
  calc
    (hsumProj ℋ i).adjoint = ((hsumIncl ℋ i).adjoint).adjoint := by
      rw [hsumIncl_adjoint (ℋ := ℋ) i]
    _ = hsumIncl ℋ i := ContinuousLinearMap.adjoint_adjoint _

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumIncl_proj_sum (z : HSum ℋ) :
    hsumIncl ℋ 0 (hsumProj ℋ 0 z) + hsumIncl ℋ 1 (hsumProj ℋ 1 z) = z := by
  ext i
  fin_cases i <;> simp [hsumProj, hsumIncl, hsumEquiv]

/-- The block diagonal operator `diag(A, B)` on the two-fold Hilbert sum. -/
noncomputable def blockDiagonal (A B : L ℋ) : L (HSum ℋ) :=
  hsumIncl ℋ 0 ∘L A ∘L hsumProj ℋ 0 + hsumIncl ℋ 1 ∘L B ∘L hsumProj ℋ 1

/-- A general `2 × 2` block operator on `HSum ℋ`. -/
noncomputable def blockOp (A00 A01 A10 A11 : L ℋ) : L (HSum ℋ) :=
  hsumIncl ℋ 0 ∘L A00 ∘L hsumProj ℋ 0 +
    hsumIncl ℋ 0 ∘L A01 ∘L hsumProj ℋ 1 +
    hsumIncl ℋ 1 ∘L A10 ∘L hsumProj ℋ 0 +
    hsumIncl ℋ 1 ∘L A11 ∘L hsumProj ℋ 1

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockOp_ext {T S : L (HSum ℋ)}
    (h0 : ∀ z : HSum ℋ, hsumProj ℋ 0 (T z) = hsumProj ℋ 0 (S z))
    (h1 : ∀ z : HSum ℋ, hsumProj ℋ 1 (T z) = hsumProj ℋ 1 (S z)) :
    T = S := by
  ext z i
  fin_cases i
  · exact h0 z
  · exact h1 z

omit [Nontrivial ℋ] in
@[simp] theorem blockDiagonal_star (A B : L ℋ) :
    star (blockDiagonal (ℋ := ℋ) A B) = blockDiagonal (ℋ := ℋ) (star A) (star B) := by
  ext z i
  fin_cases i
  · simp [blockDiagonal, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
  · simp [blockDiagonal, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]

noncomputable def blockDiagonalHom : (L ℋ × L ℋ) →⋆ₐ[ℝ] L (HSum ℋ) where
  toFun p := blockDiagonal (ℋ := ℋ) p.1 p.2
  map_one' := by
    ext z
    simp [blockDiagonal]
  map_mul' := by
    intro p q
    ext z i
    fin_cases i <;>
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, ContinuousLinearMap.mul_def]
  map_zero' := by
    ext z i
    fin_cases i <;> simp [blockDiagonal]
  map_add' := by
    intro p q
    ext z i
    fin_cases i <;>
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, add_apply]
  commutes' := by
    intro r
    ext z i
    fin_cases i <;> {
      simp [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, Algebra.algebraMap_eq_smul_one]
    }
  map_star' := by
    intro p
    simp

omit [Nontrivial ℋ] in
@[simp] theorem blockDiagonalHom_apply (p : L ℋ × L ℋ) :
    blockDiagonalHom (ℋ := ℋ) p = blockDiagonal (ℋ := ℋ) p.1 p.2 :=
  rfl

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockDiagonal_zero (A B : L ℋ) (z : HSum ℋ) :
    hsumProj ℋ 0 (blockDiagonal A B z) = A (hsumProj ℋ 0 z) := by
  simp [blockDiagonal]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockDiagonal_one (A B : L ℋ) (z : HSum ℋ) :
    hsumProj ℋ 1 (blockDiagonal A B z) = B (hsumProj ℋ 1 z) := by
  simp [blockDiagonal]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem blockDiagonal_one :
    blockDiagonal (ℋ := ℋ) (1 : L ℋ) (1 : L ℋ) = (1 : L (HSum ℋ)) := by
  ext z i
  fin_cases i <;> simp [blockDiagonal]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
theorem blockDiagonal_nonneg {A B : L ℋ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ blockDiagonal (ℋ := ℋ) A B := by
  have hApos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).mp hA
  have hBpos : B.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive B).mp hB
  refine (ContinuousLinearMap.nonneg_iff_isPositive _).mpr ?_
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro z
  have hAz := (ContinuousLinearMap.isPositive_iff_complex A).mp hApos (hsumProj ℋ 0 z)
  have hBz := (ContinuousLinearMap.isPositive_iff_complex B).mp hBpos (hsumProj ℋ 1 z)
  have hz0 :
      inner ℂ ((hsumIncl ℋ 0) (A (hsumProj ℋ 0 z))) z =
        inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z) := by
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  have hz1 :
      inner ℂ ((hsumIncl ℋ 1) (B (hsumProj ℋ 1 z))) z =
        inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z) := by
    simp [hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply]
  constructor
  · dsimp [blockDiagonal]
    erw [inner_add_left, hz0, hz1]
    calc
      ↑(RCLike.re
          (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z) +
            inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z))) =
          ↑(RCLike.re (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z)) +
            RCLike.re (inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z))) := by
            simp
      _ = inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z) +
          inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z) := by
            have hsumre :
                (↑(RCLike.re (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z)) +
                    RCLike.re (inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z))) : ℂ) =
                  ((RCLike.re (inner ℂ (A (hsumProj ℋ 0 z)) (hsumProj ℋ 0 z)) : ℂ) +
                    (RCLike.re (inner ℂ (B (hsumProj ℋ 1 z)) (hsumProj ℋ 1 z)) : ℂ)) := by
                  simp
            rw [hsumre, hAz.1, hBz.1]
  · dsimp [blockDiagonal]
    erw [inner_add_left, hz0, hz1]
    exact add_nonneg hAz.2 hBz.2

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockOp_zero (A00 A01 A10 A11 : L ℋ) (z : HSum ℋ) :
    hsumProj ℋ 0 (blockOp (ℋ := ℋ) A00 A01 A10 A11 z) =
      A00 (hsumProj ℋ 0 z) + A01 (hsumProj ℋ 1 z) := by
  simp [blockOp]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
@[simp] theorem hsumProj_blockOp_one (A00 A01 A10 A11 : L ℋ) (z : HSum ℋ) :
    hsumProj ℋ 1 (blockOp (ℋ := ℋ) A00 A01 A10 A11 z) =
      A10 (hsumProj ℋ 0 z) + A11 (hsumProj ℋ 1 z) := by
  simp [blockOp]

omit [Nontrivial ℋ] in
@[simp] theorem blockOp_star (A00 A01 A10 A11 : L ℋ) :
    star (blockOp (ℋ := ℋ) A00 A01 A10 A11) =
      blockOp (ℋ := ℋ) (star A00) (star A10) (star A01) (star A11) := by
  ext z i
  fin_cases i
  · simp [blockOp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
    abel
  · simp [blockOp, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
    abel

end JensenOperatorInequality
