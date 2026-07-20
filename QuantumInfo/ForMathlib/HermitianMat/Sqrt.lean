/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Proj

@[expose] public section

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {f g : ℝ → ℝ}

noncomputable section

open scoped MatrixOrder ComplexOrder Matrix Kronecker

namespace HermitianMat

/-- The square root of a Hermitian matrix. Negative eigenvalues are mapped to zero. -/
noncomputable def sqrt (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.sqrt

theorem sqrt_sq_eq_proj (A : HermitianMat d 𝕜) :
    A.sqrt.mat * A.sqrt.mat = A⁺ := by
  rw [sqrt, ← mat_cfc_mul, ← HermitianMat.ext_iff, posPart_eq_cfc_ite]
  congr! 2 with x
  grind [Pi.mul_apply, Real.mul_self_sqrt, Real.sqrt_eq_zero']

theorem sqrt_sq (hA : 0 ≤ A) :
    A.sqrt.mat * A.sqrt.mat = A := by
  rw [sqrt_sq_eq_proj, posPart_eq_self hA]

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem commute_sqrt_left (hAB : Commute A.mat B.mat) :
    Commute A.sqrt.mat B.mat := by
  rw [sqrt]
  commutes

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem commute_sqrt_right (hAB : Commute A.mat B.mat) :
    Commute A.mat B.sqrt.mat := by
  commutes

/--
For a positive definite matrix A, A^{-1/2} * A * A^{-1/2} = I.
-/
lemma sqrt_inv_mul_self_mul_sqrt_inv_eq_one {A : HermitianMat d 𝕜} (hA : A.mat.PosDef) :
    A⁻¹.sqrt.mat * A.mat * A⁻¹.sqrt.mat = 1 := by
  have h_comm : Commute A⁻¹.sqrt.mat A.mat := by commutes
  rw [h_comm, mul_assoc, sqrt_sq (zero_le_iff.mpr hA.inv.posSemidef)]
  exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne')

theorem sqrt_nonneg (A : HermitianMat d 𝕜) : 0 ≤ A.sqrt :=
  (HermitianMat.cfc_nonneg_iff _ _).mpr fun _ ↦ Real.sqrt_nonneg _

theorem sqrt_pos (h : 0 < A) : 0 < A.sqrt :=
  cfc_pos_of_pos h (fun _ hi ↦ Real.sqrt_pos.mpr hi) (by simp)

theorem sqrt_posDef {A : HermitianMat d 𝕜} (hA : A.mat.PosDef) :
    A.sqrt.mat.PosDef :=
  (cfc_posDef _ _).mpr fun i ↦ Real.sqrt_pos.mpr (hA.eigenvalues_pos i)

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.sqrt` -/
@[positivity HermitianMat.sqrt _]
meta def evalHermitianMatSqrt : PositivityExt where eval {_u _α} _zα _pα e := do
  let .app _sqrt (A : Expr) ← whnfR e | throwError "not sqrt application"
  try
    let (isStrictA, pfA) ← bestResult A
    if isStrictA then
      pure (.positive (← mkAppM ``HermitianMat.sqrt_pos #[pfA]))
    else
      throwError "Not strictly positive, falling back to nonnegativity"
  catch _ =>
    pure (.nonnegative (← mkAppM ``HermitianMat.sqrt_nonneg #[A]))

example {A : HermitianMat d ℂ} : 0 ≤ A.sqrt := by
  positivity

example [Nonempty d] {A : HermitianMat d ℂ} : 0 < (1 + A.sqrt).sqrt  := by
  positivity
