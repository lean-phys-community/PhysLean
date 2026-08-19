/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.Basic
/-!
# Coordinate-axis rotations in `SL(2,ℂ)`

This file defines rotations carrying the `z`-axis to a selected coordinate axis. The spatial
axis convention is `0 = x`, `1 = y`, and `2 = z`.
-/

@[expose] public section

namespace Lorentz.SL2C

open Matrix MatrixGroups

private lemma sqrtTwo_sq : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- The `SL(2,ℂ)` rotation carrying the `z`-axis to axis `i`. -/
noncomputable def rotationZToAxis : Fin 3 → SL(2,ℂ)
  | 0 =>
      ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1], by
        rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow, sqrtTwo_sq]
        norm_num⟩
  | 1 =>
      ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, Complex.I; Complex.I, 1], by
        rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow, sqrtTwo_sq,
          Complex.I_mul_I]
        norm_num⟩
  | 2 => 1

/-- The matrix entries of the rotation carrying the `z`-axis to axis `i`. -/
@[simp] lemma rotationZToAxis_apply (i : Fin 3) (j k : Fin 2) :
    (rotationZToAxis i).1 j k =
      match i with
      | 0 => ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1]) j k
      | 1 => ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ •
          !![1, Complex.I; Complex.I, 1]) j k
      | 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := by
  fin_cases i <;> rfl

/-- The matrix entries of the inverse rotation from axis `i` back to the `z`-axis. -/
@[simp] lemma rotationZToAxis_inv_apply (i : Fin 3) (j k : Fin 2) :
    ((rotationZToAxis i)⁻¹).1 j k =
      match i with
      | 0 => ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, 1; -1, 1]) j k
      | 1 => ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹ •
          !![1, -Complex.I; -Complex.I, 1]) j k
      | 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ) j k := by
  fin_cases i
  all_goals
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;> simp [rotationZToAxis]

/-- Conjugating a diagonal matrix by `rotationZToAxis i` expresses it in the basis for axis
`i`. -/
lemma rotationZToAxis_mul_diagonal_mul_inv (i : Fin 3) (a b : ℂ) :
    (rotationZToAxis i).1 * !![a, 0; 0, b] * ((rotationZToAxis i)⁻¹).1 =
      match i with
      | 0 => !![(a + b) / 2, (a - b) / 2; (a - b) / 2, (a + b) / 2]
      | 1 => !![(a + b) / 2, -Complex.I * (a - b) / 2;
          Complex.I * (a - b) / 2, (a + b) / 2]
      | 2 => !![a, 0; 0, b] := by
  have hsqrt_ne : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by simp
  fin_cases i
  · ext j k
    fin_cases j <;> fin_cases k <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_apply,
        rotationZToAxis_inv_apply] <;>
      simp <;>
      field_simp <;>
      rw [sqrtTwo_sq] <;>
      ring
  · ext j k
    fin_cases j <;> fin_cases k
    all_goals
      simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_apply,
        rotationZToAxis_inv_apply]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.smul_apply, of_apply, cons_val',
        cons_val_zero, cons_val_fin_one, smul_eq_mul, mul_one, cons_val_one, mul_zero,
        add_zero, zero_add, mul_neg, neg_mul, Fin.mk_one]
      field_simp
      rw [sqrtTwo_sq]
    · rw [Complex.I_sq]
      ring
    · ring
    · ring
    · rw [Complex.I_sq]
      ring
  · ext j k
    fin_cases j <;> fin_cases k <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, rotationZToAxis_apply,
        rotationZToAxis_inv_apply] <;>
      simp [Matrix.one_apply]

end Lorentz.SL2C

end
