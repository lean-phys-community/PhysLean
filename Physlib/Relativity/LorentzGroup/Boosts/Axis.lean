/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li, Nathaneal Sajan, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.Basic
public import Physlib.Relativity.PauliMatrices.Basic
public import Physlib.Relativity.MinkowskiMatrix
/-!
# Coordinate-axis boosts in `SL(2,ℂ)` and the Lorentz group

## i. Overview

We define the axis-indexed lift `Lorentz.SL2C.boostAxis` in `SL(2,ℂ)` and its image
`LorentzGroup.boostAxis` in the Lorentz group.

The parameter `t ≠ 0` is multiplicative: replacing `t` by `t⁻¹` reverses the boost. For
`t > 0`, its rapidity is `2 * log t`; negative values retain the action of the central
element `-1 : SL(2,ℂ)`.

For the `z`-axis, `LorentzGroup.boostAxis 2 t ht` agrees with the velocity-parameterized boost
`LorentzGroup.boost 2 β` at `β = (t² - t⁻²) / (t² + t⁻²)`.

The lift is Hermitian along every axis, and the `x`- and `y`-axis lifts are conjugates of
the diagonal `z`-axis lift.

The index `Sum.inl 0` is the time coordinate, while `Sum.inr 0`, `Sum.inr 1`, and
`Sum.inr 2` are the `x`, `y`, and `z` coordinates. Accordingly, axis indices `0`, `1`, and
`2` select the `x`-, `y`-, and `z`-axis boosts. The covering map uses the action
`X ↦ M X Mᴴ` on self-adjoint matrices.

## ii. Key results

- `Lorentz.SL2C.boostAxis` defines the axis-boost lifts.
- `Lorentz.SL2C.boostAxis_inv` and `Lorentz.SL2C.boostAxis_conjTranspose` give their
  inverses and Hermiticity.
- `LorentzGroup.boostAxis` defines the induced Lorentz transformations, with entries given by
  `LorentzGroup.boostAxis_apply`.
- `Lorentz.SL2C.exists_conj_boostAxis` proves that every lift is conjugate to the `z`-boost.

## iii. Table of contents

- A. The axis-boost lift
- B. The induced Lorentz transformation
- C. Axis conjugation

-/

@[expose] public section

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

namespace Lorentz.SL2C

/-!

## A. The axis-boost lift

-/

/-- The `SL(2,ℂ)` lift of the boost along spatial axis `i`, with `0 = x`, `1 = y`, and
`2 = z`. The parameter `t` is multiplicative, and for `t > 0` the rapidity is `2 * log t`. -/
noncomputable def boostAxis : Fin 3 → (t : ℝ) → t ≠ 0 → SL(2,ℂ)
  | 0, t, ht =>
      ⟨!![((t : ℂ) + (t : ℂ)⁻¹) / 2, ((t : ℂ) - (t : ℂ)⁻¹) / 2;
          ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        rw [Matrix.det_fin_two_of]
        field_simp
        ring⟩
  | 1, t, ht =>
      ⟨!![((t : ℂ) + (t : ℂ)⁻¹) / 2, -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2;
          Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2, ((t : ℂ) + (t : ℂ)⁻¹) / 2], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        have h2 : -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
            (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2) =
            ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
          have hI : -Complex.I * Complex.I = 1 := by
            rw [neg_mul, Complex.I_mul_I, neg_neg]
          calc -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2 *
                (Complex.I * ((t : ℂ) - (t : ℂ)⁻¹) / 2)
              = (-Complex.I * Complex.I) *
                  (((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2)) := by
                ring
            _ = ((t : ℂ) - (t : ℂ)⁻¹) / 2 * (((t : ℂ) - (t : ℂ)⁻¹) / 2) := by
                rw [hI, one_mul]
        rw [Matrix.det_fin_two_of, h2]
        field_simp
        ring⟩
  | 2, t, ht =>
      ⟨!![(t : ℂ), 0; 0, (t : ℂ)⁻¹], by
        have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
        rw [Matrix.det_fin_two_of]
        simp [mul_inv_cancel₀ htc]⟩

/-- Inverting an axis boost replaces its multiplicative parameter `t` by `t⁻¹`. -/
lemma boostAxis_inv (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht)⁻¹ = boostAxis i t⁻¹ (inv_ne_zero ht) := by
  fin_cases i
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      · simp [boostAxis, Complex.ofReal_inv, inv_inv]
        try ring
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      · simp [boostAxis, Complex.ofReal_inv, inv_inv]
        try ring
  · ext j k
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    fin_cases j <;> fin_cases k <;>
      simp [boostAxis, Complex.ofReal_inv, inv_inv]

/-- The matrix underlying an axis-boost lift is Hermitian. -/
lemma boostAxis_conjTranspose (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht).1ᴴ = (boostAxis i t ht).1 := by
  fin_cases i <;> ext j k <;> fin_cases j <;> fin_cases k <;> simp [boostAxis]

end Lorentz.SL2C

namespace LorentzGroup

/-!

## B. The induced Lorentz transformation

-/

/-- The Lorentz transformation induced by the multiplicatively parameterized `SL(2,ℂ)` boost
along spatial axis `i`. -/
noncomputable def boostAxis (i : Fin 3) (t : ℝ) (ht : t ≠ 0) : LorentzGroup 3 :=
  Lorentz.SL2C.toLorentzGroup (Lorentz.SL2C.boostAxis i t ht)

/-- The entries of an axis boost in the Lorentz group. -/
lemma boostAxis_apply (i : Fin 3) (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (boostAxis i t ht).1 a b =
      match i with
      | 0 => match a, b with
        | Sum.inl _, Sum.inl _ => (t ^ 2 + (t⁻¹) ^ 2) / 2
        | Sum.inl _, Sum.inr 0 => -((t ^ 2 - (t⁻¹) ^ 2) / 2)
        | Sum.inr 0, Sum.inl _ => -((t ^ 2 - (t⁻¹) ^ 2) / 2)
        | Sum.inr 0, Sum.inr 0 => (t ^ 2 + (t⁻¹) ^ 2) / 2
        | Sum.inr 1, Sum.inr 1 => 1
        | Sum.inr 2, Sum.inr 2 => 1
        | _, _ => 0
      | 1 => match a, b with
        | Sum.inl _, Sum.inl _ => (t ^ 2 + (t⁻¹) ^ 2) / 2
        | Sum.inl _, Sum.inr 1 => -((t ^ 2 - (t⁻¹) ^ 2) / 2)
        | Sum.inr 1, Sum.inl _ => -((t ^ 2 - (t⁻¹) ^ 2) / 2)
        | Sum.inr 0, Sum.inr 0 => 1
        | Sum.inr 1, Sum.inr 1 => (t ^ 2 + (t⁻¹) ^ 2) / 2
        | Sum.inr 2, Sum.inr 2 => 1
        | _, _ => 0
      | 2 => match a, b with
        | Sum.inl _, Sum.inl _ => (t ^ 2 + (t⁻¹) ^ 2) / 2
        | Sum.inl _, Sum.inr 2 => -((t ^ 2 - (t⁻¹) ^ 2) / 2)
        | Sum.inr 2, Sum.inl _ => -((t ^ 2 - (t⁻¹) ^ 2) / 2)
        | Sum.inr 0, Sum.inr 0 => 1
        | Sum.inr 1, Sum.inr 1 => 1
        | Sum.inr 2, Sum.inr 2 => (t ^ 2 + (t⁻¹) ^ 2) / 2
        | _, _ => 0 := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [boostAxis, Lorentz.SL2C.toLorentzGroup_eq_trace,
    PauliMatrix.trace_pauliSelfAdjoint'_mul_apply, Lorentz.SL2C.boostAxis_conjTranspose]
  fin_cases i
  all_goals
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
      simp [Lorentz.SL2C.boostAxis, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp <;>
      ring_nf
  all_goals simp only [Complex.I_sq, Complex.I_pow_four]
  all_goals ring

end LorentzGroup

namespace Lorentz.SL2C

/-!

## C. Axis conjugation

-/

private lemma sqrtTwo_sq : (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private lemma sqrtTwo_ne_zero : (((Real.sqrt 2 : ℝ) : ℂ)) ≠ 0 := by
  simp []

private lemma sqrtTwo_inv_mul :
    ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) * ((((Real.sqrt 2 : ℝ) : ℂ))⁻¹) = 2⁻¹ := by
  rw [← mul_inv, ← sq, sqrtTwo_sq]

/-- The `SL(2,ℂ)` rotation carrying the `z`-axis to the `x`-axis. -/
noncomputable def rotZX : SL(2,ℂ) :=
  ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, -1; 1, 1], by
    rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow, sqrtTwo_sq]
    norm_num⟩

/-- The `SL(2,ℂ)` rotation carrying the `z`-axis to the `y`-axis. -/
noncomputable def rotZY : SL(2,ℂ) :=
  ⟨(((Real.sqrt 2 : ℝ) : ℂ))⁻¹ • !![1, Complex.I; Complex.I, 1], by
    rw [Matrix.det_smul, Matrix.det_fin_two_of, Fintype.card_fin, inv_pow, sqrtTwo_sq,
      Complex.I_mul_I]
    norm_num⟩

set_option backward.isDefEq.respectTransparency false in
/-- The `x`-axis boost is obtained by conjugating the `z`-axis boost by `rotZX`. -/
lemma boostAxis_zero_eq_conj (t : ℝ) (ht : t ≠ 0) :
    boostAxis 0 t ht = rotZX * boostAxis 2 t ht * rotZX⁻¹ := by
  have h0 := sqrtTwo_ne_zero
  have hc := sqrtTwo_inv_mul
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.SpecialLinearGroup.coe_mul, rotZX, boostAxis,
        Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      simp only [sqrtTwo_sq]
      try ring

set_option backward.isDefEq.respectTransparency false in
/-- The `y`-axis boost is obtained by conjugating the `z`-axis boost by `rotZY`. -/
lemma boostAxis_one_eq_conj (t : ℝ) (ht : t ≠ 0) :
    boostAxis 1 t ht = rotZY * boostAxis 2 t ht * rotZY⁻¹ := by
  have h0 := sqrtTwo_ne_zero
  have hc := sqrtTwo_inv_mul
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.SpecialLinearGroup.coe_mul, rotZY, boostAxis,
        Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      simp only [sqrtTwo_sq, Complex.I_sq]
      try ring

/-- Every coordinate-axis boost is conjugate to the `z`-axis boost. -/
lemma exists_conj_boostAxis (i : Fin 3) :
    ∃ R : SL(2,ℂ), ∀ (t : ℝ) (ht : t ≠ 0),
      boostAxis i t ht = R * boostAxis 2 t ht * R⁻¹ := by
  fin_cases i
  · exact ⟨rotZX, fun t ht => boostAxis_zero_eq_conj t ht⟩
  · exact ⟨rotZY, fun t ht => boostAxis_one_eq_conj t ht⟩
  · exact ⟨1, fun t ht => by simp⟩

end Lorentz.SL2C

end
