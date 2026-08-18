/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.SL2C.Basic
public import Physlib.Relativity.PauliMatrices.Basic
public import Physlib.Relativity.MinkowskiMatrix
/-!
# Coordinate-axis boosts in `SL(2,ℂ)`

## i. Overview

We define explicit elements `boostZel`, `boostXel`, and `boostYel` of `SL(2,ℂ)`
representing boosts along the three coordinate axes. We also prove that their images under
`Lorentz.SL2C.toLorentzGroup` are the corresponding explicit Lorentz matrices.

The parameter `t ≠ 0` is multiplicative: replacing `t` by `t⁻¹` reverses the boost. For
`t > 0`, its rapidity is `2 * log t`; negative values retain the action of the central
element `-1 : SL(2,ℂ)`.

The three lifts are Hermitian, and the `x`- and `y`-axis lifts are conjugates of the
diagonal `z`-axis lift.

The index `Sum.inl 0` is the time coordinate, while `Sum.inr 0`, `Sum.inr 1`, and
`Sum.inr 2` are the `x`, `y`, and `z` coordinates. Accordingly, `boostAxis 0`,
`boostAxis 1`, and `boostAxis 2` select the `x`-, `y`-, and `z`-axis lifts. The covering
map uses the action `X ↦ M X Mᴴ` on self-adjoint matrices.

## ii. Key results

- `boostZel`, `boostXel`, and `boostYel` define the three axis-boost lifts.
- `toLorentzGroup_boostZel`, `toLorentzGroup_boostXel`, and `toLorentzGroup_boostYel`
  identify their Lorentz matrices.
- `boostZel_inv`, `boostXel_inv`, and `boostYel_inv` identify their inverses.
- `boostAxis` packages the three families using a spatial-axis index.
- `exists_conj_boostAxis` proves that every axis boost is conjugate to the `z`-boost.

## iii. Table of contents

- A. The axis-boost lifts
- B. Their Lorentz matrices
- C. Their inverses
- D. Axis indexing and conjugation

-/

@[expose] public section

namespace Lorentz

open scoped minkowskiMatrix PauliMatrix
open Matrix MatrixGroups

/-!

## A. The axis-boost lifts

The `z`-axis lift is diagonal. The `x`- and `y`-axis lifts are the same family expressed in
bases rotated toward the corresponding spatial axes.

-/


/-- The diagonal `SL(2,ℂ)` lift of the `z`-axis boost. For `t > 0`, its rapidity is
`2 * log t`; replacing `t` by `t⁻¹` reverses the boost. -/
noncomputable def boostZel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![(t : ℂ), 0; 0, (t : ℂ)⁻¹], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    rw [Matrix.det_fin_two_of]
    simp [mul_inv_cancel₀ htc]⟩

/-- The `SL(2,ℂ)` lift of the `x`-axis boost, obtained from the `z`-axis family by rotation. -/
noncomputable def boostXel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![((t : ℂ) + (t : ℂ)⁻¹)/2, ((t : ℂ) - (t : ℂ)⁻¹)/2;
      ((t : ℂ) - (t : ℂ)⁻¹)/2, ((t : ℂ) + (t : ℂ)⁻¹)/2], by
    have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
    rw [Matrix.det_fin_two_of]
    field_simp
    ring⟩

/-- The `SL(2,ℂ)` lift of the `y`-axis boost, obtained from the `z`-axis family by rotation. -/
noncomputable def boostYel (t : ℝ) (ht : t ≠ 0) : SL(2,ℂ) :=
  ⟨!![((t : ℂ) + (t : ℂ)⁻¹)/2, -Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2;
      Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2, ((t : ℂ) + (t : ℂ)⁻¹)/2], by
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

/-!

## B. Their Lorentz matrices

The following definitions give the explicit Lorentz matrices of the three lifts. Their
identification with the images under `Lorentz.SL2C.toLorentzGroup` uses Hermiticity and the
trace pairing with the covariant Pauli basis.

-/

/-- The Lorentz matrix of `boostZel t`, mixing the time and `z` coordinates. -/
noncomputable def boostMatZ (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 2 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 2, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => (t^2 + (t⁻¹)^2)/2
  | _, _ => 0

/-- The Lorentz matrix of `boostXel t`, mixing the time and `x` coordinates. -/
noncomputable def boostMatX (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 0 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => (t^2 + (t⁻¹)^2)/2
  | Sum.inr 1, Sum.inr 1 => 1
  | Sum.inr 2, Sum.inr 2 => 1
  | _, _ => 0

/-- The Lorentz matrix of `boostYel t`, mixing the time and `y` coordinates. -/
noncomputable def boostMatY (t : ℝ) : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → ℝ
  | Sum.inl _, Sum.inl _ => (t^2 + (t⁻¹)^2)/2
  | Sum.inl _, Sum.inr 1 => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 1, Sum.inl _ => -((t^2 - (t⁻¹)^2)/2)
  | Sum.inr 0, Sum.inr 0 => 1
  | Sum.inr 1, Sum.inr 1 => (t^2 + (t⁻¹)^2)/2
  | Sum.inr 2, Sum.inr 2 => 1
  | _, _ => 0

/-- The underlying matrix of the `z`-axis boost lift is Hermitian. -/
lemma boostZel_conjTranspose (t : ℝ) (ht : t ≠ 0) :
    (boostZel t ht).1ᴴ = (boostZel t ht).1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostZel]

/-- The underlying matrix of the `x`-axis boost lift is Hermitian. -/
lemma boostXel_conjTranspose (t : ℝ) (ht : t ≠ 0) :
    (boostXel t ht).1ᴴ = (boostXel t ht).1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostXel]

/-- The underlying matrix of the `y`-axis boost lift is Hermitian. -/
lemma boostYel_conjTranspose (t : ℝ) (ht : t ≠ 0) :
    (boostYel t ht).1ᴴ = (boostYel t ht).1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostYel]

/-- The image of `boostZel t` under `toLorentzGroup` is `boostMatZ t`. -/
lemma toLorentzGroup_boostZel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostZel t ht)).1 a b = boostMatZ t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace,
    PauliMatrix.trace_pauliSelfAdjoint'_mul_apply, boostZel_conjTranspose]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [boostZel, boostMatZ, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;>
    ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

/-- The image of `boostXel t` under `toLorentzGroup` is `boostMatX t`. -/
lemma toLorentzGroup_boostXel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostXel t ht)).1 a b = boostMatX t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace,
    PauliMatrix.trace_pauliSelfAdjoint'_mul_apply, boostXel_conjTranspose]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [boostXel, boostMatX, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;>
    ring_nf
  all_goals simp only [Complex.I_sq]
  all_goals ring

/-- The image of `boostYel t` under `toLorentzGroup` is `boostMatY t`. -/
lemma toLorentzGroup_boostYel (t : ℝ) (ht : t ≠ 0) (a b : Fin 1 ⊕ Fin 3) :
    (Lorentz.SL2C.toLorentzGroup (boostYel t ht)).1 a b = boostMatY t a b := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Complex.ofReal_injective ?_
  rw [Lorentz.SL2C.toLorentzGroup_eq_trace,
    PauliMatrix.trace_pauliSelfAdjoint'_mul_apply, boostYel_conjTranspose]
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [boostYel, boostMatY, PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;>
    ring_nf
  all_goals simp only [Complex.I_sq, Complex.I_pow_four]
  all_goals ring


/-!

## C. Their inverses

Replacing the multiplicative parameter `t` by `t⁻¹` reverses an axis boost. We record this
both at the level of the boost families and through their explicit matrix entries.

-/

/-- Inverting the `z`-axis boost replaces `t` by `t⁻¹`. -/
lemma boostZel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostZel t ht)⁻¹ = boostZel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    simp [boostZel, Complex.ofReal_inv, inv_inv]

/-- Inverting the `x`-axis boost replaces `t` by `t⁻¹`. -/
lemma boostXel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostXel t ht)⁻¹ = boostXel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    · simp [boostXel, Complex.ofReal_inv, inv_inv]
      try ring

/-- Inverting the `y`-axis boost replaces `t` by `t⁻¹`. -/
lemma boostYel_inv (t : ℝ) (ht : t ≠ 0) :
    (boostYel t ht)⁻¹ = boostYel t⁻¹ (inv_ne_zero ht) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  fin_cases i <;> fin_cases j <;>
    · simp [boostYel, Complex.ofReal_inv, inv_inv]
      try ring


/-- The inverse of the parametric `z`-boost, entrywise, with real entries. -/
lemma boostZel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostZel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![(((t⁻¹ : ℝ)) : ℂ), 0; 0, ((t : ℝ) : ℂ)] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostZel]

/-- The inverse of the parametric `x`-boost, entrywise. -/
lemma boostXel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostXel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![((t : ℂ) + (t : ℂ)⁻¹)/2, -(((t : ℂ) - (t : ℂ)⁻¹)/2);
         -(((t : ℂ) - (t : ℂ)⁻¹)/2), ((t : ℂ) + (t : ℂ)⁻¹)/2] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostXel]

/-- The inverse of the parametric `y`-boost, entrywise. -/
lemma boostYel_inv_coe (t : ℝ) (ht : t ≠ 0) :
    ((boostYel t ht)⁻¹ : SL(2,ℂ)).1 =
      !![((t : ℂ) + (t : ℂ)⁻¹)/2, Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2;
         -(Complex.I * ((t : ℂ) - (t : ℂ)⁻¹)/2), ((t : ℂ) + (t : ℂ)⁻¹)/2] := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;> · simp [boostYel]; try ring

/-!

## D. Axis indexing and conjugation

The three families are packaged into one axis-indexed construction. Explicit rotations show
that the `x`- and `y`-axis boosts are conjugates of the diagonal `z`-axis boost.

-/

/-- The axis-indexed boost lift, with `0 = x`, `1 = y`, and `2 = z`. -/
noncomputable def boostAxis : Fin 3 → (t : ℝ) → t ≠ 0 → SL(2,ℂ)
  | 0, t, ht => boostXel t ht
  | 1, t, ht => boostYel t ht
  | 2, t, ht => boostZel t ht

/-- The axis-indexed boost along axis `0` is the `x`-axis boost. -/
@[simp] lemma boostAxis_zero (t : ℝ) (ht : t ≠ 0) : boostAxis 0 t ht = boostXel t ht := rfl

/-- The axis-indexed boost along axis `1` is the `y`-axis boost. -/
@[simp] lemma boostAxis_one (t : ℝ) (ht : t ≠ 0) : boostAxis 1 t ht = boostYel t ht := rfl

/-- The axis-indexed boost along axis `2` is the `z`-axis boost. -/
@[simp] lemma boostAxis_two (t : ℝ) (ht : t ≠ 0) : boostAxis 2 t ht = boostZel t ht := rfl

/-- Inverting an axis-indexed boost replaces `t` by `t⁻¹`. -/
lemma boostAxis_inv (i : Fin 3) (t : ℝ) (ht : t ≠ 0) :
    (boostAxis i t ht)⁻¹ = boostAxis i t⁻¹ (inv_ne_zero ht) := by
  fin_cases i
  · exact boostXel_inv t ht
  · exact boostYel_inv t ht
  · exact boostZel_inv t ht

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
lemma boostXel_eq_conj (t : ℝ) (ht : t ≠ 0) :
    boostXel t ht = rotZX * boostZel t ht * rotZX⁻¹ := by
  have h0 := sqrtTwo_ne_zero
  have hc := sqrtTwo_inv_mul
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.SpecialLinearGroup.coe_mul, rotZX, boostZel, boostXel,
        Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      simp only [sqrtTwo_sq]
      try ring

set_option backward.isDefEq.respectTransparency false in
/-- The `y`-axis boost is obtained by conjugating the `z`-axis boost by `rotZY`. -/
lemma boostYel_eq_conj (t : ℝ) (ht : t ≠ 0) :
    boostYel t ht = rotZY * boostZel t ht * rotZY⁻¹ := by
  have h0 := sqrtTwo_ne_zero
  have hc := sqrtTwo_inv_mul
  have htc : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp [Matrix.SpecialLinearGroup.coe_mul, rotZY, boostZel, boostYel,
        Matrix.mul_apply, Fin.sum_univ_two]
      field_simp
      simp only [sqrtTwo_sq, Complex.I_sq]
      try ring

/-- Every coordinate-axis boost is conjugate to the `z`-axis boost. -/
lemma exists_conj_boostAxis (i : Fin 3) :
    ∃ R : SL(2,ℂ), ∀ (t : ℝ) (ht : t ≠ 0),
      boostAxis i t ht = R * boostAxis 2 t ht * R⁻¹ := by
  fin_cases i
  · exact ⟨rotZX, fun t ht => boostXel_eq_conj t ht⟩
  · exact ⟨rotZY, fun t ht => boostYel_eq_conj t ht⟩
  · exact ⟨1, fun t ht => by simp⟩

end Lorentz

end
