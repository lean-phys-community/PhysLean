/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.CFC
import QuantumInfo.ForMathlib.StdBasis

import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Self-adjoint operators on a Hilbert space

`HermitianOp E` is the type of self-adjoint continuous linear operators on a complex inner product
space `E`. It is the basis-free counterpart of `HermitianMat ι ℂ`, and it is the type in which
observables, density operators and POVM elements naturally live.

Given a preferred orthonormal basis (a `StdBasis ℂ E ι` instance), `HermitianOp.toMat` identifies
`HermitianOp E` with `HermitianMat ι ℂ`. Because `StdBasis.toMat` is a ⋆-algebra equivalence, the
identification is compatible with everything of interest: the additive and `ℝ`-module structures,
the Loewner order, the trace, the spectrum, and the continuous functional calculus. The lemmas
transporting those are the *matrix analogues* of the operator-level statements, and they are what
lets an existing matrix definition be reused verbatim on operators.

## Main definitions

* `HermitianOp E`: self-adjoint operators on `E`.
* `HermitianOp.toMat`, `HermitianOp.ofMat`: the mutually inverse maps to and from
  `HermitianMat ι ℂ` determined by the preferred basis.
* `HermitianOp.trace`, `HermitianOp.cfc`: the trace and the continuous functional calculus,
  defined operator-side.

## Main results

* `HermitianOp.matEquiv`: the identification with `HermitianMat ι ℂ` as an `ℝ`-linear equivalence.
* `HermitianOp.toMat_cfc`, `HermitianOp.trace_toMat`, `HermitianOp.toMat_le_toMat`: the matrix
  analogues of the operator-level `cfc`, `trace` and order.
-/

open scoped ComplexOrder

/-- The type of self-adjoint continuous linear operators on `E`, as a `Subtype`.

This is the basis-free analogue of `HermitianMat`; see `HermitianOp.matEquiv` for the
identification of the two given a preferred orthonormal basis. -/
def HermitianOp (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] :=
  (selfAdjoint (E →L[ℂ] E) : Type _)

namespace HermitianOp

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The underlying operator of a `HermitianOp`. -/
@[coe] def op : HermitianOp E → (E →L[ℂ] E) :=
  Subtype.val

instance : Coe (HermitianOp E) (E →L[ℂ] E) := ⟨op⟩

/-- The underlying operator of a `HermitianOp` is self-adjoint. -/
theorem H (A : HermitianOp E) : IsSelfAdjoint A.op :=
  A.2

@[simp]
theorem op_mk (A : E →L[ℂ] E) (h) : op ⟨A, h⟩ = A :=
  rfl

@[ext] protected theorem ext {A B : HermitianOp E} : A.op = B.op → A = B :=
  Subtype.ext

theorem op_injective : Function.Injective (op (E := E)) :=
  fun _ _ ↦ HermitianOp.ext

noncomputable instance : AddCommGroup (HermitianOp E) :=
  inferInstanceAs (AddCommGroup (selfAdjoint (E →L[ℂ] E)))

noncomputable instance : Module ℝ (HermitianOp E) :=
  inferInstanceAs (Module ℝ (selfAdjoint (E →L[ℂ] E)))

noncomputable instance : PartialOrder (HermitianOp E) :=
  inferInstanceAs (PartialOrder (selfAdjoint (E →L[ℂ] E)))

@[simp] theorem op_zero : (0 : HermitianOp E).op = 0 := rfl

@[simp] theorem op_add (A B : HermitianOp E) : (A + B).op = A.op + B.op := rfl

@[simp] theorem op_neg (A : HermitianOp E) : (-A).op = -A.op := rfl

@[simp] theorem op_sub (A B : HermitianOp E) : (A - B).op = A.op - B.op := rfl

@[simp] theorem op_smul (r : ℝ) (A : HermitianOp E) : (r • A).op = r • A.op := rfl

theorem le_def {A B : HermitianOp E} : A ≤ B ↔ A.op ≤ B.op :=
  Iff.rfl

/-- A self-adjoint operator is nonnegative exactly when it is a positive operator. -/
theorem zero_le_iff {A : HermitianOp E} : 0 ≤ A ↔ A.op.IsPositive :=
  ContinuousLinearMap.nonneg_iff_isPositive A.op

/-- The trace of a self-adjoint operator. It is real because the operator is self-adjoint. -/
noncomputable def trace [FiniteDimensional ℂ E] (A : HermitianOp E) : ℝ :=
  RCLike.re (LinearMap.trace ℂ E (A.op : E →ₗ[ℂ] E))

/-- The continuous functional calculus applied to a self-adjoint operator. -/
noncomputable def cfc (A : HermitianOp E) (f : ℝ → ℝ) : HermitianOp E :=
  ⟨_root_.cfc f A.op, cfc_predicate _ _⟩

@[simp]
theorem op_cfc (A : HermitianOp E) (f : ℝ → ℝ) : (A.cfc f).op = _root_.cfc f A.op :=
  rfl

section StdBasis

variable [Fintype ι] [DecidableEq ι] [StdBasis ℂ E ι]

/-- The matrix of a self-adjoint operator in the preferred basis. -/
noncomputable def toMat (A : HermitianOp E) : HermitianMat ι ℂ :=
  ⟨StdBasis.toMat ℂ E ι A.op, (StdBasis.isHermitian_toMat_iff _).2 A.H⟩

/-- The self-adjoint operator with a given matrix in the preferred basis. -/
noncomputable def ofMat (M : HermitianMat ι ℂ) : HermitianOp E :=
  ⟨(StdBasis.toMat ℂ E ι).symm M.mat, by
    show star ((StdBasis.toMat ℂ E ι).symm M.mat) = _
    rw [← map_star, Matrix.star_eq_conjTranspose, M.H]⟩

@[simp]
theorem toMat_mat (A : HermitianOp E) : (toMat (ι := ι) A).mat = StdBasis.toMat ℂ E ι A.op :=
  rfl

@[simp]
theorem ofMat_op (M : HermitianMat ι ℂ) :
    (ofMat (E := E) M).op = (StdBasis.toMat ℂ E ι).symm M.mat :=
  rfl

@[simp]
theorem toMat_ofMat (M : HermitianMat ι ℂ) : toMat (ofMat (E := E) M) = M := by
  ext1
  simp

@[simp]
theorem ofMat_toMat (A : HermitianOp E) : ofMat (toMat (ι := ι) A) = A := by
  ext1
  simp

theorem toMat_injective : Function.Injective (toMat (E := E) (ι := ι)) :=
  Function.LeftInverse.injective ofMat_toMat

@[simp] theorem toMat_zero : toMat (0 : HermitianOp E) = (0 : HermitianMat ι ℂ) := by
  ext1; simp

@[simp] theorem toMat_add (A B : HermitianOp E) :
    toMat (ι := ι) (A + B) = toMat A + toMat B := by
  ext1; simp

@[simp] theorem toMat_neg (A : HermitianOp E) : toMat (ι := ι) (-A) = -toMat A := by
  ext1; simp

@[simp] theorem toMat_sub (A B : HermitianOp E) :
    toMat (ι := ι) (A - B) = toMat A - toMat B := by
  ext1; simp

@[simp] theorem toMat_smul (r : ℝ) (A : HermitianOp E) :
    toMat (ι := ι) (r • A) = r • toMat A := by
  ext1
  show StdBasis.toMat ℂ E ι ((r : ℂ) • A.op) = (r : ℂ) • StdBasis.toMat ℂ E ι A.op
  exact map_smul _ _ _

/-- **Matrix analogue of the operator order.** An inequality of self-adjoint operators is exactly
the Loewner inequality of their matrices in the preferred basis. -/
@[simp]
theorem toMat_le_toMat {A B : HermitianOp E} : toMat (ι := ι) A ≤ toMat B ↔ A ≤ B := by
  rw [HermitianMat.le_iff, le_def, ContinuousLinearMap.le_def,
    ← StdBasis.posSemidef_toMat_iff (ι := ι)]
  congr! 1
  show (toMat (ι := ι) B - toMat A).mat = _
  rw [HermitianMat.mat_sub, toMat_mat, toMat_mat, ← map_sub]

/-- The identification of self-adjoint operators with Hermitian matrices determined by the
preferred basis, as an `ℝ`-linear equivalence. -/
@[simps apply symm_apply]
noncomputable def matEquiv : HermitianOp E ≃ₗ[ℝ] HermitianMat ι ℂ where
  toFun := toMat
  invFun := ofMat
  left_inv := ofMat_toMat
  right_inv := toMat_ofMat
  map_add' := toMat_add
  map_smul' := toMat_smul

/-- **Matrix analogue of the operator trace.** -/
@[simp]
theorem trace_toMat (A : HermitianOp E) : (toMat (ι := ι) A).trace = A.trace := by
  rw [HermitianMat.trace_eq_re_trace, trace, toMat_mat, StdBasis.trace_toMat]

/-- The spectrum of a self-adjoint operator is the spectrum of its matrix. -/
theorem spectrum_toMat (A : HermitianOp E) :
    spectrum ℝ (toMat (ι := ι) A).mat = spectrum ℝ A.op :=
  AlgEquiv.spectrum_eq ((StdBasis.toMat ℂ E ι).toAlgEquiv.restrictScalars ℝ) A.op

/-- The spectrum of an operator on a space with a preferred basis is finite: it is the spectrum of
a matrix. -/
instance finite_spectrum (A : E →L[ℂ] E) : Finite (spectrum ℝ A) := by
  rw [← AlgEquiv.spectrum_eq ((StdBasis.toMat ℂ E ι).toAlgEquiv.restrictScalars ℝ) A]
  infer_instance

/-- **Matrix analogue of the operator continuous functional calculus.** -/
@[simp]
theorem toMat_cfc (A : HermitianOp E) (f : ℝ → ℝ) :
    toMat (ι := ι) (A.cfc f) = (toMat A).cfc f := by
  ext1
  rw [toMat_mat, op_cfc, HermitianMat.mat_cfc, toMat_mat]
  refine StarAlgHomClass.map_cfc (S := ℂ) _ f A.op
    (HermitianMat.continuousOn_finite f _) ?_ A.H ((StdBasis.isHermitian_toMat_iff _).2 A.H)
  exact (StdBasis.toMat ℂ E ι).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional

end StdBasis

end HermitianOp
