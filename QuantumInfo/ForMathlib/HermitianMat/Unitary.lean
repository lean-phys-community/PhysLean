/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Inner
public import QuantumInfo.ForMathlib.HermitianMat.NonSingular
public import QuantumInfo.ForMathlib.Isometry

@[expose] public section

notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

namespace Matrix

variable {α : Type*} [NonUnitalNonAssocSemiring α] [StarRing α]

variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

@[simp]
theorem neg_unitary_val (u : 𝐔[α]) : (-u).val = -u := by
  rfl

omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
open Kronecker in
@[simp]
theorem star_kron (a : Matrix α α ℂ) (b : Matrix β β ℂ) : star (a ⊗ₖ b) = (star a) ⊗ₖ (star b) := by
  ext _ _
  simp

set_option backward.isDefEq.respectTransparency false in
open Kronecker in
theorem kron_unitary (a : 𝐔[α]) (b : 𝐔[β]) : a.val ⊗ₖ b.val ∈ 𝐔[α × β] := by
  simp [Matrix.mem_unitaryGroup_iff, ← Matrix.mul_kronecker_mul]

open Kronecker in
def unitary_kron (a : 𝐔[α]) (b : 𝐔[β]) : 𝐔[α × β] :=
  ⟨_, kron_unitary a b⟩

scoped infixl:60 " ⊗ᵤ " => unitary_kron

@[simp]
theorem unitary_kron_apply (a : 𝐔[α]) (b : 𝐔[β]) (i₁ i₂ : α) (j₁ j₂ : β) :
    (a ⊗ᵤ b) (i₁, j₁) (i₂, j₂) = (a i₁ i₂) * (b j₁ j₂) := by
  rfl

@[simp]
theorem unitary_kron_one_one : (1 : 𝐔[α]) ⊗ᵤ (1 : 𝐔[β]) = (1 : 𝐔[α × β]) := by
  simp [Matrix.unitary_kron]

--TODO: Cleanup? Or at least write the signature better. Definitely belongs in Mathlib in some form
--This is really a statement about isometries, not unitaries, too...
variable {d : Type*} [Fintype d] [DecidableEq d]

/--
For a unitary matrix C, the row sums of ‖C i j‖^2 equal 1.
-/
lemma unitary_row_sum_norm_sq (C : Matrix d d ℂ) (hC : C * C.conjTranspose = 1) (i : d) :
    ∑ j, ‖C i j‖ ^ 2 = 1 := by
  replace hC := congr($hC i i)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, Complex.ofReal_pow, Matrix.one_apply_eq] at hC
  exact_mod_cast hC

/--
For a unitary matrix C, the column sums of ‖C i j‖^2 equal 1.
-/
lemma unitary_col_sum_norm_sq (C : Matrix d d ℂ) (hC : C.conjTranspose * C = 1) (j : d) :
    ∑ i, ‖C i j‖ ^ 2 = 1 := by
  replace hC := congr($hC j j)
  simp_rw [Matrix.mul_apply, mul_comm] at hC
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, Matrix.one_apply_eq,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow] at hC
  exact_mod_cast hC

end Matrix
