/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati
-/
module

public import QuantumInfo.Finite.MState

/-! # Unitary operators on quantum state

This file is intended for lemmas about unitary matrices (`Matrix.unitaryGroup`) and how they apply to
`Bra`s, `Ket`s, and `MState` mixed states.

This is imported by `CPTPMap` to define things like unitary channels, Kraus operators, and
complementary channels, so this file itself does not discuss channels yet. -/

@[expose] public section

noncomputable section

open RealInnerProductSpace
open InnerProductSpace

namespace HermitianMat

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
variable (A B : HermitianMat n 𝕜) (U : Matrix.unitaryGroup n 𝕜)

@[simp]
theorem trace_conj_unitary : (conj U.val A).trace = A.trace := by
  simp [Matrix.trace_mul_cycle, conj, ← Matrix.star_eq_conjTranspose, trace]

@[simp]
theorem le_conj_unitary : A.conj U.val ≤ B.conj U ↔ A ≤ B := by
  rw [← sub_nonneg, ← sub_nonneg (b := A), ← map_sub]
  constructor
  · intro h
    simpa [HermitianMat.conj_conj] using conj_nonneg (star U).val h
  · exact fun h ↦ conj_nonneg U.val h

@[simp]
theorem inner_conj_unitary : ⟪A.conj U.val, B.conj U.val⟫ = ⟪A, B⟫ := by
  dsimp [conj]
  simp only [inner_eq_re_trace, mat_mk]
  rw [← mul_assoc, ← mul_assoc, mul_assoc _ _ U.val]
  rw [Matrix.trace_mul_cycle, ← mul_assoc, ← mul_assoc _ _ A.mat]
  simp [← Matrix.star_eq_conjTranspose]

/--
The eigenvalues of a Hermitian matrix conjugated by a unitary matrix are the same
as the eigenvalues of the original matrix.
-/
@[simp]
theorem eigenvalues_conj:(A.conj U.val).H.eigenvalues = A.H.eigenvalues := by
  rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
  change (U.val * A.mat * star U.val).charpoly = _
  rw [Matrix.charpoly_mul_comm, ← mul_assoc, U.2.1, one_mul]

end HermitianMat

namespace MState

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d]
variable {ψ φ f : Ket d}

/-- Conjugate a state by a unitary matrix (applying the unitary as an evolution). -/
def U_conj (ρ : MState d) (U : 𝐔[d]) : MState d where
  M := ρ.M.conj U.val
  nonneg := HermitianMat.conj_nonneg U.val ρ.nonneg
  tr := by simp

/-- `MState.U_conj`, the action of a unitary on a mixed state by conjugation.
The ◃ notation comes from the theory of racks and quandles, where this is a
conjugation-like operation. -/
scoped[MState] notation:80 U:80 " ◃ " ρ:81 => MState.U_conj ρ U

set_option backward.isDefEq.respectTransparency false in
/-- You might think this should only be true up to permutation, so that it would read like
`∃ σ : Equiv.Perm d, (ρ.U_conj U).spectrum = ρ.spectrum.relabel σ`. But since eigenvalues
of a matrix are always canonically sorted, this is actually an equality.
-/
@[simp]
theorem U_conj_spectrum_eq (ρ : MState d) (U : 𝐔[d]) :
    (ρ.U_conj U).spectrum = ρ.spectrum := by
  simp [spectrum, U_conj]

@[simp]
theorem inner_U_conj (ρ σ : MState d) (U : 𝐔[d]) : ⟪U ◃ ρ, U ◃ σ⟫_Prob = ⟪ρ, σ⟫_Prob := by
  simp [U_conj, inner_def]

set_option backward.isDefEq.respectTransparency false in
/-- The **No-cloning theorem**, saying that if states `ψ` and `φ` can both be perfectly cloned using a
unitary `U` and a fiducial state `f`, and they aren't identical (their inner product is less than 1),
then the two states must be orthogonal to begin with. In short: only orthogonal states can be simultaneously
cloned. -/
theorem no_cloning {U : 𝐔[d × d]}
  (hψ : U ◃ pure (ψ ⊗ᵠ f) = pure (ψ ⊗ᵠ ψ))
  (hφ : U ◃ pure (φ ⊗ᵠ f) = pure (φ ⊗ᵠ φ))
  (H : ⟪pure ψ, pure φ⟫_Prob < (1 : ℝ)) :
    ⟪pure ψ, pure φ⟫_Prob = (0 : ℝ) := by
  set ρψ := pure ψ
  set ρφ := pure φ
  have h1 : ⟪ρψ, ρφ⟫_Prob * ⟪ρψ, ρφ⟫_Prob = ⟪pure (ψ ⊗ᵠ ψ), pure (φ ⊗ᵠ φ)⟫_Prob := by
    grind only [pure_prod_pure, prod_inner_prod]
  have h2 : (⟪pure (ψ ⊗ᵠ ψ), pure (φ ⊗ᵠ φ)⟫_Prob : ℝ) = ⟪U ◃ pure (ψ ⊗ᵠ f), U ◃ pure (φ ⊗ᵠ f)⟫_Prob := by
    grind only [pure_prod_pure]
  replace h2 : ((pure (ψ ⊗ᵠ ψ)).m * (pure (φ ⊗ᵠ φ)).m).trace.re = (ρψ.m * ρφ.m).trace.re := by
    convert ← h2
    simp +zetaDelta only [inner_U_conj, pure_prod_pure, prod]
    simp [inner, ← Matrix.mul_kronecker_mul, pure_mul_self,
      Matrix.trace_kronecker]
  have h3 : (ρψ.m * ρφ.m).trace.re * ((ρψ.m * ρφ.m).trace.re - 1) = 0 := by
    rw [mul_sub, sub_eq_zero, mul_one]
    exact congr(Subtype.val $h1).trans h2
  rw [mul_eq_zero] at h3
  apply h3.resolve_right
  exact sub_ne_zero_of_ne H.ne

end MState
