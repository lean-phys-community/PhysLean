/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati
-/
module

public import QuantumInfo.States.Mixed.MState

/-! # Unitary operators on quantum state

This file is intended for lemmas about unitary matrices (`Matrix.unitaryGroup`) and how they
apply to `Bra`s, `Ket`s, and `MState` mixed states.

This is imported by `CPTPMap` to define things like unitary channels, Kraus operators, and
complementary channels, so this file itself does not discuss channels yet. -/

@[expose] public section

noncomputable section

open RealInnerProductSpace
open InnerProductSpace

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

/-- The **No-cloning theorem**, saying that if states `ψ` and `φ` can both be perfectly cloned
using a unitary `U` and a fiducial state `f`, and they aren't identical (their inner product is
less than 1), then the two states must be orthogonal to begin with. In short: only orthogonal
states can be simultaneously cloned. -/
theorem no_cloning {U : 𝐔[d × d]}
    (hψ : U ◃ pure (ψ ⊗ᵠ f) = pure (ψ ⊗ᵠ ψ))
    (hφ : U ◃ pure (φ ⊗ᵠ f) = pure (φ ⊗ᵠ φ))
    (H : ⟪pure ψ, pure φ⟫_Prob < (1 : ℝ)) :
    ⟪pure ψ, pure φ⟫_Prob = (0 : ℝ) := by
  have hf : ⟪pure f, pure f⟫_Prob = 1 :=
    Prob.ext (by simp [pure_inner, Braket.dot_self_eq_one])
  have h1 : ⟪pure ψ, pure φ⟫_Prob * ⟪pure ψ, pure φ⟫_Prob = ⟪pure ψ, pure φ⟫_Prob * 1 := by
    rw [← hf, ← prod_inner_prod, ← prod_inner_prod, ← pure_prod_pure, ← pure_prod_pure,
      ← pure_prod_pure, ← pure_prod_pure, ← hψ, ← hφ, inner_U_conj]
  have h2 := Prob.ext_iff.mp h1
  push_cast at h2
  nlinarith [Prob.zero_le_coe (p := ⟪pure ψ, pure φ⟫_Prob)]

end MState
