/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.Informal.Basic
public import Physlib.QuantumMechanics.Operators.Momentum
public import Physlib.QuantumMechanics.Operators.Multiplication
public import Physlib.QuantumMechanics.QuantumSystem.Basic
/-!

# The quantum harmonic oscillator

## i. Overview

The harmonic oscillator is one of the most important examples in non-relativistic quantum mechanics.
It describes a particle of mass `m` subject to a positive-definite quadratic potential
in `d` dimensions.

- `Basic.lean` : Properties of the potential, definition of isotropic oscillators,
    kinetic, potential and Hamiltonian operators.
- `LadderOperators.lean` : Definitions of the raising/lowering/number operators
    and their algebraic properties.

## ii. Key results

## iii. Table of contents

- A. Basic properties
  - A.1. Positive mass
  - A.2. Positive natural frequencies
- B. Characteristic lengths
- C. The quadratic potential function
  - C.1. Positive-definite matrix
  - C.2. Quadratic form
  - C.3. Potential function
- D. Isotropic oscillators
- E. Hilbert space
- F. Operators
  - E.1. Kinetic energy
  - E.2. Potential energy
  - E.3. Hamiltonian
- G. As a quantum system

## iv. References

-/

@[expose] public section

TODO "Determine the spectrum of the quantum harmonic oscillator in terms of
  the natural frequencies and integer quantum numbers."

TODO "Determine the energy eigenstates of the quantum harmonic oscillator
  in the 'Cartesian basis' in terms of Hermite polynomials."

TODO "Determine the energy eigenstates of the isotropic quantum harmonic oscillator
  in the 'spherical basis' in terms of spherical harmonics."

noncomputable section
namespace QuantumMechanics

/-- The `d`-dimensional quantum harmonic oscillator. -/
structure HarmonicOscillator (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The natural frequencies (positive). -/
  ω : Fin d → ℝ
  hω : ∀ i, 0 < ω i

variable {d : ℕ} (Q : HarmonicOscillator d) (i : Fin d)

namespace HarmonicOscillator

open Constants SpaceDHilbertSpace MeasureTheory

/-!
## A. Basic properties
-/

/-!
### A.1. Positive mass
-/

@[simp]
lemma m_pos : 0 < Q.m := Q.hm

@[simp]
lemma m_nonneg : 0 ≤ Q.m := Q.hm.le

@[simp]
lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'

/-!
### A.2. Positive natural frequencies
-/

@[simp]
lemma ω_pos : 0 < Q.ω i := Q.hω i

@[simp]
lemma ω_nonneg : 0 ≤ Q.ω i := (Q.hω i).le

@[simp]
lemma ω_ne_zero : Q.ω i ≠ 0 := (Q.hω i).ne'

/-!
## B. Characteristic lengths
-/

/-- The characteristic length `ξ i ≔ √ℏ / (√Q.m * √(Q.ω i))`. -/
def ξ : ℝ := √ℏ / (√Q.m * √(Q.ω i))

lemma ξ_eq : Q.ξ i = √ℏ / (√Q.m * √(Q.ω i)) := rfl

@[simp]
lemma ξ_pos : 0 < Q.ξ i := by simp [ξ_eq]

@[simp]
lemma ξ_nonneg : 0 ≤ Q.ξ i := (Q.ξ_pos i).le

@[simp]
lemma ξ_ne_zero : Q.ξ i ≠ 0 := (Q.ξ_pos i).ne'

lemma ξ_sq : (Q.ξ i) ^ 2 = ℏ / (Q.m * Q.ω i) := by rw [Q.ξ_eq]; field_simp; simp [← mul_rotate]

lemma ξ_inv : (Q.ξ i)⁻¹ = √Q.m * √(Q.ω i) / √ℏ := by simp [ξ_eq]

lemma ξ_inv' : (Q.ξ i)⁻¹ = Q.m * Q.ω i * Q.ξ i / ℏ := by field_simp; simp [ξ_sq, mul_assoc]

/-!
## C. The quadratic potential function
-/

section

open Matrix

/-!
### C.1. Positive-definite matrix
-/

/-- The positive-definite matrix defining the quadratic potential function. -/
def potentialMatrix : Matrix (Fin d) (Fin d) ℝ := diagonal ((2⁻¹ * Q.m) • Q.ω ^ 2)

lemma potentialMatrix_eq : Q.potentialMatrix = diagonal ((2⁻¹ * Q.m) • Q.ω ^ 2) := rfl

lemma potentialMatrix_isHermitian : Q.potentialMatrix.IsHermitian := by simp [potentialMatrix_eq]

@[simp]
lemma potentialMatrix_mulVec (v : Fin d → ℝ) :
    Q.potentialMatrix *ᵥ v = (2⁻¹ * Q.m) • (Q.ω ^ 2 * v) := by
  ext
  simp [potentialMatrix_eq, smul_mulVec, mulVec_diagonal]

/-!
### C.2. Quadratic form
-/

/-- The positive-definite quadratic form associated to the potential matrix. -/
def potentialQuadraticForm : QuadraticForm ℝ (Fin d → ℝ) := Q.potentialMatrix.toQuadraticForm'

/-!
### C.3. Potential function
-/

/-- The quadratic potential function, `½m · ∑ i, ωᵢ²·xᵢ²`. -/
def potentialFunction : Space d → ℝ := Q.potentialQuadraticForm ∘ Space.val

lemma potentialFunction_eq : Q.potentialFunction = Q.potentialQuadraticForm ∘ Space.val := rfl

/-- The potential function for the harmonic oscillator is a.e. strongly measurable. -/
informal_lemma potentialFunction_aestronglyMeasurable where
  deps := [``HarmonicOscillator]
  tag := "QM-HO-potAESM"

end

/-!
## D. Isotropic oscillators
-/

/-- A Harmonic oscillator is isotropic if all natural frequencies are equal. -/
def IsIsotropic : Prop := ∀ i j, Q.ω i = Q.ω j

lemma isIsotropic_def : Q.IsIsotropic ↔ ∀ i j, Q.ω i = Q.ω j := Iff.rfl

lemma isIsotropic_of_one (Q : HarmonicOscillator 1) : Q.IsIsotropic := by simp [isIsotropic_def]

/-!
## E. Hilbert space
-/

/-- The Hilbert space for the quantum harmonic oscillator. -/
@[nolint unusedArguments]
abbrev HS (_ : HarmonicOscillator d) : Type _ := SpaceDHilbertSpace d

/-!
## F. Operators
-/

/-!
### F.1. Kinetic energy
-/

/-- The kinetic energy operator, `p²/2m`. -/
def kineticOperator : Q.HS →ₗ.[ℂ] Q.HS := (2 * Q.m)⁻¹ • momentumSqOperator

/-!
### F.2. Potential energy
-/

section

open MeasureTheory Complex

/-- The potential operator which maps `ψ` to `Q.potentialFunction • ψ`. -/
def potentialOperator : Q.HS →ₗ.[ℂ] Q.HS := 𝓜 volume (ofReal ∘ Q.potentialFunction)

/-- The potential operators for the harmonic oscillator is self-adjoint. -/
informal_lemma potentialOperator_isSelfAdjoint where
  deps := [``HarmonicOscillator.potentialFunction_aestronglyMeasurable]
  tag := "QM-HO-potSA"

end

/-!
### F.3. Hamiltonian
-/

/-- The Hamiltonian for the harmonic oscillator. -/
def hamiltonian : Q.HS →ₗ.[ℂ] Q.HS := Q.kineticOperator + Q.potentialOperator

lemma hamiltonain_eq : Q.hamiltonian = Q.kineticOperator + Q.potentialOperator := rfl

/-- The Hamiltonian for the harmonic oscillator is essentially self-adjoint. -/
informal_lemma hamiltonian_essentially_self_adjoint where
  deps := [``HarmonicOscillator.hamiltonian]
  tag := "QM-HO-hamESA"

/-!
## G. As a quantum system
-/

/-- The `d`-dimensional harmonic oscillator as a quantum system
  (self-adjoint Hamiltonian acting on a Hilbert space). -/
informal_definition toQuantumSystem where
  deps := [``HarmonicOscillator.hamiltonian_essentially_self_adjoint]
  tag := "QM-HO-sys"

end HarmonicOscillator
end QuantumMechanics
end
