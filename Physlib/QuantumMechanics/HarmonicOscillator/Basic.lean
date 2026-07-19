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

-/

@[expose] public section

TODO "Define `HarmonicOscillator` as a structure extending `SpaceDQuantumSystem`
  (c.f. `Hydrogen.Basic.lean` for an example). In general the potential is determined by
  a positive-definite, real symmetric matrix `V = ½m(xᵗ·A·x)`.
  Note that such matrices can always be diagonalized so perhaps it suffices to take `A` diagonal.
  A special case with enhanced symmetry is the isotropic harmonic oscillator with `A = ω²·𝕀`."

TODO "Define the raising/lowering/number operators for the quantum harmonic oscillator."

TODO "Prove the commutation relations for the raising/lowering/number/Hamiltonian operators
  of the quantum harmonic oscillator."

TODO "Determine the spectrum of the quantum harmonic oscillator in terms of the eigenvalues
  of the matrix `A ≻ 0` appearing in the potential."

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

-- lemma potentialMatrix_isSymm : Q.potentialMatrix.IsSymm := by simp [potentialMatrix_eq]

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

end HarmonicOscillator
end QuantumMechanics
end
