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

end HarmonicOscillator
end QuantumMechanics
end
