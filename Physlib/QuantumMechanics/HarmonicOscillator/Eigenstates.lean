/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Mathematics.InnerProductSpace.Gaussian
public import Physlib.Mathematics.HasTemperateGrowth
public import Physlib.Mathematics.KroneckerDelta.Basic
public import Physlib.Mathematics.SpecialFunctions.PhysHermite
public import Physlib.QuantumMechanics.HarmonicOscillator.Basic
public import Physlib.Meta.Sorry
/-!

# Energy eigenstates of the quantum harmonic oscillator

## i. Overview

The quantum harmonic oscillator in `d` dimensions is exactly solvable - the energy eigenvalues
and eigenfunction can be computed analytically.

The ground-state wavefunction is a normalized Gaussian with covariance controlled
by the harmonic oscillator's characteristic lengths. A general state is then obtained by acting
on the ground state with the raising operators and is labelled by `d` integer quantum numbers.
Their wavefunctions are given by products of (physicist's) Hermite polynomials multiplying
the ground-state Gaussian.

When the potential is isotropic another description of the energy eigenstates is possible;
energy eigenspaces carry SO(d) representations and eigenfunctions can be written in terms of
hyperspherical harmonics. In such cases the energies only depend on the radial quantum number.

## ii. Key results

## iii. Table of contents

- A. Cartesian basis
  - A.1. Energy eigenvalues
  - A.2. Eigenfunctions
  - A.3. Eigenstates

## iv. References

-/
@[expose] public section

TODO "Prove that the QHO eigenstates in the Cartesian basis (Hermite polynomials) are orthonormal."

TODO "Prove that acting on the QHO eigenstates with the ladder operators shifts the integer quantum
  numbers by one."

TODO "Prove that the QHO eigenstates in the Cartesian basis (Hermite polynomials) satisfy the TISE."

TODO "Prove that the (point) spectrum of the self-adjoint Hamiltonian is `Set.range Q.eigenEnergy`."

TODO "Prove that the ground-state of the QHO is non-degenerate."

TODO "Determine the energy eigenstates of the isotropic quantum harmonic oscillator
  in the 'spherical basis' in terms of spherical harmonics."

noncomputable section
namespace QuantumMechanics
namespace HarmonicOscillator

open Complex Constants Finset InnerProductSpace Polynomial SchwartzMap Space SpaceDHilbertSpace
open scoped Nat Real ComplexConjugate

variable {d : ℕ} (Q : HarmonicOscillator d) (n n' : Fin d → ℕ) (x : Space d)

/-!
## A. Cartesian basis
-/

/-!
## A.1. Energy eigenvalues
-/

/-- The energy eigenvalues, `∑ i, ℏ ωᵢ (nᵢ + ½)`. -/
def eigenEnergy : ℝ := ∑ i, ℏ * Q.ω i * (n i + 1 / 2)

lemma eigenEnergy_eq : Q.eigenEnergy n = ∑ i, ℏ * Q.ω i * (n i + 1 / 2) := rfl

lemma eigenEnergy_strictMono : StrictMono Q.eigenEnergy := by
  intro n n' h
  obtain ⟨h, i, hi⟩ := Pi.lt_def.mp h
  exact sum_lt_sum (fun i _ ↦ by simp [h i]) ⟨i, mem_univ i, by simp [hi]⟩

/-!
### A.2. Eigenfunctions
-/

/-- The `i`th normalization constant for `Q.eigenfunction n`, `1 / √(2 ^ nᵢ * nᵢ! * √π * ξᵢ)`. -/
def eigenCoeff (i : Fin d) : ℝ := 1 / √(2 ^ n i * (n i)! * √π * Q.ξ i)

lemma eigenCoeff_eq (i : Fin d) : Q.eigenCoeff n i = 1 / √(2 ^ n i * (n i)! * √π * Q.ξ i) := rfl

/-- The eigenfunction labelled by the integer quantum numbers `n : Fin d → ℕ`, defined as a product
  of (physicist's) Hermite polynomials multiplying a Gaussian with covariance controlled
  by the characteristic lengths, `Q.ξ`. -/
def eigenfunction : 𝓢(Space d, ℂ) :=
  compCLMOfContinuousLinearEquiv ℂ Q.ξEquiv.symm <| smulLeftCLM ℂ
    (fun x ↦ ∏ i, Q.eigenCoeff n i * physHermite (n i) (x i)) (stdGaussian (Space d) ℂ)

lemma eigenfunction_eq :
    Q.eigenfunction n = compCLMOfContinuousLinearEquiv ℂ Q.ξEquiv.symm (smulLeftCLM ℂ
      (fun x ↦ ∏ i, Q.eigenCoeff n i * physHermite (n i) (x i)) (stdGaussian (Space d) ℂ)) := rfl

lemma eigenfunction_apply :
    Q.eigenfunction n x =
      ∏ i, Q.eigenCoeff n i *
        physHermite (n i) (x i / Q.ξ i) * cexp (-2⁻¹ * (x i / Q.ξ i) ^ 2) := by
  rw [eigenfunction_eq, compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    smulLeftCLM_apply_apply (by fun_prop)]
  simp [div_eq_mul_inv, prod_mul_distrib, exp_neg, norm_sq_eq, mul_sum, mul_comm, exp_sum]

/-!
### A.3. Eigenstates
-/

/-- `Q.eigenfunction n` as an element of the Schwartz submodule of the Hilbert space. -/
def eigenstate : SchwartzSubmodule d := schwartzEquiv _ (Q.eigenfunction n)

lemma eigenstate_eq : Q.eigenstate n = schwartzEquiv _ (Q.eigenfunction n) := rfl

/-- The energy eigenstates are orthonormal. -/
@[simp, sorryful]
lemma eigenstates_orthonormal : ⟪(Q.eigenstate n : Q.HS), Q.eigenstate n'⟫_ℂ = δ[n,n'] :=
  -- It might help to first prove an analogue of
  -- `MeasureTheory.integral_fin_nat_prod_(volume_)eq_prod` for `Space d` in order to split
  -- `∫ x : Space d, Π i : Fin d, fᵢ (x i) = ∏ i : Fin d, ∫ xᵢ : ℝ, fᵢ xᵢ`, using `Space.equivPi`.
  sorry

end HarmonicOscillator
end QuantumMechanics
end
