/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Mathlib.Analysis.Fourier.LpSpace
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
/-!

# The Fourier transform on `SpaceDHilbertSpace`

## i. Overview

In this module we define the Fourier transform on `SpaceDHilbertSpace d` as a unitary operator.
Mathlib's L² Fourier transform `MeasureTheory.Lp.fourierTransformₗᵢ` is a linear isometry
equivalence of `Lp ℂ 2 volume`, hence of `SpaceDHilbertSpace d`, onto itself; packaged as
`fourierUnitary d`.

## ii. Key results

- `fourierUnitary d` : the L² Fourier transform as a unitary
  `SpaceDHilbertSpace d ≃ₗᵢ[ℂ] SpaceDHilbertSpace d`, acting as `𝓕`/`𝓕⁻`
  (`fourierUnitary_apply`, `fourierUnitary_symm_apply`).
- `fourierUnitary_schwartzIncl` : `fourierUnitary d (schwartzIncl f) = schwartzIncl (𝓕 f)`.
- `fourierUnitary_symm_schwartzIncl` : the inverse acts by the inverse Schwartz Fourier transform.
- `fourierUnitary_map_schwartzSubmodule` : `fourierUnitary d` maps the Schwartz submodule onto
  itself.

## iii. Table of contents

- A. The Fourier unitary
- B. Action on the Schwartz submodule

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

open MeasureTheory
open SchwartzMap
open scoped FourierTransform

variable {d : ℕ}

/-! ## A. The Fourier unitary -/

/-- The L² Fourier transform as a unitary on `SpaceDHilbertSpace d`. -/
noncomputable def fourierUnitary (d : ℕ) :
    SpaceDHilbertSpace d ≃ₗᵢ[ℂ] SpaceDHilbertSpace d := Lp.fourierTransformₗᵢ (Space d) ℂ

/-- `fourierUnitary d` acts as the L² Fourier transform `𝓕`. -/
lemma fourierUnitary_apply (ψ : SpaceDHilbertSpace d) : fourierUnitary d ψ = 𝓕 ψ := rfl

/-- `(fourierUnitary d).symm` acts as the inverse L² Fourier transform `𝓕⁻`. -/
lemma fourierUnitary_symm_apply (ψ : SpaceDHilbertSpace d) : (fourierUnitary d).symm ψ = 𝓕⁻ ψ := rfl

/-! ## B. Action on the Schwartz submodule -/

/-- Applying `fourierUnitary d` to the L² class of a Schwartz map `f` gives the L² class of the
Schwartz Fourier transform `𝓕 f`. -/
lemma fourierUnitary_schwartzIncl (f : 𝓢(Space d, ℂ)) :
    fourierUnitary d (schwartzIncl f) = schwartzIncl (𝓕 f) := SchwartzMap.toLp_fourier_eq f

/-- Applying `(fourierUnitary d).symm` to the L² class of a Schwartz map `f` gives the L² class
of the inverse Schwartz Fourier transform `𝓕⁻ f`. -/
lemma fourierUnitary_symm_schwartzIncl (f : 𝓢(Space d, ℂ)) :
    (fourierUnitary d).symm (schwartzIncl f) = schwartzIncl (𝓕⁻ f) :=
SchwartzMap.toLp_fourierInv_eq f

/-- Pulling the L² class of `𝓕 f` back through the Fourier unitary recovers the L² class of `f`. -/
lemma fourierUnitary_symm_schwartzIncl_fourier (f : 𝓢(Space d, ℂ)) :
    (fourierUnitary d).symm (schwartzIncl (𝓕 f)) = schwartzIncl f := by
  rw [← fourierUnitary_schwartzIncl, LinearIsometryEquiv.symm_apply_apply]

/-- The Fourier unitary maps the Schwartz submodule onto itself. -/
lemma fourierUnitary_map_schwartzSubmodule :
    (SchwartzSubmodule d).map (fourierUnitary d).toLinearEquiv.toLinearMap
 = SchwartzSubmodule d := by
  apply le_antisymm
  · rintro x ⟨y, ⟨f, rfl⟩, rfl⟩
    exact ⟨𝓕 f, (fourierUnitary_schwartzIncl f).symm⟩
  · rintro x ⟨g, rfl⟩
    exact ⟨(fourierUnitary d).symm (schwartzIncl g),
      ⟨𝓕⁻ g, (fourierUnitary_symm_schwartzIncl g).symm⟩, (fourierUnitary d).apply_symm_apply _⟩

end SpaceDHilbertSpace
end QuantumMechanics
