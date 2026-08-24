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
- `schwartzIncl_fourier_eq` : `𝓕 (schwartzIncl f) = schwartzIncl (𝓕 f)`.
- `schwartzIncl_fourierInv_eq` : the inverse acts by the inverse Schwartz Fourier transform.
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
@[simp]
lemma fourierUnitary_apply (ψ : SpaceDHilbertSpace d) : fourierUnitary d ψ = 𝓕 ψ := rfl

/-- `(fourierUnitary d).symm` acts as the inverse L² Fourier transform `𝓕⁻`. -/
@[simp]
lemma fourierUnitary_symm_apply (ψ : SpaceDHilbertSpace d) : (fourierUnitary d).symm ψ = 𝓕⁻ ψ := rfl

/-! ## B. Action on the Schwartz submodule -/

/-- Applying `fourierUnitary d` to the L² class of a Schwartz map `f` gives the L² class of the
Schwartz Fourier transform `𝓕 f`. -/
lemma schwartzIncl_fourier_eq (f : 𝓢(Space d, ℂ)) :
    𝓕 (schwartzIncl volume f) = schwartzIncl volume (𝓕 f) := SchwartzMap.toLp_fourier_eq f

/-- Applying `𝓕⁻` to the L² class of a Schwartz map `f` gives the L² class of the inverse
Schwartz Fourier transform `𝓕⁻ f`. -/
lemma schwartzIncl_fourierInv_eq (f : 𝓢(Space d, ℂ)) :
    𝓕⁻ (schwartzIncl volume f) = schwartzIncl volume (𝓕⁻ f) :=
  SchwartzMap.toLp_fourierInv_eq f

/-- Pulling the L² class of `𝓕 f` back through the Fourier unitary recovers the L² class of `f`. -/
@[simp]
lemma fourierInv_schwartzIncl_fourier (f : 𝓢(Space d, ℂ)) :
    𝓕⁻ (schwartzIncl volume (𝓕 f)) = schwartzIncl volume f := by
  rw [← schwartzIncl_fourier_eq, FourierPair.fourierInv_fourier_eq]

/-- The Fourier unitary maps the Schwartz submodule onto itself. -/
lemma fourierUnitary_map_schwartzSubmodule :
    (SchwartzSubmodule d).map (fourierUnitary d).toLinearMap = SchwartzSubmodule d := by
  apply le_antisymm
  · rintro x ⟨y, ⟨f, rfl⟩, rfl⟩
    exact ⟨𝓕 f, (schwartzIncl_fourier_eq f).symm⟩
  · rintro x ⟨g, rfl⟩
    exact ⟨𝓕⁻ (schwartzIncl volume g), ⟨𝓕⁻ g, (schwartzIncl_fourierInv_eq g).symm⟩, by simp⟩

end SpaceDHilbertSpace
end QuantumMechanics
