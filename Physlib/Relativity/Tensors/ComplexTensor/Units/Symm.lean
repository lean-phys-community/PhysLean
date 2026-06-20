/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Units.Basic
/-!

## Symmetry lemmas relating to units

-/

@[expose] public section

open Matrix

namespace complexLorentzTensor

/-!

## Symmetry properties

-/
open TensorSpecies
open Tensor

/-- Swapping indices of `coContrUnit` returns `contrCoUnit`: `{δ' | μ ν = δ | ν μ}ᵀ`. -/
lemma coContrUnit_symm : {δ' | μ ν = δ | ν μ}ᵀ := by
  rw [coContrUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `contrCoUnit` returns `coContrUnit`: `{δ | μ ν = δ' | ν μ}ᵀ`. -/
lemma contrCoUnit_symm : {δ | μ ν = δ' | ν μ}ᵀ := by
  rw [contrCoUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `dualLeftLeftUnit` returns
  `leftDualLeftUnit`: `{δL' | α α' = δL | α' α}ᵀ`. -/
lemma dualLeftLeftUnit_symm : {δL' | α α' = δL | α' α}ᵀ := by
  rw [dualLeftLeftUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `leftDualLeftUnit` returns
  `dualLeftLeftUnit`: `{δL | α α' = δL' | α' α}ᵀ`. -/
lemma leftDualLeftUnit_symm : {δL | α α' = δL' | α' α}ᵀ := by
  rw [leftDualLeftUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `dualRightRightUnit` returns `rightDualRightUnit`:
`{δR' | β β' = δR | β' β}ᵀ`.
-/
lemma dualRightRightUnit_symm : {δR' | β β' = δR | β' β}ᵀ := by
  rw [dualRightRightUnit, unitTensor_eq_permT_dual]
  rfl

/-- Swapping indices of `rightDualRightUnit` returns `dualRightRightUnit`:
`{δR | β β' = δR' | β' β}ᵀ`.
-/
lemma rightDualRightUnit_symm : {δR | β β' = δR' | β' β}ᵀ := by
  rw [rightDualRightUnit, unitTensor_eq_permT_dual]
  rfl

end complexLorentzTensor
