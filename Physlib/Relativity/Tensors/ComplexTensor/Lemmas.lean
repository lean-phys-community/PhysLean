/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Basic
/-!

## Lemmas related to complex Lorentz tensors.

-/

@[expose] public section

open Matrix
open MatrixGroups
open Complex
open TensorProduct

noncomputable section

namespace complexLorentzTensor
open TensorSpecies
open Tensor

lemma antiSymm_contr_symm {A : ℂT[.up, .up]} {S : ℂT[.down, .down]}
    (hA : {A | μ ν = - (A | ν μ)}ᵀ) (hs : {S | μ ν = S | ν μ}ᵀ) :
    {A | μ ν ⊗ S | μ ν = - A | μ ν ⊗ S | μ ν}ᵀ := by
  conv_lhs =>
    rw [hA, hs, prodT_permT_left, prodT_permT_right, contrT_comm, permT_permT,
      contrT_permT, contrT_permT, permT_permT]
  simp only[LinearMap.neg_apply, map_neg]
  congr 1
  apply permT_congr_eq_id
  decide

end complexLorentzTensor

end
