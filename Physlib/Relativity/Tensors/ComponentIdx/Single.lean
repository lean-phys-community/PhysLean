/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComponentIdx.Basic
/-!

# Component indices for one-index tensors

## i. Overview

This file defines the canonical equivalence between component indices for a single
color and the basis indices of that color.

## ii. Key results

- `TensorSpecies.Tensor.ComponentIdx.single` is the equivalence between
  `ComponentIdx ![c]` and `basisIdx c`.
- `TensorSpecies.Tensor.ComponentIdx.single_apply` and
  `TensorSpecies.Tensor.ComponentIdx.single_symm_apply` are simp lemmas for the two
  directions of this equivalence.

## iii. Table of contents

- A. Single-index equivalence

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)}
  {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

/-!

## A. Single-index equivalence

-/

/-- The equivalence between component indices for a single color and the basis indices
of that color. -/
def ComponentIdx.single {c : C} :
    ComponentIdx (S := S) ![c] ≃ basisIdx c where
  toFun b := basisIdxCongr (by simp) (b 0)
  invFun b := fun _ => basisIdxCongr (by simp) b
  left_inv b := by
    ext i
    cases Fin.fin_one_eq_zero i
    simp [basisIdxCongr]
    rfl
  right_inv b := by
    simp [basisIdxCongr]
    rfl

@[simp]
lemma ComponentIdx.single_apply {c : C} (b : ComponentIdx (S := S) ![c]) :
    ComponentIdx.single (S := S) b = basisIdxCongr (by simp) (b 0) := rfl

@[simp]
lemma ComponentIdx.single_symm_apply {c : C} (b : basisIdx c) (i : Fin 1) :
    (ComponentIdx.single (S := S) (c := c)).symm b i = basisIdxCongr (by simp) b := rfl

end Tensor

end TensorSpecies
