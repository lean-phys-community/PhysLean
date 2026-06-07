/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComponentIdx.Basic
public import Mathlib.Data.Fin.Tuple.Basic
/-!

# Component indices for one-index tensors

This file defines the canonical equivalence between component indices for a single
color and the basis indices of that color.

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {S : TensorSpecies k C G basisIdx}

namespace Tensor

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
