/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.MultiIndex
/-!
# Iterated derivatives on `Space d`

## i. Overview

This module defines iterated coordinate derivatives on `Space d` indexed by multi-indices.

The implementation is intentionally modest. A multi-index is first expanded into a canonical list
of coordinate directions, and the iterated derivative is then defined by repeated application of
`Space.deriv` along that list.

## ii. Key results

- `Space.iteratedDeriv` : iterated coordinate derivatives on `Space d`.
- `∂^[I] f` : notation for the iterated derivative indexed by the multi-index `I`.

## iii. Table of contents

- A. Iterated derivatives on `Space d`

## iv. References

-/

@[expose] public section

namespace Space

open Physlib

variable {M : Type} {d : ℕ}

/-!
## A. Iterated derivatives on `Space d`

-/

/-- The iterated coordinate derivative on `Space d` indexed by a multi-index. -/
noncomputable def iteratedDeriv [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (I : MultiIndex d) (f : Space d → M) : Space d → M :=
  I.toList.foldr (fun i g => deriv i g) f

@[inherit_doc iteratedDeriv]
macro "∂^[" I:term "]" : term => `(iteratedDeriv $I)

@[simp]
lemma iteratedDeriv_zero [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Space d → M) : ∂^[0] f = f := by
  simp [iteratedDeriv, Physlib.MultiIndex.toList_zero]

@[simp]
lemma iteratedDeriv_increment_zero [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (I : MultiIndex d.succ) (f : Space d.succ → M) :
    ∂^[MultiIndex.increment I 0] f = ∂[0] (∂^[I] f) := by
  simp [iteratedDeriv, Physlib.MultiIndex.toList_increment_zero]

@[simp]
lemma iteratedDeriv_single [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (i : Fin d) (f : Space d → M) :
    ∂^[MultiIndex.increment 0 i] f = ∂[i] f := by
  simp [iteratedDeriv, Physlib.MultiIndex.toList_single]

end Space
