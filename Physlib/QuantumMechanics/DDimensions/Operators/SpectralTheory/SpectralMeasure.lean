/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.VectorMeasure.Basic
/-!

# Spectral measures

## i. Overview

## ii. Key results

## iii. Table of contents

## iv. References

-/

@[expose] public section

noncomputable section

open MeasureTheory
open Set

/-- A _spectral measure_ on a measurable space `α` is a σ-additive function `Set α → H →L[ℂ] H`
  such that each set is mapped to a star projection on `H`, the empty set and non-measurable sets
  are mapped to zero, and `univ` is mapped to the identity. -/
structure SpectralMeasure
    (α : Type*) [MeasurableSpace α]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    extends VectorMeasure α (H →L[ℂ] H) where
  isStarProjection' : ∀ A, IsStarProjection (measureOf' A)
  univ' : measureOf' univ = 1

namespace SpectralMeasure

variable {α : Type*} [MeasurableSpace α]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (μS : SpectralMeasure α H)

attribute [coe] toVectorMeasure

instance instCoeVectorMeasure : Coe (SpectralMeasure α H) (VectorMeasure α (H →L[ℂ] H)) :=
  ⟨toVectorMeasure⟩

instance instCoeFun : CoeFun (SpectralMeasure α H) fun _ ↦ Set α → H →L[ℂ] H :=
  ⟨fun μS ↦ μS.toVectorMeasure.measureOf'⟩

lemma isStarProjection (A : Set α) : IsStarProjection (μS A) := μS.isStarProjection' A

@[simp]
lemma univ : μS univ = 1 := μS.univ'

end SpectralMeasure

end
