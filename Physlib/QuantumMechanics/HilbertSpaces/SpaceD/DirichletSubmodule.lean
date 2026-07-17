/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
/-!

# Dirichlet submodule

## i. Overview

## ii. Key results

## iii. Table of contents

- A. Definitions

## iv. References

-/

@[expose] public section

noncomputable section
namespace QuantumMechanics
namespace SpaceDHilbertSpace

open MeasureTheory SchwartzMap

variable {d : ℕ} (Ω : Set (Space d)) (μ : Measure (Space d)) [μ.HasTemperateGrowth]

/-!
## A. Definitions
-/

/-- The Schwartz maps which vanish on `frontier Ω`. -/
def DirichletSchwartz : Submodule ℂ 𝓢(Space d, ℂ) where
  carrier := {f : 𝓢(Space d, ℂ) | ∀ x : frontier Ω, f x = 0}
  add_mem' := by simp_all
  zero_mem' := by simp
  smul_mem' := by simp_all

/-- The submodule of the Hilbert space on `Ω` consisting of the equivalence classes
  of Schwartz maps which vanish on `frontier Ω`. -/
def DirichletSubmoduleOn : Submodule ℂ (SpaceDHilbertSpaceOn Ω μ) :=
  (DirichletSchwartz Ω).map (subspaceProjection Ω μ ∘ₗ schwartzIncl μ)

end SpaceDHilbertSpace
end QuantumMechanics
end
