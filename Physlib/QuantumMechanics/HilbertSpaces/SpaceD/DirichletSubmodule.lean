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
- B. Contained in SchwartzSubmoduleOn

## iv. References

-/

@[expose] public section

noncomputable section
namespace QuantumMechanics
namespace SpaceDHilbertSpaceOn

open MeasureTheory SchwartzMap SpaceDHilbertSpace

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

namespace DirichletSubmoduleOn

variable {Ω μ} in
lemma mem_iff {ψ : SpaceDHilbertSpaceOn Ω μ} :
    ψ ∈ DirichletSubmoduleOn Ω μ ↔
      ∃ f : DirichletSchwartz Ω, subspaceProjection Ω μ (schwartzIncl μ f) = ψ := by
  simp [DirichletSubmoduleOn]

/-!
## B. Contained in SchwartzSubmoduleOn
-/

lemma le_schwartzSubmodule : DirichletSubmoduleOn Ω μ ≤ SchwartzSubmoduleOn Ω μ := by
  intro ψ hψ
  obtain ⟨f, hf⟩ := mem_iff.mp hψ
  apply SchwartzSubmoduleOn.mem_iff.mpr ⟨⟨schwartzIncl μ f, by simp⟩, hf⟩

end DirichletSubmoduleOn
end SpaceDHilbertSpaceOn
end QuantumMechanics
end
