/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Physlib.SpaceAndTime.Space.Module
/-!

# Momentum states

We define plane waves as a member of the dual of the
Schwartz submodule of the Hilbert space.

-/

@[expose] public section

namespace QuantumMechanics

namespace SpaceDHilbertSpace

noncomputable section

open FourierTransform MeasureTheory SchwartzMap

variable {d : ℕ}

/-- Plane wave as a member of the strong dual of the Schwartz space.

  For a given `k` this corresponds to the non-normalizable plane wave `exp (2π I k ⬝ᵥ x)`. -/
def momentumState (k : Space d) : StrongDual ℂ 𝓢(Space d, ℂ) :=
  TemperedDistribution.delta k ∘L fourierTransformCLM ℂ

@[simp]
lemma momentumState_apply (k : Space d) (ψ : 𝓢(Space d, ℂ)) :
    momentumState k ψ = 𝓕 ψ k := rfl

/-- Two Schwartz maps are equal if they are equal on all momentum states. -/
lemma eq_of_eq_momentumState {ψ φ : 𝓢(Space d, ℂ)}
    (h : ∀ k, momentumState k ψ = momentumState k φ) : ψ = φ :=
  fourierCLE ℂ 𝓢(Space d, ℂ) |>.injective <| ext h

end
end SpaceDHilbertSpace
end QuantumMechanics
