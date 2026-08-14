/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Physlib.SpaceAndTime.Space.Module
/-!

# Position states

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

noncomputable section

open scoped SchwartzMap

variable {d : ℕ}

/-- Position state as a member of the strong dual of the Schwartz space. -/
def positionState (x : Space d) : StrongDual ℂ 𝓢(Space d, ℂ) := TemperedDistribution.delta x

/-- The defining property of position states. -/
lemma positionState_apply (x : Space d) (f : 𝓢(Space d, ℂ)) : positionState x f = f x := rfl

/-- Two Schwartz maps are equal if they are equal on all position states. -/
lemma eq_of_eq_positionState {f g : 𝓢(Space d, ℂ)}
    (h : ∀ x, positionState x f = positionState x g) : f = g := by
  ext x
  exact h x

end
end SpaceDHilbertSpace
end QuantumMechanics
