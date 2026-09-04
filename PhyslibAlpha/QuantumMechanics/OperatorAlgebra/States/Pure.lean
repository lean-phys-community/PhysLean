/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.States.Convex

/-!
# Pure states

A pure state is an extreme point of the convex state space. Equivalently, it
cannot be expressed as a genuinely nontrivial probabilistic mixture of two
different states. This definition is intrinsic to the general C⋆-algebraic
theory; projector and rank-one characterizations belong to concrete or
finite-dimensional representation theory.
-/

@[expose] public section

namespace OperatorAlgebra

namespace State

variable {A : Type*} [OperatorAlgebra A]

/-- A pure state has no residual classical uncertainty: it cannot be produced by randomizing over
other, genuinely different preparations. Formally, an extreme point of the convex state space —
one lying on no open segment between two other points of the space. -/
def IsPure (ω : State A) : Prop :=
  ω.toContinuousLinearMap ∈ (stateSpace (A := A)).extremePoints ℝ

/-- The abstract "extreme point" definition of purity matches the physically direct one: `ω` is
pure iff every nontrivial (`0 < t < 1`) mixture `mix φ ψ t` equal to `ω` forces `φ = ψ = ω`. -/
lemma pure_iff_binary_decompositions_trivial (ω : State A) :
    IsPure ω ↔
      ∀ (φ ψ : State A) (t : unitInterval), t ≠ 0 → t ≠ 1 →
        mix φ ψ t = ω → φ = ω ∧ ψ = ω := by
  simp only [IsPure, mem_extremePoints]
  constructor
  · rintro ⟨-, hext⟩ φ ψ t ht₀ ht₁ hmix
    have hseg := (mem_openSegment_iff_exists_mix ω φ ψ).2 ⟨t, ht₀, ht₁, hmix⟩
    obtain ⟨hφ, hψ⟩ :=
      hext φ.toContinuousLinearMap ⟨φ, rfl⟩ ψ.toContinuousLinearMap ⟨ψ, rfl⟩ hseg
    exact ⟨toContinuousLinearMap_injective hφ, toContinuousLinearMap_injective hψ⟩
  · intro h
    refine ⟨⟨ω, rfl⟩, ?_⟩
    rintro _ ⟨φ, rfl⟩ _ ⟨ψ, rfl⟩ hseg
    obtain ⟨t, ht₀, ht₁, hmix⟩ := (mem_openSegment_iff_exists_mix ω φ ψ).1 hseg
    obtain ⟨rfl, rfl⟩ := h φ ψ t ht₀ ht₁ hmix
    exact ⟨rfl, rfl⟩

/-- A state is mixed (not pure) exactly when some genuine coin-flip between two states reproduces
it, with at least one of the two differing from `ω`. -/
lemma not_pure_iff_nontrivial_binary_decomposition (ω : State A) :
    ¬ IsPure ω ↔
      ∃ (φ ψ : State A) (t : unitInterval), t ≠ 0 ∧ t ≠ 1 ∧
        mix φ ψ t = ω ∧ (φ ≠ ω ∨ ψ ≠ ω) := by
  rw [pure_iff_binary_decompositions_trivial]
  push Not
  simp only [imp_iff_not_or]

/-- Every preparation is either pure or a genuine mixture of two other states: purity and
mixedness exhaust all states. Note `φ, ψ` are not asserted to be *pure* — this is just
`not_pure_iff_nontrivial_binary_decomposition` as a dichotomy, not the stronger (unproven here)
Krein–Milman claim that every mixed state decomposes into pure states. -/
lemma pure_or_nontrivial_binary_mixture (ω : State A) :
    IsPure ω ∨
      ∃ (φ ψ : State A) (t : unitInterval), t ≠ 0 ∧ t ≠ 1 ∧
        mix φ ψ t = ω ∧ (φ ≠ ω ∨ ψ ≠ ω) := by
  by_cases hω : IsPure ω
  · exact Or.inl hω
  · exact Or.inr ((not_pure_iff_nontrivial_binary_decomposition ω).mp hω)

end State

end OperatorAlgebra
