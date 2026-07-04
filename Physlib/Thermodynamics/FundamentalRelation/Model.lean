/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Thermodynamics.Foundation.Entropy
public import Physlib.Thermodynamics.FundamentalRelation.Basic

/-!
# The thermodynamic bridge

## i. Overview

A `ThermoModel Φ` is a model of a smooth coordinate fundamental relation `Φ`
(Callen's `S = S(U, V, N)`) as a concrete abstract thermodynamic core.
It supplies a single system `Γ`, a map `stateOf` from positive extensive states into the
abstract state space, an entropy representation, and two linking
hypotheses — `entropy_agrees` (the coordinate entropy equals the abstract entropy on mapped
states) and `comparison` (the Lieb-Yngvason Comparison Hypothesis on `Γ`).

From these we *derive* the **Entropy Principle** for the model via `entropyPrinciple`: on mapped
states, Callen's entropy order coincides with adiabatic accessibility,
`Φ.S e₁ ≤ Φ.S e₂ ↔ stateOf e₁ ≺ stateOf e₂` .

## ii. Key results

- `ThermoModel` — a model of `Φ`, bundling a core, a coordinate map, an entropy representation,
  and the two linking hypotheses `entropy_agrees` and `comparison`.
- `ThermoModel.entropyPrinciple` — the derived Entropy Principle: entropy order coincides with
  adiabatic accessibility on mapped states.

## iii. Table of contents

- A. The model
- B. The entropy principle (derived)

## iv. References

- E.H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
  Thermodynamics*, Physics Reports **310** (1999) 1-96. The Entropy Principle (monotonicity),
  §II.B eq. (2.3); the Comparison Hypothesis as a hypothesis, §II; proved for simple systems,
  §III-IV.
- H.B. Callen, *Thermodynamics and an Introduction to Thermostatistics*, 2nd ed., Wiley
  (1985). The fundamental relation `S = S(U, V, N)`, §1.10.
-/

@[expose] public section

namespace Thermodynamics

universe u

/-! ## A. The model

`ThermoModel Φ` exhibits the smooth fundamental relation `Φ` as a model of the abstract
interface. It maps only positive extensive states into one abstract system `Γ`, identifies
the two entropies there (`entropy_agrees`), and assumes the Comparison Hypothesis on `Γ`
(`comparison`). -/

/-- A model of the smooth coordinate fundamental relation `Φ` inside the abstract
accessibility-and-entropy interface.

The bundled `core` is only a `ThermoSystemCore`, so this bridge needs no `ThermoWorld`.
`stateOf` maps positive extensive states into a single abstract system `Γ`; `entropy_agrees`
identifies the coordinate and abstract entropies there; and `comparison` is the Lieb-Yngvason
Comparison Hypothesis on `Γ`. -/
structure ThermoModel (Φ : FundamentalRelation) where
  /-- The abstract type of thermodynamic systems used by this model. -/
  {System : Type u}
  /-- The operational thermodynamic core. No Lieb-Yngvason axioms are required by the bridge. -/
  core : ThermoSystemCore System
  /-- The single abstract system the coordinate states map into. -/
  Γ : System
  /-- The abstract entropy representation associated to the core. -/
  entropy : @EntropyRepresentation System core
  /-- The abstract state of a coordinate state: sends each positive extensive state `(U, V, N)`
  to its state in the abstract system `Γ`. -/
  stateOf : ExtensiveState → core.State Γ
  /-- The coordinate entropy agrees with the abstract entropy on mapped states:
  `Φ.S e = entropy.S ⟨Γ, stateOf e⟩`. Equivalently, `stateOf` is entropy-preserving. -/
  entropy_agrees : ∀ e : ExtensiveState,
    Φ.S e.U e.V e.N = entropy.S ⟨Γ, stateOf e⟩
  /-- The Lieb-Yngvason Comparison Hypothesis on the system `Γ`: any two states of `Γ` are
  adiabatically comparable. -/
  comparison : ComparisonHypothesis (T := core) Γ

namespace ThermoModel

/-! ## B. The entropy principle

The Entropy Principle for the model is a theorem, obtained by discharging the entropy
representation's conditional monotonicity with the Comparison Hypothesis. -/

/-- The **Entropy Principle** for the model: on mapped states, Callen's coordinate-entropy order
coincides with primitive adiabatic accessibility, `Φ.S e₁ ≤ Φ.S e₂ ↔ stateOf e₁ ≺ stateOf e₂`.
This is the entropy representation's conditional `Monotonicity` (valid on comparable states)
discharged everywhere on `Γ` by `comparison`. -/
lemma entropyPrinciple {Φ : FundamentalRelation} (M : ThermoModel Φ) (e₁ e₂ : ExtensiveState) :
    (Φ.S e₁.U e₁.V e₁.N ≤ Φ.S e₂.U e₂.V e₂.N) ↔
      M.core.le (M.stateOf e₁) (M.stateOf e₂) := by
  letI := M.core
  rw [M.entropy_agrees e₁, M.entropy_agrees e₂]
  exact (M.entropy.Monotonicity (M.stateOf e₁) (M.stateOf e₂)
    (M.comparison (M.stateOf e₁) (M.stateOf e₂))).symm

end ThermoModel

end Thermodynamics
