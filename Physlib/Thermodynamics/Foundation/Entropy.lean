/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.Thermodynamics.Foundation.Accessibility

/-!
# Entropy representations

## i. Overview

The **Entropy Principle** asks for a single real-valued function `S` on all states of all systems
that encodes the adiabatic-accessibility preorder `≺`: monotone (`X ≺ Y ⟺ S(X) ≤ S(Y)` on
comparable states), additive under composition, and extensive under scaling.
`EntropyRepresentation` bundles `S` together with exactly these three properties.
Lieb-Yngvason build such an `S` explicitly as `S(X) = sup {t | R_t ≺ X}`, where
`R_t = ((1-t)•X₀, t•X₁)` mixes two fixed reference states `X₀ ≺≺ X₁`; the accessibility axioms
A1-A6 are what make that supremum well-defined, monotone, additive and extensive.

The `Monotonicity` field is conditional on `Comparable`. This is faithful to
Lieb-Yngvason's eq. (2.3), which asserts the accessibility/entropy equivalence only for
comparable states, and to the design choice (see `Accessibility.lean`) that comparison
hypotheses are carried explicitly rather than baked into accessibility.

## ii. Key results

- `AllStates` — the sigma-typed domain: every state packaged with its system.
- `EntropyRepresentation` — entropy `S` bundled with monotonicity, additivity, extensivity.
- `entropy_equiv_iff_eq` / `entropy_strict_iff_lt` — the equivalence and strict forms of
  monotonicity (Lieb-Yngvason eq. 2.6).
- `AffineUniqueness` — the statement (not a field, not proved here) that any two
  representations agree up to a positive affine recalibration `S ↦ aS + b`.

## iii. Table of contents

- A. The domain of entropy
- B. Entropy as an order representation
- C. Consequences of the entropy principle
- D. Essential uniqueness

## iv. References

- E.H. Lieb and J. Yngvason, *The Physics and Mathematics of the Second Law of
  Thermodynamics*, Physics Reports **310** (1999) 1-96. The entropy principle and its
  properties (monotonicity, additivity, extensivity), §II.B, eqns (2.3)-(2.6); essential
  uniqueness up to affine scale, §II.C; the canonical construction of `S`, §II.E.
-/

@[expose] public section

namespace Thermodynamics

universe u

/-! ## A. The domain of entropy

An entropy function must range over *all* states of *all* systems at once — compound
systems included — so that additivity `S(X, Y) = S(X) + S(Y)` can even be stated across
systems. We package a state together with the system it belongs to as a sigma type. -/

/-- The type of all states of all systems in a thermodynamic core: a state packaged with
the system it belongs to. This sigma type is the domain of an entropy representation,
letting `S` compare states across different systems. -/
def AllStates (System : Type u) [T : ThermoSystemCore System] :=
  Σ Γ : System, T.State Γ

/-! ## B. Entropy as an order representation

An `EntropyRepresentation` is the Entropy Principle turned into a structure: a real-valued `S`
on `AllStates` that represents `≺` on comparable states (monotonicity), is additive under
composition, and is extensive under positive scaling. -/

/-- An abstract entropy representation of a thermodynamic core: the Lieb-Yngvason Entropy
Principle as a structure. A real-valued `S` on `AllStates` that represents adiabatic
accessibility on comparable states, is additive under composition, and is extensive under
positive scaling. -/
structure EntropyRepresentation (System : Type u) [T : ThermoSystemCore System] where
  /-- The entropy of an arbitrary state, packaged with its system. -/
  S : AllStates System → ℝ
  /-- Monotonicity, Lieb-Yngvason eq. 2.3: for comparable states, accessibility is
  equivalent to entropy increase, `X ≺ Y ↔ S(X) ≤ S(Y)`. Conditioned on `Comparable`
  because the equivalence is claimed only for comparable states. -/
  Monotonicity {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂) :
    Comparable (T := T) X Y → (T.le X Y ↔ S ⟨Γ₁, X⟩ ≤ S ⟨Γ₂, Y⟩)
  /-- Additivity, Lieb-Yngvason eq. 2.4: `S(X, Y) = S(X) + S(Y)` across a composition. -/
  Additivity {Γ₁ Γ₂ : System} (X : T.State Γ₁) (Y : T.State Γ₂) :
    S ⟨T.comp Γ₁ Γ₂, T.state_of_comp_equiv.symm (X, Y)⟩ =
      S ⟨Γ₁, X⟩ + S ⟨Γ₂, Y⟩
  /-- Extensivity, Lieb-Yngvason eq. 2.5: `S(t • X) = t · S(X)` for `t > 0`. -/
  Extensivity {Γ : System} (X : T.State Γ) {t : ℝ} (ht : 0 < t) :
    S ⟨T.scale t Γ, (T.state_of_scale_equiv (ne_of_gt ht)).symm X⟩ =
      t * S ⟨Γ, X⟩

/-! ## C. Consequences of the entropy principle

Immediate rephrasings of monotonicity: on comparable states, adiabatic equivalence is equality
of entropy and strict accessibility is strict entropy increase. These are the "entropy increases
in an irreversible process" readings of `S`. -/

section Consequences

variable {System : Type u} [T : ThermoSystemCore System]

local infix:50 " ≺ " => T.le
local notation:50 X " ≈ " Y => X ≺ Y ∧ Y ≺ X
local infix:50 " ≺≺ " => StrictlyPrecedes (T := T)

/-- For comparable states, adiabatic equivalence is equality of entropy `X ≈ Y ↔ S(X) = S(Y)`. -/
lemma entropy_equiv_iff_eq {E : EntropyRepresentation System} {Γ₁ Γ₂ : System}
    (X : T.State Γ₁) (Y : T.State Γ₂) (h_comp : Comparable (T := T) X Y) :
    (X ≈ Y) ↔ E.S ⟨Γ₁, X⟩ = E.S ⟨Γ₂, Y⟩ := by
  rw [E.Monotonicity X Y h_comp]
  have h_comp_symm : Comparable (T := T) Y X := Comparable.symm h_comp
  rw [E.Monotonicity Y X h_comp_symm]
  exact le_antisymm_iff.symm

/-- For comparable states, strict accessibility is strict entropy increase:
`X ≺≺ Y ↔ S(X) < S(Y)`. -/
lemma entropy_strict_iff_lt {E : EntropyRepresentation System} {Γ₁ Γ₂ : System}
    (X : T.State Γ₁) (Y : T.State Γ₂) (h_comp : Comparable (T := T) X Y) :
    X ≺≺ Y ↔ E.S ⟨Γ₁, X⟩ < E.S ⟨Γ₂, Y⟩ := by
  rw [StrictlyPrecedes]
  rw [E.Monotonicity X Y h_comp]
  have h_comp_symm : Comparable (T := T) Y X := Comparable.symm h_comp
  rw [E.Monotonicity Y X h_comp_symm]
  exact Iff.symm lt_iff_le_not_ge

end Consequences

/-! ## D. Essential uniqueness

Lieb-Yngvason's entropy is unique only up to a positive affine change of scale
`S ↦ aS + b`. We record that statement as a `Prop`. -/

/-- Essential affine uniqueness of entropy representations: any two
representations agree up to a positive affine recalibration `S ↦ a * S + b` (`a > 0`). -/
def AffineUniqueness (System : Type u) [T : ThermoSystemCore System] : Prop :=
  ∀ E E' : EntropyRepresentation System,
    ∃ a b : ℝ, 0 < a ∧ ∀ x, E'.S x = a * E.S x + b

end Thermodynamics
