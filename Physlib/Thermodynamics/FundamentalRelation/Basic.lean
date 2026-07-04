/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The fundamental relation of a simple thermodynamic system

## i. Overview

In the entropy representation, all thermodynamic information about a simple system is
contained in its **fundamental relation** `S = S(U, V, N)`, the entropy as a
function of the extensive parameters internal energy `U`, volume `V`, and particle number `N`.

Design choices:
- **`S` is kept total** (`ℝ → ℝ → ℝ → ℝ`); positivity is carried by field hypotheses and by
  `ExtensiveState`.
- **The domain of regularity is the positive orthant** (`posOrthant` / `ExtensiveState`); `S` is
  not assumed regular where a coordinate vanishes.
- **`StrictMonoOn` in `U` is derived**, not a field: `dS_dU_pos` (pointwise `∂S/∂U > 0`) is the
  primitive, and `strictMonoOn_U` follows from it.

This file records the assumptions used by the current entropy-representation layer:
degree-one homogeneity (`homogeneous`), smoothness on the positive orthant (`smooth`), and
positive energy derivative (`dS_dU_pos`, equivalently `T > 0`). These are bundled in
`FundamentalRelation`. Stability, concavity, and third-law behavior are not fields of this
structure.

## ii. Key results

- `ExtensiveState` — a positive extensive state `(U, V, N)`, the physical coordinate domain.
- `posOrthant` — the open positive orthant of `ℝ × ℝ × ℝ` on which a relation is regular.
- `FundamentalRelation` — the smooth entropy surface `S(U, V, N)` with its three fields.
- `FundamentalRelation.strictMonoOn_U` — entropy is strictly increasing in `U` (derived from
  `dS_dU_pos`).

## iii. Table of contents

- A. Extensive states and the coordinate domain
- B. The fundamental relation
- C. Derived monotonicity in energy

## iv. References

- H.B. Callen, *Thermodynamics and an Introduction to Thermostatistics*, 2nd ed., Wiley (1985).
-/

@[expose] public section

namespace Thermodynamics

open scoped ContDiff

/-! ## A. Extensive states and the coordinate domain

A `FundamentalRelation` is regular only on physically admissible states — those with strictly
positive `U`, `V`, `N`. We carry that positivity in two ways: `ExtensiveState` for the physical
states the later bridge charts, and `posOrthant` for the open set on which smoothness and the
energy derivative are asserted. Keeping positivity here, rather than in the type of `S`, lets the
calculus treat `S` as an ordinary total function. -/

/-- A positive **extensive state** `(U, V, N)` of a simple system: internal energy,
volume and particle number, all strictly positive. This is the physical domain over
which a `FundamentalRelation` is smooth, homogeneous, and monotone. -/
structure ExtensiveState where
  /-- Internal energy. -/
  U : ℝ
  /-- Volume. -/
  V : ℝ
  /-- Particle number. -/
  N : ℝ
  /-- Positivity of the internal energy. -/
  hU : 0 < U
  /-- Positivity of the volume. -/
  hV : 0 < V
  /-- Positivity of the particle number. -/
  hN : 0 < N

/-- The positive orthant of `ℝ × ℝ × ℝ` — the coordinate domain on which a
`FundamentalRelation` is regular. -/
def posOrthant : Set (ℝ × ℝ × ℝ) := {p | 0 < p.1 ∧ 0 < p.2.1 ∧ 0 < p.2.2}

/-! ## B. The fundamental relation

The structure bundles the entropy surface `S` with Postulate III: it is C^∞ (`smooth`),
has positive energy derivative (`dS_dU_pos`, giving `T > 0`), and is homogeneous of degree one
(`homogeneous`, i.e. extensivity). Concavity/stability (Postulate II) is deferred. -/

/-- A **fundamental relation** in the entropy representation: a total entropy function
`S(U, V, N)` that is C^∞, has positive energy derivative, and is homogeneous of degree one on the
positive orthant. -/
structure FundamentalRelation where
  /-- The entropy as a total function of `(U, V, N)`. Positivity is imposed by the field
  hypotheses below, not by the type of `S`. -/
  S : ℝ → ℝ → ℝ → ℝ
  /-- Regularity: `S` is C^∞ on the positive orthant. -/
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ × ℝ => S p.1 p.2.1 p.2.2) posOrthant
  /-- Postulate III (`T > 0`): for positive states, `∂S/∂U > 0`, i.e.
  `1 / T > 0` pointwise. This yields positive temperature without invoking concavity. -/
  dS_dU_pos : ∀ U V N, 0 < U → 0 < V → 0 < N → 0 < deriv (fun u => S u V N) U
  /-- Extensivity: `S` is homogeneous of degree one on the positive orthant,
  `S(lU, lV, lN) = l · S(U, V, N)` for `l > 0` (Callen's extensivity of the entropy). -/
  homogeneous : ∀ ⦃l : ℝ⦄, 0 < l → ∀ U V N, 0 < U → 0 < V → 0 < N →
    S (l * U) (l * V) (l * N) = l * S U V N

/-! ## C. Derived monotonicity in energy

Strict monotonicity of entropy in `U` is derived from the pointwise `dS_dU_pos` via
`strictMonoOn_of_deriv_pos`, and `T > 0` is a consequence. -/

/-- Derived: for fixed positive `V, N`, entropy is strictly increasing in the energy on
`Ioi 0`. Obtained from `dS_dU_pos` via `strictMonoOn_of_deriv_pos`. -/
lemma FundamentalRelation.strictMonoOn_U (Φ : FundamentalRelation) (V N : ℝ)
    (hV : 0 < V) (hN : 0 < N) :
    StrictMonoOn (fun U => Φ.S U V N) (Set.Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · change ContinuousOn ((fun p : ℝ × ℝ × ℝ => Φ.S p.1 p.2.1 p.2.2) ∘
      fun U : ℝ => (U, (V, N))) (Set.Ioi 0)
    exact Φ.smooth.continuousOn.comp
      (by
        show ContinuousOn (fun U : ℝ => (U, (V, N))) (Set.Ioi 0)
        fun_prop)
      (by
        intro U hU
        exact ⟨hU, hV, hN⟩)
  · rw [interior_Ioi]
    intro U hU
    exact Φ.dS_dU_pos U V N hU hV hN

end Thermodynamics
