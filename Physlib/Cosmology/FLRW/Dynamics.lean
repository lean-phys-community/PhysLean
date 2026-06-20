/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
/-!

# Dynamical criteria for FLRW cosmology

Placeholder file collecting TODO items for the qualitative consequences of the
Friedmann and acceleration equations: the energy conditions of the cosmic fluid,
the criterion for accelerated expansion, the deceleration parameter in terms of the
density parameters, the condition for eternal expansion, and the existence of a
Big-Bang singularity. This file contains only TODO items; no definitions or lemmas
are formalized yet.

-/

@[expose] public section

TODO "Define the energy conditions for the cosmic perfect fluid: the null `ρ + P/c² ≥ 0`,
  weak `ρ ≥ 0 ∧ ρ + P/c² ≥ 0`, strong `ρ + P/c² ≥ 0 ∧ ρ + 3 P/c² ≥ 0`, and dominant
  `ρ ≥ 0 ∧ |P| ≤ ρ c²` energy conditions."

TODO "Prove that the expansion accelerates iff the cosmic fluid (with the cosmological
  constant folded in as a `w = −1` component) violates the strong energy condition:
  `∂ₜ ∂ₜ a > 0 ↔ ρ_tot + 3 P_tot / c² < 0`."

TODO "Prove the deceleration parameter in terms of the density parameters and equations of
  state, for a spatially flat universe: `q = ½ Σ_x Ω_x (1 + 3 w_x)`; in particular
  `q₀ = ½ Σ_x Ω_{x0} (1 + 3 w_x)`, giving `q₀ = ½ (Ω_{m0} + 2 Ω_{r0} − 2 Ω_Λ)` for ΛCDM."

TODO "Prove that a universe with `K ≤ 0`, nonnegative density and `Λ ≥ 0` expands forever:
  the Friedmann right-hand side stays positive, so `∂ₜ a` never vanishes, and hence
  `∂ₜ a > 0` at one instant implies `∂ₜ a > 0` at all later times."

TODO "Prove the existence of a Big-Bang singularity: a currently expanding, decelerating
  universe (`ρ > 0`, `P ≥ 0`, `Λ = 0`) reaches `a = 0` at a finite cosmic time in the past,
  giving a finite age `t₀ < 1 / H₀`; contrast the de Sitter case, which has no such
  singularity."
