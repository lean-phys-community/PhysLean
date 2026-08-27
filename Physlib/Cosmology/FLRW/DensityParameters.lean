/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
/-!

# Density parameters and the standard cosmological model

Placeholder file collecting TODO items for the critical density, the density
parameters, the closure relation, and the Friedmann equation of the standard
cosmological model written in terms of the reduced Hubble function. This file
contains only TODO items; no definitions or lemmas are formalized yet.

-/

@[expose] public section

TODO "Define the critical density `ρ_cr = 3 H² / (8 π G)`."

TODO "Define the density parameter `Ω = ρ / ρ_cr` and the curvature density
  parameter `Ω_K = − K c² / (H² a²)`."

TODO "Prove the closure relation `Ω + Ω_K = 1` as a rearrangement of the
  Friedmann equation."

TODO "Define the reduced Hubble function `E(a) = H / H₀` and the normalized
  Friedmann equation `E(a)² = Σ_x Ω_{x0} f_x(a) + Ω_{K0} / a²`."

TODO "Define the Friedmann equation of the standard cosmological model
  `E(a)² = Ω_Λ + Ω_{m0} a⁻³ + Ω_{r0} a⁻⁴ + Ω_{K0} a⁻²`."

TODO "Define the age of the universe `t₀ = H₀⁻¹ ∫₀¹ da / (a E(a))` and prove
  `t₀ ∝ 1 / H₀`."

TODO "Define the radiation-matter and matter-Λ equality scale factors
  `a_eq = Ω_{r0} / Ω_{m0}` and `a_Λ = (Ω_{m0} / Ω_Λ)^(1/3)`."
