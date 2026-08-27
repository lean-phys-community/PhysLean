/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
/-!

# Distances and redshift in FLRW cosmology

Placeholder file collecting TODO items for the notions of distance used in
cosmology (comoving, proper, and the observational luminosity and
angular-diameter distances), together with the redshift, the horizons, and the
lookback time. This file contains only TODO items; no definitions or lemmas are
formalized yet.

-/

@[expose] public section

TODO "Define the line-of-sight comoving distance `χ = c ∫ dt/a`, equivalently
  `χ(z) = ∫₀ᶻ c dz'/H(z')`."

TODO "Define the proper distance `D = a * χ` and prove the Hubble-Lemaître law
  `∂ₜ D = H * D` at fixed comoving distance `χ`."

TODO "Define the Hubble radius `R_H = c / H`, the distance at which the recession
  velocity equals the speed of light."

TODO "Relate the transverse comoving distance `r(χ)` to the existing
  `Cosmology.SpatialGeometry.S`, with curvature radius `k = 1/√|K|`."

TODO "Define the redshift by `1 + z = a₀ / a` and prove the cosmological redshift
  law `E ∝ 1/a` for a photon from the null geodesic equation."

TODO "Define the particle (comoving) horizon `χ_p = c ∫₀ᵗ dt'/a` and the event
  horizon `χ_e = c ∫_t^∞ dt'/a`."

TODO "Define the lookback time `t₀ - t` and prove its model-independent expansion
  `t₀ - t = H₀⁻¹ [z - ½(2 + q₀) z² + …]` in powers of the redshift."

TODO "Define the luminosity distance `d_L = (1 + z) r(χ)` and the angular-diameter
  distance `d_A = r(χ) / (1 + z)`."

TODO "Prove Etherington's distance-duality relation `d_L = (1 + z)² d_A`."

TODO "Prove the low-redshift expansions of `χ`, `d_L` and `d_A` in powers of `z`
  in terms of the deceleration parameter `q₀`."
