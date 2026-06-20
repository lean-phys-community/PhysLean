/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
/-!

# Matter content of FLRW cosmology

Placeholder file collecting TODO items for the matter content of a
Friedmann-Lemaître-Robertson-Walker universe: the perfect-fluid stress-energy
tensor, the equation of state, the continuity equation, and the resulting
density scaling for the standard components (dust, radiation, vacuum energy).
This file contains only TODO items; no definitions or lemmas are formalized yet.

-/

@[expose] public section

TODO "Define the perfect-fluid stress-energy tensor
  `T_{μν} = (ρ + P/c²) u_μ u_ν + P g_{μν}` for the FLRW metric."

TODO "Define the continuity equation `∂ₜ ρ + 3 H (ρ + P/c²) = 0` and derive it from
  the first- and second-order Friedmann equations."

TODO "Prove that the Friedmann equation, the acceleration equation and the
  continuity equation are not independent (a consequence of the Bianchi identity
  `∇_ν Gᵘᵛ = 0`)."

TODO "Define the linear (barotropic) equation of state `P = w ρ c²` and prove the
  density scaling law `ρ = ρ₀ a^(−3(1+w))` for constant `w`."

TODO "Specialize the density scaling law to dust (`w = 0`, `ρ ∝ a⁻³`), radiation
  (`w = 1/3`, `ρ ∝ a⁻⁴`) and vacuum energy (`w = −1`, `ρ` constant)."

TODO "Prove that the cosmological constant acts as a `w = −1` perfect fluid with
  `ρ_Λ = Λ c² / (8 π G)` and `P_Λ = −ρ_Λ c²`."
