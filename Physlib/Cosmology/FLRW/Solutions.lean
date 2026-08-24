/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
/-!

# Exact solutions of the Friedmann equations

Placeholder file collecting TODO items for the standard closed-form solutions of
the Friedmann equations: the de Sitter, radiation-dominated, Einstein-de Sitter
(dust) and Milne models, together with the Einstein static universe. This file
contains only TODO items; no definitions or lemmas are formalized yet.

-/

@[expose] public section

TODO "Prove that the de Sitter solution `a(t) = a₀ exp(±√(Λ/3) c t)` (with `ρ = 0`,
  `K = 0`, `Λ > 0`) solves the Friedmann equations, and that its deceleration
  parameter is `q = −1`."

TODO "Prove that the spatially flat radiation-dominated solution `a = (t/t₀)^(1/2)`
  solves the Friedmann equations, with `q₀ = 1` and `t₀ = 1 / (2 H₀)`."

TODO "Prove that the Einstein-de Sitter (spatially flat, dust) solution
  `a = (t/t₀)^(2/3)` solves the Friedmann equations, with `q₀ = 1/2` and
  `t₀ = 2 / (3 H₀)`."

TODO "Prove that the Milne solution `a = c t` (empty universe, `K < 0`) has
  vanishing scalar curvature, i.e. it is Minkowski space in expanding coordinates."

TODO "Define the Einstein static universe (`∂ₜ a = ∂ₜ ∂ₜ a = 0`, forcing `K > 0`
  and `ρ_m = 2 ρ_Λ`) and prove that it is an unstable equilibrium."
