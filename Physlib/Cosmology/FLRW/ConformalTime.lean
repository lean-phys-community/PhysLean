/-
Copyright (c) 2026 Jinzheng Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzheng Li
-/
module

public import Physlib.Meta.TODO.Basic
/-!

# Conformal time in FLRW cosmology

Placeholder file collecting TODO items for the conformal time and the conformal
Hubble factor of a Friedmann-Lemaître-Robertson-Walker model. This file contains
only TODO items; no definitions or lemmas are formalized yet.

-/

@[expose] public section

TODO "Define the conformal time `η` of an FLRW model by `a dη = dt`, that is
  `η(t) = ∫ dt'/a(t')`."

TODO "Define the conformal Hubble factor `ℋ = a'/a` (the prime denotes the
  derivative with respect to conformal time) and prove `ℋ = a * H`, relating it
  to the Hubble parameter `H = ∂ₜ a / a`."

TODO "State the FLRW metric in conformal time as `a(η)²` times a static metric,
  making its conformal flatness manifest."

TODO "State the Friedmann and acceleration equations in conformal time:
  `ℋ² = (8πG/3) ρ a² + (Λc²/3) a² − K c²` and
  `a''/a = (4πG/3)(ρ − 3 P/c²) a² + (2Λc²/3) a² − K c²`."

TODO "Prove the cosmic-to-conformal change of variables `f' = a * ∂ₜ f` (from `dt = a dη`)
  and use it to derive the conformal-time Friedmann and acceleration equations from their
  cosmic-time forms."
