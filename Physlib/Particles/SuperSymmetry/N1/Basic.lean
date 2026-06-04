/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Logic.Equiv.Basic

/-!

# SUSY N=1 chiral sector — basic indexing data

## i. Overview

The minimal label and configuration data for the N=1 chiral sector.

A `Model` packages two finite index types — `ChiralIndexingType` (written `C`
below) indexing the chiral scalars and `AntiChiralIndexingType` (written `A`)
the anti-chiral (barred) slots — with an equivalence `equiv : C ≃ A`, kept
distinct so the two slots of a contraction `g_{IJ̄}` cannot be confused. The
physical configuration is `ChiralScalarConfiguration C = C → ℂ`, carrying
`2 · Fintype.card C` real degrees of freedom — the only field data; the
anti-chiral scalars are its complex conjugates, never an independent
configuration.

Doubling — adding an independent `A → ℂ` configuration — is the wrong choice:
the physical identities would then hold only where anti-chiral is the conjugate
of chiral, so every theorem carries that subspace as a hypothesis (e.g. the
Kähler potential is real only there, making hermiticity of `g_{IJ̄}`
conditional). Building the conjugate in keeps them unconditional — `K` is real
by construction — and leaves `A` an index type only.

This file carries only the index/configuration data; the chiral and anti-chiral
derivatives `∂_I` / `∂_J̄` (the `Model` methods `M.dChiralScalar` /
`M.dAntiChiralScalar`) are built on top of it in `Derivative.lean`.

The files of this `Particles/SuperSymmetry/N1/` folder:

* `Basic.lean` (this file) — the `Model` indexing data and the chiral
  configuration type.
* `Derivative.lean` — the chiral / anti-chiral derivative wrappers
  `M.dChiralScalar` / `M.dAntiChiralScalar` over the Wirtinger calculus.
* `SuperPotential.lean` — the abstract holomorphic superpotential `W` and its
  conjugate `W̄`.
* `KahlerPotential.lean` — the abstract Kähler potential `K`.
* `KahlerMetric.lean` — the Kähler metric `g_{IJ̄} = ∂_I ∂_J̄ K` and its
  hermiticity.
* `LogKahlerHn.lean` — worked example: the `Hⁿ` log Kähler potential (the
  reusable upper-half-plane calculus lives in
  `Mathematics/Calculus/Wirtinger/UpperHalfPlane.lean`).

## ii. Key results

- `SUSY.N1.Model` : the indexing data of an N=1 sector — a chiral index type,
    an anti-chiral (barred) index type, and an equivalence `equiv` between them.
- `SUSY.N1.ChiralScalarConfiguration` : the physical scalar configuration space
    `C → ℂ`, where `C` is the finite type indexing the chiral scalars — the only
    field data in the sector.

-/

@[expose] public section

noncomputable section

namespace SUSY.N1

/-- The indexing data of an N=1 sector: a chiral index type `ChiralIndexingType`,
an anti-chiral (barred) index type `AntiChiralIndexingType`, and a bijection
`equiv` between them. -/
structure Model (ChiralIndexingType : Type*) [Fintype ChiralIndexingType]
    (AntiChiralIndexingType : Type*) [Fintype AntiChiralIndexingType] where
  /-- The correspondence between chiral and anti-chiral (barred) labels. -/
  equiv : ChiralIndexingType ≃ AntiChiralIndexingType

/-- The chiral scalar configuration: an assignment of complex values to each
chiral label. An `abbrev` so unification applies Mathlib's `α → ℂ` calculus
lemmas directly. -/
abbrev ChiralScalarConfiguration (ChiralIndexingType : Type*) := ChiralIndexingType → ℂ

end SUSY.N1

end

end
