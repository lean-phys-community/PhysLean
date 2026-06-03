/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Particles.SuperSymmetry.N1.Basic
public import Physlib.Mathematics.Calculus.Wirtinger.Coordinate
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!

# N=1 SUSY — the abstract Kähler potential

## i. Overview

This module introduces the abstract `KahlerPotential` data of an N=1 model: a
real-valued function `K` of the chiral scalars, twice continuously
differentiable on an open domain. It is the abstraction-first counterpart of
the concrete `Hⁿ` log potential in `Particles/SuperSymmetry/N1/LogKahlerHn.lean`.

The codomain is `ℝ`, not `ℂ`: a Kähler potential is a physical real
observable, so reality is enforced by the type rather than a separate `IsReal`
predicate. The Wirtinger operators of `Mathematics/Calculus/Wirtinger/Coordinate.lean`
act on `ℂ`-valued
functions, so derivatives are taken on the ℂ-lift
`fun u => ((K u : ℝ) : ℂ)`, whose regularity follows from that of `K` via the
continuous ℝ-linear map `Complex.ofRealCLM` (`contDiffOn_lift`). The payoff is
reality of the lift, `star ∘ K.lift = K.lift` (`star_lift`) — the keystone of
Kähler-metric hermiticity in `Particles/SuperSymmetry/N1/KahlerMetric.lean`.

The regularity is `C²` on the domain: the mixed second derivative `∂_I ∂_J̄ K`
and the Schwarz step behind its hermiticity both need the first derivative to be
differentiable in turn, which `C²` supplies (`differentiableAt_of_mem` is the
weaker first-order fact the hermiticity proof also uses).

## ii. Key results

All regularity is over `ℝ` (i.e. `ContDiffOn ℝ`, `DifferentiableAt ℝ`): a
real-valued `K` cannot be `ℂ`-differentiable except as a constant, and the
Wirtinger operators of `Mathematics/Calculus/Wirtinger/Coordinate.lean` are built
on `fderiv ℝ` anyway.

- `SUSY.N1.KahlerPotential` : the abstract Kähler-potential structure
    (real-valued, `ℝ`-`C²` on an open domain).
- `SUSY.N1.KahlerPotential.lift` : the ℂ-lift fed to the Wirtinger operators
    (the chiral derivative `∂_I K` is then `dWirtingerCoord K.lift I`).
- `SUSY.N1.KahlerPotential.contDiffOn_lift` : the lift inherits the potential's
    `ℝ`-`C²` regularity, via `Complex.ofRealCLM`.
- `SUSY.N1.KahlerPotential.contDiffAt_of_mem` / `differentiableAt_of_mem` :
    `ℝ`-`C²` / `ℝ`-differentiability of the lift at a point of the domain.

## iii. Table of contents

- A. The Kähler potential structure
- B. The ℂ-lift
- C. Regularity accessors

-/

@[expose] public section

noncomputable section

namespace SUSY.N1

variable {C : Type*} [Fintype C]

/-!

## A. The Kähler potential structure

A `KahlerPotential` is a real function `toFun` of the chiral scalars, defined
with second-order regularity on an open `domain`. Globally-smooth potentials
take `domain := Set.univ`; partial-domain ones (such as the `Hⁿ` log
potential, smooth only on the slit locus) take a proper open subset.

-/

/-- The abstract Kähler potential of an N=1 model: a real-valued function of
the chiral scalars, with `ContDiffOn ℝ 2` regularity on an open domain.
Reality is by construction from the `ℝ` codomain; derivatives are taken on the
ℂ-lift `fun u => ((toFun u : ℝ) : ℂ)`. -/
structure KahlerPotential (C : Type*) [Fintype C] where
  /-- The (real) Kähler potential as a function of the chiral scalars. -/
  toFun : ChiralScalarConfiguration C → ℝ
  /-- The open set on which the potential is regular. -/
  domain : Set (ChiralScalarConfiguration C)
  /-- The domain is open. -/
  domain_open : IsOpen domain
  /-- The (real) potential is twice continuously real-differentiable on the
  domain. The ℂ-lift's regularity is derived (`contDiffOn_lift`). -/
  contDiffOn : ContDiffOn ℝ 2 toFun domain

namespace KahlerPotential

/-- Write `K u` for `K.toFun u`. -/
instance : CoeFun (KahlerPotential C)
    (fun _ => ChiralScalarConfiguration C → ℝ) where
  coe := toFun

/-!

## B. The ℂ-lift

The Wirtinger operators of `Mathematics/Calculus/Wirtinger/Coordinate.lean` act on
`ℂ`-valued functions, so
the real potential is fed to them through its ℂ-lift `K.lift`; the chiral
derivative `∂_I K` is then simply `dWirtingerCoord K.lift I`.

-/

/-- The ℂ-lift of the real Kähler potential: the `ℂ`-valued function the Wirtinger
operators consume. -/
def lift (K : KahlerPotential C) : ChiralScalarConfiguration C → ℂ :=
  fun u => ((K.toFun u : ℝ) : ℂ)

@[simp] lemma lift_apply (K : KahlerPotential C)
    (u : ChiralScalarConfiguration C) :
    K.lift u = ((K.toFun u : ℝ) : ℂ) := rfl

/-- Reality of the potential: conjugating the ℂ-lift is the identity. This is the
payoff of the `ℝ` codomain — the conjugation lemmas of
`Mathematics/Calculus/Wirtinger/Coordinate.lean` use it
to turn `∂_J̄` of `K` into `∂_I`, the key step in Kähler-metric hermiticity. -/
lemma star_lift (K : KahlerPotential C) : (fun v => star (K.lift v)) = K.lift := by
  funext v; simp [lift_apply]

/-!

## C. Regularity accessors

The real `contDiffOn` field is transported to the ℂ-lift (`Complex.ofRealCLM`
is a continuous ℝ-linear map) and unpacked into the differentiability facts the
Wirtinger layer consumes. This milestone needs only first-order
differentiability of the lift at a domain point.

-/

/-- Regularity transported to the ℂ-lift: `Complex.ofRealCLM` is a continuous
ℝ-linear map, so `ContDiffOn` of the real potential gives `ContDiffOn` of the
lift. -/
lemma contDiffOn_lift (K : KahlerPotential C) :
    ContDiffOn ℝ 2 K.lift K.domain :=
  K.contDiffOn.continuousLinearMap_comp Complex.ofRealCLM

/-- The ℂ-lift is `C²` at any point of the (open) domain. -/
lemma contDiffAt_of_mem (K : KahlerPotential C)
    {u : ChiralScalarConfiguration C} (hu : u ∈ K.domain) : ContDiffAt ℝ 2 K.lift u :=
  K.contDiffOn_lift.contDiffAt (K.domain_open.mem_nhds hu)

/-- The ℂ-lift is real-differentiable at any point of the (open) domain — the
first-order regularity the hermiticity proof consumes. -/
lemma differentiableAt_of_mem (K : KahlerPotential C)
    {u : ChiralScalarConfiguration C} (hu : u ∈ K.domain) :
    DifferentiableAt ℝ K.lift u :=
  (K.contDiffAt_of_mem hu).differentiableAt two_ne_zero

end KahlerPotential

end SUSY.N1

end

end
