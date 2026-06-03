/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Particles.SuperSymmetry.N1.KahlerPotential
public import Physlib.Particles.SuperSymmetry.N1.Derivative

/-!

# N=1 SUSY — the abstract Kähler metric

## i. Overview

The Kähler metric is the geometric object that turns a Kähler potential into a
field-space metric: a hermitian pairing on the tangent space of chiral scalar
field space, locally given by the mixed second Wirtinger derivative of `K`.
Once `K` is fixed (any `KahlerPotential`), the metric is determined,

  `g_{IJ̄}(u) = ∂_I ∂_J̄ K`     (`KahlerPotential.metric`)

— a chiral derivative of an anti-chiral one. This file takes the metric on
*any* `KahlerPotential` and proves the one structural property that holds for
all of them: **hermiticity**,

  `star (g_{IJ̄}) = g_{JĪ}`     (`KahlerPotential.metric_hermitian`)

on the regular domain. The proof is the promised payoff of the design: reality
of `K` — automatic because its codomain is `ℝ`, packaged as
`star ∘ K.lift = K.lift` — turns the conjugation into `∂_J̄ ∂_I K` via the
conjugation lemmas of `Mathematics/Calculus/Wirtinger/Coordinate.lean`,
and **Schwarz's theorem** (`dWirtingerCoord_dWirtingerAntiCoord_comm`) commutes that back to
`∂_I ∂_J̄ K`. The `C²` regularity carried by `KahlerPotential` is exactly what
both steps consume.

The canonical consumer is the concrete `Hⁿ` log potential of
`Particles/SuperSymmetry/N1/LogKahlerHn.lean`: its `kahlerMetric` is defined as `K.metric` of that
very `KahlerPotential`, and the Poincaré metric is the closed form of this
abstract `g_{IJ̄}` at that instance.

## ii. Key results

- `SUSY.N1.KahlerPotential.metric` : the Kähler metric `g_{IJ̄} = ∂_I ∂_J̄ K`.
- `SUSY.N1.KahlerPotential.metric_hermitian` : hermiticity
    `star (g_{IJ̄}) = g_{JĪ}` on the domain.

## iii. Table of contents

- A. The Kähler metric
- B. Hermiticity

-/

@[expose] public section

noncomputable section

namespace SUSY.N1

open Physlib.Wirtinger

namespace KahlerPotential

variable {C : Type*} [Fintype C] [DecidableEq C]

/-!

## A. The Kähler metric

The metric is the mixed second Wirtinger derivative of the ℂ-lift, `∂_I ∂_J̄ K`
— a chiral derivative of an anti-chiral one, both drawn from the operators of
`Mathematics/Calculus/Wirtinger/Coordinate.lean`. It mirrors the concrete `kahlerMetric` of
`Particles/SuperSymmetry/N1/LogKahlerHn.lean`, but is taken on an arbitrary `KahlerPotential`; the
concrete `H^n` potential of `Particles/SuperSymmetry/N1/LogKahlerHn.lean` is one instance
(`kahlerMetric := K.metric`).

-/

variable {A : Type*} [Fintype A]

/-- The Kähler metric `g_{IJ̄}(u) = ∂_I ∂_J̄ K` of an abstract Kähler potential:
`M.dChiralScalar` (holomorphic slot `I : C`) of `M.dAntiChiralScalar`
(barred slot `J̄ : A`), on the ℂ-lift. -/
def metric (K : KahlerPotential C) (M : Model C A)
    (I : C) (Jbar : A) (u : ChiralScalarConfiguration C) : ℂ :=
  M.dChiralScalar (fun v => M.dAntiChiralScalar K.lift Jbar v) I u

/-!

## B. Hermiticity

-/

/-- **Hermiticity** of the Kähler metric: `star (g_{IJ̄}) = g_{JĪ}` at any point of
the regular domain, slots swapped via `equiv`. Reality of `K` (free from the `ℝ`
codomain, packaged as `star ∘ K.lift = K.lift`) turns the conjugate of `∂_I ∂_J̄ K`
into `∂_J̄ ∂_I K`, which Schwarz's theorem `dWirtingerCoord_dWirtingerAntiCoord_comm`
commutes back. `hu` supplies the `C²` regularity. -/
theorem metric_hermitian (K : KahlerPotential C) (M : Model C A)
    {u : ChiralScalarConfiguration C} (hu : u ∈ K.domain)
    (I : C) (Jbar : A) :
    star (K.metric M I Jbar u) = K.metric M (M.equiv.symm Jbar) (M.equiv I) u := by
  have hg2 : ContDiffAt ℝ 2 K.lift u := K.contDiffAt_of_mem hu
  have hinner : DifferentiableAt ℝ
      (fun v => dWirtingerAntiCoord K.lift (M.equiv.symm Jbar) v) u :=
    differentiableAt_dWirtingerAntiCoord hg2 (M.equiv.symm Jbar)
  -- Near `u`, conjugating the anti-chiral derivative of `K` gives its chiral
  -- derivative (reality of `K` via `star_lift` + the conjugation lemma).
  have heq_chiral : (fun v => star (dWirtingerAntiCoord K.lift (M.equiv.symm Jbar) v))
      =ᶠ[nhds u] (fun v => dWirtingerCoord K.lift (M.equiv.symm Jbar) v) := by
    filter_upwards [K.domain_open.mem_nhds hu] with v hv
    rw [← dWirtingerCoord_star_comp_apply (K.differentiableAt_of_mem hv) (M.equiv.symm Jbar),
      K.star_lift]
  show star (dWirtingerCoord (fun v => dWirtingerAntiCoord K.lift (M.equiv.symm Jbar) v) I u)
      = dWirtingerCoord
          (fun v => dWirtingerAntiCoord K.lift (M.equiv.symm (M.equiv I)) v) (M.equiv.symm Jbar) u
  rw [M.equiv.symm_apply_apply, ← dWirtingerAntiCoord_star_comp_apply hinner I,
    dWirtingerAntiCoord_congr_of_eventuallyEq_apply heq_chiral I]
  exact (dWirtingerCoord_dWirtingerAntiCoord_comm hg2 (M.equiv.symm Jbar) I).symm

end KahlerPotential

end SUSY.N1

end

end
