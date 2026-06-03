/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Particles.SuperSymmetry.N1.Derivative
public import Physlib.Mathematics.Calculus.Wirtinger.Coordinate

/-!

# N=1 SUSY — the abstract superpotential

## i. Overview

The abstract `SuperPotential` data of an N=1 model: a globally holomorphic
`ℂ`-valued function `W` of the chiral scalars. No domain, no reality
condition — `W` is genuinely complex and entire.

The chiral derivative `∂_I W` is just `dWirtingerCoord W I`: `dWirtingerCoord` collapses to
the complex Fréchet derivative on holomorphic functions
(`dWirtingerCoord_eq_complex_fderiv` in `Mathematics/Calculus/Wirtinger/Coordinate.lean`).

### The conjugate superpotential

`W.bar u := star (W u)` — the anti-chiral superpotential `W̄`, anti-holomorphic
in the chiral coordinate per the standard N=1 convention. Bundled
anti-holomorphicity: `bar_antiHolomorphic`.

## ii. Key results

- `SUSY.N1.SuperPotential` : the abstract superpotential structure.
- `SUSY.N1.SuperPotential.bar` : the conjugate superpotential `W̄ = star ∘ W`,
    a bare anti-holomorphic function of the chiral coordinate.
- `SUSY.N1.SuperPotential.bar_antiHolomorphic` : anti-holomorphicity of `W̄`.
- `SUSY.N1.SuperPotential.bar_dChiralScalar` : `∂_I W̄ = 0`.
- `SUSY.N1.SuperPotential.bar_dAntiChiralScalar_apply` : `∂_J̄ W̄ = star (∂_J W)`.

## iii. Table of contents

- A. The superpotential structure
- B. The conjugate superpotential

-/

@[expose] public section

noncomputable section

namespace SUSY.N1

variable {C : Type*} [Fintype C]

/-!

## A. The superpotential structure

A `SuperPotential` is a globally holomorphic `ℂ`-valued function of the chiral
scalars. Holomorphy is `Differentiable ℂ`, the full physical content; there is
no domain (the abstraction takes superpotentials to be entire) and no reality
condition (the superpotential is genuinely complex).

-/

/-- The abstract chiral superpotential `W : ChiralScalarConfiguration C → ℂ` of an N=1
model, with bundled global holomorphicity. No domain field (`W` is entire) and
no reality field (`W` is genuinely complex); the conjugate `W̄` is the
anti-chiral counterpart `bar` defined below. -/
structure SuperPotential (C : Type*) [Fintype C] where
  /-- The underlying function `W : ChiralScalarConfiguration C → ℂ`. -/
  toFun : ChiralScalarConfiguration C → ℂ
  /-- Global holomorphicity of `W`: `Differentiable ℂ` on all of
  `ChiralScalarConfiguration C` (no domain restriction). -/
  holomorphic : Differentiable ℂ toFun

namespace SuperPotential

/-- Coerce `W : SuperPotential C` to its underlying function: `W u = W.toFun u`. -/
instance : CoeFun (SuperPotential C)
    (fun _ => ChiralScalarConfiguration C → ℂ) where
  coe := toFun

/-!

## B. The conjugate superpotential

-/

/-- The anti-chiral superpotential `W̄(u) := star (W u)`, anti-holomorphic in
the chiral coordinate `u` per the standard N=1 convention `W̄(Φ̄) = star(W(Φ))`.
Returned as a bare function — `W̄` is not a `SuperPotential` because the
structure bundles holomorphicity, which `W̄` does not have. Anti-holomorphicity
is captured by `bar_antiHolomorphic`. -/
def bar (W : SuperPotential C) : ChiralScalarConfiguration C → ℂ :=
  fun u => star (W u)

/-- Simp-normal form of `W.bar`: `W̄(u) = star (W u)`. -/
@[simp] lemma bar_apply (W : SuperPotential C)
    (u : ChiralScalarConfiguration C) :
    W.bar u = star (W u) := rfl

/-- Antiholomorphicity of `W̄`: `star ∘ W.bar = W.toFun` by `star_star`, so
`star ∘ W.bar` inherits `ℂ`-differentiability from `W.holomorphic`. The
derivative content is spelled out by `bar_dChiralScalar` (`∂_I W̄ = 0`) and
`bar_dAntiChiralScalar_apply` (`∂_J̄ W̄ = star (∂_J W)`). -/
lemma bar_antiHolomorphic (W : SuperPotential C) :
    Differentiable ℂ (star ∘ W.bar) := by
  simpa [Function.comp_def, star_star] using W.holomorphic

open Physlib.Wirtinger

variable [DecidableEq C] {A : Type*} [Fintype A]

/-- The chiral derivative of the conjugate superpotential vanishes, `∂_I W̄ = 0`:
`W̄` is anti-holomorphic. Not `@[simp]`: its LHS head is the reducible `M.dChiralScalar`
wrapper (unfolding to `dWirtingerCoord`), so it is not in simp-normal form — matching
the convention that the conjugation lemmas of `Wirtinger/Coordinate.lean` aren't `@[simp]`. -/
lemma bar_dChiralScalar (W : SuperPotential C) (M : Model C A) (I : C) :
    M.dChiralScalar (W.bar) I = 0 := by
  funext u
  show dWirtingerCoord (fun v => star (W v)) I u = 0
  rw [dWirtingerCoord_star_comp_apply (differentiableAt_real_of_complex (W.holomorphic u)) I,
    dWirtingerAntiCoord_eq_zero_of_holomorphic_apply (W.holomorphic u) I, star_zero]

/-- The anti-chiral derivative of the conjugate superpotential is the conjugate of
the chiral derivative of `W`, `∂_J̄ W̄ = star (∂_J W)` (dotted index `J̄ : A`) — the
literal `∂_ī W̄` the F-term contraction consumes. Pointwise (`_apply`), not
`@[simp]`; proved by unfolding the wrappers and applying `dWirtingerAntiCoord_star_comp_apply`. -/
lemma bar_dAntiChiralScalar_apply (W : SuperPotential C) (M : Model C A)
    (Jbar : A) (u : ChiralScalarConfiguration C) :
    M.dAntiChiralScalar (W.bar) Jbar u = star (M.dChiralScalar W (M.equiv.symm Jbar) u) := by
  show dWirtingerAntiCoord (fun v => star (W v)) (M.equiv.symm Jbar) u
      = star (dWirtingerCoord W (M.equiv.symm Jbar) u)
  exact dWirtingerAntiCoord_star_comp_apply (differentiableAt_real_of_complex (W.holomorphic u))
    (M.equiv.symm Jbar)

end SuperPotential

end SUSY.N1

end

end
