/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Particles.SuperSymmetry.N1.Basic
public import Physlib.Mathematics.Calculus.Wirtinger.Coordinate

/-!

# SUSY N=1 chiral sector — the scalar derivatives

## i. Overview

The chiral and anti-chiral derivatives `∂_I` / `∂_J̄` of the N=1 chiral sector,
as the `Model` methods `M.dChiralScalar` / `M.dAntiChiralScalar` — thin wrappers
over the coordinate Wirtinger calculus of
`Mathematics/Calculus/Wirtinger/Coordinate.lean`. They bind each index type of
the `Model` to a differentiation *direction*, so **a barred derivative is taken
with respect to the anti-chiral field, never the chiral one**:

* `M.dChiralScalar` (chiral index `I : C`) — the holomorphic `∂/∂z^I`, w.r.t. the
  chiral configuration; the model `M` is inert here (the chiral slot needs no
  relabel), taken only for a uniform call shape;
* `M.dAntiChiralScalar` (barred index `J̄ : A`) — the anti-holomorphic `∂/∂z̄^J̄`,
  w.r.t. the anti-chiral configuration; it also bundles the `A → C` relabel
  (`equiv.symm`) the barred index needs.

The `C`/`A` index types keep the two from being confused; proofs `rw` to
`dWirtingerCoord` / `dWirtingerAntiCoord` to use the Wirtinger calculus.

## ii. Key results

- `SUSY.N1.Model.dChiralScalar` / `SUSY.N1.Model.dAntiChiralScalar` : the chiral /
    anti-chiral derivatives `∂_I` / `∂_J̄` (written `M.dChiralScalar` /
    `M.dAntiChiralScalar`), wrapping `dWirtingerCoord` / `dWirtingerAntiCoord`.

-/

@[expose] public section

noncomputable section

namespace SUSY.N1

open Physlib.Wirtinger

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {A : Type*} [Fintype A]

namespace Model

/-- The chiral derivative `∂_I` along a chiral index `I : C`, written
`M.dChiralScalar f I`: differentiation w.r.t. the chiral configuration — the
holomorphic Wirtinger derivative `∂/∂z^I`. The model `M` plays no role for the
chiral slot (only `dAntiChiralScalar` needs `equiv`); it is taken so the chiral
and anti-chiral derivatives share the uniform `M.dChiralScalar` /
`M.dAntiChiralScalar` call shape. -/
@[nolint unusedArguments]
abbrev dChiralScalar (_M : Model C A) (f : ChiralScalarConfiguration C → ℂ) (I : C) :
    ChiralScalarConfiguration C → ℂ :=
  dWirtingerCoord f I

/-- The anti-chiral derivative `∂_J̄` along a barred index `J̄ : A`, written
`M.dAntiChiralScalar f J̄`: the anti-holomorphic Wirtinger derivative `∂/∂z̄^J̄`.

It differentiates a function of the *single* chiral configuration `C → ℂ`; there
is no `A`-indexed configuration to differentiate (no doubling — see `Basic.lean`).
`A` contributes only the barred index `Jbar`, which `M`'s `equiv.symm` relabels to
its chiral coordinate before the underlying operator acts. -/
abbrev dAntiChiralScalar (M : Model C A) (f : ChiralScalarConfiguration C → ℂ) (Jbar : A) :
    ChiralScalarConfiguration C → ℂ :=
  dWirtingerAntiCoord f (M.equiv.symm Jbar)

end Model

end SUSY.N1

end

end
