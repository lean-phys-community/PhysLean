/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.Meta.TODO.Basic
/-!

# Operator examples

This is currently a stub, intended to host examples of operators with notable properties.

-/

@[expose] public section

TODO "Give an example of a closed, symmetric operator with _no_ self-adjoint extension.
  The canonical example is the derivative operator `T = -i d/dx` on the half-space [0,∞)
  with domain `D(T) = {ψ ∈ L²([0,∞), ℂ) | ψ(0) = 0}` (or a d-dimensional generalization)."

TODO "Give an example of a densely defined, closed operator `T` such that each complex number
  is an eigenvalue of `T†` but `T` has no eigenvalues: c.f. Schmüdgen Ch 2, exercise 9."

TODO "Give an example of a symmetric operator `T` on `H` such that `(T + I • 1).range`
  and `(T - I • 1).range` are dense in `H` but `T` is not essentially self-adjoint.
  c.f. Schmüdgen Ch 3, exercise 12."
