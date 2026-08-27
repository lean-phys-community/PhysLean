/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!

# Observable algebras

The observable structure of a physical system is described by a unital complex C⋆-algebra `A`.

The same framework contains both classical and quantum systems, according to which C⋆-algebra is
chosen:

* **quantum**: `B(H)`, the bounded operators on a Hilbert space `H` — generally noncommutative.
  E.g. unitary evolution, `a ↦ U a U⋆`, is how a Hamiltonian moves observables in time.
* **classical**: `C(M)`, continuous functions on phase space `M` — commutative, matching how
  classical observables always commute. E.g. position and momentum are just two such functions.

The basic notions of observable, positive element, effect, state, unitary, channel, and finite
POVM depend only on the observable algebra.

This file only defines the vocabulary. Elementary results about each notion live in their own
file (`Observable.lean`, `Effect.lean`, `State.lean`, ...).

-/

@[expose] public section

open scoped ComplexOrder CStarAlgebra

/-- A unital complex C⋆-algebra with a compatible order making `≤` the usual positivity order.
Mathlib doesn't pick one canonically, so definitions below that need `≤` take this instead of
just `CStarAlgebra`. -/
class OperatorAlgebra (A : Type*) extends CStarAlgebra A, PartialOrder A, StarOrderedRing A

namespace OperatorAlgebra

section ObservableAlgebra

variable {A : Type*} [OperatorAlgebra A]

/-- An observable is a self-adjoint element of `A`: position, momentum, energy, spin, ... .
Self-adjointness is exactly what makes an element a *measurable* quantity — it is what forces its
spectrum, the possible measurement outcomes, to be real. -/
noncomputable abbrev Observable (A : Type*) [OperatorAlgebra A] := selfAdjoint A

/-- A positive element of `A`: an observable whose measurement outcomes are all `≥ 0`.
Positivity is what gives observables a meaningful order (`a ≤ b` meaning `b - a` is positive). -/
abbrev PositiveElement (A : Type*) [OperatorAlgebra A] := {a : Observable A // 0 ≤ (a : A)}

/-- An effect is an observable between zero and the identity, representing a yes/no measurement
outcome. -/
abbrev Effect (A : Type*) [OperatorAlgebra A] := Set.Icc (0 : Observable A) 1

/-- A finite POVM on `A`: the most general notion of a measurement with outcomes in `X`,
generalizing a single yes/no `Effect` to several possible outcomes. -/
structure POVM (A : Type*) [OperatorAlgebra A] (X : Type*) [Fintype X] where
  /-- The effect associated with each measurement outcome. -/
  effect : X → Effect A
  /-- The effects resolve the identity. -/
  sum_effect : ∑ x, (effect x : A) = 1

/-- A unitary element of `A`: implements a reversible transformation of the system — a symmetry,
or time evolution under a Hamiltonian — acting on observables by conjugation, `a ↦ U a U⋆`. -/
noncomputable abbrev Unitary (A : Type*) [OperatorAlgebra A] := unitary A

/-- A state on `A`: a positive complex-linear functional normalized by `ω 1 = 1`. `ω a` is the
expected outcome of measuring observable `a` in this state — a state records everything that can
be learned about the system by measurement. -/
structure State (A : Type*) [OperatorAlgebra A] where
  /-- The positive linear functional underlying the state. -/
  toPositiveLinearMap : A →ₚ[ℂ] ℂ
  /-- A state assigns expectation one to the identity observable. -/
  map_one : toPositiveLinearMap 1 = 1

/-- A channel from `A₁` to `A₂` — physicists' name for a unital completely positive (UCP) map,
the most general notion of dynamics this framework expresses. -/
abbrev Channel (A₁ A₂ : Type*) [OperatorAlgebra A₁] [OperatorAlgebra A₂] :=
  {φ : A₁ →CP A₂ // φ 1 = 1}

end ObservableAlgebra

end OperatorAlgebra
