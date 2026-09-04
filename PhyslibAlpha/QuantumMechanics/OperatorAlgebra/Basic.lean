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

Unitary elements and channels are the algebraic starting point for dynamics.
Observables, states, and measurements live in their respective subdirectories.

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

/-- A unitary element of `A`: implements a reversible transformation of the system — a symmetry,
or time evolution under a Hamiltonian — acting on observables by conjugation, `a ↦ U a U⋆`. -/
noncomputable abbrev Unitary (A : Type*) [OperatorAlgebra A] := unitary A

/-- A channel from `A₁` to `A₂` — physicists' name for a unital completely positive (UCP) map,
the most general notion of dynamics this framework expresses. -/
abbrev Channel (A₁ A₂ : Type*) [OperatorAlgebra A₁] [OperatorAlgebra A₂] :=
  {φ : A₁ →CP A₂ // φ 1 = 1}

end ObservableAlgebra

end OperatorAlgebra
