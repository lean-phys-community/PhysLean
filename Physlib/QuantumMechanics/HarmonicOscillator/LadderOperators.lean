/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.HarmonicOscillator.Basic
/-!

# Ladder operators

This is currently a stub, intended to house the ladder operators of the quantum harmonic oscillator.

-/

@[expose] public section

/-!
## A. Ladder operators
-/

TODO "Define the raising/lowering operators for the quantum harmonic oscillator."

TODO "Prove that the raising/lowering operators are adjoints of one another (tag as simp?)."

TODO "Prove the commutation relations for the ladder operators, `[a, a†] = δ`."

/-!
## B. Number operators
-/

TODO "Define the number operators for the quantum harmonic oscillator
  in terms of the ladder operators."

TODO "Prove that the number operators are symmetric/self-adjoint."

TODO "Prove the commutation relations for the number operators, `[N i, N j] = 0`."

TODO "Prove the commutation relations between number and ladder operators,
  `[N, a] = -δ a` and `[N, a†] = δ a†`."

/-!
## C. Hamiltonian
-/

TODO "Define a Hamiltonian in terms of the number operators."

TODO "Prove the commutation relations between the Hamiltonian and ladder/number operators."

TODO "Relate the 'number operator' Hamiltonian to the 'K + T' Hamiltonian
  (=/≤/≥ depending on their domains)."

TODO "Prove that the two Hamiltonians define the same quantum system."
