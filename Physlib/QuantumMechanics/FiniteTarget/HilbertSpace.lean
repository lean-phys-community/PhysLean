/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Physlib.Meta.TODO.Basic
/-!

# The Hilbert space of a finite target quantum mechanical system

-/

@[expose] public section

namespace QuantumMechanics

TODO "To match this with the results currently in the `QuantumInfo` part of the library,
  we should:
  1. Define `FiniteHilbertSpace` as a structure with a single entry `val`, this
    should take as an input a finite and decidable type `d`. Below this type is
    taken as default to be `Fin n`.
  2. On this type we should then define the structure of an inner-product space, and a
    Hilbert space.
  3. We could then define the notation `𝓗[d]` to denote the Hilbert space corresponding
    to the type `d`.
  4. The results from `QuantumInfo/Finite/Braket.lean` can then be moved over
    to Physlib, and related to the definition of the Hilbert space here.
  Optional. Maybe it is worth moving these files to a directory called `States`, with
  the idea that it includes this definition of the Hilbert space, the
  definition of bras and kets, and the definition of mixed states. Maybe also
  parts of `./ResourceTheory/FreeState`."

/-- The finite dimensional Hilbert space of dimension `n`. -/
def FiniteHilbertSpace (n : ℕ) : Type := EuclideanSpace ℂ (Fin n)

instance {n : ℕ} : AddCommGroup (FiniteHilbertSpace n) := inferInstanceAs
  (AddCommGroup (EuclideanSpace ℂ (Fin n)))

noncomputable instance {n : ℕ} : Module ℂ (FiniteHilbertSpace n) := inferInstanceAs
  (Module ℂ (EuclideanSpace ℂ (Fin n)))

noncomputable instance {n : ℕ} : NormedAddCommGroup (FiniteHilbertSpace n) := inferInstanceAs
  (NormedAddCommGroup (EuclideanSpace ℂ (Fin n)))

noncomputable instance {n : ℕ} : InnerProductSpace ℂ (FiniteHilbertSpace n) := inferInstanceAs
  (InnerProductSpace ℂ (EuclideanSpace ℂ (Fin n)))

noncomputable instance {n : ℕ} : CompleteSpace (FiniteHilbertSpace n) := inferInstanceAs
  (CompleteSpace (EuclideanSpace ℂ (Fin n)))

end QuantumMechanics
