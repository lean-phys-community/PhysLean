/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Finite.Distance.Fidelity
public import QuantumInfo.Finite.Distance.TraceDistance

/-!
Distances between quantum states.
 * Fidelity
 * Trace distance
 * Bures metric
 * Superfidelity
 * Quantum Wasserstein Distance

All share some axioms: https://quantiki.org/wiki/distance-measures-between-states
-/

@[expose] public section
