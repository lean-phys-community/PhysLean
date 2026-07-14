/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Physlib.QuantumMechanics.Operators.Unbounded
/-!

# Quantum systems

## i. Overview

## ii. Key results

## iii. Table of contents

## iv. References

-/

@[expose] public section

noncomputable section

namespace QuantumMechanics

open LinearPMap

/-- A quantum system is identified by its Hilbert space and self-adjoint Hamiltonian operator. -/
structure QuantumSystem where
  /-- The complex Hilbert space. -/
  HS : Type*
  [instNormed : NormedAddCommGroup HS]
  [instInner : InnerProductSpace ℂ HS]
  [instComplete : CompleteSpace HS]
  /-- The self-adjoint Hamiltonian operator. -/
  ℋ : HS →ₗ.[ℂ] HS
  ℋ_self_adjoint : IsSelfAdjoint ℋ

namespace QuantumSystem

instance (Q : QuantumSystem) : NormedAddCommGroup Q.HS := Q.instNormed

instance (Q : QuantumSystem) : InnerProductSpace ℂ Q.HS := Q.instInner

instance (Q : QuantumSystem) : CompleteSpace Q.HS := Q.instComplete

/-!
## Zero
-/

instance instZero : Zero QuantumSystem := ⟨EuclideanSpace ℂ (Fin 0), 0, adjoint_zero⟩

end QuantumSystem
end QuantumMechanics
end
