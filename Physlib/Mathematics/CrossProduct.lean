/-
Copyright (c) 2026 Giuseppe Sorge. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giuseppe Sorge
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.CrossProduct
/-!

# The cross product of three-dimensional vectors

Identities for the cross product `⨯₃` on `Fin 3 → ℝ`, beyond those already in Mathlib, used in the
formalisation of rigid-body dynamics.

-/

@[expose] public section

namespace Matrix

/-- The component form of the triple cross product `v ⨯₃ (w ⨯₃ v)`: by the `bac−cab` identity its
`i`-th entry is `|v|² wᵢ − (v · w) vᵢ`, written with the explicit component sums `∑ k, (v k)²` and
`∑ j, v j * w j`. -/
lemma cross_cross_self_apply (v w : Fin 3 → ℝ) (i : Fin 3) :
    (v ⨯₃ (w ⨯₃ v)) i = (∑ k, (v k) ^ 2) * w i - (∑ j, v j * w j) * v i := by
  rw [cross_cross_eq_smul_sub_smul']
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_three]
  ring

end Matrix
