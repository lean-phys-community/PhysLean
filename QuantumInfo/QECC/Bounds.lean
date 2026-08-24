/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.QECC.StabilizerFacts

/-!
# Bounds on stabilizer code parameters

Quantum Singleton (already in `StabilizerGroup`), quantum Hamming, and Gilbert–Varshamov bounds,
plus the rate form of Singleton. Stated for the ATP.
-/

@[expose] public section

open scoped BigOperators
namespace QuantumLib
namespace PauliOp
namespace StabGroup
variable {n : ℕ} (S : StabGroup n)

/-- **Quantum Hamming bound** (sphere-packing): a *nondegenerate* code correcting `t` errors packs
disjoint syndrome "spheres", so `(∑_{j≤t} C(n,j) 3ʲ) · 2ᵏ ≤ 2ⁿ`. -/
theorem hamming_bound {t : ℕ} (hnd : ¬ S.IsDegenerate) (ht : 2 * t < S.distance) :
    (∑ j ∈ Finset.range (t + 1), Nat.choose n j * 3 ^ j) * 2 ^ S.numLogical ≤ 2 ^ n := by
  sorry

/-- **Rate form of the Singleton bound:** `k + 2(d−1) ≤ n`. -/
theorem numLogical_add_two_mul_distance_le :
    S.numLogical + 2 * (S.distance - 1) ≤ S.numPhysical := by sorry
/-- **Gilbert–Varshamov (existence):** whenever the volume bound leaves room, a stabilizer group of
the required size and distance exists. -/
theorem gilbert_varshamov {k d : ℕ}
    (h : (∑ j ∈ Finset.range d, Nat.choose n j * 3 ^ j) * 2 ^ k < 2 ^ n) :
    ∃ T : StabGroup n, T.numLogical = k ∧ d ≤ T.distance := by sorry

/-- A single logical qubit needs at least `2d−1` physical qubits. -/
theorem numPhysical_ge_of_one_logical (h : S.numLogical = 1) :
    2 * S.distance - 1 ≤ S.numPhysical := by
  have := numLogical_add_two_mul_distance_le S
  simp [h] at this
  omega

end StabGroup
end PauliOp
end QuantumLib
