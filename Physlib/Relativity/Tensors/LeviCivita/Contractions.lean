/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.LeviCivita.Basic
public import Physlib.Mathematics.KroneckerDelta.Contraction
public import Physlib.Meta.TODO.Basic
/-!

# Euclidean contraction identities for the Levi-Civita tensor

## i. Overview

This file proves the "epsilon-epsilon" contraction identities for the rank-four Levi-Civita
tensor `leviCivita` (notation `ε4`) in `d = 3`, stated in terms of the standard-basis
components of `ε4` itself (`realLorentzTensor.leviCivita_basis_repr_apply`).

The underlying facts about the `generalizedKroneckerDelta` alone, with no
tensor content — lives in `Physlib.Mathematics.KroneckerDelta.Contraction`, next to the
definition of `generalizedKroneckerDelta`. Here we specialise those facts to the components of
`ε4`, where `(ε4)_b = (Tensor.basis _).repr ε4 b` is the standard-basis component of `ε4`, an
integer Levi-Civita symbol carried to the reals, and the sums run over the remaining
(uncontracted) component slots.

## ii. Key results

- `leviCivita_symbol_contract_zero` : `∑_b (ε4)_b · (ε4)_b = 24` (full Euclidean contraction).
- `leviCivita_symbol_contract_one` : `∑_h (ε4)_{a,h} · (ε4)_{b,h} = 6 · δ[a,b]`.
- `leviCivita_symbol_contract_two` :
  `∑_h (ε4)_{r,s,h} · (ε4)_{t,w,h} = 2 · (δ[r,t]·δ[s,w] - δ[r,w]·δ[s,t])`.

## iii. Table of contents

- A. The combinatorial bridge lemma
- B. Euclidean epsilon-epsilon contraction identities

## iv. References

-/

@[expose] public section

open Matrix TensorSpecies Tensor KroneckerDelta


/-!

## A. Euclidean epsilon-epsilon contraction identities

-/

TODO "The contractions done here use the relativistic Levi-Civita tensor `ε4`
  but treat it as a Euclidean tensor. We should define
  a euclidean form of the Levi-Civita tensor and prove replace the
  results here with theorems about that tensor."

/-- **Full Euclidean Levi-Civita contraction** `∑_b (ε4)_b · (ε4)_b = 24` at the symbol level:
summing the square of every standard-basis component of `ε4` over all four `Fin 4` index slots,
paired naively (no metric), counts the `4! = 24` permutations. The Lorentz contraction
`ε^{μνρσ} ε_{μνρσ}` lowers one factor with `η` and equals `-24` instead. -/
lemma euclidLeviCivita_symbol_contract_zero :
    ∑ g : (Fin 4 → Fin 4), euclidLeviCivita g * euclidLeviCivita g = 24 := by
  have hcast : ∀ g : Fin 4 → Fin 4,
      ((generalizedKroneckerDelta g id : ℝ)) * (generalizedKroneckerDelta g id : ℝ)
        = ((generalizedKroneckerDelta g id * generalizedKroneckerDelta g id : ℤ) : ℝ) :=
    fun g => by push_cast; ring
  erw [Finset.sum_congr rfl fun g _ => hcast g, ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_self]
  norm_num

/-- **Triple Euclidean Levi-Civita contraction** `∑_h (ε4)_{a,h} · (ε4)_{b,h} = 6 · δ[a,b]` at
the symbol level: contracting three of the four `Fin 4` component slots of `ε4` with the naive
Kronecker pairing leaves one free pair `a, b` and the factor `3! = 6`. The Lorentz form carries
an extra `det η = -1`. -/
lemma euclidLeviCivita_symbol_contract_one (a b : Fin 4) :
    ∑ h : Fin 3 → Fin 4, euclidLeviCivita (Fin.cons a h) * euclidLeviCivita (Fin.cons b h)
      = 6 * ((kroneckerDelta a b : ℕ) : ℝ) := by
  have hcast : ∀ h' : Fin 3 → Fin 4,
      (generalizedKroneckerDelta (Fin.cons a h') id : ℝ)
        * (generalizedKroneckerDelta (Fin.cons b h') id : ℝ)
        = ((generalizedKroneckerDelta (Fin.cons a h') id
            * generalizedKroneckerDelta (Fin.cons b h') id : ℤ) : ℝ) :=
    fun h' => by push_cast; ring
  erw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_cons]
  push_cast; ring

/-- **Double Euclidean Levi-Civita contraction**
`∑_h (ε4)_{r,s,h} · (ε4)_{t,w,h} = 2 · (δ[r,t]·δ[s,w] - δ[r,w]·δ[s,t])` at the symbol level:
contracting two of the four `Fin 4` component slots of `ε4` with the naive Kronecker pairing
leaves two free pairs and the factor `2! = 2`. The Lorentz form carries an extra `det η = -1`. -/
lemma euclidLeviCivita_symbol_contract_two (r s t w : Fin 4) :
    ∑ h : Fin 2 → Fin 4, euclidLeviCivita (Fin.cons r (Fin.cons s h))
          * euclidLeviCivita (Fin.cons t (Fin.cons w h))
      = 2 * (((kroneckerDelta r t : ℕ) : ℝ) * ((kroneckerDelta s w : ℕ) : ℝ)
          - ((kroneckerDelta r w : ℕ) : ℝ) * ((kroneckerDelta s t : ℕ) : ℝ)) := by
  have hcast : ∀ h' : Fin 2 → Fin 4,
      (generalizedKroneckerDelta
          (Fin.cons r (Fin.cons (s) h')) id : ℝ)
        * (generalizedKroneckerDelta
          (Fin.cons t (Fin.cons (w) h')) id : ℝ)
        = ((generalizedKroneckerDelta
            (Fin.cons r (Fin.cons (s) h')) id
            * generalizedKroneckerDelta
              (Fin.cons t (Fin.cons (w) h')) id : ℤ) : ℝ) :=
    fun h' => by push_cast; ring
  erw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_cons₂]
  push_cast; ring
