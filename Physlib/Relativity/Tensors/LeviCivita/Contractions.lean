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

**These are Euclidean contractions, not Lorentz contractions.** Each of the four component
slots is treated as a Euclidean `Fin 4` index (the component index type `Fin 1 ⊕ Fin 3`
transported along `finSumFinEquiv`), and a repeated slot is summed against itself with the naive
Kronecker pairing `δ[a,b]`. No metric appears, so the resulting constants are the *positive*
`24`, `6`, `2`. A genuine Lorentz contraction `ε^{μ}{}_{...}` would instead raise or lower one
factor with the Lorentz metric `η` on the split index type `Fin 1 ⊕ Fin 3` (one timelike, three
spacelike directions); since `det η = -1` in four dimensions, each identity would then pick up a
sign and one would recover the textbook `ε^{μνρσ} ε_{μνρσ} = -24`, `ε^{μνρσ} ε_{μνρτ} = -6 δ^σ_τ`
and `ε^{μνρσ} ε_{μντω} = -2 (δ^ρ_τ δ^σ_ω - δ^ρ_ω δ^σ_τ)`. Writing that covariant form requires the
fully index-lowered Levi-Civita tensor `ε_{μνρσ}`, which is not developed here; these Euclidean
component identities are the reusable ingredient from which such a covariant statement would be
assembled (see the `TODO` below).

The purely combinatorial backbone — facts about the `generalizedKroneckerDelta` alone, with no
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

namespace realLorentzTensor

/-!

## A. The combinatorial bridge lemma

The integer Levi-Civita symbol is `generalizedKroneckerDelta f id` for `f : Fin 4 → Fin 4`, and
`realLorentzTensor.leviCivita_basis_repr_apply` identifies it with the standard-basis component of
`ε4` after transporting the component index along `finSumFinEquiv`. The symbol-level value of each
contraction now lives in `Physlib.Mathematics.KroneckerDelta.Contraction`
(`sum_generalizedKroneckerDelta_mul_self`, `sum_generalizedKroneckerDelta_mul_cons`,
`sum_generalizedKroneckerDelta_mul_cons₂`), together with the `finSumFinEquiv`-invariance of the
Kronecker delta (`kroneckerDelta_finSumFinEquiv`). The one remaining private lemma here is the
bookkeeping needed to switch between the component indices `Fin 1 ⊕ Fin 3` and the `Fin 4` labels.

-/

/-- Transporting a `Fin.cons` along `finSumFinEquiv` component-wise. -/
private lemma cons_finSum {n : ℕ} (a : Fin 1 ⊕ Fin 3) (h : Fin n → (Fin 1 ⊕ Fin 3)) :
    (fun i => finSumFinEquiv ((Fin.cons a h : Fin (n + 1) → _) i))
      = Fin.cons (finSumFinEquiv a) (fun j => finSumFinEquiv (h j)) := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j; rfl

/-!

## B. Euclidean epsilon-epsilon contraction identities

-/

TODO "A Lorentz-indexed Levi-Civita tensor on the split index type `Fin 1 ⊕ Fin 3`, whose
  contractions raise and lower indices with the Lorentz metric `η` (rather than the naive
  Euclidean Kronecker pairing used for the `Fin 4` indices here), is future work. A natural home
  is ./Relativity/Tensors/RealEuclidean/Basic.lean, defining it for now directly via
  generalizedKroneckerDelta. This is a large change and is intentionally out of scope here."

/-- **Full Euclidean Levi-Civita contraction** `∑_b (ε4)_b · (ε4)_b = 24` at the symbol level:
summing the square of every standard-basis component of `ε4` over all four `Fin 4` index slots,
paired naively (no metric), counts the `4! = 24` permutations. The Lorentz contraction
`ε^{μνρσ} ε_{μνρσ}` lowers one factor with `η` and equals `-24` instead. -/
lemma leviCivita_symbol_contract_zero :
    ∑ b : ComponentIdx (S := realLorentzTensor 3)
        ![Color.up, Color.up, Color.up, Color.up],
      (Tensor.basis _).repr ε4 b * (Tensor.basis _).repr ε4 b = 24 := by
  simp_rw [leviCivita_basis_repr_apply]
  rw [show (∑ b : ComponentIdx (S := realLorentzTensor 3)
        ![Color.up, Color.up, Color.up, Color.up],
        (generalizedKroneckerDelta (fun i => finSumFinEquiv (b i)) (id : Fin 4 → Fin 4) : ℝ)
          * (generalizedKroneckerDelta (fun i => finSumFinEquiv (b i)) (id : Fin 4 → Fin 4) : ℝ))
      = ∑ g : Fin 4 → Fin 4,
        (generalizedKroneckerDelta g id : ℝ) * (generalizedKroneckerDelta g id : ℝ) from
    Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin 4 => finSumFinEquiv)) _ _ (fun x => rfl)]
  have hcast : ∀ g : Fin 4 → Fin 4,
      ((generalizedKroneckerDelta g id : ℝ)) * (generalizedKroneckerDelta g id : ℝ)
        = ((generalizedKroneckerDelta g id * generalizedKroneckerDelta g id : ℤ) : ℝ) :=
    fun g => by push_cast; ring
  rw [Finset.sum_congr rfl fun g _ => hcast g, ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_self]
  norm_num

/-- **Triple Euclidean Levi-Civita contraction** `∑_h (ε4)_{a,h} · (ε4)_{b,h} = 6 · δ[a,b]` at
the symbol level: contracting three of the four `Fin 4` component slots of `ε4` with the naive
Kronecker pairing leaves one free pair `a, b` and the factor `3! = 6`. The Lorentz form carries
an extra `det η = -1`. -/
lemma leviCivita_symbol_contract_one (a b : Fin 1 ⊕ Fin 3) :
    ∑ h : Fin 3 → (Fin 1 ⊕ Fin 3),
        (Tensor.basis _).repr ε4 (Fin.cons a h) * (Tensor.basis _).repr ε4 (Fin.cons b h)
      = 6 * ((kroneckerDelta a b : ℕ) : ℝ) := by
  simp_rw [leviCivita_basis_repr_apply, cons_finSum]
  rw [show (∑ h : Fin 3 → (Fin 1 ⊕ Fin 3),
        (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv a) (fun j => finSumFinEquiv (h j)))
            (id : Fin 4 → Fin 4) : ℝ)
          * (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv b) (fun j => finSumFinEquiv (h j)))
            (id : Fin 4 → Fin 4) : ℝ))
      = ∑ h' : Fin 3 → Fin 4,
        (generalizedKroneckerDelta (Fin.cons (finSumFinEquiv a) h') id : ℝ)
          * (generalizedKroneckerDelta (Fin.cons (finSumFinEquiv b) h') id : ℝ) from
    Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin 3 => finSumFinEquiv)) _ _ (fun h => rfl)]
  have hcast : ∀ h' : Fin 3 → Fin 4,
      (generalizedKroneckerDelta (Fin.cons (finSumFinEquiv a) h') id : ℝ)
        * (generalizedKroneckerDelta (Fin.cons (finSumFinEquiv b) h') id : ℝ)
        = ((generalizedKroneckerDelta (Fin.cons (finSumFinEquiv a) h') id
            * generalizedKroneckerDelta (Fin.cons (finSumFinEquiv b) h') id : ℤ) : ℝ) :=
    fun h' => by push_cast; ring
  rw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_cons, kroneckerDelta_finSumFinEquiv]
  push_cast; ring

/-- **Double Euclidean Levi-Civita contraction**
`∑_h (ε4)_{r,s,h} · (ε4)_{t,w,h} = 2 · (δ[r,t]·δ[s,w] - δ[r,w]·δ[s,t])` at the symbol level:
contracting two of the four `Fin 4` component slots of `ε4` with the naive Kronecker pairing
leaves two free pairs and the factor `2! = 2`. The Lorentz form carries an extra `det η = -1`. -/
lemma leviCivita_symbol_contract_two (r s t w : Fin 1 ⊕ Fin 3) :
    ∑ h : Fin 2 → (Fin 1 ⊕ Fin 3),
        (Tensor.basis _).repr ε4 (Fin.cons r (Fin.cons s h))
          * (Tensor.basis _).repr ε4 (Fin.cons t (Fin.cons w h))
      = 2 * (((kroneckerDelta r t : ℕ) : ℝ) * ((kroneckerDelta s w : ℕ) : ℝ)
          - ((kroneckerDelta r w : ℕ) : ℝ) * ((kroneckerDelta s t : ℕ) : ℝ)) := by
  simp_rw [leviCivita_basis_repr_apply, cons_finSum]
  rw [show (∑ h : Fin 2 → (Fin 1 ⊕ Fin 3),
        (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv r)
              (Fin.cons (finSumFinEquiv s) (fun j => finSumFinEquiv (h j))))
            (id : Fin 4 → Fin 4) : ℝ)
          * (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv t)
              (Fin.cons (finSumFinEquiv w) (fun j => finSumFinEquiv (h j))))
            (id : Fin 4 → Fin 4) : ℝ))
      = ∑ h' : Fin 2 → Fin 4,
        (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv r) (Fin.cons (finSumFinEquiv s) h')) id : ℝ)
          * (generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv t) (Fin.cons (finSumFinEquiv w) h')) id : ℝ) from
    Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin 2 => finSumFinEquiv)) _ _ (fun h => rfl)]
  have hcast : ∀ h' : Fin 2 → Fin 4,
      (generalizedKroneckerDelta
          (Fin.cons (finSumFinEquiv r) (Fin.cons (finSumFinEquiv s) h')) id : ℝ)
        * (generalizedKroneckerDelta
          (Fin.cons (finSumFinEquiv t) (Fin.cons (finSumFinEquiv w) h')) id : ℝ)
        = ((generalizedKroneckerDelta
            (Fin.cons (finSumFinEquiv r) (Fin.cons (finSumFinEquiv s) h')) id
            * generalizedKroneckerDelta
              (Fin.cons (finSumFinEquiv t) (Fin.cons (finSumFinEquiv w) h')) id : ℤ) : ℝ) :=
    fun h' => by push_cast; ring
  rw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_cons₂,
    kroneckerDelta_finSumFinEquiv, kroneckerDelta_finSumFinEquiv,
    kroneckerDelta_finSumFinEquiv, kroneckerDelta_finSumFinEquiv]
  push_cast; ring

end realLorentzTensor
