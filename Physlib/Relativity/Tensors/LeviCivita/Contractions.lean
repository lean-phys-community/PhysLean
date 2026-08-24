/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.LeviCivita.Basic
public import Physlib.Mathematics.KroneckerDelta.Contraction
public import Physlib.Relativity.Tensors.RealTensor.Metrics.Basic
public import Physlib.Relativity.Tensors.RealTensor.Units.Basic
/-!

# Contraction identities for the Levi-Civita tensor

## i. Overview

This file proves the "epsilon-epsilon" contraction identities for the rank-four Levi-Civita
tensor `leviCivita` (notation `ε4`) in `d = 3`, stated in terms of the standard-basis
components of `ε4` itself (`realLorentzTensor.leviCivita_basis_repr_apply`).

The underlying facts about the `generalizedKroneckerDelta` alone, with no
tensor content, live in `Physlib.Mathematics.KroneckerDelta.Contraction`, next to the
definition of `generalizedKroneckerDelta`. Here we specialise those facts to the components of
`ε4`, where `(ε4)_b = (Tensor.basis _).repr ε4 b` is the standard-basis component of `ε4`, an
integer Levi-Civita symbol carried to the reals, and the sums run over the remaining
(uncontracted) component slots.

It also proves the Lorentzian tensor identities obtained by lowering all four indices of one
factor: the complete contraction is `-24`, while contracting three index pairs gives `-6` times
the unit tensor.

## ii. Key results

- `euclidLeviCivita_symbol_contract_zero` : full Euclidean contraction equals `24`.
- `euclidLeviCivita_symbol_contract_one` : the triple Euclidean contraction equals `6 · δ[a,b]`.
- `euclidLeviCivita_symbol_contract_two` :
  `∑_h (ε4)_{r,s,h} · (ε4)_{t,w,h} = 2 · (δ[r,t]·δ[s,w] - δ[r,w]·δ[s,t])`.
- `leviCivita_contract_self` : `ε^{μνρσ} ε_{μνρσ} = -24`.
- `leviCivita_contract_three` : `ε^{μνρσ} ε_{μνρτ} = -6 δ^σ_τ`.

## iii. Table of contents

- A. Euclidean epsilon-epsilon contraction identities
- B. Lorentzian epsilon-epsilon contraction identities
  - B.1. The epsilon-epsilon contraction identities

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
  simp only [euclidLeviCivita]
  rw [Finset.sum_congr rfl fun g _ => hcast g, ← Int.cast_sum,
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
  simp only [euclidLeviCivita]
  rw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum,
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
  simp only [euclidLeviCivita]
  rw [Finset.sum_congr rfl fun h' _ => hcast h', ← Int.cast_sum,
    sum_generalizedKroneckerDelta_mul_cons₂]
  push_cast; ring

/-!

## B. Lorentzian epsilon-epsilon contraction identities

-/

namespace realLorentzTensor

open TensorSpecies Tensor

open ComponentIdx.DropPairSection in
private lemma section_chain {cA cB : Fin 4 → Color}
    (h1 : (0 : Fin (0+1+1)) ≠ 1) (h2 : (1 : Fin (2+1+1)) ≠ 3)
    (h3 : (2 : Fin (4+1+1)) ≠ 5) (h4 : (3 : Fin (6+1+1)) ≠ 7)
    (x x1 x2 x3 : Fin 1 ⊕ Fin 3) :
    ((ofFinEquiv (S := realLorentzTensor 3) (c := Fin.append cA cB) h4
        ((ofFinEquiv h3
            ((ofFinEquiv h2
                ((ofFinEquiv h1 (fun j => j.elim0) (x, x)).1) (x1, x1)).1) (x2, x2)).1)
          (x3, x3)).1 : Fin (6+1+1) → Fin 1 ⊕ Fin 3)
      = ![x, x1, x2, x3, x, x1, x2, x3] := by
  funext m
  fin_cases m <;> rfl

private lemma prod_fst_vec {cA cB : Fin 4 → Color} (y0 y1 y2 y3 y4 y5 y6 y7 : Fin 1 ⊕ Fin 3) :
    (((ComponentIdx.prod (S := realLorentzTensor 3) (c := cA) (c1 := cB))
        (![y0,y1,y2,y3,y4,y5,y6,y7] : Fin (4+4) → Fin 1 ⊕ Fin 3)).1 :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![y0,y1,y2,y3] := by
  funext m; fin_cases m <;> rfl

private lemma prod_snd_vec {cA cB : Fin 4 → Color} (y0 y1 y2 y3 y4 y5 y6 y7 : Fin 1 ⊕ Fin 3) :
    (((ComponentIdx.prod (S := realLorentzTensor 3) (c := cA) (c1 := cB))
        (![y0,y1,y2,y3,y4,y5,y6,y7] : Fin (4+4) → Fin 1 ⊕ Fin 3)).2 :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![y4,y5,y6,y7] := by
  funext m; fin_cases m <;> rfl

section Nest
variable (x x1 x2 x3 y0 y1 y2 y3 : Fin 1 ⊕ Fin 3)

private lemma nest3 : (Fin.insertNth (3 : Fin (3+1)) y3
    (fun m => ![x, x1, x2, x3] (Fin.succAbove 3 m)) : Fin 4 → Fin 1 ⊕ Fin 3)
      = ![x, x1, x2, y3] := by
  funext m; fin_cases m <;> rfl

private lemma nest2 : (Fin.insertNth (2 : Fin (3+1)) y2
    (fun m => (![x, x1, x2, y3] : Fin 4 → Fin 1 ⊕ Fin 3) (Fin.succAbove 2 m)) :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![x, x1, y2, y3] := by
  funext m; fin_cases m <;> rfl

private lemma nest1 : (Fin.insertNth (1 : Fin (3+1)) y1
    (fun m => (![x, x1, y2, y3] : Fin 4 → Fin 1 ⊕ Fin 3) (Fin.succAbove 1 m)) :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![x, y1, y2, y3] := by
  funext m; fin_cases m <;> rfl

private lemma nest0 : (Fin.insertNth (0 : Fin (3+1)) y0
    (fun m => (![x, y1, y2, y3] : Fin 4 → Fin 1 ⊕ Fin 3) (Fin.succAbove 0 m)) :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![y0, y1, y2, y3] := by
  funext m; fin_cases m <;> rfl

end Nest

private lemma vec4_0 {a b c e : Fin 1 ⊕ Fin 3} :
    (![a,b,c,e] : Fin 4 → Fin 1 ⊕ Fin 3) 0 = a := rfl
private lemma vec4_1 {a b c e : Fin 1 ⊕ Fin 3} :
    (![a,b,c,e] : Fin 4 → Fin 1 ⊕ Fin 3) 1 = b := rfl
private lemma vec4_2 {a b c e : Fin 1 ⊕ Fin 3} :
    (![a,b,c,e] : Fin 4 → Fin 1 ⊕ Fin 3) 2 = c := rfl
private lemma vec4_3 {a b c e : Fin 1 ⊕ Fin 3} :
    (![a,b,c,e] : Fin 4 → Fin 1 ⊕ Fin 3) 3 = e := rfl

private lemma sum_mul_eta {d : ℕ} (f : (Fin 1 ⊕ Fin d) → ℝ) (y : Fin 1 ⊕ Fin d) :
    ∑ z : Fin 1 ⊕ Fin d, f z * minkowskiMatrix z y = f y * minkowskiMatrix y y := by
  change (f ᵥ* minkowskiMatrix) y = _
  rw [minkowskiMatrix.vecMul_apply]

/-- Bundling four independent basis indices into one component index. -/
private def vec4Equiv :
    ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
      ≃ (Fin 4 → Fin 1 ⊕ Fin 3) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  invFun v := (v 0, v 1, v 2, v 3)
  left_inv p := rfl
  right_inv v := by funext m; fin_cases m <;> rfl

/-- Bundling three independent basis indices into one component index. -/
private def vec3Equiv :
    ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≃ (Fin 3 → Fin 1 ⊕ Fin 3) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv p := rfl
  right_inv v := by funext m; fin_cases m <;> rfl

private lemma sum4_eq {M : Type} [AddCommMonoid M] (F : (Fin 4 → Fin 1 ⊕ Fin 3) → M) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3, ∑ x3 : Fin 1 ⊕ Fin 3,
        F ![x, x1, x2, x3]
      = ∑ v : Fin 4 → Fin 1 ⊕ Fin 3, F v := by
  rw [← Equiv.sum_comp vec4Equiv F]
  simp only [Fintype.sum_prod_type]
  rfl

open KroneckerDelta in
/-- Abbreviation for the summand of the fully contracted epsilon-epsilon sum. -/
private noncomputable def epsEtaSummand (v : Fin 4 → Fin 1 ⊕ Fin 3) : ℝ :=
  ((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ) *
    (((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
      * minkowskiMatrix (v 0) (v 0) * minkowskiMatrix (v 1) (v 1)
      * minkowskiMatrix (v 2) (v 2) * minkowskiMatrix (v 3) (v 3))

open KroneckerDelta in
private lemma epsEtaSummand_eq (v : Fin 4 → Fin 1 ⊕ Fin 3) : epsEtaSummand v =
    - (((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
      * ((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) : ℝ)) := by
  rw [epsEtaSummand]
  by_cases hA : generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
      (id : Fin 4 → Fin 4) = 0
  · rw [hA]; norm_num
  · have hinj : Function.Injective (fun i => finSumFinEquiv (v i)) := by
      by_contra hni
      exact hA (leviCivitaSymbol_eq_zero_of_not_injective hni)
    have hv : Function.Injective v := Function.Injective.of_comp hinj
    have hp := minkowskiMatrix.prod_diagonal_comp_of_injective hv
    rw [Fin.prod_univ_four] at hp
    linear_combination
      (((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) : ℝ) *
        ((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) : ℝ)) * hp

open KroneckerDelta in
private lemma sum_epsEtaSummand : ∑ v : Fin 4 → Fin 1 ⊕ Fin 3, epsEtaSummand v = -24 := by
  have hsum : ∑ v : Fin 4 → Fin 1 ⊕ Fin 3,
      (generalizedKroneckerDelta (fun i => finSumFinEquiv (v i)) (id : Fin 4 → Fin 4)
        * generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) = 24 := by
    calc
      _ = ∑ g : Fin 4 → Fin 4,
          generalizedKroneckerDelta g (id : Fin 4 → Fin 4) *
            generalizedKroneckerDelta g (id : Fin 4 → Fin 4) :=
        Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin 4))
          (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4)) _ _ (fun _ => rfl)
      _ = 24 := sum_generalizedKroneckerDelta_mul_self
  have h : (∑ v : Fin 4 → Fin 1 ⊕ Fin 3,
      (((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * ((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
            (id : Fin 4 → Fin 4) : ℤ) : ℝ))) = 24 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsum
  rw [Finset.sum_congr rfl (fun v _ => epsEtaSummand_eq v), Finset.sum_neg_distrib, h]

open ComponentIdx.DropPairSection in
private lemma section_chain3 {cA cB : Fin 4 → Color}
    (h1 : (0 : Fin (2+1+1)) ≠ 2) (h2 : (1 : Fin (4+1+1)) ≠ 4) (h3 : (2 : Fin (6+1+1)) ≠ 6)
    (b : Fin 2 → Fin 1 ⊕ Fin 3) (x x1 x2 : Fin 1 ⊕ Fin 3) :
    ((ofFinEquiv (S := realLorentzTensor 3) (c := Fin.append cA cB) h3
        ((ofFinEquiv h2 ((ofFinEquiv h1 b (x, x)).1) (x1, x1)).1) (x2, x2)).1 :
      Fin (6+1+1) → Fin 1 ⊕ Fin 3)
      = ![x, x1, x2, b 0, x, x1, x2, b 1] := by
  funext m
  fin_cases m <;> rfl

private lemma sum3_eq' {M : Type} [AddCommMonoid M]
    (F : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → M) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3, F x x1 x2
      = ∑ w : Fin 3 → Fin 1 ⊕ Fin 3, F (w 0) (w 1) (w 2) := by
  rw [← Equiv.sum_comp vec3Equiv (fun w => F (w 0) (w 1) (w 2))]
  simp only [Fintype.sum_prod_type]
  rfl

open KroneckerDelta in
private lemma eps_eta_three (a b c y0 y1 : Fin 1 ⊕ Fin 3) :
    ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y0] :
        Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
      * (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y1] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * minkowskiMatrix a a * minkowskiMatrix b b * minkowskiMatrix c c
        * minkowskiMatrix y1 y1)
      = - (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)) := by
  by_cases hA : generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y1] :
      Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) = 0
  · rw [hA]; norm_num
  · have hinj : Function.Injective
        (fun i => finSumFinEquiv ((![a,b,c,y1] : Fin 4 → Fin 1 ⊕ Fin 3) i)) := by
      by_contra hni
      exact hA (leviCivitaSymbol_eq_zero_of_not_injective hni)
    have hv : Function.Injective (![a,b,c,y1] : Fin 4 → Fin 1 ⊕ Fin 3) :=
      Function.Injective.of_comp hinj
    have hp := minkowskiMatrix.prod_diagonal_comp_of_injective hv
    rw [Fin.prod_univ_four] at hp
    simp only [vec4_0, vec4_1, vec4_2, vec4_3] at hp
    linear_combination
      (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ) *
        ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)) * hp

open KroneckerDelta in
private lemma sum_eps_three (y0 y1 : Fin 1 ⊕ Fin 3) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3,
      ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
          * minkowskiMatrix x x * minkowskiMatrix x1 x1 * minkowskiMatrix x2 x2
          * minkowskiMatrix y1 y1)
      = -6 * (if y0 = y1 then 1 else 0) := by
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun x2 _ => eps_eta_three x x1 x2 y0 y1]
  simp only [Finset.sum_neg_distrib]
  have hZ : ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3,
      (generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4)
        * generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4))
      = 6 * ((kroneckerDelta (finSumFinEquiv y0) (finSumFinEquiv y1) : ℕ) : ℤ) := by
    rw [sum3_eq' (fun x x1 x2 => generalizedKroneckerDelta (fun i =>
        finSumFinEquiv ((![x, x1, x2, y0] : Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4)
      * generalizedKroneckerDelta (fun i =>
        finSumFinEquiv ((![x, x1, x2, y1] : Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4))]
    have hs (y : Fin 1 ⊕ Fin 3) (w : Fin 3 → Fin 1 ⊕ Fin 3) :
        (fun i => finSumFinEquiv
          ((![w 0, w 1, w 2, y] : Fin 4 → Fin 1 ⊕ Fin 3) i)) =
          Fin.snoc (fun i => finSumFinEquiv (w i)) (finSumFinEquiv y) := by
      funext i
      fin_cases i <;> rfl
    rw [Finset.sum_congr rfl fun w _ => by rw [hs y0 w, hs y1 w]]
    calc
      _ = ∑ h : Fin 3 → Fin 4,
          generalizedKroneckerDelta (Fin.snoc h (finSumFinEquiv y0)) id *
            generalizedKroneckerDelta (Fin.snoc h (finSumFinEquiv y1)) id :=
        Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin 3))
          (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4)) _ _ (fun _ => rfl)
      _ = _ := sum_generalizedKroneckerDelta_mul_snoc _ _
  have hR : ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3,
      (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ))
      = 6 * (if y0 = y1 then 1 else 0) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hZ
    push_cast at this
    rw [this]
    by_cases hy : y0 = y1
    · rw [hy]; simp [KroneckerDelta.eq_one_of_same]
    · rw [if_neg hy, KroneckerDelta.eq_zero_of_ne (fun hc => hy (finSumFinEquiv.injective hc))]
      norm_num
  rw [hR]
  ring

open KroneckerDelta in
private lemma sum_eps_three' (y0 y1 : Fin 1 ⊕ Fin 3) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3,
      ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * (((Tensor.basis ![Color.up, Color.up, Color.up, Color.up]).repr ε4)
            (![x,x1,x2,y1] : Fin 4 → Fin 1 ⊕ Fin 3)
          * minkowskiMatrix x x * minkowskiMatrix x1 x1 * minkowskiMatrix x2 x2
          * minkowskiMatrix y1 y1)
      = -6 * (if y0 = y1 then 1 else 0) := by
  rw [← sum_eps_three y0 y1]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun x2 _ => ?_
  rw [leviCivita_basis_repr_apply]

/-!

### B.1. The epsilon-epsilon contraction identities

-/

/-- Contracting three indices of the Lorentzian Levi-Civita tensor with a fully lowered copy gives
`-6` times the mixed-index unit tensor. -/
lemma leviCivita_contract_three : {ε4 | μ ν ρ σ ⊗ ε4 | τ(μ) τ(ν) τ(ρ) τ(τ) =
    (-6) • unitTensor (S := realLorentzTensor) Color.down | σ τ }ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [contrT_basis_repr_apply_eq_fin, prodT_basis_repr_apply,
    toDualMapAtIndex_basis_repr_apply, leviCivita_basis_repr_apply,
    permT_basis_repr_symm_apply,
    section_chain3, prod_fst_vec, prod_snd_vec, nest3, nest2, nest1, nest0,
    vec4_0, vec4_1, vec4_2, vec4_3, sum_mul_eta]
  simp only [map_zsmul, Finsupp.coe_smul, Pi.smul_apply, zsmul_eq_mul,
    basisIdxCongr_eq_refl, Equiv.refl_apply, unitTensor_repr_apply Color.down]
  rw [IsReindexing.inv_eq_self_of_pointwise_eq _ (by decide),
    IsReindexing.inv_eq_self_of_pointwise_eq _ (by decide), sum_eps_three' (b 0) (b 1)]
  norm_num

-- `checkType` linter: whnf on this tensor-notation statement exceeds the
-- linter's 200k-heartbeat budget (since the v4.32.0 bump; still the case on
-- v4.33.0). The proof itself elaborates within the default budget.
/-- Fully contracting the Lorentzian Levi-Civita tensor with a lowered copy gives `-24`. -/
@[nolint checkType]
lemma leviCivita_contract_self :
    {ε4 | μ ν ρ σ ⊗ ε4 | τ(μ) τ(ν) τ(ρ) τ(σ)}ᵀ.toField = - 24 := by
  rw [Tensor.toField_eq_repr]
  simp only [contrT_basis_repr_apply_eq_fin, prodT_basis_repr_apply,
    toDualMapAtIndex_basis_repr_apply, leviCivita_basis_repr_apply,
    section_chain, prod_fst_vec, prod_snd_vec, nest3, nest2, nest1, nest0]
  simp only [vec4_0, vec4_1, vec4_2, vec4_3, sum_mul_eta]
  rw [← sum_epsEtaSummand, ← sum4_eq epsEtaSummand]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun x3 _ => ?_
  rw [epsEtaSummand, leviCivita_basis_repr_apply]
  simp only [vec4_0, vec4_1, vec4_2, vec4_3]

end realLorentzTensor
