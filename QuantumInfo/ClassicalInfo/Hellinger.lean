/-
Copyright (c) 2026 Dennj Osele. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dennj Osele
-/
module

public import QuantumInfo.ClassicalInfo.Distribution
public import Mathlib.Data.Real.Sqrt

/-! # Hellinger overlap for finite probability distributions

This file contains finite-distribution API for the Hellinger overlap, also known as the
Bhattacharyya coefficient. The statements are deliberately classical/probabilistic and avoid
quantum-specific matrix or state types.
-/

@[expose] public section

noncomputable section
universe u

open scoped BigOperators

namespace ProbDistribution

/-- The Hellinger overlap, or Bhattacharyya coefficient, of two finite probability distributions. -/
def hellingerOverlap {κ : Type u} [Fintype κ] (P Q : ProbDistribution κ) : ℝ :=
  ∑ x, Real.sqrt ((P x : ℝ) * (Q x : ℝ))

/-- The Hellinger overlap is multiplicative over independent product distributions. -/
theorem hellingerOverlap_prod {κ η : Type u} [Fintype κ] [Fintype η]
    (P₁ Q₁ : ProbDistribution κ) (P₂ Q₂ : ProbDistribution η) :
    hellingerOverlap (ProbDistribution.prod P₁ P₂) (ProbDistribution.prod Q₁ Q₂) =
      hellingerOverlap P₁ Q₁ * hellingerOverlap P₂ Q₂ := by
  rw [hellingerOverlap, hellingerOverlap, hellingerOverlap, Fintype.sum_prod_type]
  calc
    (∑ x : κ, ∑ y : η,
        Real.sqrt ((((P₁ x) * (P₂ y) : Prob) : ℝ) *
          (((Q₁ x) * (Q₂ y) : Prob) : ℝ))) =
        ∑ x : κ, ∑ y : η,
          Real.sqrt ((P₁ x : ℝ) * (Q₁ x : ℝ)) *
            Real.sqrt ((P₂ y : ℝ) * (Q₂ y : ℝ)) := by
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (∑ x : κ, Real.sqrt ((P₁ x : ℝ) * (Q₁ x : ℝ))) *
          ∑ y : η, Real.sqrt ((P₂ y : ℝ) * (Q₂ y : ℝ)) := by
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]

/-- Closed form for the Hellinger overlap of two Bernoulli distributions. -/
theorem hellingerOverlap_coin (p q : Prob) :
    hellingerOverlap (ProbDistribution.coin p) (ProbDistribution.coin q) =
      Real.sqrt ((p : ℝ) * (q : ℝ)) +
        Real.sqrt ((1 - (p : ℝ)) * (1 - (q : ℝ))) := by
  simp [hellingerOverlap, Fin.sum_univ_two]

/-- Distinct Bernoulli parameters have Hellinger overlap strictly less than one. -/
theorem hellingerOverlap_coin_lt_one (p q : Prob) (hpq : (p : ℝ) < q) :
    hellingerOverlap (ProbDistribution.coin p) (ProbDistribution.coin q) < 1 := by
  rw [hellingerOverlap_coin]
  have hp0 : 0 ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hq0 : 0 ≤ (q : ℝ) := q.2.1
  have hq1 : (q : ℝ) ≤ 1 := q.2.2
  have hsqrt_lt :
      Real.sqrt (((p : ℝ) * q) * ((1 - p) * (1 - q))) <
        ((p : ℝ) + q - 2 * p * q) / 2 := by
    rw [Real.sqrt_lt' (by
      nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hq1),
        mul_pos (lt_of_le_of_lt hp0 hpq) (sub_pos.mpr (hpq.trans_le hq1))])]
    nlinarith [sq_pos_of_pos (sub_pos.mpr hpq)]
  exact (sq_lt_sq₀ (by positivity) (by positivity)).mp <| by
    rw [add_sq, Real.sq_sqrt (mul_nonneg hp0 hq0),
      Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hp1) (sub_nonneg.mpr hq1))]
    nlinarith [(Real.sqrt_mul (mul_nonneg hp0 hq0) ((1 - p) * (1 - q))).symm]

end ProbDistribution
