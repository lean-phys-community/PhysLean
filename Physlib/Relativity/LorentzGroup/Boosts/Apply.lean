/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.Tensorial
/-!

## Boosts applied to Lorentz vectors

These recover what one would describe as the ordinary Lorentz transformations
of Lorentz vectors.

-/

@[expose] public section

namespace Lorentz
open realLorentzTensor
open LorentzGroup
variable {d : ℕ}

namespace Vector

lemma boost_time_eq (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Vector d) :
    (boost i β hβ • p) (Sum.inl 0) = γ β * (p (Sum.inl 0) - β * p (Sum.inr i)) := by
  rw [smul_eq_sum, Fintype.sum_sum_type,
    Fintype.sum_eq_single i fun b hb => by simp [boost_inl_0_inr_other hβ hb]]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
    boost_inl_0_inl_0, boost_inl_0_inr_self, neg_mul]
  ring

lemma boost_inr_self_eq (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Vector d) :
    (boost i β hβ • p) (Sum.inr i) = γ β * (p (Sum.inr i) - β * p (Sum.inl 0)) := by
  rw [smul_eq_sum, Fintype.sum_sum_type,
    Fintype.sum_eq_single i fun b hb => by simp [boost_inr_self_inr_other hβ hb]]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
    boost_inr_self_inl_0, neg_mul, boost_inr_self_inr_self]
  ring

lemma boost_inr_other_eq (i j : Fin d) (hji : j ≠ i) (β : ℝ) (hβ : |β| < 1) (p : Vector d) :
    (boost i β hβ • p) (Sum.inr j) = p (Sum.inr j) := by
  rw [smul_eq_sum, Fintype.sum_sum_type,
    Fintype.sum_eq_single j fun b hb => by simp [boost_inr_other_inr hβ hji, Ne.symm hb]]
  simp [boost_inr_other_inl_0 hβ hji, boost_inr_other_inr hβ hji]

lemma boost_toCoord_eq (i : Fin d) (β : ℝ) (hβ : |β| < 1) (p : Vector d) :
    (boost i β hβ • p) = fun j =>
      match j with
      | Sum.inl 0 => γ β * (p (Sum.inl 0) - β * p (Sum.inr i))
      | Sum.inr j =>
        if j = i then γ β * (p (Sum.inr i) - β * p (Sum.inl 0))
        else p (Sum.inr j) := by
  funext j
  match j with
  | Sum.inl 0 => rw [boost_time_eq]
  | Sum.inr j =>
    by_cases hj : j = i
    · simp [hj, boost_inr_self_eq]
    · simp [hj, boost_inr_other_eq _ _ hj]

end Vector

end Lorentz
