/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Basic
public import Physlib.SpaceAndTime.SpaceTime.Basic
/-!

# Boosts of space time

## i. Overview

In this module we consider boosts acting on points in space time,and recover simple
formulae for such applications.

Note that the material here currently assumes that the speed of light `c = 1`.

## ii. Key results

- `boost_x_smul` : The action of a boost in the x-direction on a point in space time.

## iii. Table of contents

- A. The action of a boost in the x-direction

## iv. References

See e.g.
- https://en.wikipedia.org/wiki/Lorentz_transformation

-/

@[expose] public section

noncomputable section

namespace SpaceTime

open Time
open Space
open LorentzGroup
/-!

## A. The action of a boost in the x-direction

We show that boosting in the `x`-direction takes `(t, x, y, z)` to
`(γ (t - β x), γ (x - β t), y, z)`.

-/

lemma boost_x_smul (β : ℝ) (hβ : |β| < 1) (x : SpaceTime) :
    LorentzGroup.boost (d := 3) 0 β hβ • x =
      fun | Sum.inl 0 => γ β * (x (Sum.inl 0) - β * x (Sum.inr 0))
          | Sum.inr 0 => γ β * (x (Sum.inr 0) - β * x (Sum.inl 0))
          | Sum.inr 1=> x (Sum.inr 1)
          | Sum.inr 2=> x (Sum.inr 2) := by
  funext i
  fin_cases i <;>
    simp [Lorentz.Vector.smul_eq_sum, Fin.sum_univ_three, boost_inl_0_inr_other,
      boost_inr_other_inr, boost_inr_inr_other, boost_inr_other_inl_0] <;>
    ring

lemma boost_zero_apply_time_space {d : ℕ} {β : ℝ} (hβ : |β| < 1) (c : SpeedOfLight)
    (t : Time) (x : Space d.succ) :
    ((boost (0 : Fin d.succ) β hβ)⁻¹ • (SpaceTime.toTimeAndSpace c).symm (t, x)) =
    (SpaceTime.toTimeAndSpace c).symm
    (γ β * (t.val + β /c * x 0),
    ⟨fun
      | (0 : Fin d.succ) => γ β * (x 0 + c * β * t.val)
      | ⟨Nat.succ n, ih⟩ => x ⟨Nat.succ n, ih⟩⟩) := by
  funext μ
  rw [boost_inverse, Lorentz.Vector.smul_eq_sum]
  simp only [Nat.succ_eq_add_one, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton, Fin.sum_univ_succ, toTimeAndSpace_symm_apply_inl,
    toTimeAndSpace_symm_apply_inr]
  match μ with
  | Sum.inl 0 =>
    simp [γ_neg]
    field_simp
  | Sum.inr ⟨0, h⟩ =>
    simp only [toTimeAndSpace_symm_apply_inr]
    simp [γ_neg]
    ring
  | Sum.inr ⟨Nat.succ n, h⟩ =>
    simp only [Nat.succ_eq_add_one, Fin.isValue, boost_zero_inr_nat_succ_inl_0, zero_mul,
      boost_zero_inr_nat_succ_inr_0, zero_add, toTimeAndSpace_symm_apply_inr]
    rw [Finset.sum_eq_single ⟨n, by omega⟩] <;>
      simp +contextual [boost_inr_inr_other, Fin.ext_iff]

end SpaceTime

end
