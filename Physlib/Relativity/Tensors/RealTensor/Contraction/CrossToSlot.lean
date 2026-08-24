/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Contraction.CrossToEnd
/-!

# Components of real Lorentz result-to-slot contractions

## i. Overview

This file gives the standard-basis component formula for `crossToSlot` on real Lorentz tensors.
The formula keeps the uncontracted index of the rank-two tensor in the selected result slot.

## ii. Key results

- `realLorentzTensor.crossToSlot_basis_repr_apply_eq_fin` expresses each component of a
  result-to-slot contraction as a sum over the contracted Lorentz index.

## iii. Table of contents

- A. Basis components

## iv. References

-/

@[expose] public section

noncomputable section

namespace realLorentzTensor

open TensorSpecies Tensor

/-!

## A. Basis components

-/

/-- For real Lorentz tensors, the component formula for `crossToSlot` collapses to one sum because
the standard contravariant and covariant bases are dual under contraction. -/
lemma crossToSlot_basis_repr_apply_eq_fin {d nA : ℕ} {c : Fin (nA + 1) → Color}
    {cM : Fin 2 → Color} (i : Fin (nA + 1)) (j : Fin 2)
    (hc : (realLorentzTensor d).τ (c i) = cM j) (M : ℝT(d, cM)) (t : ℝT(d, c))
    (φ : ComponentIdx (S := realLorentzTensor d)
      (Function.update c i (cM (j.succAbove 0)))) :
    (Tensor.basis _).repr (crossToSlot i j hc M t) φ =
      ∑ x : Fin 1 ⊕ Fin d,
        (Tensor.basis c).repr t (i.insertNth x (fun m => φ (i.succAbove m))) *
          (Tensor.basis cM).repr M (j.insertNth x (fun _ => φ i)) := by
  rw [crossToSlot_eq_crossToEnd, permT_basis_repr_symm_apply,
    crossToEnd_basis_repr_apply_eq_fin]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [basisIdxCongr_eq_refl, Equiv.refl_apply]
  congr 2
  · funext m
    induction m using Fin.succAboveCases (i := i) with
    | x => rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
    | p q =>
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      refine congrArg φ ?_
      rw [IsReindexing.inv_equiv_symm_eq, ← Fin.append_succAbove_const_eq_cycleIcc i,
        Fin.append_left]
  · funext m
    induction m using Fin.succAboveCases (i := j) with
    | x => rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
    | p q =>
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      refine congrArg φ ?_
      rw [IsReindexing.inv_equiv_symm_eq, ← Fin.append_succAbove_const_eq_cycleIcc i,
        Fin.append_right]

end realLorentzTensor
