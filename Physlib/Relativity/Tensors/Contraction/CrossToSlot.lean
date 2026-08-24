/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Relativity.Tensors.Contraction.CrossToEnd
/-!

# Result-to-slot contraction against a rank-2 tensor

## i. Overview

`crossToEnd` deposits the surviving index of a slot contraction at the end of the survivor list.
Raising and lowering a named index instead wants the replacement to stay *in place*: contracting
slot `i` of `t` against a rank-2 tensor `M` (a metric, the unit tensor) should return `t` with only
slot `i`'s color changed, `T^{μ}{}_{νρ} ↦ T_{μνρ}`. `crossToSlot i j hc M` is that operation, and
`crossToSlot_eq_crossToEnd` is the one place the two conventions meet.

This module stays at the `CommRing` altitude of `crossToEnd`; the `RCLike` round trips built on the
operation live with the unit-tensor collapse theory in
`Physlib.Relativity.Tensors.Contraction.UnitTensorContraction`.

## ii. Key results

- `TensorSpecies.Tensor.crossToSlot` : contract slot `i` against slot `j` of a rank-2 tensor and
    rotate the survivor back into position `i`; raising and lowering a named index.
- `TensorSpecies.Tensor.crossToSlot_eq_crossToEnd` : the bridge to the result-to-end convention.
- `TensorSpecies.Tensor.crossToSlotInv` : the returning half of a round trip, the contraction
    against the second factor with the round trip's color cast absorbed.
- `TensorSpecies.Tensor.crossToSlot_permT_right_id` : an identity reindexing of the rank-2 tensor
    passes through the contraction.
- `TensorSpecies.Tensor.crossToSlot_equivariant` : the contraction commutes with the `G`-action.

## iii. Table of contents

- A. The result-to-slot contraction

## iv. References

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C : Type} {G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k G (V c)} {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
    {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

/-!

## A. The result-to-slot contraction

-/

/-- The survivor color of `crossToEnd i j` against a rank-2 tensor of color `cM` is `c` with
  slot `i` replaced by the surviving color `cM (j.succAbove 0)`, once the survivors are rotated
  back by the inverse of the cycle `[i, last]`. -/
lemma IsReindexing.crossToSlot_cycle {nA : ℕ} {c : Fin (nA + 1) → C} {cM : Fin 2 → C}
    (i : Fin (nA + 1)) (j : Fin 2) :
    IsReindexing
      (Fin.append (c ∘ i.succAbove) (cM ∘ j.succAbove))
      (Function.update c i (cM (j.succAbove 0)))
      ⇑(Fin.cycleIcc i (Fin.last nA)).symm := by
  refine ⟨(Fin.cycleIcc i (Fin.last nA)).symm.bijective, fun y => ?_⟩
  obtain ⟨z, rfl⟩ : ∃ z, y = Fin.cycleIcc i (Fin.last nA) z :=
    ⟨_, (Equiv.apply_symm_apply _ _).symm⟩
  rw [Equiv.symm_apply_apply, ← Fin.append_succAbove_const_eq_cycleIcc i]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) z
  · rw [Fin.append_left, Fin.append_left, Function.comp_apply,
      Function.update_of_ne (Fin.succAbove_ne i a)]
  · rw [Fin.append_right, Fin.append_right, Function.comp_apply, Function.update_self]
    fin_cases a
    rfl

/-- Contract slot `i` of `t` against slot `j` of the rank-2 tensor `M`, whose `j`-slot color must
  equal the dual color `τ (c i)` (propositionally, via `hc`), and rotate `M`'s surviving slot back
  into position `i`. The result is `t` with slot `i` relabelled to `M`'s surviving color.

  This is raising and lowering a named index; the metric case is `j = 0`,
  `M = metricTensor (τ (c i))`. Because `hc` is propositional, a rank-2 tensor whose slot color
  matches only up to an equality enters directly, with no transport. -/
noncomputable def crossToSlot {nA : ℕ} {c : Fin (nA + 1) → C} {cM : Fin 2 → C}
    (i : Fin (nA + 1)) (j : Fin 2) (hc : S.τ (c i) = cM j) (M : S.Tensor cM) :
    S.Tensor c →ₗ[k] S.Tensor (Function.update c i (cM (j.succAbove 0))) :=
  permT ⇑(Fin.cycleIcc i (Fin.last nA)).symm (IsReindexing.crossToSlot_cycle i j) ∘ₗ
    (crossToEnd i j hc).flip M

/-- The bridge between the two conventions: `crossToSlot i j hc M t` is `crossToEnd i j hc t M`
  with the survivor rotated from the last slot back to slot `i` by the inverse cycle. -/
lemma crossToSlot_eq_crossToEnd {nA : ℕ} {c : Fin (nA + 1) → C} {cM : Fin 2 → C}
    (i : Fin (nA + 1)) (j : Fin 2) (hc : S.τ (c i) = cM j) (M : S.Tensor cM) (t : S.Tensor c) :
    crossToSlot i j hc M t =
      permT ⇑(Fin.cycleIcc i (Fin.last nA)).symm (IsReindexing.crossToSlot_cycle i j)
        (crossToEnd i j hc t M) := rfl

/-- Contract slot `i` of a tensor whose color there is `d` against `M'`, then absorb the color cast
  the two `Function.update`s generate, landing back on `c`. This is the returning half of a
  raise-then-lower round trip; absorbing the cast here is what keeps the round trip cast-free at
  both ends. -/
noncomputable def crossToSlotInv {nA : ℕ} {c : Fin (nA + 1) → C} {b d e : C} (i : Fin (nA + 1))
    (he : c i = e) (hb : S.τ d = b) (M' : S.Tensor ![b, e]) :
    S.Tensor (Function.update c i d) →ₗ[k] S.Tensor c :=
  permT (id : Fin (nA + 1) → Fin (nA + 1))
      (IsReindexing.on_id_symm (IsReindexing.update_update_of_eq (d := d) i he)) ∘ₗ
    crossToSlot i (0 : Fin 2)
      (by rw [Function.update_self]; exact hb : S.τ (Function.update c i d i) = b) M'

/-- An identity reindexing of the rank-2 tensor becomes the corresponding identity reindexing of
  the contracted output: the `crossToSlot`-level case of `crossToEnd_permT_right` where the rank-2
  tensor's colors are only propositionally recast. -/
lemma crossToSlot_permT_right_id {nA : ℕ} {c : Fin (nA + 1) → C} {cM cM' : Fin 2 → C}
    (i : Fin (nA + 1)) (j : Fin 2) (hc : S.τ (c i) = cM' j)
    (M : Tensor S cM) (hM : IsReindexing cM cM' (id : Fin 2 → Fin 2)) (t : Tensor S c) :
    crossToSlot i j hc (permT (id : Fin 2 → Fin 2) hM M) t =
      permT (id : Fin (nA + 1) → Fin (nA + 1))
        (IsReindexing.on_id.mpr (fun a => by
          by_cases ha : a = i
          · subst ha
            simpa using hM.2 (j.succAbove 0)
          · simp [Function.update_of_ne ha]))
        (crossToSlot i j (hc.trans (hM.2 j).symm) M t) := by
  rw [crossToSlot_eq_crossToEnd, crossToSlot_eq_crossToEnd]
  rw [crossToEnd_permT_right i j
    (id : Fin 2 → Fin 2) id hM (by rfl)]
  simp only [permT_permT]
  apply permT_congr
  · funext x
    simpa only [Function.comp_apply, Function.comp_id, id_eq] using
      congrFun Fin.append_castAdd_natAdd_eq_id ((Fin.cycleIcc i (Fin.last nA)).symm x)
  · rfl

/-- Cross contraction into a slot is `G`-equivariant, both constituents (`crossToEnd`, `permT`)
  being so. -/
@[simp]
lemma crossToSlot_equivariant {nA : ℕ} {c : Fin (nA + 1) → C} {cM : Fin 2 → C}
    (i : Fin (nA + 1)) (j : Fin 2) (hc : S.τ (c i) = cM j) (g : G)
    (M : Tensor S cM) (t : Tensor S c) :
    crossToSlot i j hc (g • M) (g • t) = g • crossToSlot i j hc M t := by
  rw [crossToSlot_eq_crossToEnd, crossToSlot_eq_crossToEnd, crossToEnd_equivariant,
    permT_equivariant]

end Tensor

end TensorSpecies
