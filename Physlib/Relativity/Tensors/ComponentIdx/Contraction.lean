/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.ComponentIdx.Basic
public import Physlib.Relativity.Tensors.Contraction.SuccSuccAbove
/-!

# Contractions of component indices

## i. Overview

This file contains the component-index API induced by dropping a pair of contracted
indices from a tensor.

The constructions here describe how component indices restrict along
`Fin.succSuccAbove`, and how the fiber of this restriction is equivalent to the two
component choices at the contracted positions.

## ii. Key results

- `TensorSpecies.Tensor.ComponentIdx.dropPair` restricts a component index by dropping
  two positions.
- `TensorSpecies.Tensor.ComponentIdx.DropPairSection` is the finite set of component
  indices mapping to a fixed restricted component index.
- `TensorSpecies.Tensor.ComponentIdx.DropPairSection.ofFinEquiv` identifies a
  `DropPairSection` with the two basis indices at the dropped positions.

## iii. Table of contents

- A. Dropping a pair
- B. Sections of the drop-pair map

## iv. References

There are no known references for the material in this module.

-/

@[expose] public section

namespace TensorSpecies

variable {k : Type} [CommRing k] {C G : Type} [Group G]
  {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k (V c)]
  {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
  {rep : (c : C) → Representation k G (V c)}
  {b : (c : C) → Module.Basis (basisIdx c) k (V c)}
  {S : TensorSpecies k C G V basisIdx rep b}

namespace Tensor

namespace ComponentIdx

/-!

## A. Dropping a pair

-/

/-- The `ComponentIdx` obtained by dropping two components. -/
def dropPair {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (i j : Fin (n + 1 + 1)) (b : ComponentIdx (S := S) c) :
    ComponentIdx (S := S) (c ∘ Fin.succSuccAbove i j) :=
  fun m => b (Fin.succSuccAbove i j m)

/-!

## B. Sections of the drop-pair map

-/

/-- Given a coordinate parameter
  `b : Π k, Fin (S.repDim ((c ∘ i.succAbove ∘ j.succAbove) k)))`, the
  coordinate parameter `Π k, Fin (S.repDim (c k))` which map down to `b`. -/
def DropPairSection {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i : Fin (n + 1 + 1)} {j : Fin (n + 1 + 1)}
    (b : ComponentIdx (S := S) (c ∘ Fin.succSuccAbove i j)) :
    Finset (ComponentIdx (S := S) c) :=
  {b' : ComponentIdx c | dropPair i j b' = b}

namespace DropPairSection

lemma mem_iff_apply_succSuccAbove_eq {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)}
    (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (b' : ComponentIdx c) :
    b' ∈ DropPairSection (S := S) b ↔
      ∀ m, b' (Fin.succSuccAbove i j m) = b m := by
  simp only [DropPairSection, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [funext_iff]
  simp [dropPair]

@[simp]
lemma mem_self_of_dropPair {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)}
    (b : ComponentIdx (c)) :
    b ∈ DropPairSection (S := S) (b.dropPair i j) := by
  simp [DropPairSection]

/-- Given a `b` in `ComponentIdx (c ∘ Fin.succSuccAbove i j))` and
  an `x` in `Fin (S.repDim (c i)) × Fin (S.repDim (c j))`, the corresponding
  coordinate parameter in `ComponentIdx c`. -/
def ofFin {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (S := S) (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    ComponentIdx (S := S) c := fun m =>
  if hi : m = i then basisIdxCongr (by subst hi; rfl) x.1
  else if hj : m = j then basisIdxCongr (by subst hj; rfl) x.2
  else
    basisIdxCongr (by simp)
    (b (Fin.predPredAbove i j hij m (by omega)))

@[simp]
lemma ofFin_apply_fst {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    ofFin (S := S) hij b x i = x.1 := by
  simp [ofFin]

@[simp]
lemma ofFin_apply_snd {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    ofFin (S := S) hij b x j = x.2 := by
  simp [ofFin]
  intro h
  omega

lemma ofFin_mem_succSuccAboveSection {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    ofFin (S := S) hij b x ∈ DropPairSection b := by
  simp only [DropPairSection, Finset.mem_filter, Finset.mem_univ, true_and]
  ext m
  simp only [ofFin, dropPair, Fin.succSuccAbove_ne_fst, ↓reduceDIte, Fin.succSuccAbove_ne_snd,
    Function.comp_apply]
  symm
  apply ComponentIdx.congr_right
  simp

/-- The equivalence between `ContrSection b` and
  `basisIdx (c i) × basisIdx (c j)`. -/
def ofFinEquiv {n : ℕ} {c : Fin n.succ.succ → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j)
    (b : ComponentIdx (c ∘ Fin.succSuccAbove i j)) :
    basisIdx (c i) × basisIdx (c j) ≃ DropPairSection (S := S) b where
  invFun b' := ⟨b'.1 i, b'.1 j⟩
  toFun x := ⟨ofFin hij b x, ofFin_mem_succSuccAboveSection hij b x⟩
  right_inv b' := by
    ext m
    simp
    rcases Fin.eq_or_exists_succSuccAbove i j hij m with rfl | rfl | ⟨m, rfl⟩
    · simp
    · simp
    · simp [ofFin]
      obtain ⟨b', hb'⟩ := b'
      simp only [mem_iff_apply_succSuccAbove_eq] at hb'
      simp [hb']
      symm
      apply ComponentIdx.congr_right
      simp
  left_inv x := by
    simp

@[simp]
lemma ofFinEquiv_apply_fst {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    (ofFinEquiv (S := S) hij b x).1 i = x.1 := by
  simp [ofFinEquiv]

@[simp]
lemma ofFinEquiv_apply_snd {n : ℕ} {c : Fin (n + 1 + 1) → C}
    {i j : Fin (n + 1 + 1)} (hij : i ≠ j) (b : ComponentIdx (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) :
    (ofFinEquiv (S := S) hij b x).1 j = x.2 := by
  simp [ofFinEquiv]

end DropPairSection

end ComponentIdx

end Tensor

end TensorSpecies
