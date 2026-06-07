/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.TensorSpecies.Basic
/-!

# Component indices

## i. Overview

For a tensor species `S` and a list of colors `c : Fin n → C`, `ComponentIdx S c`
is the type of choices of a basis index for every color in `c`. For example, for a
tensor with colors `![.up, .down]`, an element of `ComponentIdx ![.up, .down]`
records one contravariant component index and one covariant component index.

This file contains the basic definition and congruence/cast API. Operations on
component indices induced by tensor products and contractions live in sibling files.

## ii. Key results

- `TensorSpecies.Tensor.ComponentIdx` is the type of component indices for a tensor
  with a given list of colors.
- `TensorSpecies.Tensor.ComponentIdx.congr_right` relates entries whose positions are equal.
- `TensorSpecies.Tensor.ComponentIdx.cast` casts component indices along equivalent color maps.

## iii. Table of contents

- A. Basic definitions

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

/-!

## A. Basic definitions

-/

set_option linter.unusedVariables false in
/-- Given a list of indices `c : Fin n → C`, the type `ComponentIdx c` is the type of
component indices of a tensor with those colors. For instance, if `c = ![.up, .down]`,
then an element of `ComponentIdx c` specifies one basis index for `.up` and one for
`.down`. -/
@[nolint unusedArguments]
abbrev ComponentIdx {n : ℕ} {S : TensorSpecies k C G V basisIdx rep b}
    (c : Fin n → C) : Type :=
  Π j, basisIdx (c j)

lemma ComponentIdx.congr_right {n : ℕ} {c : Fin n → C} (b : ComponentIdx (S := S) c)
    (i j : Fin n) (h : i = j) : b i = basisIdxCongr (by simp [h]) (b j) := by
  subst h
  simp [basisIdxCongr]

/-- Casting of a `ComponentIdx` through equivalent color maps. -/
def ComponentIdx.cast {n m : ℕ} {c : Fin n → C} {cm : Fin m → C}
    (h : n = m) (hc : c = cm ∘ Fin.cast h) (b : ComponentIdx (S := S) c) :
    ComponentIdx (S := S) cm := fun j =>
      basisIdxCongr (by simp [hc]) (b (Fin.cast h.symm j))

end Tensor

end TensorSpecies
