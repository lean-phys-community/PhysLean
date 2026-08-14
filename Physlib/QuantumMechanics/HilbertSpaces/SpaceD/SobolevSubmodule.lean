/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Bornemann
-/
module

public import Mathlib.Analysis.Distribution.Sobolev
public import Physlib.QuantumMechanics.HilbertSpaces.SpaceD.SchwartzSubmodule
/-!

# Sobolev submodules of `SpaceDHilbertSpace`

## i. Overview

In this module we define the Sobolev submodules of `SpaceDHilbertSpace`.

## ii. Key results

- `SobolevSubmodule d s` : the Sobolev space `H^s` as a submodule of `SpaceDHilbertSpace d`.
- `SobolevSubmodule.schwartzIncl_mem` / `schwartzSubmodule_le_sobolevSubmodule` /
    `SobolevSubmodule.dense` : Schwartz maps lie in every `H^s`, which is therefore dense.
- `SobolevSubmodule.antitone` : `H^s ≤ H^s'` for `s' ≤ s`.

## iii. Table of contents

- A. The Sobolev submodule `H^s`

## iv. References

-/

@[expose] public section

namespace QuantumMechanics
namespace SpaceDHilbertSpace

open MeasureTheory TemperedDistribution
open scoped SchwartzMap

variable {d : ℕ} {μ : Measure (Space d)} [μ.HasTemperateGrowth]

/-!
## A. The Sobolev submodule `H^s`
-/

/-- The Sobolev space `H^s` as a submodule of `SpaceDHilbertSpace d`: the L² classes whose
associated tempered distribution satisfies `MemSobolev s 2`. -/
def SobolevSubmodule (d : ℕ) (s : ℝ) : Submodule ℂ (SpaceDHilbertSpace d) where
  carrier := {ψ | MemSobolev s 2 (toTemperedDistributionCLM d volume ψ)}
  add_mem' {ψ φ} hψ hφ := by simpa only [Set.mem_ofPred_eq, map_add] using hψ.add hφ
  zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using memSobolev_fun_zero (Space d) ℂ s 2
  smul_mem' c ψ hψ := by simpa only [Set.mem_ofPred_eq, map_smul] using hψ.smul c

/-- Membership in `H^s` is the Sobolev condition on the associated tempered distribution. -/
lemma mem_sobolevSubmodule_iff {s : ℝ} {ψ : SpaceDHilbertSpace d} :
    ψ ∈ SobolevSubmodule d s ↔ MemSobolev s 2 (toTemperedDistribution ψ) := Iff.rfl

/-- Schwartz maps lie in every Sobolev space `H^s`. -/
lemma SobolevSubmodule.schwartzIncl_mem (s : ℝ) (g : 𝓢(Space d, ℂ)) :
    schwartzIncl volume g ∈ SobolevSubmodule d s := by
  rw [mem_sobolevSubmodule_iff, SchwartzSubmodule.toTemperedDistribution_schwartzIncl_eq]
  exact g.memSobolev

/-- The Schwartz submodule is contained in every Sobolev space `H^s`. -/
lemma schwartzSubmodule_le_sobolevSubmodule (s : ℝ) :
    SchwartzSubmodule d ≤ SobolevSubmodule d s := by
  rintro ψ ⟨g, rfl⟩
  exact SobolevSubmodule.schwartzIncl_mem s g

/-- Every Sobolev space `H^s` is dense in `SpaceDHilbertSpace d`, containing the dense Schwartz
submodule. -/
lemma SobolevSubmodule.dense (s : ℝ) :
    Dense (SobolevSubmodule d s : Set (SpaceDHilbertSpace d)) :=
  (SchwartzSubmodule.dense d volume).mono (schwartzSubmodule_le_sobolevSubmodule s)

/-- The Sobolev spaces shrink as the regularity index grows: `H^s ≤ H^s'` for `s' ≤ s`. -/
lemma SobolevSubmodule.antitone (d : ℕ) : Antitone (SobolevSubmodule d) :=
  fun _ _ h _ hψ => hψ.mono h

end SpaceDHilbertSpace
end QuantumMechanics
