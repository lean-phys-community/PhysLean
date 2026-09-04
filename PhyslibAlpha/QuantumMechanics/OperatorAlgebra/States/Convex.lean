/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Ole Diem
-/
module

public import PhyslibAlpha.QuantumMechanics.OperatorAlgebra.States.Basic
public import Mathlib.Analysis.Convex.Extreme

/-!
# Convex state spaces

The state space is convex: probabilistic mixtures of physical preparations are
again states. This file provides binary and finite mixtures as states.
-/

@[expose] public section

open scoped ComplexOrder

namespace OperatorAlgebra

namespace State

variable {A : Type*} [OperatorAlgebra A]

/-- Every physically realizable preparation, viewed inside the continuous dual of `A` so its
topology and convex structure come for free. -/
def stateSpace : Set (A →L[ℂ] ℂ) :=
  Set.range fun ω : State A => ω.toContinuousLinearMap

/-- Randomizing between two preparations: flip a `t`-biased coin, prepare `ω` or `φ` accordingly.
Every observable's expectation is then the `t`-weighted average `tω(a) + (1-t)φ(a)`. -/
noncomputable def mix (ω φ : State A) (t : unitInterval) : State A where
  toPositiveLinearMap := PositiveLinearMap.mk₀
    ((t : ℝ) • ω.toPositiveLinearMap.toLinearMap +
      (1 - (t : ℝ)) • φ.toPositiveLinearMap.toLinearMap)
    (fun a ha => by
      simp only [LinearMap.add_apply, LinearMap.smul_apply, RCLike.real_smul_eq_coe_mul]
      exact add_nonneg
        (mul_nonneg (RCLike.ofReal_nonneg.mpr (unitInterval.nonneg t))
          (ω.toPositiveLinearMap.map_nonneg ha))
        (mul_nonneg (RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr (unitInterval.le_one t)))
          (φ.toPositiveLinearMap.map_nonneg ha)))
  map_one := by
    change (t : ℝ) • ω 1 + (1 - (t : ℝ)) • φ 1 = 1
    rw [ω.map_one, φ.map_one]
    simp only [RCLike.real_smul_eq_coe_mul, mul_one]
    push_cast
    ring

/-- Unfolds `mix` to its defining formula. -/
@[simp]
lemma mix_apply (ω φ : State A) (t : unitInterval) (a : A) :
    mix ω φ t a = (t : ℝ) • ω a + (1 - (t : ℝ)) • φ a :=
  rfl

/-- Mixing states and then embedding into the continuous dual agrees with embedding first and
mixing there: `mix` and the dual space's convex combination describe the same blend. -/
@[simp]
lemma mix_toContinuousLinearMap (ω φ : State A) (t : unitInterval) :
    (mix ω φ t).toContinuousLinearMap =
      (t : ℝ) • ω.toContinuousLinearMap + (1 - (t : ℝ)) • φ.toContinuousLinearMap := by
  ext a
  rfl

/-- A state lies strictly between two states exactly when it is a genuine mixture of them. -/
lemma mem_openSegment_iff_exists_mix (ω φ ψ : State A) :
    ω.toContinuousLinearMap ∈
        openSegment ℝ φ.toContinuousLinearMap ψ.toContinuousLinearMap ↔
      ∃ t : unitInterval, t ≠ 0 ∧ t ≠ 1 ∧ mix φ ψ t = ω := by
  constructor
  · rintro ⟨t, s, ht, hs, hts, heq⟩
    have ht₁ : t < 1 := by linarith
    let u : unitInterval := ⟨t, ht.le, ht₁.le⟩
    refine ⟨u, ?_, ?_, ?_⟩
    · exact ne_of_gt (by exact_mod_cast ht)
    · exact ne_of_lt (by exact_mod_cast ht₁)
    · apply toContinuousLinearMap_injective
      change (mix φ ψ u).toContinuousLinearMap = ω.toContinuousLinearMap
      rw [mix_toContinuousLinearMap]
      change t • φ.toContinuousLinearMap + (1 - t) • ψ.toContinuousLinearMap =
        ω.toContinuousLinearMap
      rwa [show (1 : ℝ) - t = s by linarith]
  · rintro ⟨t, ht₀, ht₁, rfl⟩
    refine ⟨(t : ℝ), 1 - (t : ℝ), ?_, ?_, by ring, ?_⟩
    · exact_mod_cast unitInterval.pos_iff_ne_zero.mpr ht₀
    · exact sub_pos.mpr (by exact_mod_cast unitInterval.lt_one_iff_ne_one.mpr ht₁)
    · rw [mix_toContinuousLinearMap]

/-- The state space is closed under forming mixtures `tω + (1-t)φ`, which is exactly what makes it
convex as a subset of the continuous dual. -/
lemma stateSpace_convex : Convex ℝ (stateSpace (A := A)) := by
  rintro x ⟨ω, rfl⟩ y ⟨φ, rfl⟩ t s ht hs hts
  have ht₁ : t ≤ 1 := by linarith
  refine ⟨mix ω φ ⟨t, ht, ht₁⟩, ?_⟩
  dsimp only
  rw [mix_toContinuousLinearMap, show s = 1 - t by linarith]

/-- Randomizing over a finite ensemble of preparations `ω i`, each with classical probability
`p i`: the state-level analogue of a density matrix built as `∑ p i • ρ i`. `mix` is the
two-element case. -/
noncomputable def finiteMix {ι : Type*} [Fintype ι] (ω : ι → State A) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : State A where
  toPositiveLinearMap := PositiveLinearMap.mk₀
    { toFun := fun a => ∑ i, (p i : ℂ) * ω i a
      map_add' := fun a b => by
        simp only [map_add, mul_add]
        exact Finset.sum_add_distrib
      map_smul' := fun c a => by
        simp only [RingHom.id_apply, map_smul, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
    (fun a ha => Finset.sum_nonneg fun i _ =>
      mul_nonneg (RCLike.ofReal_nonneg.mpr (hp i)) ((ω i).toPositiveLinearMap.map_nonneg ha))
  map_one := by
    show (∑ i, (p i : ℂ) * ω i 1) = 1
    simp only [State.map_one, mul_one]
    exact_mod_cast hsum

/-- Unfolds `finiteMix` to its defining formula. -/
@[simp]
lemma finiteMix_apply {ι : Type*} [Fintype ι] (ω : ι → State A) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (a : A) :
    finiteMix ω p hp hsum a = ∑ i, (p i : ℂ) * ω i a :=
  rfl

end State

end OperatorAlgebra
