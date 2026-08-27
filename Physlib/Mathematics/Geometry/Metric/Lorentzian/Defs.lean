/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Lorentzian manifolds

A Lorentzian metric is a pseudo-Riemannian metric of index `1`. The index is locally constant, so
on a connected manifold the condition need only be checked at one point; see
`PseudoRiemannian.isLorentzian_of_index_eq_one`.

We use the "mostly plus" convention, signature `(-, +, …, +)`; in the "mostly minus" convention
the same metric has index `dim M - 1`.

## Main definitions

* `PseudoRiemannian.IsLorentzian I M`: the index is `1` everywhere.

## Tags

Lorentzian, pseudo-Riemannian, index, signature, spacetime
-/

@[expose] public section

open Bundle
open scoped Manifold Bundle ContDiff

namespace PseudoRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}
  [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]

variable (I M) in
/-- The metric is Lorentzian: its index is `1` at every point, i.e. its signature is
`(-, +, …, +)`. -/
class IsLorentzian : Prop where
  /-- A Lorentzian metric has index `1` at every point. -/
  index_eq_one : ∀ x : M, index I x = 1

@[simp]
lemma index_eq_one [IsLorentzian I M] (x : M) : index I x = 1 :=
  IsLorentzian.index_eq_one x

variable [IsManifold I 1 M] [FiniteDimensional ℝ E]

/-- On a connected manifold, being Lorentzian can be checked at a single point. -/
lemma isLorentzian_of_index_eq_one [PreconnectedSpace M]
    [IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _)] {x₀ : M}
    (h : index I x₀ = 1) : IsLorentzian I M :=
  ⟨fun x ↦ (index_eq_of_preconnectedSpace (n := n) x x₀).trans h⟩

end PseudoRiemannian
