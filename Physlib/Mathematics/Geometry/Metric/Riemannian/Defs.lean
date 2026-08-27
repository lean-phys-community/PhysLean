/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs

/-!
# Riemannian manifolds as the index-zero pseudo-Riemannian manifolds

Riemannian geometry is a special case of the pseudo-Riemannian development, not a parallel one:
Mathlib's Riemannian hypotheses already discharge the pseudo-Riemannian ones, as the `example`
below checks. This file records the invariant separating the two cases.

## Main definitions

* `RiemannianMetric I n M`: Mathlib's `Bundle.ContMDiffRiemannianMetric` for the tangent bundle.
* `PseudoRiemannian.IsRiemannian I M`: the index vanishes everywhere.

## Main results

* `PseudoRiemannian.index_eq_zero_of_riemannianBundle`: a Riemannian metric has index `0`.

## Tags

Riemannian, pseudo-Riemannian, index
-/

@[expose] public section

open Bundle
open scoped Manifold Bundle ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : WithTop ℕ∞}

/-- A `C^n` Riemannian metric on `M`: Mathlib's bundle-level notion for the tangent bundle. -/
abbrev RiemannianMetric (I : ModelWithCorners ℝ E H) (n : WithTop ℕ∞) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] :=
  Bundle.ContMDiffRiemannianMetric (IB := I) (n := n) (F := E)
    (E := fun x : M ↦ TangentSpace I x)

namespace PseudoRiemannian

section Riemannian

variable [IsManifold I 1 M] [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Transparency check: a Riemannian manifold satisfies the pseudo-Riemannian hypotheses with no
adapter. -/
example [IsContMDiffRiemannianBundle I n E (TangentSpace I : M → Type _)] :
    IsContMDiffPseudoRiemannianBundle I n E (TangentSpace I : M → Type _) := inferInstance

omit [IsManifold I 1 M] in
/-- A Riemannian metric has index `0` at every point. -/
@[simp]
lemma index_eq_zero_of_riemannianBundle [FiniteDimensional ℝ E] (x : M) : index I x = 0 :=
  PseudoInnerProductSpace.index_eq_zero_of_innerProductSpace (TangentSpace I x)

end Riemannian

variable [∀ x : M, PseudoInnerProductSpace (TangentSpace I x)]

variable (I M) in
/-- The metric is Riemannian: its index vanishes at every point. -/
class IsRiemannian : Prop where
  /-- A Riemannian metric has index `0` at every point. -/
  index_eq_zero : ∀ x : M, index I x = 0

@[simp]
lemma index_eq_zero [IsRiemannian I M] (x : M) : index I x = 0 :=
  IsRiemannian.index_eq_zero x

/-- A pointwise positive definite metric is Riemannian. -/
lemma isRiemannian_of_posDef [FiniteDimensional ℝ E]
    (h : ∀ x : M, (PseudoInnerProductSpace.toQuadraticForm (TangentSpace I x)).PosDef) :
    IsRiemannian I M :=
  ⟨fun x ↦ PseudoInnerProductSpace.index_eq_zero_of_posDef (h x)⟩

end PseudoRiemannian
