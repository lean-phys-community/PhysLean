/-
Copyright (c) 2026 Nathaneal Sajan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaneal Sajan
-/
module

public import Physlib.ClassicalMechanics.HarmonicOscillator.Basic
public import Physlib.ClassicalMechanics.HarmonicOscillator.Geometric.Basic
public import Physlib.Mathematics.Geometry.Metric.PseudoRiemannian.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Geometric kinetic energy of the harmonic oscillator

## i. Overview

The configuration space `Q` of the geometric harmonic oscillator is `ConfigurationSpace`.
Velocities lie in the tangent bundle `TQ`; at a configuration `q`, a velocity is a tangent
vector in `TangentSpace I q`.

Given a pseudo-Riemannian metric `g` on `Q`, the definition of the kinetic-energy function
on `TQ` is given by `geometricKineticEnergy g q v = 1 / 2 * g.inner q v v`. This is the
metric-induced kinetic term used for natural mechanical systems.

For the oscillator mass metric, tangent vectors are first read in the chosen global
Euclidean coordinate. The map `tangentCoord q : TangentSpace I q ≃L[ℝ] Model` is the
chart-induced continuous linear equivalence from the tangent space at `q` to the Euclidean
coordinate model `Model := EuclideanSpace ℝ (Fin 1)`. We use it to form the pullback of
the Euclidean inner product to `TangentSpace I q`.

The mass metric `massPseudoRiemannianMetric S` is the mass-scaled pullback of the Euclidean
inner product along `tangentCoord q`: `S.m * ⟪tangentCoord q v, tangentCoord q w⟫_ℝ`.
Positivity of `S.m`, together with positive-definiteness of the Euclidean inner product on
`Model`, gives nondegeneracy and negative index `0`.

Evaluating `geometricKineticEnergy` on `massPseudoRiemannianMetric` gives the usual coordinate
kinetic-energy expression
`(1 / 2 : ℝ) * S.m * ⟪tangentCoord q v, tangentCoord q v⟫_ℝ`.

## ii. Key results

- `Model` : the Euclidean coordinate model for the oscillator configuration space.
- `I` : the model-with-corners structure used for the global chart on `ConfigurationSpace`.
- `tangentCoord` : the chart-induced continuous linear equivalence from `TangentSpace I q`
  to `Model`.
- `instFiniteDimensionalTangent` : finite-dimensionality of each tangent space, transported
  from `Model` through `tangentCoord`.
- `geometricKineticEnergy` : for a metric `g` on `Q`, the function
  `K_g(q, v) = 1 / 2 * g_q(v, v)` on `TQ`.
- `geometricKineticEnergy_eq` : the formula
  `geometricKineticEnergy g q v = 1 / 2 * g.inner q v v`.
- `massPseudoRiemannianMetric` : the mass-scaled pullback of the Euclidean inner product,
  as a pseudo-Riemannian metric on `ConfigurationSpace`.
- `massPseudoRiemannianMetric_inner_apply` : evaluation of the mass metric in the global
  coordinate.
- `massPseudoRiemannianMetric_pos` : positivity of the oscillator mass metric.
- `geometricKineticEnergy_massMetric_eq` : the metric-induced kinetic energy for
  `massPseudoRiemannianMetric` is the mass-scaled coordinate kinetic energy.

## iii. Table of contents

- A. Coordinate identification of the tangent space
- B. Metric-induced kinetic energy
- C. The mass pseudo-Riemannian metric
- D. Positivity
- E. Coordinate form of kinetic energy

## iv. References

- Ivo Terek, Introductory Variational Calculus on Manifolds, pages 1-2.
-/

@[expose] public section

namespace ClassicalMechanics

namespace HarmonicOscillator

open scoped Manifold
open Manifold ContDiff
open InnerProductSpace

noncomputable section

/-!
## A. Coordinate identification of the tangent space

The oscillator configuration space has a single chosen global coordinate modeled on
`EuclideanSpace ℝ (Fin 1)`. In this one-chart model, each tangent space is represented by
the same Euclidean coordinate model. The continuous linear equivalence `tangentCoord q`
gives the coordinate representative of a tangent vector at `q`; it does not install an
intrinsic inner-product structure on tangent spaces.
-/

-- Let Lean use the definitional tangent/model identification used by `tangentCoord`
set_option backward.isDefEq.respectTransparency false

/-- The Euclidean coordinate model for the harmonic oscillator configuration space. -/
abbrev Model := EuclideanSpace ℝ (Fin 1)

/-- The model-with-corners structure for the global chart on `ConfigurationSpace`. -/
abbrev I := 𝓘(ℝ, Model)

/-- The chart-induced continuous linear equivalence from the tangent space at `q` to the
Euclidean coordinate model. It sends a tangent vector to its coordinate representative in
`Model`. -/
def tangentCoord (q : ConfigurationSpace) :
    TangentSpace I q ≃L[ℝ] Model where
  toFun v := v
  invFun v := v
  map_add' := by simp
  map_smul' := by simp

/-- Each tangent space is finite-dimensional because it is linearly equivalent to the
finite-dimensional coordinate model through `tangentCoord`. -/
instance instFiniteDimensionalTangent (q : ConfigurationSpace) :
    FiniteDimensional ℝ (TangentSpace I q) :=
  LinearEquiv.finiteDimensional (tangentCoord q).symm.toLinearEquiv

/-- In the single global chart, differentiating the chart inverse in the model direction `v`
and then reading the resulting tangent vector through `tangentCoord` returns `v`. This is the
coordinate identity used to show that the mass metric is constant in charts. -/
private lemma tangentCoord_mfderiv_extChartAt_symm
    (x₀ : ConfigurationSpace) (y v : Model) :
    tangentCoord ((extChartAt I x₀).symm y) (mfderiv I I (extChartAt I x₀).symm y v) = v := by
  change mfderiv I I (extChartAt I x₀).symm y v = v
  let q : ConfigurationSpace := (extChartAt I x₀).symm y
  have hpoint : (extChartAt I q) q = y := by
    simp [q, extChartAt, ConfigurationSpace.valHomeomorphism, ConfigurationSpace.valEquiv]
  have hderiv := congrArg (fun L => L v)
    (mfderivWithin_range_extChartAt_symm (I := I) (x := q))
  rw [hpoint] at hderiv
  have hid :
      ((ContinuousLinearMap.id ℝ (TangentSpace 𝓘(ℝ, Model) y)) v : TangentSpace I q) = v := rfl
  have hderiv' :
      mfderivWithin 𝓘(ℝ, Model) I (extChartAt I q).symm (Set.range I) y v = v :=
    hderiv.trans hid
  simpa [q, extChartAt, mfderivWithin_univ, ConfigurationSpace.valHomeomorphism,
    ConfigurationSpace.valEquiv] using hderiv'

/-!
## B. Metric-induced kinetic energy

A pseudo-Riemannian metric `g` on `Q` assigns a bilinear form `g_q` to each tangent space
`TangentSpace I q`. The kinetic-energy function associated to `g` is
`K_g(q, v) = 1 / 2 * g_q(v, v)`.
-/

/-- For a pseudo-Riemannian metric `g` on `Q`, the kinetic-energy function
`K_g(q, v) = 1 / 2 * g.inner q v v` on the tangent bundle `TQ`. -/
noncomputable def geometricKineticEnergy
    (g : PseudoRiemannianMetric
      Model
      Model
      ConfigurationSpace
      ω
      I)
    (q : ConfigurationSpace)
    (v : TangentSpace I q) : ℝ :=
  (1 / 2 : ℝ) * g.inner q v v

/-- The defining formula for `geometricKineticEnergy`. -/
lemma geometricKineticEnergy_eq
    (g : PseudoRiemannianMetric
      Model
      Model
      ConfigurationSpace
      ω
      I)
    (q : ConfigurationSpace)
    (v : TangentSpace I q) :
    geometricKineticEnergy g q v = (1 / 2 : ℝ) * g.inner q v v := by
  rfl

/-!
## C. The mass pseudo-Riemannian metric

The oscillator mass determines the inertial metric. At each configuration `q`, this metric is
the mass-scaled pullback of the Euclidean inner product on `Model` along the continuous linear
equivalence `tangentCoord q`.
-/

/-- The value of the oscillator mass metric at `q`. It is the mass-scaled pullback of the
Euclidean inner product along `tangentCoord q`, so
`massMetricVal S q v w = S.m * ⟪tangentCoord q v, tangentCoord q w⟫_ℝ`. -/
noncomputable def massMetricVal (S : HarmonicOscillator) (q : ConfigurationSpace) :
    TangentSpace I q →L[ℝ] TangentSpace I q →L[ℝ] ℝ :=
  S.m • (innerSL ℝ : Model →L[ℝ] Model →L[ℝ] ℝ)

/-- Applying the mass metric value to two tangent vectors gives the mass-scaled Euclidean
inner product of their coordinate representatives. -/
private lemma massMetricVal_apply
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v w : TangentSpace I q) :
    massMetricVal S q v w = S.m * ⟪tangentCoord q v, tangentCoord q w⟫_ℝ := by
  rfl

/-- A nonzero tangent vector has nonzero coordinate representative under `tangentCoord`. -/
private lemma tangentCoord_ne_zero {q : ConfigurationSpace} {v : TangentSpace I q}
    (hv : v ≠ 0) : tangentCoord q v ≠ 0 := by
  intro h
  apply hv
  exact (tangentCoord q).injective (by simpa using h)

/-- The quadratic form associated to the oscillator mass metric has negative index zero at
every configuration, because `S.m > 0` and the Euclidean inner product is positive definite
on coordinate representatives. -/
private lemma massMetricVal_negDim_eq_zero
    (S : HarmonicOscillator) (q : ConfigurationSpace) :
    (pseudoRiemannianMetricValToQuadraticForm (massMetricVal S)
      (by
        intro q v w
        rw [massMetricVal_apply, massMetricVal_apply, real_inner_comm]) q).negDim = 0 := by
  apply QuadraticForm.rankNeg_eq_zero
  intro v hv
  change 0 < massMetricVal S q v v
  rw [massMetricVal_apply]
  exact mul_pos S.m_pos (real_inner_self_pos.mpr (tangentCoord_ne_zero hv))

/-- The mass-scaled pullback of the Euclidean inner product, as a pseudo-Riemannian metric on
the oscillator configuration space. -/
noncomputable def massPseudoRiemannianMetric (S : HarmonicOscillator) :
    PseudoRiemannianMetric
      Model
      Model
      ConfigurationSpace
      ω
      I where
  val := massMetricVal S
  symm := by
    intro q v w
    rw [massMetricVal_apply, massMetricVal_apply, real_inner_comm]
  nondegenerate := by
    intro q v h
    have hv := h v
    rw [massMetricVal_apply] at hv
    have h_inner : ⟪tangentCoord q v, tangentCoord q v⟫_ℝ = 0 := by
      exact (mul_eq_zero.mp hv).resolve_left S.m_ne_zero
    apply (tangentCoord q).injective
    simpa using (inner_self_eq_zero.mp h_inner)
  smooth_in_charts' := by
    intro x₀ v w
    refine (contDiffWithinAt_const (c := S.m * ⟪v, w⟫_ℝ)).congr (fun y _hy => ?_) ?_
    · rw [massMetricVal_apply, tangentCoord_mfderiv_extChartAt_symm,
        tangentCoord_mfderiv_extChartAt_symm]
    · rw [massMetricVal_apply, tangentCoord_mfderiv_extChartAt_symm,
        tangentCoord_mfderiv_extChartAt_symm]
  negDim_isLocallyConstant := by
    apply IsLocallyConstant.of_constant
    intro x y
    rw [massMetricVal_negDim_eq_zero S x, massMetricVal_negDim_eq_zero S y]

/-!
## D. Positivity

The mass metric is positive definite because `S.m` is positive and every nonzero tangent
vector has a nonzero coordinate representative in the Euclidean model.
-/

/-- The oscillator mass pseudo-Riemannian metric is positive definite. -/
lemma massPseudoRiemannianMetric_pos
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v : TangentSpace I q)
    (hv : v ≠ 0) :
    0 < S.massPseudoRiemannianMetric.inner q v v := by
  rw [PseudoRiemannianMetric.inner_apply, massPseudoRiemannianMetric, massMetricVal_apply]
  exact mul_pos S.m_pos (real_inner_self_pos.mpr (tangentCoord_ne_zero hv))

/-!
## E. Coordinate form of kinetic energy

The continuous linear equivalence `tangentCoord q` represents tangent vectors at `q` as
vectors in `Model`. Under these coordinate representatives, the mass metric and the induced
kinetic energy have the standard coordinate formulas.
-/

/-- In the global coordinate, the oscillator mass metric is the mass-scaled Euclidean inner
product of coordinate representatives. -/
lemma massPseudoRiemannianMetric_inner_apply
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v w : TangentSpace I q) :
    S.massPseudoRiemannianMetric.inner q v w =
      S.m * ⟪tangentCoord q v, tangentCoord q w⟫_ℝ := by
  rw [PseudoRiemannianMetric.inner_apply, massPseudoRiemannianMetric]
  exact massMetricVal_apply S q v w

/-- The metric-induced kinetic energy for the mass metric has the standard
harmonic-oscillator coordinate form. -/
lemma geometricKineticEnergy_massMetric_eq
    (S : HarmonicOscillator) (q : ConfigurationSpace)
    (v : TangentSpace I q) :
    geometricKineticEnergy S.massPseudoRiemannianMetric q v =
      (1 / 2 : ℝ) * S.m * ⟪tangentCoord q v, tangentCoord q v⟫_ℝ := by
  rw [geometricKineticEnergy_eq, massPseudoRiemannianMetric_inner_apply]
  ring

end

end HarmonicOscillator

end ClassicalMechanics
