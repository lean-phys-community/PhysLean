/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
module

public import Physlib.SpaceAndTime.Space.Derivatives.Div
/-!

# The Laplacian operator on `Space d`

## i. Overview

In this module we define the Laplacian operator on functions and vector-valued
functions defined on `Space d`.

## ii. Key results

- `laplacian` : The Laplacian operator on scalar functions on `Space d`.
- `laplacianVec` : The Laplacian operator on vector-valued functions on `Space d`.
- `distLaplacian` : The Laplacian operator on distributions on `Space d`.

## iii. Table of contents

- A. Laplacian on functions to ℝ
  - A.1. Relation between laplacian and divergence of gradient
- B. Laplacian on vector valued functions
- C. Laplacian of distributions
  - C.1. Laplacian of constant distributions

## iv. References

-/

@[expose] public section

namespace Space

/-!

## A. Laplacian on functions to ℝ

-/

/-- The scalar `laplacian` operator. -/
noncomputable def laplacian {d} (f : Space d → ℝ) : Space d → ℝ :=
    ∇ ⬝ ∇ f

@[inherit_doc laplacian]
scoped[Space] notation "Δ" => laplacian

/-!

### A.1. Relation between laplacian and divergence of gradient

-/

lemma laplacian_eq_sum_snd_deriv {d} (f : Space d → ℝ) :
    Δ f = fun x => ∑ i, ∂[i] (∂[i] f) x := by
  unfold laplacian div grad
  simp

/-!

## B. Laplacian on vector valued functions

-/

/-- The vector `laplacianVec` operator. -/
noncomputable def laplacianVec {d} (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → EuclideanSpace ℝ (Fin d) := fun x => WithLp.toLp 2 fun i =>
  -- get i-th component of `f`
  Δ (fun x => f x i) x

@[inherit_doc laplacianVec]
scoped[Space] notation "Δᵥ" => laplacianVec

open Physlib Distribution

/-!

## C. Laplacian of distributions

-/

/-- The distributional `distLaplacian` operator. -/
noncomputable def distLaplacian {d} :
    ((Space d) →d[ℝ] ℝ) →ₗ[ℝ] (Space d) →d[ℝ] ℝ :=
    distDiv ∘ₗ distGrad

@[inherit_doc distLaplacian]
scoped[Space] notation "Δᵈ" => distLaplacian

/-!

### C.1. Laplacian of constant distributions

-/

@[simp]
lemma distLaplacian_const {d : ℕ} (c : ℝ) :
    Δᵈ (Distribution.const ℝ (Space d) c) = 0 := by
  simp [distLaplacian, distGrad_const]

end Space
