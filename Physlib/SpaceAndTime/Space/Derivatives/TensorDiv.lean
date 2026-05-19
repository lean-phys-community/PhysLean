/-
Copyright (c) 2025 Florian Wiesner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Wiesner
-/
module

public import Mathlib.Data.Matrix.Basic
public import Physlib.SpaceAndTime.Space.Derivatives.Basic
/-!

# Tensor divergence on Space

## i. Overview

In this module we define the tensor divergence operator on matrix-valued
functions from `Space d`.

For a field `T : Space d → Matrix (Fin d) (Fin d) ℝ`, the tensor divergence is
the vector field whose `i`th component is

`∑ j, ∂[j] (fun x => T x i j) x`.

## ii. Key results

- `tensorDiv` : The divergence of a matrix-valued function on `Space d`.

## iii. Table of contents

- A. The tensor divergence on functions
  - A.1. Basic equalities
  - A.2. The tensor divergence on the zero function
  - A.3. The tensor divergence on a constant function
  - A.4. The tensor divergence distributes over addition
  - A.5. The tensor divergence distributes over scalar multiplication

## iv. References

-/

@[expose] public section

open Physlib

namespace Space

/-!

## A. The tensor divergence on functions

-/

/-- The divergence of a matrix-valued spatial field.

For a field `T : Space d → Matrix (Fin d) (Fin d) ℝ`, `tensorDiv T` is the
vector field whose `i`th component is

`∑ j, ∂[j] (fun x => T x i j) x`.
-/
noncomputable def tensorDiv (d : ℕ) (T : Space d → Matrix (Fin d) (Fin d) ℝ) :
    Space d → EuclideanSpace ℝ (Fin d) := fun x => WithLp.toLp 2 fun i =>
  ∑ j, ∂[j] (fun x => T x i j) x

/-!

### A.1. Basic equalities

-/

@[simp]
lemma tensorDiv_apply (d : ℕ) (T : Space d → Matrix (Fin d) (Fin d) ℝ)
    (x : Space d) (i : Fin d) :
    tensorDiv d T x i = ∑ j, ∂[j] (fun x => T x i j) x := rfl

/-!

### A.2. The tensor divergence on the zero function

-/

@[simp]
lemma tensorDiv_zero (d : ℕ) :
    tensorDiv d (0 : Space d → Matrix (Fin d) (Fin d) ℝ) = 0 := by
  ext x i
  change (∑ j : Fin d, ∂[j] (fun _ : Space d => (0 : ℝ)) x) = 0
  simp

/-!

### A.3. The tensor divergence on a constant function

-/

@[simp]
lemma tensorDiv_const (d : ℕ) (T : Matrix (Fin d) (Fin d) ℝ) :
    tensorDiv d (fun _ : Space d => T) = 0 := by
  ext x i
  change (∑ j : Fin d, ∂[j] (fun _ : Space d => T i j) x) = 0
  simp

/-!

### A.4. The tensor divergence distributes over addition

-/

lemma tensorDiv_add (d : ℕ) (T1 T2 : Space d → Matrix (Fin d) (Fin d) ℝ)
    (hT1 : Differentiable ℝ T1) (hT2 : Differentiable ℝ T2) :
    tensorDiv d (T1 + T2) = tensorDiv d T1 + tensorDiv d T2 := by
  ext x i
  change (∑ j, ∂[j] (fun x => (T1 x + T2 x) i j) x) =
    (∑ j, ∂[j] (fun x => T1 x i j) x) +
      ∑ j, ∂[j] (fun x => T2 x i j) x
  rw [← Finset.sum_add_distrib]
  congr
  funext j
  change ∂[j] ((fun x => T1 x i j) + fun x => T2 x i j) x =
    ∂[j] (fun x => T1 x i j) x + ∂[j] (fun x => T2 x i j) x
  rw [deriv_add]
  · rfl
  · exact differentiable_pi.mp (differentiable_pi.mp hT1 i) j
  · exact differentiable_pi.mp (differentiable_pi.mp hT2 i) j

/-!

### A.5. The tensor divergence distributes over scalar multiplication

-/

lemma tensorDiv_smul (d : ℕ) (T : Space d → Matrix (Fin d) (Fin d) ℝ) (k : ℝ)
    (hT : Differentiable ℝ T) :
    tensorDiv d (k • T) = k • tensorDiv d T := by
  ext x i
  change (∑ j, ∂[j] (fun x => (k • T x) i j) x) =
    k * ∑ j, ∂[j] (fun x => T x i j) x
  rw [Finset.mul_sum]
  congr
  funext j
  change ∂[j] (k • fun x => T x i j) x = k • ∂[j] (fun x => T x i j) x
  rw [deriv_const_smul]
  · rfl
  · exact differentiable_pi.mp (differentiable_pi.mp hT i) j

end Space
