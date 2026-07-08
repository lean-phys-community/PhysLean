/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolai Kashcheev, Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic
public import Physlib.SpaceAndTime.Space.Module
public import Physlib.SpaceAndTime.Time.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Calculus
/-!

# Time Derivatives

## i. Overview

In this module we define and prove basic lemmas about derivatives of functions on `Time`.

## ii. Key results

- `deriv` : The derivative of a function `Time → M` at a given time.
- `manifoldDeriv` : The derivative of a function from `Time` to a manifold.

## iii. Table of contents

- A. The definition of the derivative
  - A.1. Derivatives of functions into vector spaces
  - A.2. Derivatives of functions into manifolds
- B. Linearlity properties of the derivative
- C. Derivative of constant functions
- D. Smoothness properties
- E. Derivatives of components

## iv. References

-/

@[expose] public section

namespace Time

variable {M : Type} {d : ℕ} {t : Time}

/-!

## A. The definition of the derivative

-/

/-!

### A.1. Derivatives of functions into vector spaces

-/

/-- Given a function `f : Time → M` the derivative of `f`. -/
noncomputable def deriv [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Time → M) : Time → M :=
  (fun t => fderiv ℝ f t 1)

@[inherit_doc deriv]
scoped notation "∂ₜ" => deriv

lemma deriv_eq [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    (f : Time → M) (t : Time) : Time.deriv f t = fderiv ℝ f t 1 := rfl

/-!

### A.2. Derivatives of functions into manifolds

-/

open Manifold in
/-- The time derivative of a function from `Time` to a manifold, as a tangent vector at
the value of the function. -/
noncomputable def manifoldDeriv {E H N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace N]
    [ChartedSpace H N] (f : Time → N) : (t : Time) → TangentSpace I (f t) :=
  fun t => mfderiv 𝓘(ℝ, Time) I f t ((1 : Time) : TangentSpace 𝓘(ℝ, Time) t)

open Manifold in
lemma manifoldDeriv_eq {E H N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace N]
    [ChartedSpace H N] (f : Time → N) (t : Time) :
    manifoldDeriv I f t =
      mfderiv 𝓘(ℝ, Time) I f t ((1 : Time) : TangentSpace 𝓘(ℝ, Time) t) := rfl

open Manifold in
/-- The time derivative is the manifold derivative for functions into normed spaces. -/
lemma deriv_eq_mfderiv [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → M) (t : Time) :
    deriv f t =
      mfderiv 𝓘(ℝ, Time) 𝓘(ℝ, M) f t
        ((1 : Time) : TangentSpace 𝓘(ℝ, Time) t) := by
  rw [deriv_eq, ← mfderiv_eq_fderiv]
  rfl

open Manifold in
lemma deriv_eq_manifoldDeriv [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → M) (t : Time) :
    deriv f t = manifoldDeriv 𝓘(ℝ, M) f t := by
  rw [deriv_eq_mfderiv, manifoldDeriv_eq]

open Manifold in
@[simp]
lemma manifoldDeriv_const {E H N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [TopologicalSpace N]
    [ChartedSpace H N] (n : N) :
    manifoldDeriv I (fun _ : Time => n) t = 0 := by
  simp [manifoldDeriv]

/-!

## B. Linearlity properties of the derivative

-/

lemma deriv_smul (f : Time → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∂ₜ (fun t => k • f t) t = k • ∂ₜ (fun t => f t) t := by
  rw [deriv, fderiv_fun_const_smul]
  rfl
  fun_prop

lemma deriv_neg [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) :
    ∂ₜ (-f) t = -∂ₜ f t := by
  rw [deriv, fderiv_neg]
  rfl

lemma deriv_add [NormedAddCommGroup M] [NormedSpace ℝ M] (f g : Time → M)
    (hf : DifferentiableAt ℝ f t) (hg : DifferentiableAt ℝ g t) :
    ∂ₜ (fun s => f s + g s) t = ∂ₜ f t + ∂ₜ g t := by
  simp only [Time.deriv_eq]
  rw [fderiv_fun_add hf hg, _root_.add_apply]

lemma deriv_fun_sum {ι : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (s : Finset ι) (a : ι → Time → M) (ha : ∀ i ∈ s, DifferentiableAt ℝ (a i) t) :
    ∂ₜ (fun x => ∑ i ∈ s, a i x) t = ∑ i ∈ s, ∂ₜ (a i) t := by
  simp only [Time.deriv_eq]
  rw [fderiv_fun_sum ha, _root_.sum_apply]

lemma deriv_mul_const (f : Time → ℝ) (c : ℝ) (hf : DifferentiableAt ℝ f t) :
    ∂ₜ (fun s => f s * c) t = ∂ₜ f t * c := by
  simp only [Time.deriv_eq]
  rw [fderiv_mul_const hf c, _root_.smul_apply, smul_eq_mul, mul_comm]

/-- Quotient rule for `Time.deriv` on real-valued functions: if `c` and `g` are
  differentiable at `t` and `g t ≠ 0`, then
  `∂ₜ (c / g) t = (∂ₜ c t * g t - c t * ∂ₜ g t) / (g t)^2`. -/
lemma deriv_div {c g : Time → ℝ}
    (hc : DifferentiableAt ℝ c t) (hg : DifferentiableAt ℝ g t) (hgz : g t ≠ 0) :
    ∂ₜ (fun s => c s / g s) t =
      (∂ₜ c t * g t - c t * ∂ₜ g t) / (g t) ^ 2 := by
  repeat rw [Time.deriv_eq]
  ring_nf
  simp [fderiv_fun_mul hc (DifferentiableAt.fun_inv (by fun_prop) hgz),
    fderiv_fun_comp t (differentiableAt_inv hgz) hg]
  field_simp
  ring

/-!

## C. Derivative of constant functions

-/

@[simp]
lemma deriv_const [NormedAddCommGroup M] [NormedSpace ℝ M] (m : M) :
    ∂ₜ (fun _ => m) t = 0 := by
  rw [deriv]
  simp

/-!

## D. Smoothness properties

-/

open MeasureTheory ContDiff InnerProductSpace Time

@[fun_prop]
lemma val_contDiff {n : WithTop ℕ∞} : ContDiff ℝ n Time.val := by
  change ContDiff ℝ n toRealCLM
  fun_prop

@[fun_prop]
lemma deriv_differentiable_of_contDiff {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ (∂ₜ f) := by
  unfold deriv
  change Differentiable ℝ ((fun x => x 1) ∘ (fun t => fderiv ℝ f t))
  apply Differentiable.comp
  · fun_prop
  · rw [contDiff_infty_iff_fderiv, contDiff_infty_iff_fderiv] at hf
    exact hf.2.1

@[fun_prop]
lemma deriv_contDiff_of_contDiff {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] (f : Time → M) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (∂ₜ f) := by
  unfold deriv
  change ContDiff ℝ ∞ ((fun x => x 1) ∘ (fun t => fderiv ℝ f t))
  apply ContDiff.comp <;> fun_prop

@[fun_prop]
lemma deriv_contDiff_of_space {n} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (f : Time → Space d → M) (hf : ContDiff ℝ (n + 1) ↿f) :
    ContDiff ℝ n fun (x : Space d) => (∂ₜ fun t => f t x) t := by
  unfold deriv
  fun_prop

/-!

## E. Derivatives of components

-/

lemma differentiable_euclid {f : Time → EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i, Differentiable ℝ (fun t => f t i)) :
    Differentiable ℝ f := by
  rw [differentiable_euclidean]
  fun_prop

lemma deriv_euclid { μ} {f : Time→ EuclideanSpace ℝ (Fin n)}
    (hf : Differentiable ℝ f) (t : Time) :
    deriv (fun t => f t μ) t = deriv (fun t => f t) t μ := by
  rw [deriv_eq]
  change fderiv ℝ (EuclideanSpace.proj μ ∘ fun x => f x) t 1 = _
  rw [fderiv_comp]
  · simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp, Function.comp_apply,
    PiLp.proj_apply]
    rw [← deriv_eq]
  · fun_prop
  · fun_prop

lemma fderiv_euclid { μ} {f : Time→ EuclideanSpace ℝ (Fin n)}
    (hf : Differentiable ℝ f) (t dt : Time) :
    fderiv ℝ (fun t => f t μ) t dt = fderiv ℝ (fun t => f t) t dt μ := by
  change fderiv ℝ (EuclideanSpace.proj μ ∘ fun x => f x) t dt = _
  rw [fderiv_comp]
  · simp [-EuclideanSpace.coe_proj]
  · fun_prop
  · fun_prop

lemma deriv_lorentzVector {d : ℕ} {f : Time → Lorentz.Vector d}
    (hf : Differentiable ℝ f) (t : Time) (i : Fin 1 ⊕ Fin d) :
    deriv (fun t => f t i) t = deriv (fun t => f t) t i := by
  rw [deriv_eq]
  change fderiv ℝ (Lorentz.Vector.coordCLM i ∘ fun x => f x) t 1 = _
  rw [fderiv_comp]
  · simp
    rw [← deriv_eq]
    rfl
  · fun_prop
  · fun_prop

lemma deriv_space {d : ℕ} {f : Time → Space d}
    (hf : Differentiable ℝ f) (t : Time) (i : Fin d) :
    deriv (fun s => f s i) t = deriv f t i :=
  (Space.fderiv_space_components i f hf t 1).symm

end Time
