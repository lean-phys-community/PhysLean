/-
Copyright (c) 2025 Rein Zustand. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rein Zustand
-/
module

public import Physlib.Mathematics.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Physlib.SpaceAndTime.Time.Derivatives
public import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
public import Physlib.Mathematics.VariationalCalculus.HasVarGradient
public import Physlib.ClassicalMechanics.EulerLagrange

/-!

# Equivalent Lagrangians under Total Derivatives

## i. Overview

Two Lagrangians are physically equivalent if they differ by a total time derivative
d/dt F(q, t). This is because the Euler-Lagrange equations depend only on extremizing
the action integral, and total derivatives don't affect which paths are extremal.

This module defines the key concept of a function being a total time derivative,
which is essential for analyzing symmetries like Galilean invariance.

Note: Some authors call this "gauge equivalence" by analogy with gauge transformations
in field theory, but we avoid that terminology here since no gauge fields are involved.

## ii. Key insight

A general function δL(t, q, dₜ q) is a total time derivative if there exists a function
F(t, q) (independent of velocity) such that:
  δL(t, q, dₜ q) = d/dt F(t, q) = fderiv ℝ F (t q) (v, 1)

By the chain rule, this expands to:
  δL(t, q, dₜ q) = ∂F/∂t + ⟨∇ᵣF, dₜ q⟩

For the special case where δL depends only on velocity dₜ q (not position or time),
this implies a strong constraint:
  δL(dₜ q) = ⟨g, dₜ q⟩ for some constant vector g

This is because:
1. d/dt F(t, q) = ∂F/∂t + ⟨∇F, dₜ q⟩
2. For δL to be q-independent, ∇F must be q-independent
3. For δL to be t-independent, the time-dependent part must vanish
4. The result is δL = ⟨g, dₜ q⟩ for constant g

## iii. Key definitions

- `IsTotalTimeDerivative`: General case for δL(t, q, dₜ q)
- `IsTotalTimeDerivativeVelocity`: Velocity-only case, equivalent to δL(dₜ q) = ⟨g, dₜ q⟩

## iv. References

- Landau & Lifshitz, "Mechanics", §2 (The principle of least action)
- Landau & Lifshitz, "Mechanics", §4 (The Lagrangian for a free particle)

-/

@[expose] public section

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

namespace ClassicalMechanics

open InnerProductSpace ContDiff Time ContinuousMultilinearMap

namespace Lagrangian
/-!

## A. General Total Time Derivative

-/

/-- A function δL(t, q, dₜ q) is a total time derivative if it can be written as d/dt F(r, t)
    for some function F that depends on position and time but not velocity,

δL(t, q, dₜ q) = (d/dt) F(t, q)

    This is the most general form of Lagrangian equivalence under total derivatives.
    The key point is that F must be independent of velocity. -/
def IsTotalTimeDerivative
    (δL : Time → X → X → ℝ) : Prop :=
    ∃ (F : Time → X → ℝ) (_ : ContDiff ℝ ∞ ↿F),
    ∀ t (q : Time → X), (ContDiff ℝ ∞ q) → δL t (q t) (∂ₜ q t) = ∂ₜ (fun t' => F t' (q t')) t

/--
    Explicit reformulation (by the chain rule):
    δL(t, q, dₜ q) = ∂F/∂t(t, q) + ⟨∇ᵣF(t, q), dₜ q⟩

    or

    δL(t, q, dₜ q) = fderiv ℝ F (t, q) (1, dₜ q)
-/
lemma isTotalTimeDerivative_explicit {δL : Time → X → X → ℝ} :
    IsTotalTimeDerivative δL ↔  (∃ (F : Time → X → ℝ) (_ : ContDiff ℝ ∞ ↿F),
    ∀ t q v, δL t q v = fderiv ℝ ↿F (t, q) ((1 : Time), v)) := by
  let tq := fun (q : Time → X) t => (t, q t)
  have h_tq_der_val : ∀ (q : Time → X) t, ContDiff ℝ ∞ q ->
      fderiv ℝ (tq q) t 1 = (1, ∂ₜ q t) := by
    intro q t hq
    have h := (differentiableAt_id (𝕜 := ℝ) (x := t)).fderiv_prodMk
      ((hq.contDiffAt (x := t)).differentiableAt (by simp))
    dsimp [tq]
    simpa [Time.deriv_eq] using congrArg (fun f => f 1) h
  have h_F_tq_der : ∀ (q : Time → X) (F : Time → X → ℝ) t, (ContDiff ℝ ∞ ↿F) → (ContDiff ℝ ∞ q) →
      ∂ₜ (fun t' => ↿F (t', q t')) t = fderiv ℝ ↿F (t, q t) ((1 : Time), ∂ₜ q t) := by
    intro q F t hF hq
    have h_diff_F : DifferentiableAt ℝ ↿F (t, q t) :=
      hF.contDiffAt.differentiableAt (by simp)
    have h_diff_tq : DifferentiableAt ℝ (tq q) t := by
      have h_contDiff : ContDiff ℝ ∞ (tq q) := by fun_prop
      exact h_contDiff.contDiffAt.differentiableAt (by simp)
    calc
      ∂ₜ (fun t' => ↿F (t', q t')) t = fderiv ℝ (fun t' => ↿F (t', q t')) t 1 := by
        rw [Time.deriv_eq]
      _ = fderiv ℝ ((↿F) ∘ (tq q)) t 1 := rfl
      _ = (fderiv ℝ ↿F ((tq q) t) ∘SL fderiv ℝ (tq q) t) 1 := by
        rw [fderiv_comp t h_diff_F h_diff_tq]
      _ = fderiv ℝ ↿F ((tq q) t) (fderiv ℝ (tq q) t 1) := rfl
      _ = fderiv ℝ ↿F (t, q t) ((1 : Time), ∂ₜ q t) := by
        rw [h_tq_der_val q t hq]
  constructor
  · intro h
    rcases h with ⟨F, hF⟩
    rcases hF with ⟨hFdif, hFder⟩
    use F, hFdif
    intro t q₀ v
    let qv := fun (t' : Time) => (q₀ - t.val • v) + t'.val • v
    have h_qv_contDiff : ContDiff ℝ ∞ qv := by fun_prop
    have h_qv_t : qv t = q₀ := by
      dsimp [qv]; simp [sub_add_cancel]
    have h_qv_der : ∂ₜ qv t = v := by
      rw [Time.deriv_eq]
      dsimp [qv]
      rw [fderiv_const_add (q₀ - t.val • v) (f := fun (t' : Time) => t'.val • v)]
      have h := fderiv_smul_const (by fun_prop : DifferentiableAt ℝ (fun (t' : Time) => t'.val) t) v
      simpa [fderiv_val] using congrArg (fun f => f 1) h
    rw [← h_qv_t, ← h_qv_der, hFder, ← h_F_tq_der]
    · rfl
    · exact hFdif
    · exact h_qv_contDiff
    · exact h_qv_contDiff
  · intro h
    rcases h with ⟨F, hF⟩
    rcases hF with ⟨hFdif, hFder⟩
    use F, hFdif
    intro t q hq
    rw [hFder, ← h_F_tq_der]
    · rfl
    · exact hFdif
    · exact hq

/--
Elementary fact: if δL is a time derivative, then so is -δL.
-/
lemma isTotalTimeDerivative_neg {δL : Time → X → X → ℝ} (h :  IsTotalTimeDerivative δL) :
    IsTotalTimeDerivative (- δL) := by
    rcases h with ⟨F, hF_contDiff, hF⟩
    refine ⟨fun t q => -F t q, hF_contDiff.neg, fun t q hq => ?_⟩
    calc
      (-δL) t (q t) (∂ₜ q t) = -(δL t (q t) (∂ₜ q t)) := rfl
      _ = -(∂ₜ (fun t' => F t' (q t')) t) := by rw [hF t q hq]
      _ = ∂ₜ (-(fun t' => F t' (q t'))) t := by rw [← Time.deriv_neg]
      _ = ∂ₜ (fun t' => -F t' (q t')) t := rfl

/--
If δL is a total time derivative (of a smooth function), then it is smooth
-/
lemma totalTimeDerivative_contDiff {δL : Time → X → X → ℝ} (h : IsTotalTimeDerivative δL):
    ContDiff ℝ ∞ ↿δL := by
  rcases (isTotalTimeDerivative_explicit.mp h) with ⟨F, hF, heq⟩
  have hδL :
      δL = fun (t : Time) (q : X) (v : X) => fderiv ℝ ↿F (t, q) (1, v) := by
    funext t q v; exact heq t q v
  rw [hδL]
  fun_prop

/-!
## B. Total time derivative do not affect the physical content
  The total time derivative does not affect the Euler-Lagrange equations, because its variational
  derivative is zero:
  ∫d/dt F(t, q)= F(t₁,q₁) - F(t₀,q₀)
  is fixed by the boundary conditions.
-/


 /--
Total time derivative has a variational derivative, which is zero
 -/
lemma totalTimeDerivative_hasZeroVarGradient [CompleteSpace X] {δL : Time → X → X → ℝ}
    (h : IsTotalTimeDerivative δL) (q : Time → X) (hq : ContDiff ℝ ∞ q):
     HasVarGradientAt (fun q' t => δL t (q' t) (∂ₜ q' t)) (fun _ => 0) q := by
  rcases h with ⟨F,hF_contDiff, hF⟩
  let traj_deriv := fun (G : Time → ℝ) t => fderiv ℝ G t 1
  let F_traj := fun (q : Time → X) t => F t (q t)
  apply HasVarGradientAt.intro _
  · apply HasVarAdjDerivAt.congr (F := fun q' => traj_deriv (F_traj q'))
    · apply HasVarAdjDerivAt.comp (F := traj_deriv) (G := F_traj)
      · apply HasVarAdjDerivAt.fderiv
        fun_prop
      · apply HasVarAdjDerivAt.fmap (f := fun t => F t)
        · exact hq
        · fun_prop
        · intro t x
          apply DifferentiableAt.hasAdjFDerivAt
          apply Differentiable.differentiableAt
          apply ContDiff.differentiable
          fun_prop
          decide
    · intro q' hq'
      funext t'
      rw [hF t' q' hq']
      rfl
  funext t
  unfold adjFDeriv
  simp [adjoint_eq_clm_adjoint]

/--
If two lagrangians, L and L', differ by a total time derivative, and L has a variational derivative
grad, then so does L'.
 -/
lemma totalTimeDerivative_hasVarGradientAt_equivalence [CompleteSpace X] (L δL : Time → X → X → ℝ)
    (hδL : IsTotalTimeDerivative δL)
    (q : Time → X)    (hq : ContDiff ℝ ∞ q) (grad : Time → X)
    (hgrad :  HasVarGradientAt (fun q' t => L t (q' t) (fderiv ℝ  q' t 1)) grad q) :
    HasVarGradientAt (fun q' t => (L + δL) t (q' t) (fderiv ℝ q' t 1)) grad q := by
  have h_add := HasVarGradientAt.add
    (F := fun q' t => L t (q' t) (fderiv ℝ q' t 1))
    (F' := fun q' t => δL t (q' t) (∂ₜ q' t))
    hgrad (totalTimeDerivative_hasZeroVarGradient hδL q hq)
  convert h_add using 1
  · rfl
  · ext
    simp


/-
Reformulation of the previous result:
If two lagrangians, L and L', differ by a total time derivative, their variational time derivatives
coincide (or neither of them has a variational derivative).
-/
lemma totalTimeDerivative_varGradient_equivalenvce [CompleteSpace X] (L L' : Time → X → X → ℝ)
    (htot : IsTotalTimeDerivative (L' - L))
    (q : Time → X) (hq : ContDiff ℝ ∞ q):
    (δ (q':=q), ∫ t, L' t (q' t) (fderiv ℝ q' t 1)) =
       (δ (q':=q), ∫ t, L t (q' t) (fderiv ℝ q' t 1)) := by
  let δL := (fun t q v => L' t q v - L t q v)
  by_cases hL : ∃ grad, HasVarGradientAt (fun q' t => L t (q' t) (fderiv ℝ q' t 1)) grad q
  · apply HasVarGradientAt.varGradient
    have h_triv : L' = L + (L' - L) := by module
    rw [h_triv]
    apply totalTimeDerivative_hasVarGradientAt_equivalence
    · exact htot
    · exact hq
    · rcases hL with ⟨grad, hgrad⟩
      rw [ HasVarGradientAt.varGradient (fun q' t => L t (q' t) (fderiv ℝ  q' t 1)) grad q hgrad]
      exact hgrad
  · by_cases hL' : ∃ grad, HasVarGradientAt (fun q' t => L' t (q' t) (fderiv ℝ q' t 1)) grad q
    · apply Eq.symm
      apply HasVarGradientAt.varGradient
      have h_triv : L = L' +(-(L' - L)) := by module
      rw [h_triv]
      apply totalTimeDerivative_hasVarGradientAt_equivalence
      · apply isTotalTimeDerivative_neg
        exact htot
      · exact hq
      · rcases hL' with ⟨grad, hgrad⟩
        rw [HasVarGradientAt.varGradient (fun q' t => L' t (q' t) (fderiv ℝ  q' t 1)) grad q hgrad]
        exact hgrad
    · unfold varGradient
      simp only [hL, hL', ↓reduceDIte]

/--
Corollary: If L and L' differ by a total time derivative, then the corresponding Euler-Lagrange
operators coincide
-/
lemma totalTimeDerivative_eulerLagrange_equivalenvce [CompleteSpace X] (L L' : Time → X → X → ℝ)
    (htot : IsTotalTimeDerivative (L' - L)) (hContDiff : (ContDiff ℝ ∞ ↿L) ∨ (ContDiff ℝ ∞ ↿L'))
    (q : Time → X) (hq : ContDiff ℝ ∞ q) : eulerLagrangeOp L q = eulerLagrangeOp L' q := by
  rcases (isTotalTimeDerivative_explicit.mp htot) with ⟨F, hFContDiff, hEq⟩
  have h_δL_contDiff := totalTimeDerivative_contDiff htot
  have h_δL_contDiff_neg := totalTimeDerivative_contDiff (isTotalTimeDerivative_neg htot)
  have hContDiff_both : (ContDiff ℝ ∞ ↿L) ∧ (ContDiff ℝ ∞ ↿L') := by
    cases hContDiff with
    | inl hL =>
      have hL' : ContDiff ℝ ∞ ↿L' := by
        have : ↿L' = ↿L + ↿(L' - L) := by
          ext tqv; rcases tqv with ⟨t, q', v⟩; show L' t q' v = L t q' v + (L' - L) t q' v; simp
        rw [this]
        exact hL.add h_δL_contDiff
      exact ⟨hL, hL'⟩
    | inr hL' =>
      have hL : ContDiff ℝ ∞ ↿L := by
        have : ↿L = ↿L' + ↿(-(L' - L)) := by
          ext ⟨t, q', v⟩; show L t q' v = L' t q' v + (-(L' - L)) t q' v; simp
        rw [this]
        exact hL'.add h_δL_contDiff_neg
      exact ⟨hL, hL'⟩
  rw [← euler_lagrange_varGradient L q hq hContDiff_both.left]
  rw [← euler_lagrange_varGradient L' q hq hContDiff_both.right]
  apply Eq.symm
  apply totalTimeDerivative_varGradient_equivalenvce
  · exact htot
  · exact hq

/-!

## C. Velocity-Only Total Time Derivative

When δL depends only on velocity (the free particle case), the condition simplifies.

-/

/-- A velocity-only function that is a total time derivative must be linear in velocity.

    If δL depends only on velocity and equals d/dt F(t, q) for some F,
    then δL(dₜ q) = ⟨g, dₜ q⟩ for some constant vector g.

    This characterization comes from the requirement that:
    - d/dt F(t, q) = ∂F/∂t + ⟨∇F, dₜ q⟩ = ∂F/∂t + ⟨∇F, dₜ q⟩
    - For the result to be independent of q and t, we need ∇F = g (constant) and ∂F/∂t = 0
    - Thus δL(dₜ q) = ⟨g, dₜ q⟩

    WLOG, we assume `δL 0 = 0` since constants are total derivatives (c = d/dt(c·t))
    and can be absorbed without affecting the equations of motion. -/
lemma isTotalTimeDerivativeVelocity  [CompleteSpace X]
    (δL : X → ℝ)
    (hδL0 : δL 0 = 0)
    (h : IsTotalTimeDerivative (fun _ _ v => δL v)) :
    ∃ g : X, ∀ v, δL v = ⟪g, v⟫_ℝ := by
  classical
  rcases (isTotalTimeDerivative_explicit.mp h) with ⟨F, hFdiff, hEq⟩
  let dF : (Time × X) →L[ℝ] ℝ := fderiv ℝ ↿F ((0 : Time), (0 : X))
  have h_time : dF ((1 : Time), (0 : X)) = 0 := by
    simpa [dF, hδL0] using (hEq (0 : Time) (0 : X) (0 : X)).symm
  let φ : X →L[ℝ] ℝ := dF.comp (ContinuousLinearMap.inr ℝ Time X)
  have hφ : ∀ v : X, δL v = φ v := by
    intro v
    have h := hEq (0 : Time) (0 : X) v
    have h1 : δL v = dF ((1 : Time), v) := by simpa [dF] using h
    have h2 : dF ((1 : Time), v) = dF ((0 : Time), v) := by
      calc
        dF ((1 : Time), v) = dF (((0 : Time), v) + ((1 : Time), (0 : X))) := by simp
        _ = dF ((0 : Time), v) + dF ((1 : Time), (0 : X)) := by rw [map_add]
        _ = dF ((0 : Time), v) + 0 := by rw [h_time]
        _ = dF ((0 : Time), v) := by simp
    have h3 : dF ((0 : Time), v) = φ v := by simp [φ, dF]
    rw [h1, h2, h3]
  refine ⟨(InnerProductSpace.toDual ℝ (X)).symm φ, fun v => ?_⟩
  simp [hφ v, InnerProductSpace.toDual_symm_apply]

end Lagrangian

end ClassicalMechanics
