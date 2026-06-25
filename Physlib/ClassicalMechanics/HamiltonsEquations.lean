/-
Copyright (c) 2025 Tomas Skrivan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomas Skrivan, Joseph Tooby-Smith
-/
module

public import Physlib.Mathematics.VariationalCalculus.HasVarGradient
public import Physlib.SpaceAndTime.Time.Derivatives
/-!

# Hamilton's equations

In this module, given a Hamiltonian function `H : Time → X → X → ℝ`,
we define the operator `hamiltonEqOp`
which when equals zero implies hamilton's equations.

We show that the variational derivative of the action functional
`∫ ⟪p, dq/dt⟫ - H(t, p, q) dt` is equal to the `hamiltonEqOp`
applied to `(p, q)`.

## References

- G. J. Sussman and J. Wisdom, "Structure and Interpretation of Classical Mechanics", Section 3.1.2.
<https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book-Z-H-36.html#%_sec_3.1.2>

-/

@[expose] public section

open MeasureTheory ContDiff InnerProductSpace Time

namespace ClassicalMechanics

variable {X} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- Given a hamiltonian `H : Time → X → X → ℝ` the operator which when
  set to zero implies the Hamilton equations. -/
noncomputable def hamiltonEqOp (H : Time → X → X → ℝ) (p : Time → X) (q : Time → X) :
    Time → X × X :=
  fun t => (∂ₜ q t + -gradient (fun x => H t x (q t)) (p t),
    - ∂ₜ p t + -gradient (fun x => H t (p t) x) (q t))

lemma hamiltonEqOp_eq (H : Time → X → X → ℝ) (p : Time → X) (q : Time → X) :
    hamiltonEqOp H p q = fun t => (∂ₜ q t + -gradient (fun x => H t x (q t)) (p t),
      - ∂ₜ p t + -gradient (fun x => H t (p t) x) (q t)) := by
  rfl

lemma hamiltonEqOp_eq_zero_iff_hamiltons_equations (H : Time → X → X → ℝ)
    (p : Time → X) (q : Time → X) :
    hamiltonEqOp H p q = 0 ↔
    (∀ t, ∂ₜ q t = gradient (fun x => H t x (q t)) (p t)) ∧
    (∀ t, ∂ₜ p t = -gradient (fun x => H t (p t) x) (q t)) := by
  simp [hamiltonEqOp_eq, funext_iff, Prod.mk_eq_zero, forall_and, add_eq_zero_iff_neg_eq]

/-- A smooth (`C^∞`) function is differentiable at every point. -/
private lemma differentiableAt_of_contDiff {W Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {g : W → Z} {y : W} (hg : ContDiff ℝ ∞ g) :
    DifferentiableAt ℝ g y :=
  (hg.differentiable (by simp)).differentiableAt

/-- `HasVarAdjDerivAt.fmap` specialized to a smooth uncurried family `f`, with the pointwise
  adjoint given by `adjFDeriv`. The differentiability of each slice `f x` follows from
  smoothness of `↿f`. -/
private lemma hasVarAdjDerivAt_fmap_uncurry {U V : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [InnerProductSpace' ℝ U] [CompleteSpace U]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [InnerProductSpace' ℝ V] [CompleteSpace V]
    (f : Time → U → V) (u : Time → U) (hu : ContDiff ℝ ∞ u) (hf : ContDiff ℝ ∞ ↿f) :
    HasVarAdjDerivAt (fun φ x => f x (φ x)) (fun ψ x => adjFDeriv ℝ (f x) (u x) (ψ x)) u :=
  HasVarAdjDerivAt.fmap f u hu hf fun x _ =>
    (differentiableAt_of_contDiff (hf.comp (contDiff_prodMk_right x))).hasAdjFDerivAt

theorem hamiltons_equations_varGradient
    (H : Time → X → X → ℝ) (pq : Time → X × X) (hp : ContDiff ℝ ∞ pq)
    (hL : ContDiff ℝ ∞ ↿H) :
    (δ (pq':= pq), ∫ t, ⟪(pq' t).1, ∂ₜ (Prod.snd ∘ pq') t⟫_ℝ - H t (pq' t).1 (pq' t).2) =
    fun t => hamiltonEqOp H (fun t => (pq t).1) (fun t => (pq t).2) t := by
  apply HasVarGradientAt.varGradient
  apply HasVarGradientAt.intro _
  · apply HasVarAdjDerivAt.add
    · let i := fun (t : Time) (x : X × X) => ⟪x.1, x.2⟫_ℝ
      apply HasVarAdjDerivAt.comp
        (F := fun (φ : Time → X × X) t => i t (φ t))
        (G := fun (φ : Time → X × X) t => ((φ t).1, fderiv ℝ (Prod.snd ∘ φ) t 1))
      · exact hasVarAdjDerivAt_fmap_uncurry _ _ (by fun_prop) (by fun_prop)
      · apply HasVarAdjDerivAt.prod
        · exact HasVarAdjDerivAt.fst (HasVarAdjDerivAt.id _ (by fun_prop))
        · apply HasVarAdjDerivAt.fderiv' (F := fun (φ : Time → X × X) t => (φ t).2)
          exact hasVarAdjDerivAt_fmap_uncurry _ _ (by fun_prop) (by fun_prop)
    · apply HasVarAdjDerivAt.neg
      exact hasVarAdjDerivAt_fmap_uncurry (fun t => ↿(H t)) _ (by fun_prop) (by fun_prop)
  · simp only [adjFDeriv_prod_snd, Prod.mk_add_mk, add_zero, zero_add]
    funext x
    rw [adjFDeriv_uncurry (differentiableAt_of_contDiff (by fun_prop))]
    simp only [Prod.neg_mk, Prod.mk_add_mk]
    rw [adjFDeriv_inner]
    simp only [one_smul]
    conv_rhs =>
      enter [2, 1, 1, 1, 2, x]
      rw [adjFDeriv_inner]
      simp
    rw [← gradient_eq_adjFDeriv, ← gradient_eq_adjFDeriv]
    rfl
    all_goals exact differentiableAt_of_contDiff (by fun_prop)

end ClassicalMechanics
