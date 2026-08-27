/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Physlib.Mathematics.InnerProductSpace.PseudoInner
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.QuadraticForm.Signature

/-!
# Index of a pseudo-inner product, and stability of the signature

The index of a pseudo-inner product is `QuadraticForm.sigNeg` of its quadratic form: the largest
dimension of a subspace on which the form is negative definite. Index `0` is the Riemannian case,
index `1` the Lorentzian one.

The main result is that the signature cannot jump under perturbation. It is what makes local
constancy of the index of a pseudo-Riemannian metric a theorem rather than a hypothesis, so that
constructing a metric — Minkowski, Schwarzschild, FLRW — carries no signature-constancy
obligation.

## Main results

* `ContinuousLinearMap.eventually_forall_pos`, `eventually_forall_neg`: definiteness on a fixed
  subspace is an open condition on the form.
* `ContinuousLinearMap.eventually_sigNeg_eq`: on a finite-dimensional real normed space, `sigPos`,
  `sigNeg` and triviality of the radical are locally constant. No symmetry is assumed.
* `PseudoInnerProductSpace.index`, `index_dual_eq`, `index_eq_zero_of_innerProductSpace`.

## Implementation notes

The proof is classical: maximal definite subspaces for `b` remain definite for nearby `c`, so
`sigPos` and `sigNeg` can only grow, while `QuadraticForm.sigPos_add_sigNeg_add_radical` caps
their sum at `finrank`. Openness of definiteness comes from compactness of the unit sphere of a
finite-dimensional subspace.

## Tags

signature, index, inertia, Sylvester, nondegenerate, locally constant
-/

@[expose] public section

open Filter Module Metric Set QuadraticMap
open scoped Topology

namespace ContinuousLinearMap

section Perturbation

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Positive definiteness on a subspace is quantitative: `ε ‖v‖ ^ 2 ≤ b v v` for some `ε > 0`,
by compactness of the unit sphere and homogeneity. -/
lemma exists_pos_forall_le_of_posDef (b : F →L[ℝ] F →L[ℝ] ℝ) {V : Submodule ℝ F}
    (hV : ∀ v : V, v ≠ 0 → 0 < b v v) :
    ∃ ε > 0, ∀ v : V, ε * ‖(v : F)‖ ^ 2 ≤ b v v := by
  have hcont : Continuous fun v : V ↦ b (v : F) (v : F) :=
    b.continuous₂.comp (continuous_subtype_val.prodMk continuous_subtype_val)
  rcases subsingleton_or_nontrivial V with _ | _
  · -- The subspace is trivial: every vector is `0` and both sides vanish.
    refine ⟨1, one_pos, fun v ↦ ?_⟩
    have hv : v = 0 := Subsingleton.elim _ _
    simp [hv]
  · obtain ⟨v₀, hv₀, hmin⟩ :=
      (isCompact_sphere (0 : V) 1).exists_isMinOn
        (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont.continuousOn
    have hv₀norm : ‖v₀‖ = 1 := by simpa using hv₀
    have hv₀ne : v₀ ≠ 0 := by
      intro h; rw [h] at hv₀norm; simp at hv₀norm
    refine ⟨b (v₀ : F) (v₀ : F), hV v₀ hv₀ne, fun v ↦ ?_⟩
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    -- Normalise `v` to the unit sphere and use homogeneity of `v ↦ b v v`.
    have hvn : (0 : ℝ) < ‖(v : F)‖ := by
      simpa using norm_pos_iff.mpr hv
    set u : V := ‖(v : F)‖⁻¹ • v with hu_def
    have hu : u ∈ sphere (0 : V) 1 := by
      simp only [mem_sphere_iff_norm, sub_zero, hu_def, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (by simpa using hvn.ne')
    have hbu : b (v₀ : F) (v₀ : F) ≤ b (u : F) (u : F) := hmin hu
    have hcoe : (u : F) = ‖(v : F)‖⁻¹ • (v : F) := rfl
    have hscale : b (u : F) (u : F) = (‖(v : F)‖ ^ 2)⁻¹ * b (v : F) (v : F) := by
      simp only [hcoe, map_smul, smul_apply, smul_eq_mul]
      ring
    rw [hscale] at hbu
    have hpos : (0 : ℝ) < ‖(v : F)‖ ^ 2 := pow_pos hvn 2
    calc b (v₀ : F) (v₀ : F) * ‖(v : F)‖ ^ 2
        ≤ ((‖(v : F)‖ ^ 2)⁻¹ * b (v : F) (v : F)) * ‖(v : F)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hbu hpos.le
      _ = b (v : F) (v : F) := by field_simp

omit [FiniteDimensional ℝ F] in
/-- If `b ≥ ε ‖·‖ ^ 2` on a subspace and `‖c - b‖ < ε`, then `c` is positive there. -/
private lemma pos_of_norm_sub_lt {b c : F →L[ℝ] F →L[ℝ] ℝ} {V : Submodule ℝ F} {ε : ℝ}
    (hle : ∀ v : V, ε * ‖(v : F)‖ ^ 2 ≤ b v v) (hc : ‖c - b‖ < ε) :
    ∀ v : V, v ≠ 0 → 0 < c (v : F) (v : F) := by
  intro v hv
  have hvn : (0 : ℝ) < ‖(v : F)‖ := by simpa using norm_pos_iff.mpr hv
  have hbound : |c (v : F) (v : F) - b (v : F) (v : F)| ≤ ‖c - b‖ * ‖(v : F)‖ ^ 2 := by
    have h := (c - b).le_opNorm₂ (v : F) (v : F)
    simp only [sub_apply, Real.norm_eq_abs] at h
    calc |c (v : F) (v : F) - b (v : F) (v : F)| ≤ ‖c - b‖ * ‖(v : F)‖ * ‖(v : F)‖ := h
      _ = ‖c - b‖ * ‖(v : F)‖ ^ 2 := by ring
  have hsq : (0 : ℝ) < ‖(v : F)‖ ^ 2 := by positivity
  nlinarith [hle v, (abs_le.mp hbound).1, (abs_le.mp hbound).2]

/-- Positive definiteness on a fixed subspace is an open condition on the bilinear form. -/
lemma eventually_forall_pos {b : F →L[ℝ] F →L[ℝ] ℝ} {V : Submodule ℝ F}
    (hV : ∀ v : V, v ≠ 0 → 0 < b v v) :
    ∀ᶠ c in 𝓝 b, ∀ v : V, v ≠ 0 → 0 < c (v : F) (v : F) := by
  obtain ⟨ε, hε, hle⟩ := exists_pos_forall_le_of_posDef b hV
  filter_upwards [ball_mem_nhds b hε] with c hc
  have h1 : dist c b < ε := Metric.mem_ball.mp hc
  rw [dist_eq_norm c b] at h1
  exact pos_of_norm_sub_lt hle h1

/-- Negative definiteness on a fixed subspace is an open condition on the bilinear form. -/
lemma eventually_forall_neg {b : F →L[ℝ] F →L[ℝ] ℝ} {V : Submodule ℝ F}
    (hV : ∀ v : V, v ≠ 0 → b v v < 0) :
    ∀ᶠ c in 𝓝 b, ∀ v : V, v ≠ 0 → c (v : F) (v : F) < 0 := by
  have hneg : ∀ v : V, v ≠ 0 → 0 < (-b) (v : F) (v : F) := fun v hv ↦ by simpa using hV v hv
  obtain ⟨ε, hε, hle⟩ := exists_pos_forall_le_of_posDef (-b) hneg
  filter_upwards [ball_mem_nhds b hε] with c hc v hv
  have hcb : dist c b < ε := Metric.mem_ball.mp hc
  rw [dist_eq_norm c b] at hcb
  have heq : (-c) - (-b) = -(c - b) := by abel
  have hnorm : ‖(-c) - (-b)‖ < ε := by
    have h2 : ‖(-c) - (-b)‖ = ‖c - b‖ := by rw [heq]; exact norm_neg (c - b)
    rw [h2]; exact hcb
  have := pos_of_norm_sub_lt hle hnorm v hv
  simpa using this

/-! ### Local constancy of the signature -/

variable {b : F →L[ℝ] F →L[ℝ] ℝ}

private lemma sigPos_add_sigNeg_of_radical_eq_bot (hb : b.toQuadraticForm.radical = ⊥) :
    sigPos b.toQuadraticForm + sigNeg b.toQuadraticForm = finrank ℝ F := by
  have h := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := b.toQuadraticForm)
  rwa [hb, finrank_bot, Nat.add_zero] at h

/-- **The signature is locally constant.** If `b.toQuadraticForm` has trivial radical, so does
every nearby form, with the same `sigPos` and `sigNeg`.

No symmetry is assumed: `sigPos`, `sigNeg` and `radical` see only `v ↦ b v v`, which is unchanged
by symmetrising `b`. -/
theorem eventually_sigNeg_eq (hb : b.toQuadraticForm.radical = ⊥) :
    ∀ᶠ c in 𝓝 b, c.toQuadraticForm.radical = ⊥ ∧
      sigPos c.toQuadraticForm = sigPos b.toQuadraticForm ∧
      sigNeg c.toQuadraticForm = sigNeg b.toQuadraticForm := by
  classical
  obtain ⟨Vp, hVpdim, hVppos⟩ :=
    exists_finrank_eq_sigPos_and_posDef b.toQuadraticForm
  obtain ⟨Vn, hVndim, hVnneg⟩ :=
    exists_finrank_eq_sigNeg_and_negDef b.toQuadraticForm
  have hsum := sigPos_add_sigNeg_of_radical_eq_bot hb
  have hpos : ∀ v : Vp, v ≠ 0 → 0 < b (v : F) (v : F) := fun v hv ↦ hVppos v hv
  have hneg : ∀ v : Vn, v ≠ 0 → b (v : F) (v : F) < 0 := fun v hv ↦ by
    have h : (0 : ℝ) < -(b (v : F) (v : F)) := hVnneg v hv
    linarith
  filter_upwards [eventually_forall_pos hpos, eventually_forall_neg hneg] with c hcp hcn
  -- Both maximal subspaces stay definite, so the two parts of the signature can only grow.
  have hle_pos : sigPos b.toQuadraticForm ≤ sigPos c.toQuadraticForm := by
    rw [← hVpdim]
    exact le_sigPos_of_posDef _ fun v hv ↦ hcp v hv
  have hle_neg : sigNeg b.toQuadraticForm ≤ sigNeg c.toQuadraticForm := by
    rw [← hVndim]
    refine le_sigNeg_of_negDef _ fun v hv ↦ ?_
    show (0 : ℝ) < -(c (v : F) (v : F))
    linarith [hcn v hv]
  -- Sylvester's law caps the total, so both inequalities are equalities.
  have hc := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := c.toQuadraticForm)
  have hrad : finrank ℝ c.toQuadraticForm.radical = 0 := by lia
  refine ⟨Submodule.finrank_eq_zero.mp hrad, by lia, by lia⟩

/-! ### Transport along a linear equivalence -/

section Congr

variable {X Y : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y]

/-- A linear equivalence intertwining two continuous bilinear forms preserves `sigNeg`. Used to
transport a fibrewise computation to the model fibre of a vector bundle. -/
lemma sigNeg_toQuadraticForm_of_congr (b : X →L[ℝ] X →L[ℝ] ℝ) (b' : Y →L[ℝ] Y →L[ℝ] ℝ)
    (φ : X ≃ₗ[ℝ] Y) (h : ∀ u w : X, b' (φ u) (φ w) = b u w) :
    sigNeg b.toQuadraticForm = sigNeg b'.toQuadraticForm :=
  QuadraticMap.Equivalent.sigNeg_eq ⟨{ toLinearEquiv := φ, map_app' := fun m ↦ h m m }⟩

/-- Nondegeneracy is likewise transported along a linear equivalence. -/
lemma radical_toQuadraticForm_eq_bot_of_congr (b : X →L[ℝ] X →L[ℝ] ℝ) (b' : Y →L[ℝ] Y →L[ℝ] ℝ)
    (φ : X ≃ₗ[ℝ] Y) (h : ∀ u w : X, b' (φ u) (φ w) = b u w)
    (hb : b.toQuadraticForm.radical = ⊥) : b'.toQuadraticForm.radical = ⊥ := by
  have hiso : QuadraticMap.IsometryEquiv b.toQuadraticForm b'.toQuadraticForm :=
    { toLinearEquiv := φ, map_app' := fun m ↦ h m m }
  rw [← QuadraticMap.IsometryEquiv.map_radical hiso, hb, Submodule.map_bot]

end Congr

end Perturbation

end ContinuousLinearMap

/-! ## The index of a pseudo-inner product space -/

namespace PseudoInnerProductSpace

variable (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [PseudoInnerProductSpace E]

/-- The index, or negative inertia: the largest dimension of a subspace on which the form is
negative definite. Index `0` is the Riemannian case, index `1` the Lorentzian one. -/
noncomputable def index : ℕ := sigNeg (toQuadraticForm E)

lemma index_def : index E = sigNeg (toQuadraticForm E) := rfl

/-- Nondegeneracy, restated: the quadratic form has trivial radical. -/
lemma radical_toQuadraticForm_eq_bot : (toQuadraticForm E).radical = ⊥ := by
  rw [QuadraticMap.radical_eq_ker_polarBilin, Submodule.eq_bot_iff]
  intro v hv
  refine eq_zero_of_pseudoInner_eq_zero fun w ↦ ?_
  have h0 : QuadraticMap.polar (toQuadraticForm E) v w = 0 := by
    simpa using DFunLike.congr_fun (LinearMap.mem_ker.mp hv) w
  have hpolar : QuadraticMap.polar (toQuadraticForm E) v w = 2 * pseudoInner v w := by
    simp only [QuadraticMap.polar, toQuadraticForm_apply, pseudoInner_add_left,
      pseudoInner_add_right]
    rw [pseudoInner_comm w v]
    ring
  linarith

variable [FiniteDimensional ℝ E]

variable {E} in
/-- A positive definite form has index `0`. -/
lemma index_eq_zero_of_posDef (h : (toQuadraticForm E).PosDef) : index E = 0 := by
  obtain ⟨W, hW, hWneg⟩ :=
    exists_finrank_eq_sigNeg_and_negDef (Q := toQuadraticForm E)
  have hWbot : W = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have hxW : (⟨x, hx⟩ : W) ≠ 0 := fun hcontra ↦ hx0 (congrArg Subtype.val hcontra)
    have hlt : toQuadraticForm E x < 0 := by
      have := hWneg _ hxW
      simp only [QuadraticMap.restrict_apply, neg_apply] at this
      linarith
    exact absurd (h x hx0) (by linarith)
  simp [index, ← hW, hWbot]

/-- Raising both indices is an isometry, so the inverse metric has the same index. -/
lemma index_dual_eq [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] :
    sigNeg (dualPseudoInnerSL E).toQuadraticForm = index E := by
  have key : ∀ u w : E, dualPseudoInnerSL E (flatL E u) (flatL E w) = pseudoInner u w := by
    intro u w
    rw [dualPseudoInnerSL_apply, sharpL_flatL, flatL_apply]
  exact (ContinuousLinearMap.sigNeg_toQuadraticForm_of_congr
    (PseudoInnerProductSpace.pseudoInnerSL (E := E)) (dualPseudoInnerSL E)
    (flatEquiv E).toLinearEquiv key).symm

/-- **Riemannian geometry is the index-zero case.** -/
@[simp]
lemma index_eq_zero_of_innerProductSpace (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] : index F = 0 :=
  index_eq_zero_of_posDef fun v hv ↦ by
    simpa using real_inner_self_pos.mpr hv

end PseudoInnerProductSpace
