/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Calculus.Wirtinger.Coordinate
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!

# Half-plane Wirtinger calculus on `ι → ℂ`

Model-independent complex-analysis on the configuration space `ι → ℂ`, reusable by
any logarithmic half-plane potential. The headline object is the real-linear
coordinate argument `coordArgCLM a b I u = a·zᴵ + b·z̄ᴵ`, with Wirtinger
derivatives `∂_J coordArg = a·δ_{JI}`, `∂̄_J coordArg = b·δ_{JI}` and the
derivatives of `∑ log ∘ coordArg`. Under the realness condition `b = star a` it is
the positive real `2 Re(a·zᴵ)` on the slit plane. Two instances:

- `imArgCLM = coordArgCLM (−i) i` — the upper half-plane, `arg = 2 Im(zᴵ)`;
- `reArgCLM = coordArgCLM 1 1` — the right half-plane, `arg = 2 Re(zᴵ)`.

The open slit-set `{v | ∀ I, imArgCLM I v ∈ Complex.slitPlane}` (a product of
upper half-planes) and its non-vanishing facts are recorded for the `imArgCLM`
instance.

This is the calculus layer: everything uses the raw `dWirtingerCoord` /
`dWirtingerAntiCoord` operators, with no SUSY content.

-/

@[expose] public section

noncomputable section

namespace Physlib.Wirtinger

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!

## A. The general coordinate argument `coordArgCLM`

-/

/-- The inner real-linear map `imArgCLM I u = i (star (uᴵ) − uᴵ)`, the ℂ-valued
projection onto `2 Im(uᴵ)`. Built from the coordinate CLMs `coordProjCLM I` and
`conjCoordCLM I`; on the upper half-plane it is the positive real `2 Im(uᴵ)`. -/
def imArgCLM (I : ι) : (ι → ℂ) →L[ℝ] ℂ :=
  (-Complex.I) • (coordProjCLM I - conjCoordCLM I)

/-- The general ℝ-linear coordinate argument `coordArgCLM a b I u = a·uᴵ + b·z̄ᴵ`.
`imArgCLM` is the `(−i, i)` instance and `reArgCLM` the `(1, 1)` instance; the map
is real-linear (the `z̄` term is conjugate-linear), hence a `→L[ℝ]`. -/
def coordArgCLM (a b : ℂ) (I : ι) : (ι → ℂ) →L[ℝ] ℂ :=
  a • coordProjCLM I + b • conjCoordCLM I

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma coordArgCLM_apply (a b : ℂ) (I : ι) (u : ι → ℂ) :
    coordArgCLM a b I u = a * u I + b * star (u I) := by
  simp only [coordArgCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    coordProjCLM_apply, conjCoordCLM_apply, smul_eq_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- Under the realness condition `b = star a` the coordinate argument is a real:
`coordArgCLM a (star a) I u = a·uᴵ + ā·z̄ᴵ = ↑(2 Re(a·uᴵ))`. Both instances satisfy
it (`imArgCLM`: `star (−i) = i`; `reArgCLM`: `star 1 = 1`), making the argument a
*positive* real on the slit plane — the hypothesis of the metric/positivity story. -/
lemma coordArgCLM_eq_ofReal (a : ℂ) (I : ι) (u : ι → ℂ) :
    coordArgCLM a (star a) I u = ((2 * (a * u I).re : ℝ) : ℂ) := by
  simp only [coordArgCLM_apply, Complex.star_def]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] <;>
    ring

omit [Fintype ι] [DecidableEq ι] in
/-- `imArgCLM` is the `(−i, i)` instance of `coordArgCLM`. -/
lemma imArgCLM_eq_coordArgCLM (I : ι) :
    imArgCLM I = coordArgCLM (-Complex.I) Complex.I I := by
  ext u
  simp only [imArgCLM, coordArgCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    coordProjCLM_apply, conjCoordCLM_apply, smul_eq_mul]
  ring

/-- Holomorphic Wirtinger derivative of the general argument: `∂_J (coordArg a b I) = a·δ_JI`. -/
lemma dWirtingerCoord_coordArgCLM (a b : ℂ) (I J : ι) (u : ι → ℂ) :
    dWirtingerCoord (fun v : ι → ℂ => coordArgCLM a b I v) J u = if J = I then a else 0 := by
  have e : (fun v : ι → ℂ => coordArgCLM a b I v)
      = ⇑(a • coordProjCLM I) + ⇑(b • conjCoordCLM I) := by
    funext v
    simp only [coordArgCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      Pi.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [e, dWirtingerCoord_add_apply (a • coordProjCLM I).differentiableAt
        (b • conjCoordCLM I).differentiableAt J,
      ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_smul',
      dWirtingerCoord_smul_apply a (coordProjCLM I).differentiableAt J,
      dWirtingerCoord_smul_apply b (conjCoordCLM I).differentiableAt J]
  have h1 : dWirtingerCoord (⇑(coordProjCLM I)) J u = if J = I then 1 else 0 :=
    congrFun (dWirtingerCoord_coordProj J I) u
  have h2 : dWirtingerCoord (⇑(conjCoordCLM I)) J u = 0 :=
    congrFun (dWirtingerCoord_conjCoord J I) u
  rw [h1, h2]
  by_cases h : J = I <;> simp [h]

/-- Anti-holomorphic Wirtinger derivative of the general argument: `∂̄_J coordArg = b·δ_JI`. -/
lemma dWirtingerAntiCoord_coordArgCLM (a b : ℂ) (I J : ι) (u : ι → ℂ) :
    dWirtingerAntiCoord (fun v : ι → ℂ => coordArgCLM a b I v) J u = if J = I then b else 0 := by
  have e : (fun v : ι → ℂ => coordArgCLM a b I v)
      = ⇑(a • coordProjCLM I) + ⇑(b • conjCoordCLM I) := by
    funext v
    simp only [coordArgCLM, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      Pi.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  rw [e, dWirtingerAntiCoord_add_apply (a • coordProjCLM I).differentiableAt
        (b • conjCoordCLM I).differentiableAt J,
      ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_smul',
      dWirtingerAntiCoord_smul_apply a (coordProjCLM I).differentiableAt J,
      dWirtingerAntiCoord_smul_apply b (conjCoordCLM I).differentiableAt J]
  have h1 : dWirtingerAntiCoord (⇑(coordProjCLM I)) J u = 0 :=
    congrFun (dWirtingerAntiCoord_coordProj J I) u
  have h2 : dWirtingerAntiCoord (⇑(conjCoordCLM I)) J u = if J = I then 1 else 0 :=
    congrFun (dWirtingerAntiCoord_conjCoord J I) u
  rw [h1, h2]
  by_cases h : J = I <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma imArgCLM_apply (I : ι) (u : ι → ℂ) :
    imArgCLM I u = Complex.I * (star (u I) - u I) := by
  simp only [imArgCLM, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    coordProjCLM_apply, conjCoordCLM_apply, smul_eq_mul]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The inner map is the positive real `2 Im(uᴵ)`, viewed in ℂ:
`imArgCLM I u = ↑(2 Im(uᴵ))`. -/
lemma imArgCLM_eq_ofReal (I : ι) (u : ι → ℂ) :
    imArgCLM I u = ((2 * (u I).im : ℝ) : ℂ) := by
  rw [imArgCLM_apply, Complex.star_def]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im] <;>
    ring

/-!

## B. The slit set and the upper half-plane

-/

omit [Fintype ι] [DecidableEq ι] in
/-- On the slit plane the inner argument is a *positive* real: membership of
`imArgCLM I u = ↑(2 Im(uᴵ))` forces `0 < Im(uᴵ)`, i.e. `uᴵ` lies in the upper
half-plane. -/
lemma im_pos_of_mem_slitPlane {I : ι} {u : ι → ℂ}
    (h : imArgCLM I u ∈ Complex.slitPlane) : 0 < (u I).im := by
  rw [imArgCLM_eq_ofReal] at h
  have := Complex.ofReal_mem_slitPlane.1 h
  linarith

omit [DecidableEq ι] in
/-- The set of configurations on which every inner argument `imArgCLM I v` lies in
the slit plane is open: a finite intersection of preimages of the open set
`Complex.slitPlane` under the continuous CLMs `imArgCLM I`. -/
lemma isOpen_slitSet :
    IsOpen {v : ι → ℂ | ∀ I, imArgCLM I v ∈ Complex.slitPlane} := by
  rw [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun I =>
    (imArgCLM I).continuous.isOpen_preimage _ Complex.isOpen_slitPlane

omit [Fintype ι] [DecidableEq ι] in
/-- Non-vanishing of `z − z̄` on the upper half-plane, via slit-plane membership of
the inner map: `uᴶ − star (uᴶ) ≠ 0`. -/
lemma sub_star_ne_zero {u : ι → ℂ} {J : ι}
    (h : imArgCLM J u ∈ Complex.slitPlane) : u J - star (u J) ≠ 0 := fun hzero =>
  Complex.slitPlane_ne_zero h <| by
    rw [imArgCLM_apply, ← neg_sub, hzero, neg_zero, mul_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- Mirror of `sub_star_ne_zero` with the subtraction reversed: `star (zᴶ) − zᴶ ≠ 0`
on the slit plane — the orientation `field_simp` needs. -/
lemma star_sub_ne_zero {u : ι → ℂ} {J : ι}
    (h : imArgCLM J u ∈ Complex.slitPlane) : star (u J) - u J ≠ 0 := by
  rw [← neg_sub]; exact neg_ne_zero.mpr (sub_star_ne_zero h)

/-!

## C. Wirtinger derivatives of `∑ log ∘ coordArgCLM`

-/

omit [DecidableEq ι] in
/-- Every summand `Complex.log ∘ coordArgCLM a b I` is real-differentiable at `u`
once its inner argument lies in the slit plane. -/
private lemma differentiableAt_log_coordArgCLM {a b : ℂ} {u : ι → ℂ}
    (h : ∀ I, coordArgCLM a b I u ∈ Complex.slitPlane) (I : ι) :
    DifferentiableAt ℝ (fun v : ι → ℂ => Complex.log (coordArgCLM a b I v)) u :=
  ((hasFDerivAt_restrictScalarsℝℂ (Complex.hasDerivAt_log (h I)).hasFDerivAt).comp u
    (coordArgCLM a b I).hasFDerivAt).differentiableAt

/-- Closed form of the holomorphic Wirtinger derivative of a single log summand:
`(coordArgCLM a b I u)⁻¹ · (a · δ_{JI})`. -/
private lemma dWirtingerCoord_log_comp_coordArgCLM {a b : ℂ} {u : ι → ℂ}
    (h : ∀ I, coordArgCLM a b I u ∈ Complex.slitPlane) (I J : ι) :
    dWirtingerCoord (fun v : ι → ℂ => Complex.log (coordArgCLM a b I v)) J u =
      (coordArgCLM a b I u)⁻¹ * (if J = I then a else 0) := by
  rw [dWirtingerCoord_comp_holomorphic_apply (Complex.differentiableAt_log (h I))
    (coordArgCLM a b I).hasFDerivAt.differentiableAt J, dWirtingerCoord_coordArgCLM,
    (Complex.hasDerivAt_log (h I)).deriv]

/-- Holomorphic Wirtinger derivative of the summed log argument: collapses to
`(coordArgCLM a b J u)⁻¹ · a`. -/
lemma dWirtingerCoord_sum_log_comp_coordArgCLM {a b : ℂ} {u : ι → ℂ}
    (h : ∀ I, coordArgCLM a b I u ∈ Complex.slitPlane) (J : ι) :
    dWirtingerCoord (fun v : ι → ℂ => ∑ I, Complex.log (coordArgCLM a b I v)) J u =
      (coordArgCLM a b J u)⁻¹ * a := by
  have hsum :
      dWirtingerCoord (fun v : ι → ℂ => ∑ I, Complex.log (coordArgCLM a b I v)) J u =
        ∑ I, dWirtingerCoord (fun v : ι → ℂ => Complex.log (coordArgCLM a b I v)) J u := by
    simpa using dWirtingerCoord_fun_sum_apply (s := Finset.univ)
      (F := fun I v => Complex.log (coordArgCLM a b I v))
      (fun I _ => differentiableAt_log_coordArgCLM h I) J
  rw [hsum]
  simp_rw [dWirtingerCoord_log_comp_coordArgCLM h]
  rw [Finset.sum_eq_single J
    (fun I _ hI => by rw [if_neg (Ne.symm hI)]; ring)
    (fun hJ => absurd (Finset.mem_univ J) hJ), if_pos rfl]

/-- Closed form of the anti-holomorphic Wirtinger derivative of a single log
summand: `(coordArgCLM a b I u)⁻¹ · (b · δ_{JI})`. -/
private lemma dWirtingerAntiCoord_log_comp_coordArgCLM {a b : ℂ} {u : ι → ℂ}
    (h : ∀ I, coordArgCLM a b I u ∈ Complex.slitPlane) (I J : ι) :
    dWirtingerAntiCoord (fun v : ι → ℂ => Complex.log (coordArgCLM a b I v)) J u =
      (coordArgCLM a b I u)⁻¹ * (if J = I then b else 0) := by
  rw [dWirtingerAntiCoord_comp_holomorphic_apply (Complex.differentiableAt_log (h I))
    (coordArgCLM a b I).hasFDerivAt.differentiableAt J, dWirtingerAntiCoord_coordArgCLM,
    (Complex.hasDerivAt_log (h I)).deriv]

/-- Anti-holomorphic Wirtinger derivative of the summed log argument: collapses to
`(coordArgCLM a b J u)⁻¹ · b`. -/
lemma dWirtingerAntiCoord_sum_log_comp_coordArgCLM {a b : ℂ} {u : ι → ℂ}
    (h : ∀ I, coordArgCLM a b I u ∈ Complex.slitPlane) (J : ι) :
    dWirtingerAntiCoord (fun v : ι → ℂ => ∑ I, Complex.log (coordArgCLM a b I v)) J u =
      (coordArgCLM a b J u)⁻¹ * b := by
  have hsum :
      dWirtingerAntiCoord (fun v : ι → ℂ => ∑ I, Complex.log (coordArgCLM a b I v)) J u =
        ∑ I, dWirtingerAntiCoord (fun v : ι → ℂ => Complex.log (coordArgCLM a b I v)) J u := by
    simpa using dWirtingerAntiCoord_fun_sum_apply (s := Finset.univ)
      (F := fun I v => Complex.log (coordArgCLM a b I v))
      (fun I _ => differentiableAt_log_coordArgCLM h I) J
  rw [hsum]
  simp_rw [dWirtingerAntiCoord_log_comp_coordArgCLM h]
  rw [Finset.sum_eq_single J
    (fun I _ hI => by rw [if_neg (Ne.symm hI)]; ring)
    (fun hJ => absurd (Finset.mem_univ J) hJ), if_pos rfl]

/-!

## D. The upper half-plane instance `imArgCLM = coordArgCLM (−i) i`

-/

omit [Fintype ι] [DecidableEq ι] in
/-- Slit-plane membership transports between `imArgCLM` and its `coordArgCLM`
form, the bridge through which the `imArgCLM` log-chain lemmas reduce to the
general ones. -/
private lemma mem_slitPlane_coordArgCLM_of_imArgCLM {u : ι → ℂ}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) (I : ι) :
    coordArgCLM (-Complex.I) Complex.I I u ∈ Complex.slitPlane := by
  rw [← imArgCLM_eq_coordArgCLM]; exact h I

/-- Holomorphic Wirtinger derivative of the summed log argument on `H^n`: the
`(−i, i)` instance of `dWirtingerCoord_sum_log_comp_coordArgCLM`. -/
lemma dWirtingerCoord_sum_log_comp_imArgCLM {u : ι → ℂ}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) (J : ι) :
    dWirtingerCoord (fun v : ι → ℂ => ∑ I, Complex.log (imArgCLM I v)) J u =
      (imArgCLM J u)⁻¹ * (-Complex.I) := by
  simp_rw [imArgCLM_eq_coordArgCLM]
  exact dWirtingerCoord_sum_log_comp_coordArgCLM (mem_slitPlane_coordArgCLM_of_imArgCLM h) J

/-- Anti-holomorphic Wirtinger derivative of the summed log argument on `H^n`: the
`(−i, i)` instance of `dWirtingerAntiCoord_sum_log_comp_coordArgCLM`. -/
lemma dWirtingerAntiCoord_sum_log_comp_imArgCLM {u : ι → ℂ}
    (h : ∀ I, imArgCLM I u ∈ Complex.slitPlane) (J : ι) :
    dWirtingerAntiCoord (fun v : ι → ℂ => ∑ I, Complex.log (imArgCLM I v)) J u =
      (imArgCLM J u)⁻¹ * Complex.I := by
  simp_rw [imArgCLM_eq_coordArgCLM]
  exact dWirtingerAntiCoord_sum_log_comp_coordArgCLM (mem_slitPlane_coordArgCLM_of_imArgCLM h) J

/-!

## E. The right half-plane instance `reArgCLM = coordArgCLM 1 1`

-/

/-- The right-half-plane coordinate argument `reArgCLM I u = uᴵ + z̄ᴵ = 2 Re(uᴵ)`,
the `(1, 1)` instance of `coordArgCLM`; on the right half-plane it is the positive
real `2 Re(uᴵ)`, the no-scale modulus combination `T + T̄`. -/
def reArgCLM (I : ι) : (ι → ℂ) →L[ℝ] ℂ := coordArgCLM 1 1 I

omit [Fintype ι] [DecidableEq ι] in
@[simp] lemma reArgCLM_apply (I : ι) (u : ι → ℂ) :
    reArgCLM I u = u I + star (u I) := by
  simp only [reArgCLM, coordArgCLM_apply, one_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- The right-half-plane argument is the positive real `2 Re(uᴵ)`, viewed in ℂ. -/
lemma reArgCLM_eq_ofReal (I : ι) (u : ι → ℂ) :
    reArgCLM I u = ((2 * (u I).re : ℝ) : ℂ) := by
  have h : reArgCLM I u = coordArgCLM (1 : ℂ) (star (1 : ℂ)) I u := by rw [reArgCLM, star_one]
  rw [h, coordArgCLM_eq_ofReal, one_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- On the open right half-plane the argument lies in the slit plane: `0 < Re(uᴵ)`
forces `reArgCLM I u = ↑(2 Re uᴵ)` to be a positive real. -/
lemma reArgCLM_mem_slitPlane {I : ι} {u : ι → ℂ} (h : 0 < (u I).re) :
    reArgCLM I u ∈ Complex.slitPlane := by
  rw [reArgCLM_eq_ofReal]
  exact Complex.ofReal_mem_slitPlane.2 (by linarith)

/-- Holomorphic Wirtinger derivative of the right-half-plane argument:
`∂_J reArg = δ_{JI}` (the `(1, 1)` instance of `dWirtingerCoord_coordArgCLM`). -/
lemma dWirtingerCoord_reArgCLM (I J : ι) (u : ι → ℂ) :
    dWirtingerCoord (fun v : ι → ℂ => reArgCLM I v) J u = if J = I then 1 else 0 := by
  simpa only [reArgCLM] using dWirtingerCoord_coordArgCLM 1 1 I J u

/-- Anti-holomorphic Wirtinger derivative of the right-half-plane argument:
`∂̄_J reArg = δ_{JI}` (the `(1, 1)` instance of `dWirtingerAntiCoord_coordArgCLM`). -/
lemma dWirtingerAntiCoord_reArgCLM (I J : ι) (u : ι → ℂ) :
    dWirtingerAntiCoord (fun v : ι → ℂ => reArgCLM I v) J u = if J = I then 1 else 0 := by
  simpa only [reArgCLM] using dWirtingerAntiCoord_coordArgCLM 1 1 I J u

end Physlib.Wirtinger

end

end
