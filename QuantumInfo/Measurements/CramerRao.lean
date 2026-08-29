/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import QuantumInfo.States.Mixed.MState
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The quantum Cramér–Rao bound, unitary parametrization

For a state `ρ` and a one-parameter family `ρ_θ = e^{-iθG} ρ e^{iθG}` generated unitarily by a
self-adjoint `G`, and an observable `O` used to build a locally unbiased estimator of `θ`
(normalized so that `∂_θ⟨O⟩_θ|_{θ=0} = 1`), the standard quantum Cramér–Rao bound states

    Var_ρ(O) ≥ 1 / (4 · Var_ρ(G)).

This file proves the algebraic content that this rests on:

* `MState.robertson_uncertainty` — Robertson's 1929 uncertainty relation for two Hermitian
  observables on an arbitrary finite-dimensional state (H. P. Robertson, *The Uncertainty
  Principle*, Phys. Rev. **34**, 163–164 (1929)). It holds for mixed states verbatim: the only
  input is Cauchy–Schwarz for the GNS inner product `⟪X, Y⟫_ρ = Tr(ρ X† Y)`.
* `MState.cramerRao_unitary` — the Cramér–Rao bound as its corollary under the commutator
  normalization hypothesis `⟨i[G,O]⟩_ρ = 1`.
* `MState.cramerRao_pure_unitary` — the pure-state specialization, for which `4 · Var_ρ(G)` is
  *exactly* the quantum Fisher information.

## On the quantum Fisher information

For a **pure** state `4 · Var_ρ(G)` is the quantum Fisher information of the family at `θ = 0`
(Helstrom, *Quantum Detection and Estimation Theory*, Academic Press, 1976, Chap. VIII.4;
Braunstein and Caves, Phys. Rev. Lett. **72**, 3439 (1994), Eqs. (32)–(33): the density-operator
metric becomes an equality on the pure-state boundary, giving `4⟨(Δĥ)²⟩` exactly, and combining
with their Eq. (32) yields the bound above). Braunstein and Caves identify this pure-state case
explicitly as "a Mandelstam–Tamm uncertainty principle... for a parameter `X` and the 'conjugate'
operator `ĥ`" (paragraph after their Eq. (33)).

For a **mixed** state `4 · Var_ρ(G) ≥ QFI_SLD(ρ, G)`, with equality iff `ρ` is pure. Hence
`MState.cramerRao_unitary` is a valid Cramér–Rao lower bound for every state, but it is *tight*
(equal to the inverse quantum Fisher information) only in the pure case. The bound itself follows
*directly* from `robertson_uncertainty` applied to `(G, O)` together with the identity
`∂_θ⟨O⟩_θ|_{θ=0} = ⟨i[G,O]⟩_ρ` for a unitarily generated family. This file does *not* formalize
the dynamics that produces the normalization — that identity is a calculus fact about
differentiating a unitary conjugation, external to this module — the normalization is taken as an
explicit hypothesis, exactly as the cited literature states it for a locally unbiased estimator.

## Table of contents

- A. The Hilbert–Schmidt embedding `Matrix d d ℂ ↪ EuclideanSpace ℂ (d × d)`
- B. Expectation value, variance, and the commutator pairing on a mixed state
- C. Robertson's uncertainty relation
- D. The quantum Cramér–Rao bound
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix

namespace MState

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ## A. The Hilbert–Schmidt embedding

We need exactly one nontrivial analytic fact — Cauchy–Schwarz for the GNS inner product
`⟪X, Y⟫_ρ = Tr(ρ X† Y)` — and we obtain it by writing `Tr(ρ X† Y) = ⟪X √ρ, Y √ρ⟫` for the
genuine Hilbert–Schmidt inner product on `d × d` matrices, realized as `EuclideanSpace ℂ (d × d)`.
Nothing here is specific to quantum information; if it is wanted elsewhere it should move to
`QuantumInfo/ForMathlib/`.
-/

/-- A `d × d` matrix seen as a vector of `EuclideanSpace ℂ (d × d)`, where Mathlib's inner
product space API (Cauchy–Schwarz in particular) is available. This is the Hilbert–Schmidt
picture: `⟪hsVec A, hsVec B⟫ = Tr(Aᴴ B)` (`hsVec_inner`). -/
private def hsVec (M : Matrix d d ℂ) : EuclideanSpace ℂ (d × d) :=
  (WithLp.equiv 2 (d × d → ℂ)).symm (fun p => M p.1 p.2)

set_option linter.unusedSectionVars false in
@[simp]
private lemma hsVec_apply (M : Matrix d d ℂ) (p : d × d) : hsVec M p = M p.1 p.2 := rfl

set_option linter.unusedSectionVars false in
/-- The defining property of `hsVec`: its inner product is `Tr(Aᴴ B)`. -/
private lemma hsVec_inner (A B : Matrix d d ℂ) :
    inner ℂ (hsVec A) (hsVec B) = (Aᴴ * B).trace := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Matrix.trace]
  simp only [hsVec_apply, RCLike.inner_apply, starRingEnd_apply, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact mul_comm _ _

/-! ## B. Expectation value, variance, and the commutator pairing -/

section observables

variable (ρ : MState d)

/-- `exp_val_ℂ` on a Hermitian matrix is real, and equal to `exp_val`. -/
lemma exp_val_ℂ_hermitian (A : HermitianMat d ℂ) :
    ρ.exp_val_ℂ A.mat = (ρ.exp_val A : ℂ) := by
  have hreal : (starRingEnd ℂ) (ρ.exp_val_ℂ A.mat) = ρ.exp_val_ℂ A.mat := by
    simp only [MState.exp_val_ℂ, starRingEnd_apply, ← Matrix.trace_conjTranspose,
      Matrix.conjTranspose_mul, ρ.Hermitian.eq, (A.H).eq]
    rw [Matrix.trace_mul_comm]
  have hre : (ρ.exp_val_ℂ A.mat).re = ρ.exp_val A := by
    simp only [MState.exp_val_ℂ, MState.exp_val, HermitianMat.inner_eq_re_trace, MState.mat_M]
    rw [Matrix.trace_mul_comm]
    simp
  rw [← hre]
  exact (Complex.conj_eq_iff_re.mp hreal).symm

/-- The Hermitian square root of `ρ`, as a bare matrix. -/
private def sqrtMat : Matrix d d ℂ := ρ.M.sqrt.mat

private lemma sqrtMat_isHermitian : (ρ.sqrtMat).IsHermitian := ρ.M.sqrt.H

private lemma sqrtMat_mul_self : ρ.sqrtMat * ρ.sqrtMat = ρ.m := by
  show ρ.M.sqrt.mat * ρ.M.sqrt.mat = ρ.m
  simp [HermitianMat.sqrt_sq ρ.nonneg, MState.mat_M]

/-- `Tr(√ρ X √ρ) = Tr(X ρ)`. -/
private lemma trace_sandwich (X : Matrix d d ℂ) :
    (ρ.sqrtMat * X * ρ.sqrtMat).trace = (X * ρ.m).trace := by
  rw [Matrix.trace_mul_cycle, ρ.sqrtMat_mul_self, Matrix.trace_mul_comm]

/-- `⟪hsVec √ρ, hsVec (A √ρ)⟫ = Tr(A ρ) = ⟨A⟩_ρ`, for Hermitian `A`. -/
private lemma inner_sqrt_left (A : HermitianMat d ℂ) :
    inner ℂ (hsVec ρ.sqrtMat) (hsVec (A.mat * ρ.sqrtMat)) = (ρ.exp_val A : ℂ) := by
  rw [hsVec_inner, ρ.sqrtMat_isHermitian.eq,
    show ρ.sqrtMat * (A.mat * ρ.sqrtMat) = ρ.sqrtMat * A.mat * ρ.sqrtMat by
      simp [Matrix.mul_assoc],
    ρ.trace_sandwich, ← exp_val_ℂ, exp_val_ℂ_hermitian]

/-- `⟪hsVec √ρ, hsVec √ρ⟫ = Tr(ρ) = 1`. -/
private lemma inner_sqrt_self : inner ℂ (hsVec ρ.sqrtMat) (hsVec ρ.sqrtMat) = (1 : ℂ) := by
  rw [hsVec_inner, ρ.sqrtMat_isHermitian.eq, ρ.sqrtMat_mul_self, ρ.tr']

/-- `⟪hsVec (G √ρ), hsVec (O √ρ)⟫ = Tr(G O ρ) = ⟨GO⟩_ρ`. -/
private lemma inner_hsVec_hsVec (G O : HermitianMat d ℂ) :
    inner ℂ (hsVec (G.mat * ρ.sqrtMat)) (hsVec (O.mat * ρ.sqrtMat)) =
      ρ.exp_val_ℂ (G.mat * O.mat) := by
  rw [hsVec_inner, Matrix.conjTranspose_mul, ρ.sqrtMat_isHermitian.eq, (G.H).eq,
    show ρ.sqrtMat * G.mat * (O.mat * ρ.sqrtMat) = ρ.sqrtMat * (G.mat * O.mat) * ρ.sqrtMat by
      simp [Matrix.mul_assoc],
    ρ.trace_sandwich, ← exp_val_ℂ]

/-- The variance of a Hermitian observable `A` on the state `ρ`. -/
def variance (A : HermitianMat d ℂ) : ℝ :=
  ρ.exp_val (A ^ 2) - (ρ.exp_val A) ^ 2

/-- The **commutator pairing** `⟨i[G,O]⟩_ρ` of two Hermitian observables. It is a real number
because `i[G,O]` is Hermitian when `G` and `O` are; it is the quantity normalized to `1` for a
locally unbiased estimator. -/
def comm_exp_val (G O : HermitianMat d ℂ) : ℝ :=
  (ρ.exp_val_ℂ (Complex.I • (G.mat * O.mat - O.mat * G.mat))).re

/-- The centered Hilbert–Schmidt vector `A √ρ - ⟨A⟩_ρ √ρ`, whose squared norm is `Var_ρ(A)`
(`norm_centered_sq`). -/
private def centeredVec (A : HermitianMat d ℂ) : EuclideanSpace ℂ (d × d) :=
  hsVec (A.mat * ρ.sqrtMat) - (ρ.exp_val A : ℂ) • hsVec ρ.sqrtMat

private lemma norm_centered_sq (A : HermitianMat d ℂ) :
    ‖ρ.centeredVec A‖ ^ 2 = ρ.variance A := by
  have hself := ρ.inner_sqrt_self
  have hleft := ρ.inner_sqrt_left A
  have hright : inner ℂ (hsVec (A.mat * ρ.sqrtMat)) (hsVec ρ.sqrtMat) = (ρ.exp_val A : ℂ) := by
    rw [← inner_conj_symm, hleft, Complex.conj_ofReal]
  have hAA := ρ.inner_hsVec_hsVec A A
  have hAsq : ρ.exp_val_ℂ (A.mat * A.mat) = (ρ.exp_val (A ^ 2) : ℂ) := by
    rw [← ρ.exp_val_ℂ_hermitian (A ^ 2), HermitianMat.mat_pow, pow_two]
  have hexpand : (inner ℂ (ρ.centeredVec A) (ρ.centeredVec A) : ℂ) =
      ρ.exp_val_ℂ (A.mat * A.mat) - (ρ.exp_val A : ℂ) * (ρ.exp_val A : ℂ) := by
    unfold centeredVec
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hself, hleft, hright, hAA]
    ring
  have hre : ‖ρ.centeredVec A‖ ^ 2 = (inner ℂ (ρ.centeredVec A) (ρ.centeredVec A) : ℂ).re :=
    (inner_self_eq_norm_sq (𝕜 := ℂ) (ρ.centeredVec A)).symm
  rw [hre, hexpand, variance, hAsq, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_re]
  ring

/-- `Var_ρ(A) ≥ 0`. -/
lemma variance_nonneg (A : HermitianMat d ℂ) : 0 ≤ ρ.variance A := by
  rw [← ρ.norm_centered_sq]
  positivity

/-! ## C. Robertson's uncertainty relation -/

/-- `exp_val_ℂ` of a product is conjugate-antisymmetric: `conj ⟨GO⟩_ρ = ⟨OG⟩_ρ`. -/
private lemma exp_val_ℂ_swap (G O : HermitianMat d ℂ) :
    (starRingEnd ℂ) (ρ.exp_val_ℂ (G.mat * O.mat)) = ρ.exp_val_ℂ (O.mat * G.mat) := by
  simp only [MState.exp_val_ℂ, starRingEnd_apply, ← Matrix.trace_conjTranspose]
  rw [show ((G.mat * O.mat) * ρ.m)ᴴ = ρ.m * O.mat * G.mat by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, ρ.Hermitian.eq, (G.H).eq,
          (O.H).eq, ← Matrix.mul_assoc],
      Matrix.mul_assoc, Matrix.trace_mul_comm]

private lemma inner_centered_centered (G O : HermitianMat d ℂ) :
    (inner ℂ (ρ.centeredVec G) (ρ.centeredVec O) : ℂ) =
      ρ.exp_val_ℂ (G.mat * O.mat) - (ρ.exp_val G : ℂ) * (ρ.exp_val O : ℂ) := by
  have hself := ρ.inner_sqrt_self
  have hGl := ρ.inner_sqrt_left G
  have hOl := ρ.inner_sqrt_left O
  have hGr : inner ℂ (hsVec (G.mat * ρ.sqrtMat)) (hsVec ρ.sqrtMat) = (ρ.exp_val G : ℂ) := by
    rw [← inner_conj_symm, hGl, Complex.conj_ofReal]
  have hGO := ρ.inner_hsVec_hsVec G O
  unfold centeredVec
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, hself, hOl, hGr, hGO]
  ring

/-- **Robertson's uncertainty relation** (H. P. Robertson, Phys. Rev. **34**, 163–164 (1929)),
for two Hermitian observables on an arbitrary finite-dimensional state: the product of variances
dominates a quarter of the squared commutator pairing. -/
theorem robertson_uncertainty (G O : HermitianMat d ℂ) :
    (ρ.comm_exp_val G O) ^ 2 / 4 ≤ ρ.variance G * ρ.variance O := by
  set z : ℂ := inner ℂ (ρ.centeredVec G) (ρ.centeredVec O) with hz
  have hCS : ‖z‖ ≤ ‖ρ.centeredVec G‖ * ‖ρ.centeredVec O‖ := norm_inner_le_norm _ _
  have hprodsq : (‖ρ.centeredVec G‖ * ‖ρ.centeredVec O‖) ^ 2 = ρ.variance G * ρ.variance O := by
    rw [mul_pow, ρ.norm_centered_sq G, ρ.norm_centered_sq O]
  -- `z - conj z` is the raw commutator expectation.
  have hz_sub : z - conj z =
      ρ.exp_val_ℂ (G.mat * O.mat) - ρ.exp_val_ℂ (O.mat * G.mat) := by
    have hzz : z =
        ρ.exp_val_ℂ (G.mat * O.mat) - (ρ.exp_val G : ℂ) * (ρ.exp_val O : ℂ) := by
      rw [hz]; exact ρ.inner_centered_centered G O
    rw [hzz, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, ρ.exp_val_ℂ_swap]
    ring
  -- `⟨i[G,O]⟩_ρ = -2 · Im z`.
  have hlin : ρ.exp_val_ℂ (Complex.I • (G.mat * O.mat - O.mat * G.mat)) =
      Complex.I * (ρ.exp_val_ℂ (G.mat * O.mat) - ρ.exp_val_ℂ (O.mat * G.mat)) := by
    simp only [MState.exp_val_ℂ, Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_smul,
      Matrix.trace_sub, smul_eq_mul]
  have hw : z - conj z = 2 * Complex.I * (z.im : ℂ) := by
    apply Complex.ext
    · simp [Complex.sub_re, Complex.conj_re, Complex.mul_re, Complex.mul_im]
    · simp [Complex.sub_im, Complex.conj_im, Complex.mul_re, Complex.mul_im]
      ring
  have hcomm : ρ.comm_exp_val G O = -2 * z.im := by
    have hval : ρ.exp_val_ℂ (Complex.I • (G.mat * O.mat - O.mat * G.mat)) =
        ((-2 * z.im : ℝ) : ℂ) := by
      rw [hlin, ← hz_sub, hw]
      push_cast
      rw [show Complex.I * (2 * Complex.I * (z.im : ℂ)) =
          2 * (Complex.I * Complex.I) * (z.im : ℂ) by ring, Complex.I_mul_I]
      ring
    rw [comm_exp_val, hval, Complex.ofReal_re]
  -- Combine Cauchy–Schwarz with `Im z ^ 2 ≤ ‖z‖ ^ 2`.
  have hnormsq : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [sq, Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
  have hzim : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hnormsq, sq]; nlinarith [sq_nonneg z.re]
  have hfinal : (ρ.comm_exp_val G O) ^ 2 / 4 ≤ ‖z‖ ^ 2 := by
    rw [hcomm]; nlinarith [hzim]
  calc (ρ.comm_exp_val G O) ^ 2 / 4
      ≤ ‖z‖ ^ 2 := hfinal
    _ ≤ (‖ρ.centeredVec G‖ * ‖ρ.centeredVec O‖) ^ 2 := by gcongr
    _ = ρ.variance G * ρ.variance O := hprodsq

/-! ## D. The quantum Cramér–Rao bound -/

/-- **The quantum Cramér–Rao bound**, unitary parametrization (Helstrom 1976, Chap. VIII.4;
Braunstein–Caves, Phys. Rev. Lett. **72**, 3439 (1994), Eqs. (32)–(33)). For a family
`ρ_θ = e^{-iθG} ρ e^{iθG}` and an observable `O` normalized to `∂_θ⟨O⟩_θ|_{θ=0} = 1` — the
standard normalization of a locally unbiased estimator, taken here as the explicit hypothesis
`comm_exp_val` rather than derived from the dynamics — the variance of `O` is at least the
inverse of `4 · Var_ρ(G)`. For a pure state `4 · Var_ρ(G)` is exactly the quantum Fisher
information (see the module docstring); in general it only bounds it from above, so this is a
valid but not tight Cramér–Rao bound. -/
theorem cramerRao_unitary (G O : HermitianMat d ℂ)
    (hG : 0 < ρ.variance G) (hnorm : ρ.comm_exp_val G O = 1) :
    1 / (4 * ρ.variance G) ≤ ρ.variance O := by
  have hR := ρ.robertson_uncertainty G O
  rw [hnorm] at hR
  norm_num at hR
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hR, ρ.variance_nonneg O]

/-- The pure-state quantum Cramér–Rao bound: the specialization of `cramerRao_unitary` to
`MState.pure ψ`, for which `4 · Var_ρ(G)` is *exactly* the quantum Fisher information of the
family (Braunstein–Caves 1994, pure-state boundary), so the bound is tight. -/
theorem cramerRao_pure_unitary {ψ : Ket d} (G O : HermitianMat d ℂ)
    (hG : 0 < (MState.pure ψ).variance G) (hnorm : (MState.pure ψ).comm_exp_val G O = 1) :
    1 / (4 * (MState.pure ψ).variance G) ≤ (MState.pure ψ).variance O :=
  (MState.pure ψ).cramerRao_unitary G O hG hnorm

end observables

end MState

end
