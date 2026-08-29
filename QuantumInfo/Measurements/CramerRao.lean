/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import QuantumInfo.States.Pure.Braket
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The quantum Cramér–Rao bound, pure states, unitary parametrization

For a pure state `ψ` and a one-parameter family `ψ_θ = e^{-iθG}ψ` generated unitarily by a
self-adjoint `G`, and an observable `O` used to build a locally unbiased estimator of `θ`
(normalized so that `∂_θ⟨O⟩_θ|_{θ=0} = 1`), the standard quantum Cramér–Rao bound states

    Var_ψ(O) ≥ 1 / (4 · Var_ψ(G)),

with `4 · Var_ψ(G)` the quantum Fisher information of the family at `θ = 0`. This is the
textbook identification of Helstrom (*Quantum Detection and Estimation Theory*, Academic Press,
1976, Chap. VIII.4) and of Braunstein and Caves (Phys. Rev. Lett. **72**, 3439 (1994),
Eqs. (32)–(33), the density-operator metric `ds²_DO/dX² ≤ Σⱼ(dpⱼ/dX)²/pⱼ + 4⟨(Δĥ)²⟩_X` becomes
an *equality* on the pure-state boundary, giving `4⟨(Δĥ)²⟩_X` exactly, and combines with their
Eq. (32), `N⟨(δX)²⟩_X · (ds²_DO/dX²) ≥ 1`, to give the bound stated above). Braunstein and Caves
identify this pure-state case explicitly as "a Mandelstam–Tamm uncertainty principle... for a
parameter `X` and the 'conjugate' operator `ĥ`" (paragraph following their Eq. (33)), i.e. the
same Cramér–Rao/Mandelstam–Tamm identification, from the primary source, rather than re-derived.

The bound follows *directly* from the Robertson uncertainty relation applied to the pair
`(G, O)`, using the identity `∂_θ⟨O⟩_θ|_{θ=0} = i⟨ψ, [G, O] ψ⟩` for a unitarily generated family.

This file proves the algebraic content: Robertson's inequality for two Hermitian matrices on a
finite-dimensional pure state, and the Cramér–Rao bound as its corollary under the commutator
normalization hypothesis. It does *not* formalize the dynamics that produces the normalization
(that identity is a calculus fact about differentiating a unitary conjugation, external to this
module); the normalization is taken as an explicit hypothesis, exactly as the cited literature
states it for a locally unbiased estimator.

## A. Expectation value and variance of a Hermitian observable on a pure state

## B. Robertson's uncertainty relation

## C. The quantum Cramér–Rao bound
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate

variable {d : Type*} [Fintype d]

/-! ## A. Expectation value and variance of a Hermitian observable on a pure state -/

/-- The state vector of a `Ket`, seen in `EuclideanSpace ℂ d` where Mathlib's inner product
space API (in particular Cauchy–Schwarz) is available. -/
def Ket.toEuclideanSpace (ψ : Ket d) : EuclideanSpace ℂ d :=
  (WithLp.equiv 2 (d → ℂ)).symm ψ.vec

@[simp]
lemma Ket.toEuclideanSpace_apply (ψ : Ket d) (i : d) :
    ψ.toEuclideanSpace i = ψ.vec i := rfl

lemma Ket.norm_toEuclideanSpace (ψ : Ket d) : ‖ψ.toEuclideanSpace‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp only [Ket.toEuclideanSpace_apply]
  rw [ψ.normalized']
  exact Real.sqrt_one

lemma Ket.inner_self_toEuclideanSpace (ψ : Ket d) :
    inner ℂ ψ.toEuclideanSpace ψ.toEuclideanSpace = (1 : ℂ) := by
  rw [@inner_self_eq_norm_sq_to_K ℂ, ψ.norm_toEuclideanSpace]
  norm_num

/-- The action of a matrix on a vector of `EuclideanSpace ℂ d`, via `Matrix.mulVec` on the
underlying function. -/
def Matrix.onVec (A : Matrix d d ℂ) (v : EuclideanSpace ℂ d) : EuclideanSpace ℂ d :=
  (WithLp.equiv 2 (d → ℂ)).symm (A.mulVec (WithLp.equiv 2 (d → ℂ) v))

@[simp]
lemma Matrix.onVec_apply (A : Matrix d d ℂ) (v : EuclideanSpace ℂ d) (i : d) :
    A.onVec v i = ∑ j, A i j * v j := rfl

lemma Matrix.onVec_mul (A B : Matrix d d ℂ) (v : EuclideanSpace ℂ d) :
    (A * B).onVec v = A.onVec (B.onVec v) := by
  ext i
  simp only [Matrix.onVec_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

lemma Matrix.onVec_sub (A B : Matrix d d ℂ) (v : EuclideanSpace ℂ d) :
    (A - B).onVec v = A.onVec v - B.onVec v := by
  ext i
  simp [Matrix.onVec_apply, sub_mul, Finset.sum_sub_distrib]

lemma Matrix.onVec_smul (c : ℂ) (A : Matrix d d ℂ) (v : EuclideanSpace ℂ d) :
    (c • A).onVec v = c • A.onVec v := by
  ext i
  simp [Matrix.onVec_apply, Finset.mul_sum, mul_assoc]

/-- Two Hermitian matrices commute past the inner product: `⟪v, A w⟫ = ⟪A v, w⟫`. This is the
only place `A.IsHermitian` is used in this file; everything else is Cauchy–Schwarz. -/
lemma Matrix.IsHermitian.inner_onVec_comm {A : Matrix d d ℂ} (hA : A.IsHermitian)
    (v w : EuclideanSpace ℂ d) :
    inner ℂ v (A.onVec w) = inner ℂ (A.onVec v) w := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', Matrix.onVec_apply, Finset.mul_sum,
    Finset.sum_mul, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hij : (starRingEnd ℂ) (A i j) = A j i := by
    have := congrFun (congrFun hA.eq j) i
    simpa [Matrix.conjTranspose_apply] using this
  rw [hij]
  ring

/-- Expectation value of a matrix `A` on the pure state `ψ`: `⟨ψ, A ψ⟩`. -/
def Ket.expValC (ψ : Ket d) (A : Matrix d d ℂ) : ℂ :=
  inner ℂ ψ.toEuclideanSpace (A.onVec ψ.toEuclideanSpace)

/-- The expectation value of a Hermitian matrix on a pure state is real: it equals its own
conjugate. -/
lemma Ket.expValC_conj {ψ : Ket d} {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    (starRingEnd ℂ) (ψ.expValC A) = ψ.expValC A := by
  unfold Ket.expValC
  rw [inner_conj_symm, hA.inner_onVec_comm]

/-- Expectation value of a Hermitian matrix `A` on the pure state `ψ`, as a real number. -/
def Ket.expVal (ψ : Ket d) (A : Matrix d d ℂ) : ℝ :=
  (ψ.expValC A).re

lemma Ket.expValC_eq_ofReal_expVal {ψ : Ket d} {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    ψ.expValC A = (ψ.expVal A : ℂ) := by
  have h := ψ.expValC_conj hA
  have him : (ψ.expValC A).im = 0 := by
    have h2 := congrArg Complex.im h
    simp only [Complex.conj_im] at h2
    linarith
  apply Complex.ext
  · simp [Ket.expVal]
  · simp [him]

/-- The variance of a Hermitian observable `A` on the pure state `ψ`. -/
def Ket.variance (ψ : Ket d) (A : Matrix d d ℂ) : ℝ :=
  ψ.expVal (A * A) - ψ.expVal A ^ 2

/-- The centered vector `A ψ - ⟨A⟩ ψ`, whose squared norm is the variance of `A` on `ψ`
(`Ket.norm_centered_sq`, below). -/
def Ket.centered (ψ : Ket d) (A : Matrix d d ℂ) : EuclideanSpace ℂ d :=
  A.onVec ψ.toEuclideanSpace - (ψ.expVal A : ℂ) • ψ.toEuclideanSpace

/-- The cross term `⟨A⟩ = ⟪ψ, A ψ⟫ = ⟪A ψ, ψ⟫` for a Hermitian `A`, in both orders. -/
lemma Ket.inner_onVec_self {ψ : Ket d} {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    inner ℂ ψ.toEuclideanSpace (A.onVec ψ.toEuclideanSpace) = (ψ.expVal A : ℂ) ∧
      inner ℂ (A.onVec ψ.toEuclideanSpace) ψ.toEuclideanSpace = (ψ.expVal A : ℂ) := by
  have h1 : inner ℂ ψ.toEuclideanSpace (A.onVec ψ.toEuclideanSpace) = (ψ.expVal A : ℂ) :=
    ψ.expValC_eq_ofReal_expVal hA
  refine ⟨h1, ?_⟩
  rw [← hA.inner_onVec_comm, h1]

lemma Ket.norm_centered_sq {ψ : Ket d} {A : Matrix d d ℂ} (hA : A.IsHermitian) :
    ‖ψ.centered A‖ ^ 2 = ψ.variance A := by
  have hAA : ψ.expValC (A * A) =
      inner ℂ (A.onVec ψ.toEuclideanSpace) (A.onVec ψ.toEuclideanSpace) := by
    show inner ℂ ψ.toEuclideanSpace ((A * A).onVec ψ.toEuclideanSpace) = _
    rw [Matrix.onVec_mul]
    exact hA.inner_onVec_comm _ _
  obtain ⟨hcross, hcross'⟩ := ψ.inner_onVec_self hA
  have hone := ψ.inner_self_toEuclideanSpace
  have hexpand : (inner ℂ (ψ.centered A) (ψ.centered A) : ℂ) = ψ.expValC (A * A) -
      (ψ.expVal A : ℂ) * (ψ.expVal A : ℂ) := by
    unfold Ket.centered
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, ← hAA, hcross, hcross', hone]
    ring
  have hre : ‖ψ.centered A‖ ^ 2 = (inner ℂ (ψ.centered A) (ψ.centered A) : ℂ).re :=
    (inner_self_eq_norm_sq (𝕜 := ℂ) (ψ.centered A)).symm
  have hre2 : (ψ.expValC (A * A) - (ψ.expVal A : ℂ) * (ψ.expVal A : ℂ)).re =
      ψ.expVal (A * A) - ψ.expVal A ^ 2 := by
    rw [Complex.sub_re, ← Complex.ofReal_mul, Complex.ofReal_re]
    show ψ.expVal (A * A) - ψ.expVal A * ψ.expVal A = ψ.expVal (A * A) - ψ.expVal A ^ 2
    ring
  rw [hre, hexpand, hre2]
  rfl

/-! ## B. Robertson's uncertainty relation -/

private lemma Ket.inner_centered_centered {ψ : Ket d} {G O : Matrix d d ℂ}
    (hG : G.IsHermitian) (hO : O.IsHermitian) :
    (inner ℂ (ψ.centered G) (ψ.centered O) : ℂ) =
      ψ.expValC (G * O) - (ψ.expVal G : ℂ) * (ψ.expVal O : ℂ) := by
  have hGO : ψ.expValC (G * O) =
      inner ℂ (G.onVec ψ.toEuclideanSpace) (O.onVec ψ.toEuclideanSpace) := by
    show inner ℂ ψ.toEuclideanSpace ((G * O).onVec ψ.toEuclideanSpace) = _
    rw [Matrix.onVec_mul]
    exact hG.inner_onVec_comm _ _
  obtain ⟨hGψψ, hGψ⟩ := ψ.inner_onVec_self hG
  obtain ⟨hOψψ, hOψ⟩ := ψ.inner_onVec_self hO
  have hone := ψ.inner_self_toEuclideanSpace
  unfold Ket.centered
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, ← hGO, hGψ, hOψψ, hone]
  ring

/-- **Robertson's uncertainty relation**, for two Hermitian matrices on a finite-dimensional
pure state: the product of variances dominates a quarter of the squared expectation of the
commutator. This is the standard 1929 inequality (H. P. Robertson, *The Uncertainty Principle*,
Phys. Rev. 34, 163–166), specialized here to finite dimension. -/
theorem robertson_uncertainty {ψ : Ket d} {G O : Matrix d d ℂ}
    (hG : G.IsHermitian) (hO : O.IsHermitian) :
    (ψ.expVal (Complex.I • (G * O - O * G))) ^ 2 / 4 ≤ ψ.variance G * ψ.variance O := by
  have hCS : ‖(inner ℂ (ψ.centered G) (ψ.centered O) : ℂ)‖ ≤
      ‖ψ.centered G‖ * ‖ψ.centered O‖ := norm_inner_le_norm _ _
  have hprodsq : (‖ψ.centered G‖ * ‖ψ.centered O‖) ^ 2 = ψ.variance G * ψ.variance O := by
    rw [mul_pow, ψ.norm_centered_sq hG, ψ.norm_centered_sq hO]
  have hcomm_herm : (Complex.I • (G * O - O * G)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hG.eq, hO.eq, Complex.star_def, Complex.conj_I]
    module
  have hantisym : ψ.expValC (G * O) - ψ.expValC (O * G) =
      (inner ℂ (ψ.centered G) (ψ.centered O) : ℂ) -
        (starRingEnd ℂ) (inner ℂ (ψ.centered G) (ψ.centered O) : ℂ) := by
    have h1 := ψ.inner_centered_centered hG hO
    have h2 := ψ.inner_centered_centered hO hG
    have hOG' : inner ℂ (ψ.centered O) (ψ.centered G) =
        (starRingEnd ℂ) (inner ℂ (ψ.centered G) (ψ.centered O) : ℂ) :=
      (inner_conj_symm (ψ.centered O) (ψ.centered G)).symm
    rw [hOG'] at h2
    rw [h2, h1]
    ring
  have hcommC : ψ.expValC (Complex.I • (G * O - O * G)) =
      Complex.I * (ψ.expValC (G * O) - ψ.expValC (O * G)) := by
    show inner ℂ ψ.toEuclideanSpace ((Complex.I • (G * O - O * G)).onVec ψ.toEuclideanSpace) = _
    have hlin : (Complex.I • (G * O - O * G)).onVec ψ.toEuclideanSpace =
        Complex.I • ((G * O - O * G).onVec ψ.toEuclideanSpace) := Matrix.onVec_smul _ _ _
    rw [hlin, inner_smul_right, Matrix.onVec_sub, inner_sub_right]
    unfold Ket.expValC
    ring
  have hCreal := ψ.expValC_eq_ofReal_expVal hcomm_herm
  set z : ℂ := inner ℂ (ψ.centered G) (ψ.centered O) with hz
  have him : z - (starRingEnd ℂ) z = 2 * Complex.I * z.im := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im]; ring
  have hCz : (ψ.expVal (Complex.I • (G * O - O * G)) : ℂ) = -2 * z.im := by
    rw [← hCreal, hcommC, hantisym, him]
    have : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
    ring_nf
    rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [sq]; exact this]
    ring
  have hCz' : ψ.expVal (Complex.I • (G * O - O * G)) = -2 * z.im := by
    exact_mod_cast hCz
  have hnormsq : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
    rw [sq, Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
  have hzim : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [hnormsq, sq]
    nlinarith [sq_nonneg z.re]
  have hfinal : (ψ.expVal (Complex.I • (G * O - O * G))) ^ 2 / 4 ≤ ‖z‖ ^ 2 := by
    rw [hCz']
    nlinarith [hzim]
  calc (ψ.expVal (Complex.I • (G * O - O * G))) ^ 2 / 4
      ≤ ‖z‖ ^ 2 := hfinal
    _ ≤ (‖ψ.centered G‖ * ‖ψ.centered O‖) ^ 2 := by
        gcongr
    _ = ψ.variance G * ψ.variance O := hprodsq

/-! ## C. The quantum Cramér–Rao bound -/

/-- **The quantum Cramér–Rao bound**, pure states, unitary parametrization (Helstrom 1976, Chap.
VIII.4; Braunstein–Caves, Phys. Rev. Lett. 72, 3439 (1994), Eqs. (32)–(33), pure-state case). For
a family `ψ_θ = e^{-iθG}ψ` and an
observable `O` normalized to `∂_θ⟨O⟩_θ|_{θ=0} = 1` — the standard normalization of a locally
unbiased estimator, taken here as an explicit hypothesis rather than derived from the dynamics
of the family — the variance of `O` is at least the inverse of the quantum Fisher information
`4 · Var_ψ(G)`. -/
theorem cramerRao_pureState_unitary {ψ : Ket d} {G O : Matrix d d ℂ}
    (hG : G.IsHermitian) (hO : O.IsHermitian)
    (hnorm : ψ.expVal (Complex.I • (G * O - O * G)) = 1) :
    1 / (4 * ψ.variance G) ≤ ψ.variance O := by
  have hR := robertson_uncertainty (ψ := ψ) hG hO
  rw [hnorm] at hR
  have hGpos : 0 < ψ.variance G := by
    rcases lt_or_eq_of_le (by rw [← ψ.norm_centered_sq hG]; positivity : (0:ℝ) ≤ ψ.variance G)
      with h | h
    · exact h
    · exfalso; rw [← h] at hR; norm_num at hR
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hR]

end
