/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Rpow
public import QuantumInfo.ForMathlib.Majorization

@[expose] public section

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
variable [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {x q r : ℝ}

/-! # Schatten norms

-/

noncomputable section

/--
The Schatten p-norm of a matrix A is (Tr[(A*A)^(p/2)])^(1/p).
-/
noncomputable def schattenNorm (A : Matrix d d ℂ) (p : ℝ) : ℝ :=
  RCLike.re ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).cfc (· ^ (p/2))).trace ^ (1/p)

/-
For a positive Hermitian matrix A, ||A||_p = (Tr(A^p))^(1/p).
-/
theorem schattenNorm_hermitian_pow {A : HermitianMat d ℂ} (hA : 0 ≤ A) {p : ℝ} (hp : 0 < p) :
    schattenNorm A.mat p = (A ^ p).trace ^ (1/p) := by
  unfold schattenNorm
  rw [HermitianMat.rpow_eq_cfc, ← A.cfc_sq_rpow_eq_cfc_rpow hA p hp.le,
    HermitianMat.trace_eq_re_trace, HermitianMat.mat_cfc]
  simp only [← Matrix.IsHermitian.cfc_eq, HermitianMat.conjTranspose_mat,
    HermitianMat.mat_pow, pow_two]

lemma schattenNorm_nonneg (A : Matrix d d ℂ) (p : ℝ) :
    0 ≤ schattenNorm A p := by
  refine Real.rpow_nonneg ?_ _
  simp [Matrix.IsHermitian.cfc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  exact Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i) _

lemma schattenNorm_pow_eq
  (A : HermitianMat d ℂ) (hA : 0 ≤ A) (p k : ℝ) (hp : 0 < p) (hk : 0 < k) :
    schattenNorm (A ^ k).mat p = (schattenNorm A.mat (k * p)) ^ k := by
  rw [schattenNorm_hermitian_pow (HermitianMat.rpow_nonneg hA) hp,
    schattenNorm_hermitian_pow hA (by positivity), ← HermitianMat.rpow_mul hA, mul_comm k p,
    ← Real.rpow_mul (HermitianMat.trace_nonneg (HermitianMat.rpow_nonneg hA)),
    ← div_div, div_mul_cancel₀ _ hk.ne']

lemma trace_eq_schattenNorm_rpow
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (r : ℝ) (hr : 0 < r) :
    (A ^ r).trace = (schattenNorm A.mat r) ^ r := by
  rw [schattenNorm_hermitian_pow hA hr,
    ← Real.rpow_mul (HermitianMat.trace_nonneg (HermitianMat.rpow_nonneg hA)),
    one_div_mul_cancel hr.ne', Real.rpow_one]

/-! ## Relating schattenNorm to singular values -/

/- The trace of cfc(A†A, t ↦ t^{p/2}) expressed as a sum of eigenvalues. -/
lemma schattenNorm_trace_as_eigenvalue_sum (A : Matrix d d ℂ) (p : ℝ) :
    RCLike.re ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).cfc (· ^ (p/2))).trace =
    ∑ i : d, ((Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i) ^ (p/2) := by
  simp [Matrix.IsHermitian.cfc, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-
The Schatten p-norm raised to the p-th power equals the sum of singular values
    raised to the p-th power: `‖A‖_p^p = ∑ σᵢ(A)^p`.
-/
lemma schattenNorm_rpow_eq_sum_singularValues (A : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p ^ p = ∑ i : d, singularValues A i ^ p := by
  have h0 : ∀ i, 0 ≤ (Matrix.isHermitian_mul_conjTranspose_self A.conjTranspose).eigenvalues i :=
    fun i => by simpa using Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i
  unfold schattenNorm singularValues
  rw [schattenNorm_trace_as_eigenvalue_sum,
    ← Real.rpow_mul (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (h0 i) (p / 2)),
    one_div_mul_cancel hp.ne', Real.rpow_one]
  exact Finset.sum_congr rfl fun i _ => Real.rpow_div_two_eq_sqrt p (h0 i)

/- The Schatten p-norm equals the ℓ^p quasi-norm of the singular values:
    `‖A‖_p = (∑ σᵢ(A)^p)^{1/p}`. -/
lemma schattenNorm_eq_sum_singularValues_rpow (A : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p = (∑ i : d, singularValues A i ^ p) ^ (1/p) := by
  rw [← schattenNorm_rpow_eq_sum_singularValues A hp,
    ← Real.rpow_mul (schattenNorm_nonneg A p), mul_one_div_cancel hp.ne', Real.rpow_one]

/-- `‖A‖_p^p` equals the same sum over sorted singular values. -/
lemma schattenNorm_rpow_eq_sum_sorted (A : Matrix d d ℂ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p ^ p =
    ∑ i : Fin (Fintype.card d), singularValuesSorted A i ^ p := by
  rw [schattenNorm_rpow_eq_sum_singularValues A hp, sum_singularValues_rpow_eq_sum_sorted A p]

open InnerProductSpace in
/--
Scalar trace Young inequality for PSD matrices:
⟪A, B⟫ ≤ Tr[A^p]/p + Tr[B^q]/q for PSD A, B and conjugate p, q > 1.
-/
lemma HermitianMat.trace_young
    (A B : HermitianMat d ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ⟪A, B⟫_ℝ ≤ (A ^ p).trace / p + (B ^ q).trace / q := by
  rw [trace_rpow_eq_sum, trace_rpow_eq_sum, inner_eq_doubly_stochastic_sum]
  set C := A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val with hC
  have hCU : C * C.conjTranspose = 1 ∧ C.conjTranspose * C = 1 := by
    constructor <;>
      simp [hC, Matrix.mul_assoc] <;>
      simp [← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary]
  calc ∑ i, ∑ j, A.H.eigenvalues i * B.H.eigenvalues j * ‖C i j‖ ^ 2
      ≤ ∑ i, ∑ j, (A.H.eigenvalues i ^ p / p + B.H.eigenvalues j ^ q / q) * ‖C i j‖ ^ 2 := by
        gcongr with i _ j _
        exact Real.young_inequality_of_nonneg ((zero_le_iff.mp hA).eigenvalues_nonneg i)
          ((zero_le_iff.mp hB).eigenvalues_nonneg j)
          (Real.holderConjugate_iff.mpr ⟨hp, by simpa using hpq⟩)
    _ = (∑ i, A.H.eigenvalues i ^ p) / p + (∑ i, B.H.eigenvalues i ^ q) / q := by
        simp only [add_mul, Finset.sum_add_distrib, ← Finset.mul_sum,
          Matrix.unitary_row_sum_norm_sq C hCU.1, mul_one, Finset.sum_div]
        congr 1
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, Matrix.unitary_col_sum_norm_sq C hCU.2, mul_one]

/-- For PSD `A` and Hermitian `B`, the product
`C = A^{1/2} * B` satisfies `C^* C = (A.conj B.mat).mat = B * A * B`. -/
lemma conjTranspose_half_mul_eq_conj
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) :
    ((A ^ (1/2 : ℝ)).mat * B.mat).conjTranspose * ((A ^ (1/2 : ℝ)).mat * B.mat)
    = (A.conj B.mat).mat := by
  simp only [Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat,
    HermitianMat.conj_apply_mat, Matrix.mul_assoc, ← HermitianMat.pow_half_mul hA]

lemma schattenNorm_half_mul_rpow_eq_trace_conj
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A)
    {α : ℝ} (hα : 0 < α) :
    (schattenNorm ((A ^ (1/2 : ℝ)).mat * B.mat) (2 * α)) ^ (2 * α) =
    ((A.conj B.mat) ^ α).trace := by
  unfold schattenNorm
  rw [← Matrix.IsHermitian.cfc_eq, Matrix.conjTranspose_conjTranspose,
    conjTranspose_half_mul_eq_conj hA, mul_div_cancel_left₀ α two_ne_zero,
    ← HermitianMat.mat_cfc, ← HermitianMat.rpow_eq_cfc, ← HermitianMat.trace_eq_re_trace,
    ← Real.rpow_mul (HermitianMat.trace_nonneg
      (HermitianMat.rpow_nonneg (A.conj_nonneg B.mat hA))),
    one_div_mul_cancel (by positivity : (2 * α : ℝ) ≠ 0), Real.rpow_one]

/-!
## Schatten–Hölder inequality

The *Schatten–Hölder inequality* for matrix products:
For matrices `A`, `B` and exponents `r, p, q > 0` with `1/r = 1/p + 1/q`,
the Schatten `r`-norm of the product satisfies
  `‖A * B‖_{S^r} ≤ ‖A‖_{S^p} * ‖B‖_{S^q}`.
This version includes the quasi-norm case (r, p, q < 1).

### Proof sketch

The proof proceeds in three steps:
1. Express Schatten norms in terms of singular values:
   `‖A‖_p = (∑ σᵢ(A)^p)^{1/p}`.
2. Use the **weak log-majorization** of singular values of products
   (`weakLogMaj_singularValues_mul` + `sum_rpow_le_of_weakLogMaj`) to obtain
   `∑ σᵢ(AB)^r ≤ ∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r`.
3. Apply the **classical Hölder inequality** for finite sums
   (`NNReal.inner_le_Lp_mul_Lq` from Mathlib, with conjugate exponents
   `p/r` and `q/r`) to bound
   `∑ σ↓ᵢ(A)^r · σ↓ᵢ(B)^r ≤ (∑ σᵢ(A)^p)^{r/p} · (∑ σᵢ(B)^q)^{r/q}`.
4. Take `1/r`-th powers and combine.
-/
lemma schattenNorm_mul_le (A B : Matrix d d ℂ) {r p q : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hq : 0 < q) (hpqr : 1 / r = 1 / p + 1 / q) :
    schattenNorm (A * B) r ≤ schattenNorm A p * schattenNorm B q := by
  have hS : ∀ (C : Matrix d d ℂ) (s : ℝ), 0 ≤ ∑ i, singularValuesSorted C i ^ s := fun C s =>
    Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValuesSorted_nonneg C i) s
  rw [schattenNorm_eq_sum_singularValues_rpow (A * B) hr,
    schattenNorm_eq_sum_singularValues_rpow A hp, schattenNorm_eq_sum_singularValues_rpow B hq,
    sum_singularValues_rpow_eq_sum_sorted (A * B) r, sum_singularValues_rpow_eq_sum_sorted A p,
    sum_singularValues_rpow_eq_sum_sorted B q]
  calc (∑ i, singularValuesSorted (A * B) i ^ r) ^ (1/r)
      ≤ ((∑ i, singularValuesSorted A i ^ p) ^ (r / p) *
          (∑ i, singularValuesSorted B i ^ q) ^ (r / q)) ^ (1/r) :=
        Real.rpow_le_rpow (hS _ _) ((sum_rpow_singularValues_mul_le A B hr).trans
          (holder_step_for_singularValues A B hr hp hq hpqr)) (by positivity)
    _ = _ := by
        rw [Real.mul_rpow (Real.rpow_nonneg (hS A p) _) (Real.rpow_nonneg (hS B q) _)]
        congr 1 <;> rw [← Real.rpow_mul (hS _ _)] <;> congr 1 <;> field_simp

lemma HermitianMat.trace_rpow_conj_le
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    {α p q : ℝ} (hα : 0 < α) (hp : 0 < p) (hq : 0 < q)
    (hpq : 1 / (2 * α) = 1 / p + 1 / q) :
    ((A.conj B.mat) ^ α).trace ≤
    (((A ^ (p / 2)).trace) ^ (1 / p) * ((B ^ q).trace) ^ (1 / q)) ^ (2 * α) := by
  rw [← schattenNorm_half_mul_rpow_eq_trace_conj hA hα, show (p / 2 : ℝ) = 1/2 * p by ring,
    rpow_mul hA, ← schattenNorm_hermitian_pow (rpow_nonneg hA) hp,
    ← schattenNorm_hermitian_pow hB hq]
  exact Real.rpow_le_rpow (schattenNorm_nonneg _ _)
    (schattenNorm_mul_le _ _ (by positivity) hp hq hpq) (by positivity)
