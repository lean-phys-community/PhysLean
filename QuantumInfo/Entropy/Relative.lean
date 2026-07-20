/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Entropy.VonNeumann
public import Physlib.Meta.Sorry

@[expose] public section

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ} {ρ σ : MState d}

open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace HermitianMat

/-!
To do relative entropies, we start with the _sandwiched Renyi Relative Entropy_ which is a nice general form.
Then instead of proving many theorems (like DPI, relabelling, additivity, etc.) several times, we just prove
it for this one quantity, then it follows for other quantities (like the relative entropy) as a special case.
-/

--Note: without the assumption `h`, we could still get nonnegativity, just not strict positivity.
private theorem sandwiched_trace_pos (h : σ.M.ker ≤ ρ.M.ker) :
    0 < ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace := by
  apply HermitianMat.trace_pos
  apply HermitianMat.rpow_pos
  apply HermitianMat.conj_pos ρ.pos
  grw [← h]
  exact HermitianMat.ker_rpow_le_of_nonneg σ.nonneg

--TODO: We don't actually use this, and it's not clear that it's useful (since it's just a
-- specialization); remove?
omit [DecidableEq d] in
/--
Weighted Jensen inequality: for weights w_j ≥ 0 with ∑ w_j = 1, values b_j ≥ 0,
and q ≥ 1: (∑_j w_j * b_j)^q ≤ ∑_j w_j * b_j^q.

This is the special case of `Real.rpow_arith_mean_le_arith_mean_rpow` applied to
`Finset.univ`
-/
lemma weighted_jensen_rpow (b w : d → ℝ) (q : ℝ)
  (hb : ∀ j, 0 ≤ b j) (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) (hq : 1 ≤ q) :
    (∑ j, w j * b j) ^ q ≤ ∑ j, w j * b j ^ q :=
  Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ _ _ (fun i _ ↦ hw i) hsum (fun i _ ↦ hb i) hq

omit [DecidableEq d] in
/--
Doubly stochastic Hölder inequality: for nonneg a, b, doubly stochastic w,
and conjugate p, q > 1:
∑_{ij} a_i * b_j * w_{ij} ≤ (∑ a_i^p)^{1/p} * (∑ b_j^q)^{1/q}.
-/
lemma doubly_stochastic_holder (a b : d → ℝ) (w : d → d → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hw : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j, w i j = 1) (hcol : ∀ j, ∑ i, w i j = 1)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ∑ i, ∑ j, a i * b j * w i j ≤ (∑ i, a i ^ p) ^ (1/p) * (∑ j, b j ^ q) ^ (1/q) := by
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := one_div_pos.mp (by linarith [(div_lt_one hp0).mpr hp])
  have hq1 : 1 ≤ q := (div_le_one hq0).mp (by linarith [one_div_pos.mpr hp0])
  have hs : ∀ i, 0 ≤ ∑ j, w i j * b j :=
    fun i => Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (hb j)
  calc ∑ i, ∑ j, a i * b j * w i j
      = ∑ i, a i * ∑ j, w i j * b j := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ ≤ (∑ i, |a i| ^ p) ^ (1/p) * (∑ i, |∑ j, w i j * b j| ^ q) ^ (1/q) :=
        Real.inner_le_Lp_mul_Lq Finset.univ a _ ⟨by simpa [one_div] using hpq, hp0, hq0⟩
    _ ≤ (∑ i, a i ^ p) ^ (1/p) * (∑ j, b j ^ q) ^ (1/q) := by
        have h3 : ∑ i, (∑ j, w i j * b j) ^ q ≤ ∑ j, b j ^ q := by
          calc ∑ i, (∑ j, w i j * b j) ^ q
              ≤ ∑ i, ∑ j, w i j * b j ^ q :=
                Finset.sum_le_sum fun i _ => weighted_jensen_rpow b (w i) q hb (hw i) (hrow i) hq1
            _ = ∑ j, b j ^ q := by
                rw [Finset.sum_comm]
                simp_rw [← Finset.sum_mul]
                simp [hcol]
        simp_rw [fun i => abs_of_nonneg (ha i), fun i => abs_of_nonneg (hs i)]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hs i) q) h3
            (by positivity))
          (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (ha i) p) _)

--PULLOUT
/--
Hermitian trace Hölder inequality: for PSD A, B and conjugate exponents p, q > 1,
⟪A, B⟫ ≤ Tr[A^p]^(1/p) * Tr[B^q]^(1/q).
-/
lemma HermitianMat.inner_le_trace_rpow_mul
    {A B : HermitianMat d ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (p q : ℝ) (hp : 1 < p) (hpq : 1/p + 1/q = 1) :
    ⟪A, B⟫_ℝ ≤ (A ^ p).trace ^ (1/p) * (B ^ q).trace ^ (1/q) := by
  by_cases hq : q > 1;
  · -- Apply the doubly_stochastic_holder lemma with the weights $w_{ij} = \|C_{ij}\|^2$.
    rw [trace_rpow_eq_sum, trace_rpow_eq_sum, inner_eq_doubly_stochastic_sum]
    refine doubly_stochastic_holder
      A.H.eigenvalues B.H.eigenvalues
      (fun i j ↦ ‖(A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val) i j‖ ^ 2)
      (fun i ↦ by simpa using hA.eigenvalues_nonneg i)
      (fun i ↦ by simpa using hB.eigenvalues_nonneg i)
      (by bound) ?_ ?_ p q hp hpq
    · apply Matrix.unitary_row_sum_norm_sq (A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val)
      simp [mul_assoc]
      simp [← mul_assoc, Matrix.IsHermitian.eigenvectorUnitary]
    · apply Matrix.unitary_col_sum_norm_sq (A.H.eigenvectorUnitary.val.conjTranspose * B.H.eigenvectorUnitary.val)
      simp [mul_assoc]
      simp [← mul_assoc, Matrix.IsHermitian.eigenvectorUnitary]
  · rcases eq_or_ne q 0 with _ | _
    · grind only [cases Or]
    · field_simp at hpq
      nlinarith

--PULLOUT
lemma MState.rpow_le_one' {r : ℝ} (hσ : 0 < r) : σ.M ^ r ≤ 1 := by
  obtain ⟨e, he⟩ := σ.M.cfc_eigenvalues (f := (· ^ r))
  refine ((σ.M ^ r).eigenvalues_le_imp_le_smul_one 1 fun i => ?_).trans_eq (one_smul _ _)
  rw [HermitianMat.rpow_eq_cfc, he]
  exact Real.rpow_le_one (σ.eigenvalue_nonneg _) (σ.eigenvalue_le_one _) hσ.le

--PULLOUT
/-- If A ≥ 0 and A ≤ 1, then each eigenvalue of A is in [0, 1]. -/
lemma HermitianMat.eigenvalues_le_one_of_le_one
    (A : HermitianMat d ℂ) (hA1 : A ≤ 1) (i : d) :
    A.H.eigenvalues i ≤ 1 :=
  A.le_smul_one_imp_eigenvalues_le 1 (by simpa using hA1) i

--PULLOUT
/-- For positive A ≤ 1 and p ≥ 1, `Tr[A^p] ≤ Tr[A]`.
-/
lemma HermitianMat.trace_rpow_le_trace_of_le_one
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (hA1 : A ≤ 1)
    (p : ℝ) (hp : 1 ≤ p) :
    (A ^ p).trace ≤ A.trace := by
  rw [HermitianMat.trace_rpow_eq_sum, ← A.sum_eigenvalues_eq_trace]
  exact Finset.sum_le_sum fun i _ => Real.rpow_le_self_of_le_one
    ((HermitianMat.zero_le_iff.mp hA).eigenvalues_nonneg i)
    (A.eigenvalues_le_one_of_le_one hA1 i) hp

private lemma trace_conj_rpow_eq_inner (hα₀ : 0 < α) (hα : α < 1) :
    ((ρ.M ^ α).conj (σ.M ^ ((1 - α) / (2 * α) * α)).mat).trace = ⟪ρ.M ^ α, σ.M ^ (1 - α)⟫_ℝ := by
  have h2 : (1 - α) / (2 * α) * α = (1 - α) / 2 := by field_simp
  have hs : (σ.M ^ ((1 - α) / 2)).mat * (σ.M ^ ((1 - α) / 2)).mat = (σ.M ^ (1 - α)).mat := by
    rw [← HermitianMat.mat_rpow_add σ.nonneg (by linarith)]
    norm_num
  rw [h2, HermitianMat.inner_eq_re_trace, HermitianMat.trace_eq_re_trace,
    HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, hs, Matrix.trace_mul_comm]

private lemma inner_rpow_le_one (hα₀ : 0 < α) (hα : α < 1) :
    ⟪ρ.M ^ α, σ.M ^ (1 - α)⟫_ℝ ≤ 1 := by
  convert HermitianMat.inner_le_trace_rpow_mul
      (HermitianMat.rpow_nonneg ρ.nonneg) (HermitianMat.rpow_nonneg σ.nonneg)
      (1 / α) (1 / (1 - α)) _ _ using 1
  · rw [← HermitianMat.rpow_mul ρ.nonneg, ← HermitianMat.rpow_mul σ.nonneg]
    simp [hα₀.ne', (sub_pos.mpr hα).ne']
  · field_simp
    exact hα
  · simp

private theorem sandwiched_trace_of_lt_1 (hα₀ : 0 < α) (hα : α < 1) :
    ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace ≤ 1 := by
    have h1α : 0 < 1 - α := sub_pos.mpr hα
    -- Apply trace_rpow_conj_le with p = 2 and q = 2α/(1-α)
    set t := (1 - α) / (2 * α) with ht_def
    have ht_pos : 0 < t := by positivity
    have hp : (0 : ℝ) < 2 := by positivity
    have hq : (0 : ℝ) < 2 * α / (1 - α) := by positivity
    have hpq : 1 / (2 * α) = 1 / 2 + 1 / (2 * α / (1 - α)) := by
      field_simp
      ring
    calc ((ρ.M.conj (σ.M ^ t).mat) ^ α).trace
        ≤ (((ρ.M ^ (2 / 2)).trace) ^ (1 / 2) *
          (((σ.M ^ t) ^ (2 * α / (1 - α))).trace) ^ (1 / (2 * α / (1 - α)))) ^ (2 * α) :=
          HermitianMat.trace_rpow_conj_le ρ.nonneg (HermitianMat.rpow_nonneg σ.nonneg) hα₀ hp hq hpq
      _ = 1 := by
          -- Simplify: ρ.M ^ (2/2) = ρ.M ^ 1 = ρ.M, Tr[ρ.M] = 1
          -- (σ.M ^ t) ^ (2α/(1-α)) = σ.M ^ (t * 2α/(1-α)) = σ.M ^ 1, Tr[σ.M] = 1
          have h1 : (2 : ℝ) / 2 = 1 := by norm_num
          have h2 : t * (2 * α / (1 - α)) = 1 := by
            rw [ht_def]; field_simp
          rw [h1, HermitianMat.rpow_one,
              ← HermitianMat.rpow_mul σ.nonneg, h2, HermitianMat.rpow_one,
              ρ.tr, σ.tr]
          simp

/-- For PSD A and p ≠ 0, `A^{-p} * A^p = HermitianMat.supportProj A`. -/
lemma HermitianMat.rpow_neg_mul_rpow_eq_supportProj
    {A : HermitianMat d ℂ} (hA : 0 ≤ A) {p : ℝ} (hp : p ≠ 0) :
    (A ^ (-p)).mat * (A ^ p).mat = A.supportProj.mat := by
  rw [HermitianMat.supportProj_eq_cfc, HermitianMat.rpow_eq_cfc, HermitianMat.rpow_eq_cfc,
    ← HermitianMat.mat_cfc_mul_apply]
  exact congrArg _ (A.cfc_congr_of_nonneg hA fun x hx => by
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with rfl | h
    · simp [hp]
    · simp [← Real.rpow_add h, h.ne'])

lemma HermitianMat.supportProj_mul_self (A : HermitianMat d ℂ) :
    A.supportProj.mat * A.mat = A.mat := by
  have h : (A.cfc fun x => (if x = 0 then (0:ℝ) else 1) * x).mat = A.mat :=
    congrArg _ ((A.cfc_congr fun x _ => by by_cases hx : x = 0 <;> simp [hx]).trans A.cfc_id')
  rw [HermitianMat.mat_cfc_mul_apply, HermitianMat.cfc_id'] at h
  rwa [HermitianMat.supportProj_eq_cfc]

lemma HermitianMat.inner_supportProj_self (A : HermitianMat d ℂ) :
    ⟪A, A.supportProj⟫ = A.trace := by
  rw [HermitianMat.inner_eq_re_trace, Matrix.trace_mul_comm, HermitianMat.supportProj_mul_self,
    HermitianMat.trace_eq_re_trace]

lemma HermitianMat.mul_supportProj_of_ker_le {A B : HermitianMat d ℂ}
  (h : LinearMap.ker B.lin.toLinearMap ≤ LinearMap.ker A.lin.toLinearMap) :
    A.mat * B.supportProj.mat = A.mat := by
  have hsupp : A.support ≤ B.support := by
    rw [← ker_orthogonal_eq_support, ← ker_orthogonal_eq_support]
    exact Submodule.orthogonal_le h
  have h0 : B.kerProj.mat * A.mat = 0 := by
    rw [Matrix.ext_iff_mulVec]
    intro v
    have hm : WithLp.toLp 2 (A.mat.mulVec v) ∈ B.kerProj.ker := by
      rw [kerProj_ker]
      exact hsupp ⟨WithLp.toLp 2 v, rfl⟩
    simpa [← Matrix.mulVec_mulVec] using (B.kerProj.mem_ker_iff_mulVec_zero _).mp hm
  have h0' : A.mat * B.kerProj.mat = 0 := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose h0
  rw [eq_sub_of_add_eq' B.kerProj_add_supportProj]
  simp [Matrix.mul_sub, h0']

lemma HermitianMat.inner_supportProj_of_ker_le {A B : HermitianMat d ℂ}
  (h : LinearMap.ker B.lin.toLinearMap ≤ LinearMap.ker A.lin.toLinearMap) :
    ⟪A, B.supportProj⟫ = A.trace := by
  rw [inner_def, mul_supportProj_of_ker_le h, trace]

lemma supportProj_inner_density (h : σ.M.ker ≤ ρ.M.ker) :
    ⟪σ.M.supportProj, ρ.M⟫_ℝ = 1 := by
  rw [HermitianMat.inner_comm, HermitianMat.inner_supportProj_of_ker_le h]
  simp

/-
⟪ρ.M.conj (σ.M ^ t).mat, σ.M ^ (-2 * t)⟫_ℝ = 1 for density matrices ρ, σ with ker(σ) ≤ ker(ρ).
-/
private lemma sandwiched_inner_eq_one (h : σ.M.ker ≤ ρ.M.ker) (t : ℝ) :
    ⟪ρ.M.conj (σ.M ^ t).mat, σ.M ^ (-2 * t)⟫_ℝ = 1 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp
  · have h_combine : (σ.M ^ (-2 * t)).mat * (σ.M ^ t).mat = (σ.M ^ (-t)).mat := by
      rw [show (-t : ℝ) = -2 * t + t by ring,
        HermitianMat.mat_rpow_add σ.nonneg fun hh => ht (by linarith)]
    have h_support : (σ.M ^ t).mat * (σ.M ^ (-t)).mat = σ.M.supportProj.mat := by
      simpa only [neg_neg] using
        σ.M.rpow_neg_mul_rpow_eq_supportProj σ.nonneg (neg_ne_zero.mpr ht)
    rw [HermitianMat.inner_def, HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat]
    rw [Matrix.trace_mul_comm, ← mul_assoc, ← mul_assoc, h_combine]
    rw [Matrix.trace_mul_cycle, h_support, ← HermitianMat.inner_def]
    exact supportProj_inner_density h

private theorem sandwiched_trace_of_gt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα : α > 1) :
    1 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace := by
  -- Let t = (1 - α) / (2 * α), A = ρ.M.conj (σ.M ^ t) and B = σ.M ^ (-2 * t)
  set t : ℝ := (1 - α) / (2 * α)
  set A := ρ.M.conj (σ.M ^ t).mat
  set B := σ.M ^ (-2 * t)
  have h_trace : ⟪A, B⟫ = 1 := sandwiched_inner_eq_one h t
  have h_inner : ⟪A, B⟫ ≤
      (A ^ α).trace ^ (1 / α) * (B ^ (α / (α - 1))).trace ^ (1 / (α / (α - 1))) :=
    HermitianMat.inner_le_trace_rpow_mul (by positivity) (HermitianMat.rpow_nonneg σ.nonneg)
      _ _ hα (by
        rw [div_div_eq_mul_div, div_add_div _ _ (by positivity) (by positivity),
          div_eq_iff (by positivity)]
        ring)
  have h_trace_B : (B ^ (α / (α - 1))).trace = 1 := by
    rw [← HermitianMat.rpow_mul σ.nonneg, show -2 * t * (α / (α - 1)) = 1 by
      rw [mul_div, div_eq_iff (by linarith only [hα])]
      linarith [mul_div_cancel₀ (1 - α) (by linarith : (2 * α) ≠ 0)]]
    simp
  have h_final : 1 ≤ (A ^ α).trace ^ (1 / α) := by
    simpa only [h_trace, one_div, h_trace_B, Real.one_rpow, mul_one] using h_inner
  have h0 : 0 ≤ (A ^ α).trace :=
    HermitianMat.trace_nonneg (HermitianMat.rpow_nonneg (by positivity))
  refine le_of_not_gt fun hlt => h_final.not_gt ?_
  simpa using Real.rpow_lt_one h0 hlt (by positivity)

private theorem sandwichedRelRentropy_nonneg_α_lt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα0 : 0 < α) (hα : α < 1) :
    0 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  apply div_nonneg_of_nonpos
  · apply Real.log_nonpos
    · exact (sandwiched_trace_pos h).le
    · exact sandwiched_trace_of_lt_1 hα0 hα
  · linarith

private theorem sandwichedRelRentropy_nonneg_α_gt_1 (h : σ.M.ker ≤ ρ.M.ker) (hα : α > 1) :
    0 ≤ ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  grw [← sandwiched_trace_of_gt_1 h hα]
  positivity
  positivity

private lemma sandwichedRelRentropy.trace_at_one (ρ σ : MState d) :
    ((ρ.M.conj (σ.M ^ ((1 - (1:ℝ)) / (2 * (1:ℝ)))).mat) ^ (1:ℝ)).trace = 1 := by
  simp

/-
For fixed PSD B, the derivative of α ↦ Tr[B^α] at α = 1 is ⟪B, B.log⟫ = Tr[B log B].
-/
private lemma hasDerivAt_trace_rpow_at_one (B : HermitianMat d ℂ) (hB : 0 ≤ B) :
    HasDerivAt (fun α : ℝ => (B ^ α).trace) ⟪B, B.log⟫ 1 := by
  have h_inner : ⟪B, B.log⟫ = ∑ i, (B.H.eigenvalues i) * Real.log (B.H.eigenvalues i) := by
    rw [HermitianMat.inner_eq_re_trace, show B.log = B.cfc Real.log from rfl, B.trace_mul_cfc]
    simp
  have h_deriv : ∀ i, HasDerivAt (fun α : ℝ => (B.H.eigenvalues i) ^ α)
      (B.H.eigenvalues i * Real.log (B.H.eigenvalues i)) 1 := fun i => by
    rcases eq_or_lt_of_le (show 0 ≤ B.H.eigenvalues i by simpa using hB.eigenvalues_nonneg i)
      with h0 | h0
    · simp only [← h0, Real.log_zero, mul_zero]
      exact (hasDerivAt_const _ _).congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
        (Ioi_mem_nhds zero_lt_one) fun x hx => Real.zero_rpow hx.out.ne')
    · simpa using (Real.hasStrictDerivAt_const_rpow h0 1).hasDerivAt
  rw [h_inner]
  simp only [HermitianMat.trace_rpow_eq_sum, ← Finset.sum_apply]
  exact HasDerivAt.sum fun i _ => h_deriv i

/-
PROBLEM
Trace cyclicity for conj: Tr[conj(σ^t, ρ)] = ⟪ρ, σ^{2t}⟫ = Tr[ρ σ^{2t}].
    Since σ^t is Hermitian: Tr[σ^t ρ σ^t] = Tr[ρ (σ^t)²] = Tr[ρ σ^{2t}].
PROVIDED SOLUTION
By definition, (ρ.M.conj (σ.M ^ t).mat).mat = (σ.M ^ t).mat * ρ.M.mat * ((σ.M ^ t).mat)^* (from conj_apply_mat). Since σ.M ^ t is Hermitian, ((σ.M ^ t).mat)^* = (σ.M ^ t).mat (from σ.M ^ t property .H). So the trace is Tr[(σ^t).mat * ρ.mat * (σ^t).mat].
By Matrix.trace_mul_comm applied to the product ((σ^t).mat * ρ.mat) and (σ^t).mat:
Tr[(σ^t).mat * ρ.mat * (σ^t).mat] = Tr[(σ^t).mat * (σ^t).mat * ρ.mat].
Now use mat_rpow_add with σ.nonneg and t + t = 2t (≠ 0 since t ≠ 0): (σ.M ^ (t+t)).mat = (σ.M ^ t).mat * (σ.M ^ t).mat. So the trace becomes Tr[(σ.M ^ (2*t)).mat * ρ.mat].
By inner_eq_trace_rc: ⟪ρ.M, σ.M ^ (2*t)⟫ = (ρ.M.mat * (σ.M ^ (2*t)).mat).trace.
By Matrix.trace_mul_comm: Tr[ρ.mat * (σ^{2t}).mat] = Tr[(σ^{2t}).mat * ρ.mat].
Combine: the conj trace = Tr[(σ^{2t}).mat * ρ.mat] = Tr[ρ.mat * (σ^{2t}).mat] = ⟪ρ, σ^{2t}⟫.
Note: show t + t = 2 * t by ring, and 2 * t ≠ 0 from ht using two_mul_ne_zero or similar.
-/
private lemma trace_conj_eq_inner_rpow {ρ σ : MState d} {t : ℝ} (ht : t ≠ 0) :
    (ρ.M.conj (σ.M ^ t).mat).trace = ⟪ρ.M, σ.M ^ (2 * t)⟫ := by
  have hs : (σ.M ^ t).mat * (σ.M ^ t).mat = (σ.M ^ (2 * t)).mat := by
    rw [two_mul, HermitianMat.mat_rpow_add σ.nonneg fun h => ht (by linarith)]
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.trace_eq_re_trace,
    HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, hs, Matrix.trace_mul_comm]

-- The weight of eigenvalue i in the inner product decomposition
private def eigenWeight (ρ σ : MState d) (i : d) : ℝ :=
  RCLike.re ((Matrix.vecMul (star (σ.M.H.eigenvectorBasis i : d → ℂ)) ρ.M.mat) ⬝ᵥ (σ.M.H.eigenvectorBasis i : d → ℂ))

private lemma inner_cfc_eq_sum_eigenWeight (ρ σ : MState d) (f : ℝ → ℝ) :
    ⟪ρ.M, σ.M.cfc f⟫ = ∑ i, f (σ.M.H.eigenvalues i) * eigenWeight ρ σ i := by
  rw [HermitianMat.inner_eq_re_trace, σ.M.cfc_toMat_eq_sum_smul_proj f, Matrix.mul_sum]
  simp only [Matrix.mul_smul, Matrix.trace_sum, Matrix.trace_smul, map_sum, RCLike.smul_re]
  refine Finset.sum_congr rfl fun i _ => congrArg _ (congrArg _ ?_)
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_single]
  simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply]
  rfl

private lemma eigenWeight_nonneg (ρ σ : MState d) (i : d) : 0 ≤ eigenWeight ρ σ i := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (HermitianMat.zero_le_iff.mp ρ.nonneg)).2
    (σ.M.H.eigenvectorBasis i)
  simpa [eigenWeight, Matrix.dotProduct_mulVec] using h.1

set_option backward.isDefEq.respectTransparency false in
private lemma eigenWeight_zero_of_eigenvalue_zero {i : d} (hσ : σ.M.ker ≤ ρ.M.ker)
  (hei : σ.M.H.eigenvalues i = 0) :
    eigenWeight ρ σ i = 0 := by
  have h1 : σ.M.mat.mulVec (σ.M.H.eigenvectorBasis i) = 0 := by
    simpa [hei] using σ.M.H.mulVec_eigenvectorBasis i
  have h0 : ρ.m.mulVec (σ.M.H.eigenvectorBasis i) = 0 :=
    congr(WithLp.ofLp $(hσ congr(WithLp.toLp 2 $h1)))
  simp [eigenWeight, ← Matrix.dotProduct_mulVec, h0]

/-
The derivative of u ↦ ⟪ρ, σ^u⟫ at u = 0 is ⟪ρ, σ.log⟫.
    Use inner_cfc_eq_sum_eigenWeight to write ⟪ρ, σ^u⟫ = ∑ i, q_i^u * eigenWeight ρ σ i,
    differentiate term by term using HasDerivAt.sum.
-/
set_option backward.isDefEq.respectTransparency false in
private lemma hasDerivAt_inner_rpow_at_zero (h : σ.M.ker ≤ ρ.M.ker) :
    HasDerivAt (fun u : ℝ => ⟪ρ.M, σ.M ^ u⟫) ⟪ρ.M, σ.M.log⟫ 0 := by
  have h_deriv : ∀ i, HasDerivAt (fun u : ℝ => σ.M.H.eigenvalues i ^ u * eigenWeight ρ σ i)
      (Real.log (σ.M.H.eigenvalues i) * eigenWeight ρ σ i) 0 := fun i => by
    rcases (σ.eigenvalue_nonneg i).lt_or_eq' with h_pos | h_zero
    · simpa using (Real.hasStrictDerivAt_const_rpow h_pos 0).hasDerivAt.mul_const _
    · simpa [eigenWeight_zero_of_eigenvalue_zero h h_zero] using hasDerivAt_const (0:ℝ) (0:ℝ)
  refine HasDerivAt.congr_of_eventuallyEq ?_ (Filter.Eventually.of_forall fun u =>
    inner_cfc_eq_sum_eigenWeight ρ σ (· ^ u))
  rw [show σ.M.log = σ.M.cfc Real.log from rfl, inner_cfc_eq_sum_eigenWeight]
  convert HasDerivAt.sum (u := Finset.univ) fun i _ => h_deriv i using 1
  exact (Finset.sum_fn _ _).symm

/-  The derivative of α ↦ Tr[ρ σ^((1-α)/α)] at α = 1 is -⟪ρ, log σ⟫.
    Uses trace cyclic: Tr[σ^t ρ σ^t] = Tr[ρ σ^(2t)].
    With 2t(α) = (1-α)/α, d/dα (2t) = -1/α², and d/dε σ^ε|_{ε=0} = log σ. -/
private lemma hasDerivAt_trace_conj_at_one {ρ σ : MState d}
    (h : σ.M.ker ≤ ρ.M.ker) :
    HasDerivAt
      (fun α : ℝ => ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat)).trace)
      (-⟪ρ.M, σ.M.log⟫)
      1 := by
  have h_chain : HasDerivAt (fun α : ℝ => ⟪ρ.M, σ.M ^ ((1 - α) / α)⟫) (⟪ρ.M, σ.M.log⟫ * (-1)) 1 := by
    apply HasDerivAt.comp (h₂ := fun u => ⟪ρ.M, σ.M ^ u⟫) (h := fun α => (1 - α) / α)
    · simpa using hasDerivAt_inner_rpow_at_zero h
    · simpa only [Pi.div_def, id_eq, mul_one, sub_self, sub_zero, one_pow, div_one] using
        ((hasDerivAt_id (1:ℝ)).const_sub 1).div (hasDerivAt_id 1) one_ne_zero
  ring_nf at h_chain
  apply h_chain.congr_of_eventuallyEq _
  filter_upwards [ lt_mem_nhds zero_lt_one ] with α hα
  by_cases h : ( 1 - α ) / ( 2 * α ) = 0
  · simp [ne_of_gt, hα] at h
    obtain ⟨⟩ : α = 1 := by linarith
    simp [*]
  · simp only [trace_conj_eq_inner_rpow h]
    ring_nf

/-
For a differentiable function b with b(1) = c ≥ 0 and b(α) ≥ 0 near α = 1,
the function α ↦ b(α)^α - b(α) has derivative c * log c at α = 1.
-/
private lemma scalar_rpow_cross_term {b : ℝ → ℝ} {c : ℝ}
    (hb : HasDerivAt b (deriv b 1) 1) (hc : b 1 = c) (hc_pos : 0 < c) :
    HasDerivAt (fun α => b α ^ α - b α) (c * Real.log c) 1 := by
  subst c
  have := (hb.rpow (hasDerivAt_id 1) hc_pos).sub hb
  simp_all only [hasDerivAt_deriv_iff, id_eq, mul_one, sub_self, Real.rpow_zero, Real.rpow_one,
    one_mul, add_sub_cancel_left]
  exact this

/-- For a PSD matrix A, Tr[A^s] - Tr[A] has derivative ⟪A, log A⟫ at s = 1.
    This generalizes `hasDerivAt_trace_rpow_at_one` to give the derivative of the
    difference Tr[A^s] - Tr[A], which equals ⟪A, log A⟫ since d/ds Tr[A] = 0. -/
private lemma hasDerivAt_trace_rpow_sub_trace (A : HermitianMat d ℂ) (hA : 0 ≤ A) :
    HasDerivAt (fun s : ℝ => (A ^ s).trace - A.trace) ⟪A, A.log⟫ 1 := by
  simpa using hasDerivAt_trace_rpow_at_one A hA

-- Abbreviation for the "B(α)" matrix appearing in the sandwiched trace.
private abbrev B_of (ρ σ : MState d) (α : ℝ) : HermitianMat d ℂ :=
  ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat

-- At α = 1, B(α) = ρ.M since (1-1)/(2·1) = 0 and conj by 1 is identity.
private lemma B_of_one (ρ σ : MState d) : B_of ρ σ 1 = ρ.M := by
  simp [B_of, HermitianMat.rpow_zero, HermitianMat.conj_one]

-- B(α) is nonneg for α > 0, because it's a conj of a nonneg matrix.
private lemma B_of_nonneg (ρ σ : MState d) (α : ℝ) : 0 ≤ B_of ρ σ α := by
  exact HermitianMat.conj_nonneg _ ρ.nonneg

-- The function g(M) = Tr[M^s] - Tr[M] satisfies g(M) = 0 when s = 1.
private lemma trace_rpow_sub_trace_at_one (M : HermitianMat d ℂ) :
    (M ^ (1 : ℝ)).trace - M.trace = 0 := by
  simp [HermitianMat.rpow_one]

-- The cross term function value at α = 1 is zero.
private lemma cross_term_at_one (ρ σ : MState d) :
    ((B_of ρ σ 1) ^ (1 : ℝ)).trace - (B_of ρ σ 1).trace
    - (ρ.M ^ (1 : ℝ)).trace + 1 = 0 := by
  simp [B_of_one, HermitianMat.rpow_one, ρ.tr]

/-
Scalar rpow cross term with just continuity: for a continuous function b with
  b(1) = c > 0, b(α) > 0 near 1, the function α ↦ b(α)^α - b(α) has derivative
  c * log c at α = 1. The key insight is that ∂/∂x(x^α - x)|_{α=1} = 0,
  so the derivative of b doesn't matter.
-/
private lemma scalar_rpow_cross_term_of_continuous {b : ℝ → ℝ} {c : ℝ}
    (hb_cont : ContinuousAt b 1) (hc : b 1 = c) (hc_pos : 0 < c)
    (hb_pos : ∀ᶠ α in nhds 1, 0 < b α) :
    HasDerivAt (fun α => b α ^ α - b α) (c * Real.log c) 1 := by
  rw [ hasDerivAt_iff_tendsto_slope_zero ];
  -- Use the fact that $b(1 + t)^{1 + t} - b(1 + t)$ can be rewritten as $b(1 + t) \cdot (b(1 + t)^t - 1)$.
  suffices h_rewrite : Filter.Tendsto (fun t => t⁻¹ * (b (1 + t) * (b (1 + t) ^ t - 1))) (nhdsWithin 0 {0}ᶜ) (nhds (c * Real.log c)) by
    refine' h_rewrite.congr' _;
    rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
    rw [ Metric.eventually_nhds_iff ] at *;
    obtain ⟨ ε, ε_pos, hε ⟩ := hb_pos; use ε, ε_pos; intros y hy hy'; rw [ Real.rpow_add ( hε ( show Dist.dist ( 1 + y ) 1 < ε from by simpa using hy ) ), Real.rpow_one ]
    ring_nf
    norm_num [ hc ]
  -- Use the fact that $b(1 + t) \to c$ as $t \to 0$.
  have h_b : Filter.Tendsto (fun t => b (1 + t)) (nhdsWithin 0 {0}ᶜ) (nhds c) := by
    exact hc ▸ hb_cont.tendsto.comp ( tendsto_nhdsWithin_of_tendsto_nhds ( by norm_num [ Filter.Tendsto ] ) );
  -- Use the fact that $b(1 + t)^t - 1 \sim t \log(b(1 + t))$ as $t \to 0$.
  have h_exp : Filter.Tendsto (fun t => t⁻¹ * (b (1 + t) ^ t - 1)) (nhdsWithin 0 {0}ᶜ) (nhds (Real.log c)) := by
    have h_exp : Filter.Tendsto (fun t => (b (1 + t) ^ t - 1) / t) (nhdsWithin 0 {0}ᶜ) (nhds (Real.log c)) := by
      have h_log : Filter.Tendsto (fun t => (Real.log (b (1 + t)) * t) / t) (nhdsWithin 0 {0}ᶜ) (nhds (Real.log c)) := by
        exact Filter.Tendsto.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with t ht using by rw [ mul_div_cancel_right₀ _ ht ] ) ( Filter.Tendsto.log h_b hc_pos.ne' )
      have h_exp : Filter.Tendsto (fun t => (Real.exp (Real.log (b (1 + t)) * t) - 1) / t) (nhdsWithin 0 {0}ᶜ) (nhds (Real.log c)) := by
        have h_exp : HasDerivAt (fun t => Real.exp (Real.log (b (1 + t)) * t)) (Real.log c) 0 := by
          have h_log : HasDerivAt (fun t => Real.log (b (1 + t)) * t) (Real.log c) 0 := by
            rw [ hasDerivAt_iff_tendsto_slope_zero ];
            simpa [ div_eq_inv_mul ] using h_log
          convert h_log.exp using 1 ; norm_num [ hc ];
        simpa [ div_eq_inv_mul ] using h_exp.tendsto_slope_zero;
      refine' h_exp.congr' _;
      filter_upwards [ h_b.eventually ( lt_mem_nhds hc_pos ) ] with t ht using by rw [ Real.rpow_def_of_pos ht, mul_comm ] ;
    simpa only [ div_eq_inv_mul ] using h_exp;
  convert h_b.mul h_exp using 2 ; ring

/-
Scalar rpow cross term for the zero case: for continuous b with b(1) = 0,
  0 ≤ b(α) near 1, the function α ↦ b(α)^α - b(α) has derivative 0 at α = 1.
  Uses the convention 0 * log 0 = 0.
-/
private lemma scalar_rpow_cross_term_of_continuous_zero {b : ℝ → ℝ}
    (hb_cont : ContinuousAt b 1) (hc : b 1 = 0)
    (hb_nonneg : ∀ᶠ α in nhds 1, 0 ≤ b α) :
    HasDerivAt (fun α => b α ^ α - b α) 0 1 := by
  -- Let's choose any $\epsilon > 0$.
  have h_eps : ∀ ε > 0, ∃ δ > 0, ∀ α, abs (α - 1) < δ → abs (b α ^ α - b α) ≤ ε * abs (α - 1) := by
    -- Use the fact that $|b(α)^α - b(α)| ≤ |h| · sqrt(b(α)) · |log b(α)|$ for $0 < b(α) ≤ 1$ and $|h| ≤ 1/2$.
    have h_bound : ∀ᶠ α in nhds 1, |b α ^ α - b α| ≤ |α - 1| * Real.sqrt (|b α|) * |Real.log (|b α|)| := by
      have h_bound : ∀ᶠ α in nhds 1, 0 ≤ b α ∧ b α ≤ 1 ∧ |α - 1| ≤ 1 / 2 → |b α ^ α - b α| ≤ |α - 1| * Real.sqrt (b α) * |Real.log (b α)| := by
        filter_upwards [ hb_nonneg ] with α hα₁ hα₂ ; rcases eq_or_lt_of_le hα₂.1 with hα₃ | hα₃ <;> simp_all [ Real.rpow_def_of_nonneg ] ; ring_nf ;
        · norm_num [ ← hα₃ ] at *;
          linarith [ abs_le.mp hα₂ ];
        · split_ifs <;> simp_all [ne_of_gt]
          -- Use the fact that $|e^{x} - 1| \leq |x| e^{|x|}$ for any $x$.
          have h_exp_bound : ∀ x : ℝ, |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
            intro x; rw [ abs_le ] ; constructor <;> cases abs_cases x <;> simp [ * ] <;> nlinarith [ Real.exp_pos x, Real.exp_neg x, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos x ) ), Real.add_one_le_exp x, Real.add_one_le_exp ( -x ), Real.exp_le_exp.2 ( by linarith : x ≤ |x| ), Real.exp_le_exp.2 ( by linarith : -x ≤ |x| ) ] ;
          -- Apply the exponential bound to $x = \log(b(\alpha)) \cdot (\alpha - 1)$.
          have h_exp_bound_applied : |Real.exp (Real.log (b α) * (α - 1)) - 1| ≤ |Real.log (b α)| * |α - 1| * Real.exp (|Real.log (b α)| * |α - 1|) := by
            simpa only [ abs_mul, mul_assoc ] using h_exp_bound ( Real.log ( b α ) * ( α - 1 ) ) |> le_trans <| by simp [ abs_mul, mul_assoc ] ;
          -- Use the fact that $|b(\alpha)| \leq \sqrt{b(\alpha)}$ for $0 < b(\alpha) \leq 1$.
          have h_sqrt_bound : |b α| * Real.exp (|Real.log (b α)| * |α - 1|) ≤ Real.sqrt (b α) := by
            rw [ abs_of_nonneg hα₂.1 ] ; rw [ Real.sqrt_eq_rpow ] ; rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_rpow ( by positivity ) ] ; ring_nf ; norm_num [ hα₂.1, hα₂.2.1, hα₂.2.2 ] ;
            cases abs_cases ( Real.log ( b α ) ) <;> cases abs_cases ( -1 + α ) <;> nlinarith [ Real.log_le_sub_one_of_pos hα₃, abs_le.mp hα₂.2.2 ] ;
          rw [ show Real.exp ( Real.log ( b α ) * α ) = Real.exp ( Real.log ( b α ) * ( α - 1 ) ) * Real.exp ( Real.log ( b α ) ) by rw [ ← Real.exp_add ] ; ring_nf, Real.exp_log hα₃ ];
          field_simp;
          rw [ abs_mul ] ; nlinarith [ abs_nonneg ( Real.log ( b α ) ), abs_nonneg ( α - 1 ), abs_nonneg ( b α ), Real.sqrt_nonneg ( b α ), mul_le_mul_of_nonneg_left h_sqrt_bound ( abs_nonneg ( Real.log ( b α ) ) ), mul_le_mul_of_nonneg_left h_sqrt_bound ( abs_nonneg ( α - 1 ) ), mul_le_mul_of_nonneg_left h_sqrt_bound ( abs_nonneg ( b α ) ) ] ;
      have h_bound : ∀ᶠ α in nhds 1, 0 ≤ b α ∧ b α ≤ 1 ∧ |α - 1| ≤ 1 / 2 := by
        have h_bound : ∀ᶠ α in nhds 1, 0 ≤ b α ∧ b α ≤ 1 := by
          filter_upwards [ hb_nonneg, hb_cont.eventually ( Metric.ball_mem_nhds _ zero_lt_one ) ] with α hα₁ hα₂ using ⟨ hα₁, by linarith [ abs_lt.mp hα₂ ] ⟩;
        filter_upwards [ h_bound, Metric.ball_mem_nhds 1 ( show ( 0 : ℝ ) < 1 / 2 by norm_num ) ] with α hα₁ hα₂ using ⟨ hα₁.1, hα₁.2, by exact hα₂.out.le ⟩;
      filter_upwards [ h_bound, ‹∀ᶠ α in nhds 1, 0 ≤ b α ∧ b α ≤ 1 ∧ |α - 1| ≤ 1 / 2 → |b α ^ α - b α| ≤ |α - 1| * Real.sqrt ( b α ) * |Real.log ( b α )|› ] with α hα₁ hα₂ using by simpa [ abs_of_nonneg hα₁.1 ] using hα₂ hα₁;
    -- Use the fact that $\sqrt{|b(α)|} \cdot |\log(|b(α)|)| \to 0$ as $b(α) \to 0$.
    have h_sqrt_log : Filter.Tendsto (fun α => Real.sqrt (|b α|) * |Real.log (|b α|)|) (nhds 1) (nhds 0) := by
      have h_sqrt_log : Filter.Tendsto (fun x => Real.sqrt x * |Real.log x|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h_sqrt_log : Filter.Tendsto (fun x => Real.sqrt x * Real.log x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          -- Let $y = \sqrt{x}$, so we can rewrite the limit as $\lim_{y \to 0^+} y \log(y^2) = \lim_{y \to 0^+} 2y \log(y)$.
          suffices h_log_y : Filter.Tendsto (fun y => 2 * y * Real.log y) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) by
            have h_subst : Filter.Tendsto (fun x => 2 * Real.sqrt x * Real.log (Real.sqrt x)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
              exact h_log_y.comp <| Filter.Tendsto.inf ( Real.continuous_sqrt.tendsto' _ _ <| by norm_num ) <| Filter.tendsto_principal_principal.mpr fun x hx => Real.sqrt_pos.mpr hx;
            generalize_proofs at *; (
            exact h_subst.congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by rw [ Real.log_sqrt hx.out.le ] ; ring ) |> fun h => h.trans ( by norm_num ) ;);
          exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [ mul_assoc ] using Filter.Tendsto.const_mul 2 ( Real.continuous_mul_log.tendsto 0 ) ) |> fun h => h.trans ( by norm_num ) ;
        exact tendsto_zero_iff_norm_tendsto_zero.mpr ( by simpa using h_sqrt_log.norm );
      have h_sqrt_log : Filter.Tendsto (fun α => Real.sqrt (|b α|) * |Real.log (|b α|)|) (nhdsWithin 1 {α | 0 < |b α|}) (nhds 0) := by
        refine' h_sqrt_log.comp _;
        rw [ tendsto_nhdsWithin_iff ];
        exact ⟨ tendsto_nhdsWithin_of_tendsto_nhds ( by simpa [ hc ] using hb_cont.abs.tendsto ), Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => hx ⟩;
      rw [ Metric.tendsto_nhdsWithin_nhds ] at h_sqrt_log;
      exact Metric.tendsto_nhds_nhds.mpr fun ε hε => by rcases h_sqrt_log ε hε with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, by intro x hx; by_cases hx' : 0 < |b x| <;> aesop ⟩ ;
    intro ε hε_pos
    obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ α, abs (α - 1) < δ₁ → Real.sqrt (|b α|) * |Real.log (|b α|)| < ε := by
      simpa using Metric.tendsto_nhds_nhds.mp h_sqrt_log ε hε_pos |> fun ⟨ δ₁, hδ₁₁, hδ₁₂ ⟩ => ⟨ δ₁, hδ₁₁, fun α hα => lt_of_abs_lt <| by simpa using hδ₁₂ hα ⟩;
    obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ α, abs (α - 1) < δ₂ → |b α ^ α - b α| ≤ |α - 1| * Real.sqrt (|b α|) * |Real.log (|b α|)| := by
      exact Metric.mem_nhds_iff.mp h_bound |> fun ⟨ δ₂, hδ₂_pos, hδ₂ ⟩ => ⟨ δ₂, hδ₂_pos, fun α hα => hδ₂ hα ⟩;
    exact ⟨ Min.min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun α hα => le_trans ( hδ₂ α ( lt_of_lt_of_le hα ( min_le_right _ _ ) ) ) ( by nlinarith [ hδ₁ α ( lt_of_lt_of_le hα ( min_le_left _ _ ) ), abs_nonneg ( α - 1 ) ] ) ⟩;
  rw [ hasDerivAt_iff_isLittleO_nhds_zero ];
  rw [ Asymptotics.isLittleO_iff ];
  intro ε hε; rcases h_eps ε hε with ⟨ δ, hδ, H ⟩ ; filter_upwards [ Metric.ball_mem_nhds _ hδ ] with x hx using by simpa [ hc ] using H ( 1 + x ) ( by simpa using hx ) ;

/-- If ker A ≤ ker ρM, then conjugating ρM by the support projection of A gives back ρM.
    This is because ρM is supported entirely on the support (= range) of A. -/
private lemma conj_supportProj_eq_of_ker_le (A ρM : HermitianMat d ℂ) (hker : A.ker ≤ ρM.ker) :
    ρM.conj (A.supportProj).mat = ρM := by
  have h1 : ρM.mat * A.supportProj.mat = ρM.mat := HermitianMat.mul_supportProj_of_ker_le hker
  have h2 : A.supportProj.mat * ρM.mat = ρM.mat := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose h1
  ext1
  simp only [HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat, h2, h1]

/-- For a PSD matrix A, the function r ↦ A ^ r converges to A.supportProj
    as r → 0 through nonzero values. On positive eigenvalues λ, λ^r → 1.
    On zero eigenvalues, 0^r = 0 for r ≠ 0. So the limit is the support
    projection (indicator of nonzero eigenvalues). -/
private lemma rpow_tendsto_supportProj
    (A : HermitianMat d ℂ)  :
    Filter.Tendsto (fun r : ℝ => A ^ r) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds A.supportProj) := by
  have hg : ∀ x : ℝ, Continuous
      (fun r : ℝ => if r = 0 then (if x = 0 then (0:ℝ) else 1) else x ^ r) := by
    intro x
    by_cases hx : x = 0 <;> simp [hx]
    · rw [Metric.continuous_iff]
      aesop
    · rw [show (fun r : ℝ => if r = 0 then 1 else x ^ r) = fun r : ℝ => x ^ r from
        funext fun r => by by_cases hr : r = 0 <;> simp [hr]]
      fun_prop (disch := exact Or.inl hx)
  have h2 : Filter.Tendsto (fun r : ℝ => A.cfc fun i => if r = 0 then (if i = 0 then (0:ℝ) else 1)
      else i ^ r) (nhdsWithin 0 {0}ᶜ) (nhds A.supportProj) := by
    simpa [HermitianMat.supportProj_eq_cfc] using
      ((HermitianMat.continuous_cfc_fun A hg).tendsto 0).mono_left nhdsWithin_le_nhds
  exact h2.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx => by
    simp [HermitianMat.rpow_eq_cfc, show x ≠ 0 from hx])

set_option backward.isDefEq.respectTransparency false in
/-- For PSD matrices A, ρ with A.ker ≤ ρ.ker, the function r ↦ ρ.conj (A ^ r).mat
    is continuous at r = 0. Even though A ^ r is discontinuous at r = 0 when A
    has zero eigenvalues, the kernel condition ensures the conj "kills" the
    discontinuity. -/
private lemma conj_rpow_continuousAt_zero
    (A ρM : HermitianMat d ℂ)
    (hker : A.ker ≤ ρM.ker) :
    ContinuousAt (fun r : ℝ => ρM.conj (A ^ r).mat) 0 := by
  have h1 : Filter.Tendsto (fun r : ℝ => ρM.conj (A ^ r).mat) (nhdsWithin 0 {0}ᶜ) (nhds ρM) := by
    have hc : Continuous fun B : HermitianMat d ℂ => ρM.conj B.mat := by fun_prop
    have h2 := (hc.tendsto A.supportProj).comp (rpow_tendsto_supportProj A)
    rwa [conj_supportProj_eq_of_ker_le A ρM hker] at h2
  have h0 : ρM.conj (A ^ (0:ℝ)).mat = ρM := by simp
  rw [ContinuousAt, h0, ← nhdsNE_sup_pure 0, Filter.tendsto_sup]
  refine ⟨h1, ?_⟩
  simpa [h0] using tendsto_pure_nhds (fun r : ℝ => ρM.conj (A ^ r).mat) 0

/-
ContinuousAt for B_of: the function α ↦ B(α) is continuous at α = 1.
  This requires the kernel condition because σ.M ^ r is discontinuous at r = 0
  on the kernel of σ. The kernel condition ensures the discontinuity is
  "killed" by ρ vanishing on σ's kernel.
-/
private lemma B_of_continuousAt (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    ContinuousAt (B_of ρ σ) 1 := by
  have h_exp : ContinuousAt (fun α : ℝ => (1 - α) / (2 * α)) 1 :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  exact ContinuousAt.comp (by simpa using conj_rpow_continuousAt_zero σ.M ρ.M h) h_exp

private lemma trace_cfc_sub_le (A : HermitianMat d ℂ) (f g : ℝ → ℝ) :
    |(A.cfc f).trace - (A.cfc g).trace| ≤
      (Fintype.card d : ℝ) * (⨆ i, |f (A.H.eigenvalues i) - g (A.H.eigenvalues i)|) := by
  rw [HermitianMat.trace_cfc_eq, HermitianMat.trace_cfc_eq]
  convert! Finset.abs_sum_le_sum_abs _ Finset.univ |> le_trans <| Finset.sum_le_card_nsmul _ _ _ fun i _ => show |f ( A.H.eigenvalues i ) - g ( A.H.eigenvalues i )| ≤ ⨆ i, |f ( A.H.eigenvalues i ) - g ( A.H.eigenvalues i )| from le_ciSup ( Finite.bddAbove_range fun i => |f ( A.H.eigenvalues i ) - g ( A.H.eigenvalues i )| ) i using 1
  · simp [← Finset.sum_sub_distrib]
  · simp

/-- Eigenvalues of M(α) are uniformly bounded near α = 1. -/
private lemma eigenvalues_bounded_near {M : ℝ → HermitianMat d ℂ}
    (hM_nonneg : ∀ᶠ α in nhds 1, 0 ≤ M α)
    (hM_cont : ContinuousAt M 1) :
    ∃ K > 0, ∀ᶠ α in nhds 1, ∀ i, 0 ≤ (M α).H.eigenvalues i ∧ (M α).H.eigenvalues i ≤ K := by
  refine ⟨‖M 1‖ + 1, by positivity, ?_⟩
  filter_upwards [hM_nonneg, hM_cont.norm.eventually (ge_mem_nhds (lt_add_one ‖M 1‖))]
    with α h1 h2 i
  exact ⟨by simpa using h1.eigenvalues_nonneg i,
    (le_of_abs_le (HermitianMat.eigenvalue_norm_le (M α) i)).trans h2⟩

/-
Uniform convergence of (x^{1+h} - x)/h to x * log x on [0, K] as h → 0.
This is the uniform version of the derivative of s ↦ x^s at s = 1.
-/
set_option maxHeartbeats 800000 in
private lemma rpow_slope_tendsto_uniformly (K : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ h : ℝ, 0 < |h| → |h| < δ →
    ∀ x ∈ Set.Icc 0 K, |(x ^ (1 + h) - x) / h - x * Real.log x| < ε := by
  intro ε ε_pos
  obtain ⟨δ₁, δ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₁ → |x * Real.log x| < ε / 4 ∧ ∀ h, 0 < |h| → |h| < 1 / 2 → |(x ^ (1 + h) - x) / h| < ε / 4 := by
    obtain ⟨δ₁, δ₁_pos, hδ₁⟩ : ∃ δ₁ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₁ → |x * Real.log x| < ε / 4 := by
      have h_cont : Filter.Tendsto (fun x => x * Real.log x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( by simpa using Real.continuous_mul_log.tendsto 0 );
      have := Metric.tendsto_nhdsWithin_nhds.mp h_cont ( ε / 4 ) ( by linarith );
      exact ⟨ this.choose, this.choose_spec.1, fun x hx₁ hx₂ hx₃ => by simpa [ abs_mul ] using this.choose_spec.2 hx₂ ( by simpa [ abs_of_pos hx₂ ] using hx₃ ) ⟩;
    have h_bound : ∃ δ₁ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₁ → ∀ h, 0 < |h| → |h| < 1 / 2 → |x ^ (1 + h) - x| ≤ |h| * x * (|Real.log x| + 1) * Real.exp (|h| * (|Real.log x| + 1)) := by
      have h_bound : ∀ x ∈ Set.Icc 0 K, 0 < x → ∀ h : ℝ, 0 < |h| → |h| < 1 / 2 → |x ^ (1 + h) - x| ≤ |h| * x * (|Real.log x| + 1) * Real.exp (|h| * (|Real.log x| + 1)) := by
        intros x hx hx_pos h hh_pos hh_lt_half
        have h_exp_bound : |Real.exp (h * Real.log x) - 1| ≤ |h| * |Real.log x| * Real.exp (|h| * |Real.log x|) := by
          have h_exp_bound : ∀ y : ℝ, |Real.exp y - 1| ≤ |y| * Real.exp (|y|) := by
            intro y; rw [ abs_le ] ; constructor <;> cases abs_cases y <;> simp [ * ];
            · nlinarith [ Real.add_one_le_exp y ];
            · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
            · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
            · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
          simpa only [ abs_mul ] using h_exp_bound ( h * Real.log x );
        rw [ Real.rpow_add hx_pos, Real.rpow_one ];
        rw [ Real.rpow_def_of_pos hx_pos ];
        rw [ show x * Real.exp ( Real.log x * h ) - x = x * ( Real.exp ( h * Real.log x ) - 1 ) by ring_nf ]
        rw [ abs_mul, abs_of_nonneg hx_pos.le ]
        refine' le_trans ( mul_le_mul_of_nonneg_left h_exp_bound hx_pos.le ) _
        ring_nf
        exact le_add_of_le_of_nonneg ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr ( by nlinarith [ abs_nonneg h, abs_nonneg ( Real.log x ) ] ) ) ( by positivity ) ) ( by positivity );
      exact ⟨ δ₁, δ₁_pos, fun x hx hx' hx'' h hh hh' => h_bound x hx hx' h hh hh' ⟩;
    obtain ⟨δ₂, δ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₂ → x * (|Real.log x| + 1) * Real.exp (1 / 2 * (|Real.log x| + 1)) < ε / 4 := by
      have h_bound : Filter.Tendsto (fun x => x * (|Real.log x| + 1) * Real.exp (1 / 2 * (|Real.log x| + 1))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        -- Let $y = -\log x$, so we can rewrite the limit as $y \to \infty$.
        suffices h_log : Filter.Tendsto (fun y => Real.exp (-y) * (y + 1) * Real.exp ((y + 1) / 2)) Filter.atTop (nhds 0) by
          have h_subst : Filter.Tendsto (fun x => Real.exp (-(-Real.log x)) * ((-Real.log x) + 1) * Real.exp ((-Real.log x + 1) / 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            exact h_log.comp ( Filter.tendsto_neg_atBot_atTop.comp ( Real.tendsto_log_nhdsNE_zero.mono_left <| nhdsWithin_mono _ <| by norm_num ) );
          refine' h_subst.congr' _;
          filter_upwards [ Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, zero_lt_one ⟩ ] with x hx
          rw [ abs_of_nonpos ( Real.log_nonpos hx.1.le hx.2.le ) ]
          rw [ neg_neg, Real.exp_log hx.1 ]
          ring_nf
        -- We can factor out $e^{-y/2}$ and use the fact that $e^{-y/2} \to 0$ as $y \to \infty$.
        suffices h_factor : Filter.Tendsto (fun y => Real.exp (-y / 2) * (y + 1)) Filter.atTop (nhds 0) by
          convert h_factor.const_mul ( Real.exp ( 1 / 2 ) ) using 2 <;> ring_nf
          norm_num [ mul_assoc, ← Real.exp_add ] ; ring_nf
        -- Let $z = \frac{y}{2}$, so we can rewrite the limit as $z \to \infty$.
        suffices h_z : Filter.Tendsto (fun z => Real.exp (-z) * (2 * z + 1)) Filter.atTop (nhds 0) by
          convert h_z.comp ( Filter.tendsto_id.atTop_mul_const ( by norm_num : 0 < ( 2⁻¹ : ℝ ) ) ) using 2 ; norm_num ; ring_nf
        have := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1;
        convert this.const_mul 2 |> Filter.Tendsto.add <| Real.tendsto_exp_atBot.comp <| Filter.tendsto_neg_atTop_atBot using 2 <;> norm_num
        ring;
      have := Metric.tendsto_nhdsWithin_nhds.mp h_bound ( ε / 4 ) ( by linarith );
      obtain ⟨ δ₂, δ₂_pos, H ⟩ := this; exact ⟨ δ₂, δ₂_pos, fun x hx₁ hx₂ hx₃ => by linarith [ abs_lt.mp ( H hx₂ ( by simpa [ abs_of_pos hx₂ ] using hx₃ ) ) ] ⟩ ;
    obtain ⟨δ₃, δ₃_pos, hδ₃⟩ : ∃ δ₃ > 0, ∀ x ∈ Set.Icc 0 K, 0 < x → x < δ₃ → ∀ h, 0 < |h| → |h| < 1 / 2 → |(x ^ (1 + h) - x) / h| ≤ x * (|Real.log x| + 1) * Real.exp (|h| * (|Real.log x| + 1)) := by
      obtain ⟨ δ₃, δ₃_pos, hδ₃ ⟩ := h_bound;
      exact ⟨ δ₃, δ₃_pos, fun x hx hx' hx'' h hh hh' => by rw [ abs_div, div_le_iff₀ ( by positivity ) ] ; convert! hδ₃ x hx hx' hx'' h hh hh' using 1 ; ring ⟩;
    refine' ⟨ Min.min δ₁ ( Min.min δ₂ δ₃ ), lt_min δ₁_pos ( lt_min δ₂_pos δ₃_pos ), fun x hx hx' hx'' => ⟨ hδ₁ x hx hx' ( lt_of_lt_of_le hx'' ( min_le_left _ _ ) ), fun h hh₁ hh₂ => lt_of_le_of_lt ( hδ₃ x hx hx' ( lt_of_lt_of_le hx'' ( min_le_right _ _ |> le_trans <| min_le_right _ _ ) ) h hh₁ hh₂ ) _ ⟩ ⟩;
    exact lt_of_le_of_lt ( mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_right hh₂.le <| by positivity ) <| by positivity ) <| hδ₂ x hx hx' <| lt_of_lt_of_le hx'' <| min_le_right _ _ |> le_trans <| min_le_left _ _;
  obtain ⟨δ₂, δ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < δ₂ → |(x ^ (1 + h) - x) / h - x * Real.log x| < ε / 4 := by
    have h_mean_value : ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < 1 / 2 → |(x ^ (1 + h) - x) / h - x * Real.log x| ≤ |h| * x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) := by
      intros x hx h h_pos h_lt
      have h_mean_value : |(x ^ h - 1) / h - Real.log x| ≤ |h| * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) := by
        -- Applying the inequality |e^y - 1 - y| ≤ |y|^2 e^|y| with y = h * Real.log x.
        have h_exp_ineq : ∀ y : ℝ, |Real.exp y - 1 - y| ≤ |y|^2 * Real.exp |y| := by
          intro y; rw [ abs_le ] ; constructor <;> cases abs_cases y <;> simp [ * ];
          · nlinarith [ Real.add_one_le_exp y, Real.exp_pos y ];
          · nlinarith [ Real.add_one_le_exp y, Real.add_one_le_exp ( -y ), Real.exp_pos y, Real.exp_pos ( -y ) ];
          · -- Using the Taylor series expansion of $e^y$, we have $e^y \leq 1 + y + y^2 e^y$ for $y \geq 0$.
            have h_taylor : ∀ y : ℝ, 0 ≤ y → Real.exp y ≤ 1 + y + y^2 * Real.exp y := by
              intro y hy; nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ), mul_nonneg hy ( Real.exp_nonneg y ), mul_nonneg hy ( Real.exp_nonneg ( -y ) ) ] ;
            linarith [ h_taylor y ( by linarith ) ];
          · nlinarith [ Real.exp_pos y, Real.exp_neg y, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos y ) ), Real.add_one_le_exp y, Real.add_one_le_exp ( -y ) ];
        convert! mul_le_mul_of_nonneg_left ( h_exp_ineq ( h * Real.log x ) ) ( inv_nonneg.mpr h_pos.le ) using 1 <;> norm_num [ Real.rpow_def_of_pos ( show 0 < x from lt_of_lt_of_le δ₁_pos hx.1 ), mul_comm ] ; ring_nf
        · rw [ ← abs_inv, ← abs_mul ] ; ring_nf;
          by_cases hh : h = 0 <;> aesop;
        · simp [ sq, mul_assoc, mul_comm, mul_left_comm, h_pos.ne' ];
      convert! mul_le_mul_of_nonneg_left h_mean_value ( show 0 ≤ x by linarith [ hx.1 ] ) using 1 <;> ring_nf

      rw [ show x ^ (1 + h) * h⁻¹ - x * h⁻¹ - x * Real.log x = x * ( -h⁻¹ + ( h⁻¹ * x ^ h - Real.log x ) ) by rw [ Real.rpow_add ( by linarith [ hx.1 ] ), Real.rpow_one ] ; ring ]
      rw [ abs_mul, abs_of_nonneg ( by linarith [ hx.1 ] : 0 ≤ x ) ]
      ring_nf

    -- Choose δ₂ such that |h| * x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) < ε / 4 for all x ∈ [δ₁, K] and |h| < δ₂.
    obtain ⟨δ₂, δ₂_pos, hδ₂⟩ : ∃ δ₂ > 0, ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < δ₂ → |h| * x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) < ε / 4 := by
      -- Since $x * (\log x)^2 * \exp(|h| * |\log x|)$ is continuous on the compact interval $[\delta₁, K]$, it is bounded.
      obtain ⟨M, hM⟩ : ∃ M > 0, ∀ x ∈ Set.Icc δ₁ K, ∀ h, 0 < |h| → |h| < 1 / 2 → x * (Real.log x) ^ 2 * Real.exp (|h| * |Real.log x|) ≤ M := by
        have h_cont : ContinuousOn (fun x => x * (Real.log x) ^ 2 * Real.exp (1 / 2 * |Real.log x|)) (Set.Icc δ₁ K) := by
          exact ContinuousOn.mul ( ContinuousOn.mul continuousOn_id ( ContinuousOn.pow ( Real.continuousOn_log.mono ( by exact fun x hx => ne_of_gt <| lt_of_lt_of_le δ₁_pos hx.1 ) ) _ ) ) ( ContinuousOn.rexp <| ContinuousOn.mul continuousOn_const <| ContinuousOn.abs <| Real.continuousOn_log.mono ( by exact fun x hx => ne_of_gt <| lt_of_lt_of_le δ₁_pos hx.1 ) );
        obtain ⟨ M, hM ⟩ := IsCompact.exists_bound_of_continuousOn ( CompactIccSpace.isCompact_Icc ) h_cont;
        norm_num +zetaDelta at *;
        exact ⟨ Max.max M 1, by positivity, fun x hx₁ hx₂ h hh₁ hh₂ => le_trans ( by rw [ abs_of_nonneg ( by linarith : 0 ≤ x ) ] ; exact mul_le_mul_of_nonneg_left ( Real.exp_le_exp.mpr <| by nlinarith [ abs_nonneg ( Real.log x ) ] ) <| by nlinarith [ abs_nonneg ( Real.log x ) ] ) <| le_trans ( hM x hx₁ hx₂ ) <| le_max_left _ _ ⟩;
      exact ⟨ Min.min ( 1 / 2 ) ( ε / 4 / M ), lt_min ( by norm_num ) ( div_pos ( by linarith ) hM.1 ), fun x hx h hh₁ hh₂ => by nlinarith [ min_le_left ( 1 / 2 ) ( ε / 4 / M ), min_le_right ( 1 / 2 ) ( ε / 4 / M ), mul_div_cancel₀ ( ε / 4 ) hM.1.ne', abs_nonneg h, hM.2 x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ), mul_le_mul_of_nonneg_left ( hM.2 x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ) ) ( abs_nonneg h ) ] ⟩;
    exact ⟨ Min.min δ₂ ( 1 / 2 ), lt_min δ₂_pos ( by norm_num ), fun x hx h hh₁ hh₂ => lt_of_le_of_lt ( h_mean_value x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_right _ _ ) ) ) ( hδ₂ x hx h hh₁ ( lt_of_lt_of_le hh₂ ( min_le_left _ _ ) ) ) ⟩;
  refine' ⟨ Min.min ( 1 / 2 ) δ₂, lt_min ( by positivity ) δ₂_pos, fun h hh₁ hh₂ x hx => _ ⟩ ; cases lt_or_ge x δ₁ <;> simp_all [ abs_lt ];
  · cases lt_or_eq_of_le hx.1 <;> simp_all [ abs_of_nonneg ];
    · constructor <;> cases abs_cases ( Real.log x ) <;> nlinarith [ hδ₁ x hx.1 hx.2 ‹_› ‹_›, hδ₁ x hx.1 hx.2 ‹_› ‹_› |>.2 h hh₁ hh₂.1.1 hh₂.1.2 ];
    · by_cases h : 1 + h = 0 <;> simp_all [ division_def ] ; linarith [ Real.log_le_sub_one_of_pos ( show 0 < ε by linarith ) ] ;
      norm_num [ ← ‹0 = x› ] at * ; aesop;
  · constructor <;> linarith [ hδ₂ x ‹_› hx.2 h hh₁ hh₂.2.1 hh₂.2.2 ]

/-
CFC trace continuity: if M → ρ.M and f is continuous on [0,∞),
then Tr[(M α).cfc(f)] → Tr[ρ.M.cfc(f)].
-/
private lemma trace_cfc_tendsto_of_tendsto (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 0))
    {M : ℝ → HermitianMat d ℂ}
    (hM_cont : ContinuousAt M 1) (hM_nonneg : ∀ᶠ α in nhds 1, 0 ≤ M α)
    (hM_one : M 1 = ρ.M) :
    Filter.Tendsto (fun α => ((M α).cfc f).trace) (nhds 1) (nhds ((ρ.M.cfc f).trace)) := by
  have h_cfc_cont : ContinuousWithinAt (fun A : HermitianMat d ℂ => A.cfc f)
      {A : HermitianMat d ℂ | 0 ≤ A} ρ.M :=
    (HermitianMat.continuousWithinAt_cfc_of_continuousOn hf
        ((HermitianMat.posSemidef_iff_spectrum_Ici _).mp ρ.nonneg)).mono
      fun A hA => (HermitianMat.posSemidef_iff_spectrum_Ici A).mp hA
  exact HermitianMat.trace_Continuous.continuousAt.tendsto.comp (h_cfc_cont.tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hM_one ▸ hM_cont.tendsto, hM_nonneg⟩))

/-
The remainder term r(1+h)/h → 0 where
`r(α) = Tr[M(α)^α] - Tr[M(α)] - Tr[ρ.M^α] + Tr[ρ.M]`
-/
set_option maxHeartbeats 800000 in
private lemma cross_term_slope_tendsto_zero
    {M : ℝ → HermitianMat d ℂ}
    (hM_nonneg : ∀ᶠ α in nhds 1, 0 ≤ M α)
    (hM_cont : ContinuousAt M 1)
    (hM_one : M 1 = ρ.M) :
    Filter.Tendsto
      (fun h : ℝ => ((M (1 + h) ^ (1 + h)).trace - (M (1 + h)).trace
                    - (ρ.M ^ (1 + h)).trace + ρ.M.trace) / h)
      (nhdsWithin 0 {0}ᶜ)
      (nhds 0) := by
  obtain ⟨K, hK_pos, hK⟩ := eigenvalues_bounded_near hM_nonneg hM_cont
  have h1add : Filter.Tendsto (fun h : ℝ => 1 + h) (nhdsWithin 0 {0}ᶜ) (nhds 1) :=
    ((continuous_const.add continuous_id).tendsto' 0 1 (by norm_num)).mono_left
      nhdsWithin_le_nhds
  have key : ∀ lam : ℝ → d → ℝ,
      (∀ᶠ h in nhdsWithin (0:ℝ) {0}ᶜ, ∀ i, 0 ≤ lam h i ∧ lam h i ≤ K) →
      Filter.Tendsto (fun h => ∑ i, ((lam h i ^ (1 + h) - lam h i) / h
        - lam h i * Real.log (lam h i))) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    intro lam hlam
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ₁, hδ₁, H⟩ := rpow_slope_tendsto_uniformly K (ε / (Fintype.card d + 1))
      (by positivity)
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hlam
    obtain ⟨δ₂, hδ₂, H₂⟩ := hlam
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {h} hh hdist => ?_⟩
    rw [Real.dist_eq, sub_zero] at hdist ⊢
    have hmem := H₂ (show dist h 0 < δ₂ by
      rw [Real.dist_eq, sub_zero]
      exact hdist.trans_le (min_le_right _ _)) hh
    calc |∑ i, ((lam h i ^ (1 + h) - lam h i) / h - lam h i * Real.log (lam h i))|
        ≤ ∑ i, |(lam h i ^ (1 + h) - lam h i) / h - lam h i * Real.log (lam h i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : d, ε / (Fintype.card d + 1) :=
          Finset.sum_le_sum fun i _ => le_of_lt <|
            H h (abs_pos.mpr hh) (hdist.trans_le (min_le_left _ _)) _
              (Set.mem_Icc.mpr (hmem i))
      _ < ε := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          calc (Fintype.card d : ℝ) * (ε / (Fintype.card d + 1))
              < (Fintype.card d + 1) * (ε / (Fintype.card d + 1)) :=
                mul_lt_mul_of_pos_right (by linarith) (by positivity)
            _ = ε := by field_simp
  have hμ : ∀ i, 0 ≤ ρ.M.H.eigenvalues i ∧ ρ.M.H.eigenvalues i ≤ K := by
    have h0 := hK.self_of_nhds
    rwa [hM_one] at h0
  have hA := key (fun h i => (M (1 + h)).H.eigenvalues i) (h1add.eventually hK)
  have hB := key (fun _ i => ρ.M.H.eigenvalues i) (Filter.Eventually.of_forall fun _ => hμ)
  have hT3 : Filter.Tendsto (fun h : ℝ =>
      ∑ i, (M (1 + h)).H.eigenvalues i * Real.log ((M (1 + h)).H.eigenvalues i)
        - ∑ i, ρ.M.H.eigenvalues i * Real.log (ρ.M.H.eigenvalues i))
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have h2 := (trace_cfc_tendsto_of_tendsto (fun x => x * Real.log x)
      Real.continuous_mul_log.continuousOn hM_cont hM_nonneg hM_one).comp h1add
    simpa [HermitianMat.trace_cfc_eq, Function.comp_def] using h2.sub_const
      ((ρ.M.cfc fun x => x * Real.log x).trace)
  have hfinal := (hA.sub hB).add hT3
  norm_num at hfinal
  refine hfinal.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := by simpa using hh
  rw [HermitianMat.trace_rpow_eq_sum, HermitianMat.trace_rpow_eq_sum,
    ← HermitianMat.sum_eigenvalues_eq_trace, ← HermitianMat.sum_eigenvalues_eq_trace]
  simp only [div_eq_mul_inv, sub_mul, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring_nf
  rfl

/-- For a differentiable family of PSD matrices M(α) with M(1) having eigenvalues p_i,
    the function α ↦ Tr[M(α)^α] - Tr[M(α)] has derivative ⟪M(1), M(1).log⟫ at α = 1.
    This is because at α = 1, the function x^s - x has zero x-derivative (since d/dx(x^1) = 1),
    so only the s-derivative contributes, giving the same answer as for fixed eigenvalues. -/
private lemma hasDerivAt_trace_rpow_sub_trace_variable_base
    {M : ℝ → HermitianMat d ℂ}
    (hM_nonneg : ∀ᶠ α in nhds 1, 0 ≤ M α)
    (hM_cont : ContinuousAt M 1)
    (hM_one : M 1 = ρ.M) :
    HasDerivAt (fun α : ℝ => (M α ^ α).trace - (M α).trace) ⟪ρ.M, ρ.M.log⟫ 1 := by
  have h_deriv : HasDerivAt (fun α : ℝ => ((M α) ^ α).trace - (M α).trace - ((ρ.M) ^ α).trace + ρ.M.trace) 0 1 := by
    convert hasDerivAt_iff_tendsto_slope_zero.mpr _ using 1
    convert cross_term_slope_tendsto_zero hM_nonneg hM_cont hM_one using 2 ; norm_num [ hM_one ] ; ring!
  convert! h_deriv.add ( hasDerivAt_trace_rpow_sub_trace ρ.M ρ.nonneg ) using 1 <;> norm_num
  ring_nf
  ext; norm_num; ring

/-- The cross term in the derivative decomposition vanishes: the function
    α ↦ Tr[B(α)^α] - Tr[B(α)] - Tr[ρ^α] + 1 has derivative 0 at α = 1.
    This is because at α=1, B^1 = B, so ∂/∂B Tr[B^α] = Tr[·] (the trace is linear),
    making the cross term (variation in B times variation in α) vanish. -/
private lemma rpow_trace_cross_term_vanishes {ρ σ : MState d}
    (h : σ.M.ker ≤ ρ.M.ker) :
    HasDerivAt
      (fun α : ℝ => ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace
        - (ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat).trace
        - (ρ.M ^ α).trace + 1)
      0
      1 := by
  have h_cross_term : HasDerivAt (fun α : ℝ => ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace - (ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat).trace) ⟪ρ.M, ρ.M.log⟫ 1 ∧ HasDerivAt (fun α : ℝ => (ρ.M ^ α).trace) ⟪ρ.M, ρ.M.log⟫ 1 := by
    apply And.intro;
    · convert hasDerivAt_trace_rpow_sub_trace_variable_base _ _ _ using 1;
      · exact Filter.Eventually.of_forall fun α => B_of_nonneg ρ σ α;
      · convert B_of_continuousAt ρ σ h using 1;
      · simp [ HermitianMat.conj ];
    · convert hasDerivAt_trace_rpow_at_one ρ.M ( by exact ρ.nonneg ) using 1
  convert! HasDerivAt.add ( HasDerivAt.sub h_cross_term.1 h_cross_term.2 ) ( hasDerivAt_const _ _ ) using 1
  ring

private theorem sandwichedRelRentropy.hasDerivAt_trace_at_one {ρ σ : MState d}
    (h : σ.M.ker ≤ ρ.M.ker) :
    HasDerivAt
      (fun α : ℝ => ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace)
      ⟪ρ.M, ρ.M.log - σ.M.log⟫
      1 := by
  have h_deriv :=
    have h_cross_term := rpow_trace_cross_term_vanishes h
    have h_conj := hasDerivAt_trace_conj_at_one h
    have h_rpow := hasDerivAt_trace_rpow_at_one ρ.M ρ.nonneg
    (h_cross_term.add (h_conj.add h_rpow)).sub (hasDerivAt_const 1 1)
  convert! h_deriv using 2
  · simp only [Pi.sub_apply, Pi.add_apply]
    ring
  · simp only [inner_sub_right]
    ring

/--
The key limit: as α → 1, log(Tr[(ρ.conj σ^t)^α]) / (α-1) → ⟪ρ, log ρ - log σ⟫,
    where t = (1-α)/(2α). Derived from hasDerivAt_trace_at_one via L'Hôpital
    (or equivalently, log(1+x)/x → 1 and (f(α)-1)/(α-1) → f'(1)).
-/
private theorem sandwichedRelRentropy.limit_at_one (ρ σ : MState d)
    (h : σ.M.ker ≤ ρ.M.ker) :
    Filter.Tendsto
      (fun α : ℝ ↦ ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace.log / (α - 1))
      (nhdsWithin 1 (Set.Ioi 0 \ {1}))
      (nhds ⟪ρ.M, ρ.M.log - σ.M.log⟫) := by
  have h_log_approx : HasDerivAt (fun α : ℝ ↦ Real.log (((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace)) (⟪ρ.M, ρ.M.log - σ.M.log⟫) 1 := by
    have h_deriv := sandwichedRelRentropy.hasDerivAt_trace_at_one h
    convert h_deriv.log (by simp) using 1
    simp
  rw [hasDerivAt_iff_tendsto_slope] at h_log_approx
  convert h_log_approx.mono_left (nhdsWithin_mono _ _) using 2
  · norm_num [ div_eq_inv_mul, slope_def_field ]
  · simp

theorem inner_log_sub_log_nonneg (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  -- Take the limit α → 1+ of the sandwiched Renyi relative entropy,
  -- which converges to ⟪ρ.M, ρ.M.log - σ.M.log⟫ and is nonneg for all α > 1.
  -- Use the limit from the right: for α > 1, log(Tr[...]^α) / (α - 1) ≥ 0
  have h_limit := sandwichedRelRentropy.limit_at_one ρ σ h
  -- Restrict the filter to (1, ∞) ⊂ (0, ∞) \ {1}
  have h_mono : nhdsWithin (1 : ℝ) (Set.Ioi 1) ≤ nhdsWithin 1 (Set.Ioi 0 \ {1}) := by
    apply nhdsWithin_mono
    intro x hx
    exact ⟨Set.mem_Ioi.mpr (lt_trans zero_lt_one hx), ne_of_gt hx⟩
  haveI : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := inferInstance
  apply ge_of_tendsto (h_limit.mono_left h_mono)
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact sandwichedRelRentropy_nonneg_α_gt_1 h hα

theorem sandwichedRelRentropy_nonneg {α : ℝ} (hα : 0 < α) (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫
      else ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1) := by
  split_ifs with h1
  · exact inner_log_sub_log_nonneg h
  by_cases hα₂ : α > 1
  · exact sandwichedRelRentropy_nonneg_α_gt_1 h hα₂
  · have : α < 1 := by push Not at hα₂; exact lt_of_le_of_ne hα₂ h1
    exact sandwichedRelRentropy_nonneg_α_lt_1 h hα this

section additivity

--TODO Cleanup. Ugh.

/--
If the kernels of the components are contained, then the kernel of the Kronecker product is contained.
-/
lemma ker_kron_le_of_le {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (A C : Matrix d₁ d₁ ℂ) (B D : Matrix d₂ d₂ ℂ)
    (hA : LinearMap.ker A.toEuclideanLin ≤ LinearMap.ker C.toEuclideanLin)
    (hB : LinearMap.ker B.toEuclideanLin ≤ LinearMap.ker D.toEuclideanLin) :
    LinearMap.ker (A.kronecker B).toEuclideanLin ≤ LinearMap.ker (C.kronecker D).toEuclideanLin := by
  intro x hx
  simp only [Matrix.kronecker, LinearMap.mem_ker, Matrix.toLpLin_apply,
    WithLp.toLp_eq_zero] at hx ⊢
  -- By definition of Kronecker product, we know that $(A \otimes B)x = 0$ if and only if for all $i$ and $j$, $\sum_{k,l} A_{ik} B_{jl} x_{kl} = 0$.
  have h_kronecker : ∀ i j, ∑ k, A i k • ∑ l, B j l • x (k, l) = 0 := by
    intro i j
    replace hx := congr_fun hx ( i, j )
    simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
      Pi.zero_apply, smul_eq_mul, Finset.mul_sum] at hx ⊢
    rw [ ← Finset.sum_product' ]
    simpa only [mul_assoc, Finset.univ_product_univ] using hx
  -- Apply the hypothesis `hA` to each term in the sum.
  have h_apply_hA : ∀ i j, ∑ k, C i k • ∑ l, B j l • x (k, l) = 0 := by
    intro i j
    specialize hA ( show (WithLp.toLp 2 ( fun k => ∑ l, B j l • x ( k, l ) )) ∈ LinearMap.ker ( Matrix.toEuclideanLin A ) from ?_ )
    · simp_all only [smul_eq_mul, LinearMap.mem_ker]
      ext i_1 : 1
      simp_all only [PiLp.zero_apply]
      apply h_kronecker
    · exact congr(WithLp.ofLp $hA i)
  ext ⟨ i, j ⟩
  simp only [smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Pi.zero_apply] at h_kronecker h_apply_hA ⊢
  have h_apply_hB : ∑ l, D j l • ∑ k, C i k • x (k, l) = 0 := by
    specialize hB
    simp_all only [funext_iff, Pi.zero_apply, Prod.forall, smul_eq_mul]
    have := hB ( show  (WithLp.toLp 2 ( fun l => ∑ k, C i k * x ( k, l ) )) ∈ LinearMap.ker ( Matrix.toEuclideanLin B ) from ?_ )
    · simp_all only [LinearMap.mem_ker] ;
      exact congr(WithLp.ofLp $this j)
    · ext j
      specialize h_apply_hA i j
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum ] at h_apply_hA ⊢
      simp_rw [mul_left_comm]
      rw [Finset.sum_comm]
      exact h_apply_hA
  rw [← h_apply_hB]
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [ Finset.sum_sigma' ];
  refine' Finset.sum_bij ( fun x _ => ⟨ x.2, x.1 ⟩ ) _ _ _ _
  · simp
  · simp
  · simp
  · simp only [Finset.mem_univ, mul_assoc, Prod.mk.eta, mul_left_comm, imp_self, implies_true]

--TODO: Generalize to arbitrary PSD matrices.
/--
If the kernel of a product state is contained in another, the left component kernel is contained.
-/
lemma ker_le_of_ker_kron_le_left (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h : (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker) :
    σ₁.M.ker ≤ ρ₁.M.ker := by
  have hkron : ∀ (A : Matrix d₁ d₁ ℂ) (B : Matrix d₂ d₂ ℂ) (a : d₁ → ℂ) (b : d₂ → ℂ),
      (A.kronecker B).mulVec (fun p => a p.1 * b p.2) =
        fun p => A.mulVec a p.1 * B.mulVec b p.2 := by
    intro A B a b
    ext ⟨i, j⟩
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    exact Fintype.sum_prod_type_right fun x => A i x.1 * (B j x.2 * (a x.1 * b x.2))
  have hker_ne : ∀ (τ : MState d₂), τ.M.ker ≠ ⊤ := fun τ hτ => τ.pos.ne' <| by
    ext1
    rw [Matrix.ext_iff_mulVec]
    intro w
    simpa using (τ.M.mem_ker_iff_mulVec_zero (WithLp.toLp 2 w)).mp (hτ ▸ Submodule.mem_top)
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    ![ρ₂.M.ker, σ₂.M.ker] (fun i => by fin_cases i <;> exact hker_ne _)
  intro u hu
  have hu0 : σ₁.m.mulVec u = 0 := (σ₁.M.mem_ker_iff_mulVec_zero u).mp hu
  have hz : (WithLp.toLp 2 fun p : d₁ × d₂ => u p.1 * v p.2) ∈ (σ₁ ⊗ᴹ σ₂).M.ker := by
    refine ((σ₁ ⊗ᴹ σ₂).M.mem_ker_iff_mulVec_zero _).mpr ?_
    refine (hkron σ₁.M.mat σ₂.M.mat u v).trans ?_
    ext p
    simp [hu0]
  have hz' := ((ρ₁ ⊗ᴹ ρ₂).M.mem_ker_iff_mulVec_zero _).mp (h hz)
  rw [show ((ρ₁ ⊗ᴹ ρ₂).M.mat).mulVec _ = _ from hkron ρ₁.M.mat ρ₂.M.mat u v] at hz'
  have hvne : ρ₂.m.mulVec v ≠ 0 := fun h0 => by
    simpa using hv 0 ((ρ₂.M.mem_ker_iff_mulVec_zero v).mpr h0)
  obtain ⟨b, hb⟩ := Function.ne_iff.mp hvne
  refine (ρ₁.M.mem_ker_iff_mulVec_zero u).mpr (funext fun a => ?_)
  have h2 := congr_fun hz' (a, b)
  simp only [Pi.zero_apply, mul_eq_zero] at h2
  exact h2.resolve_right hb


--TODO: Generalize to arbitrary PSD matrices.
--TODO: Rewrite the proof using the `ker_le_of_ker_kron_le_left` lemma, and the fact that
-- there's a unitary whose conjugation swaps the kronecker product.
/--
If the kernel of a product state is contained in another, the right component kernel is contained.
-/
lemma ker_le_of_ker_kron_le_right (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h : (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker) :
    σ₂.M.ker ≤ ρ₂.M.ker := by
  have hkron : ∀ (A : Matrix d₁ d₁ ℂ) (B : Matrix d₂ d₂ ℂ) (a : d₁ → ℂ) (b : d₂ → ℂ),
      (A.kronecker B).mulVec (fun p => a p.1 * b p.2) =
        fun p => A.mulVec a p.1 * B.mulVec b p.2 := by
    intro A B a b
    ext ⟨i, j⟩
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    exact Fintype.sum_prod_type_right fun x => A i x.1 * (B j x.2 * (a x.1 * b x.2))
  have hker_ne : ∀ (τ : MState d₁), τ.M.ker ≠ ⊤ := fun τ hτ => τ.pos.ne' <| by
    ext1
    rw [Matrix.ext_iff_mulVec]
    intro w
    simpa using (τ.M.mem_ker_iff_mulVec_zero (WithLp.toLp 2 w)).mp (hτ ▸ Submodule.mem_top)
  obtain ⟨u, hu⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    ![ρ₁.M.ker, σ₁.M.ker] (fun i => by fin_cases i <;> exact hker_ne _)
  intro v hv
  have hv0 : σ₂.m.mulVec v = 0 := (σ₂.M.mem_ker_iff_mulVec_zero v).mp hv
  have hz : (WithLp.toLp 2 fun p : d₁ × d₂ => u p.1 * v p.2) ∈ (σ₁ ⊗ᴹ σ₂).M.ker := by
    refine ((σ₁ ⊗ᴹ σ₂).M.mem_ker_iff_mulVec_zero _).mpr ?_
    refine (hkron σ₁.M.mat σ₂.M.mat u v).trans ?_
    ext p
    simp [hv0]
  have hz' := ((ρ₁ ⊗ᴹ ρ₂).M.mem_ker_iff_mulVec_zero _).mp (h hz)
  rw [show ((ρ₁ ⊗ᴹ ρ₂).M.mat).mulVec _ = _ from hkron ρ₁.M.mat ρ₂.M.mat u v] at hz'
  have hune : ρ₁.m.mulVec u ≠ 0 := fun h0 => by
    simpa using hu 0 ((ρ₁.M.mem_ker_iff_mulVec_zero u).mpr h0)
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hune
  refine (ρ₂.M.mem_ker_iff_mulVec_zero v).mpr (funext fun b => ?_)
  have h2 := congr_fun hz' (a, b)
  simp only [Pi.zero_apply, mul_eq_zero] at h2
  exact h2.resolve_left ha

/--
The kernel of a product state is contained in another product state's kernel iff the individual
kernels are contained.
-/
lemma ker_prod_le_iff (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker ↔ σ₁.M.ker ≤ ρ₁.M.ker ∧ σ₂.M.ker ≤ ρ₂.M.ker := by
  constructor <;> intro h;
  · exact ⟨ ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂ h, ker_le_of_ker_kron_le_right ρ₁ σ₁ ρ₂ σ₂ h ⟩;
  · convert! ker_kron_le_of_le _ _ _ _ h.1 h.2 using 1

--TODO: Generalize to RCLike.
omit [DecidableEq d₁] [DecidableEq d₂] in
lemma HermitianMat.inner_kron
    (A : HermitianMat d₁ ℂ) (B : HermitianMat d₂ ℂ) (C : HermitianMat d₁ ℂ) (D : HermitianMat d₂ ℂ) :
    ⟪A ⊗ₖ B, C ⊗ₖ D⟫ = ⟪A, C⟫ * ⟪B, D⟫ := by
  rw [← RCLike.ofReal_inj (K := ℂ), RCLike.ofReal_mul, HermitianMat.inner_eq_trace_rc,
    HermitianMat.inner_eq_trace_rc, HermitianMat.inner_eq_trace_rc, HermitianMat.kronecker_mat,
    HermitianMat.kronecker_mat, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

attribute [fun_prop] ContinuousAt.rpow

lemma continuousOn_rpow_uniform {K : Set ℝ} (hK : IsCompact K) :
    ContinuousOn (fun r : ℝ ↦ UniformOnFun.ofFun {K} (fun t : ℝ ↦ t ^ r)) (Set.Ioi 0) := by
  refine continuousOn_of_forall_continuousAt fun r hr => ?_
  rw [Set.mem_Ioi] at hr
  apply UniformOnFun.tendsto_iff_tendstoUniformlyOn.mpr
  simp only [Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, Metric.tendstoUniformlyOn_iff,
    Function.comp_apply, forall_eq]
  intro ε hεpos;
  have h_unif_cont : UniformContinuousOn (fun (p : ℝ × ℝ) => p.1 ^ p.2) (K ×ˢ Set.Icc (r / 2) (r * 2)) := by
    apply IsCompact.uniformContinuousOn_of_continuous
    · exact hK.prod CompactIccSpace.isCompact_Icc
    · refine continuousOn_of_forall_continuousAt fun p ⟨hp₁, ⟨hp₂₁, hp₂₂⟩⟩ ↦ ?_
      have _ : p.1 ≠ 0 ∨ 0 < p.2 := by right; linarith
      fun_prop (disch := assumption)
  rw [Metric.uniformContinuousOn_iff] at h_unif_cont
  obtain ⟨δ, hδpos, H⟩ := h_unif_cont ε hεpos
  filter_upwards [Ioo_mem_nhds (show r / 2 < r by linarith) (show r < r * 2 by linarith), Ioo_mem_nhds (show r - δ < r by linarith) (show r < r + δ by linarith)] with n ⟨_, _⟩ ⟨_, _⟩ x hx
  refine H (x, r) ⟨hx, ?_⟩ (x, n) ⟨hx, ?_⟩ ?_
  · constructor <;> linarith
  · constructor <;> linarith
  · have : |r - n| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    simpa

theorem sandwichedRelRentropy_additive_alpha_one_aux (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h1 : σ₁.M.ker ≤ ρ₁.M.ker) (h2 : σ₂.M.ker ≤ ρ₂.M.ker) :
    ⟪(ρ₁ ⊗ᴹ ρ₂).M, (ρ₁ ⊗ᴹ ρ₂).M.log - (σ₁ ⊗ᴹ σ₂).M.log⟫ =
    ⟪ρ₁.M, ρ₁.M.log - σ₁.M.log⟫_ℝ + ⟪ρ₂.M, ρ₂.M.log - σ₂.M.log⟫ := by
  have h_log_kron : (ρ₁ ⊗ᴹ ρ₂).M.log = ρ₁.M.log ⊗ₖ ρ₂.M.supportProj + ρ₁.M.supportProj ⊗ₖ ρ₂.M.log ∧ (σ₁ ⊗ᴹ σ₂).M.log = σ₁.M.log ⊗ₖ σ₂.M.supportProj + σ₁.M.supportProj ⊗ₖ σ₂.M.log := by
    constructor <;> apply HermitianMat.log_kron_with_proj;
  have h_inner_supportProj : ∀ (A : HermitianMat d₁ ℂ) (B : HermitianMat d₂ ℂ), ⟪A ⊗ₖ B, ρ₁ ⊗ᴹ ρ₂⟫ = ⟪A, ρ₁⟫ * ⟪B, ρ₂⟫ := by
    exact fun A B => HermitianMat.inner_kron A B ρ₁ ρ₂;
  simp only [HermitianMat.ker] at h1 h2
  simp_all only [inner_sub_right, inner_add_right, real_inner_comm,
    HermitianMat.inner_supportProj_self, MState.tr, mul_one, one_mul,
    HermitianMat.inner_supportProj_of_ker_le]
  abel

/-- The Sandwiched Renyi Relative Entropy, defined with ln (nits). Note that at `α = 1` this definition
  switch to the standard Relative Entropy, for continuity. For α ≤ 0, this gives junk value 0. (There
  is no conventional value for α < 0; there is a continuous limit at α = 0, but it is complicated and
  unneeded at the moment.)-/
def SandwichedRelRentropy (α : ℝ) (ρ σ : MState d) : ENNReal :=
  open Classical in
  if hα : 0 < α then
    if h : σ.M.ker ≤ ρ.M.ker
    then (.ofNNReal ⟨if α = 1 then
        ⟪ρ.M, ρ.M.log - σ.M.log⟫
      else
        ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1),
      sandwichedRelRentropy_nonneg hα h⟩)
    else ⊤
  else 0

notation "D̃_" α "(" ρ "‖" σ ")" => SandwichedRelRentropy α ρ σ

/-- The quantum relative entropy `𝐃(ρ‖σ) := Tr[ρ (log ρ - log σ)]`. Also called
the Umegaki quantum relative entropy, when it's necessary to distinguish from other
relative entropies. -/
def qRelativeEnt (ρ σ : MState d) : ENNReal :=
  D̃_1(ρ‖σ)

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

/--
The Sandwiched Renyi Relative entropy is additive for α=1 (standard relative entropy).
-/
private theorem sandwichedRelRentropy_additive_alpha_one (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ 1(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ 1(ρ₁‖σ₁) + D̃_ 1(ρ₂‖σ₂) := by
  by_cases h1 : σ₁.M.ker ≤ ρ₁.M.ker
  <;> by_cases h2 : σ₂.M.ker ≤ ρ₂.M.ker
  · simp only [SandwichedRelRentropy, ↓reduceIte, ↓reduceDIte, h1, h2]
    split_ifs <;> simp_all [ ker_prod_le_iff ];
    simp only [sandwichedRelRentropy_additive_alpha_one_aux ρ₁ σ₁ ρ₂ σ₂ h1 h2]
    rfl
  · simp only [SandwichedRelRentropy, zero_lt_one, ↓reduceDIte, ↓reduceIte, h1, h2,
      add_top, dite_eq_right_iff, ENNReal.coe_ne_top, imp_false]
    have := ker_prod_le_iff ρ₁ σ₁ ρ₂ σ₂
    tauto
  · simp only [SandwichedRelRentropy, zero_lt_one, ↓reduceDIte, ↓reduceIte, h1, h2,
      top_add, dite_eq_right_iff, ENNReal.coe_ne_top, imp_false]
    contrapose! h1
    exact (ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂) h1
  · simp only [SandwichedRelRentropy, zero_lt_one, ↓reduceDIte, ↓reduceIte, h1, h2,
      add_top, dite_eq_right_iff, ENNReal.coe_ne_top, imp_false]
    contrapose! h1
    exact (ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂) h1

lemma sandwiched_term_product (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) (α β : ℝ) :
    (((ρ₁ ⊗ᴹ ρ₂).M.conj ((σ₁ ⊗ᴹ σ₂).M ^ β).mat) ^ α).trace =
    ((ρ₁.M.conj (σ₁.M ^ β).mat) ^ α).trace * ((ρ₂.M.conj (σ₂.M ^ β).mat) ^ α).trace := by
  simp only [MState.prod]
  rw [← HermitianMat.trace_kronecker]
  rw [← HermitianMat.rpow_kron α ?_ ?_, ← HermitianMat.conj_kron,
    HermitianMat.rpow_kron β σ₁.nonneg σ₂.nonneg, HermitianMat.kronecker_mat]
  · exact HermitianMat.conj_nonneg _ ρ₁.nonneg
  · exact HermitianMat.conj_nonneg _ ρ₂.nonneg

/-
The Sandwiched Renyi Relative entropy is additive for alpha != 1.
-/
theorem sandwichedRelRentropy_additive_alpha_ne_one {α : ℝ} (hα : α ≠ 1) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  by_cases hα0 : 0 < α; swap
  · simp [SandwichedRelRentropy, hα0]
  by_cases h_ker : σ₁.M.ker ≤ ρ₁.M.ker ∧ σ₂.M.ker ≤ ρ₂.M.ker
  · simp_all [SandwichedRelRentropy]
    -- Apply the additivity of the trace term to split the logarithm into the sum of the logarithms.
    have h_trace_add : Real.log ((ρ₁ ⊗ᴹ ρ₂).M.conj ((σ₁ ⊗ᴹ σ₂).M ^ ((1 - α) / (2 * α))).mat ^ α).trace = Real.log ((ρ₁.M.conj (σ₁.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace + Real.log ((ρ₂.M.conj (σ₂.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace := by
      rw [ sandwiched_term_product, Real.log_mul ];
      · exact (sandwiched_trace_pos h_ker.1).ne'
      · exact (sandwiched_trace_pos h_ker.2).ne'
    split_ifs <;> simp_all
    · norm_num [ add_div ];
      exact rfl;
    · exact False.elim ( ‹¬ ( σ₁ ⊗ᴹ σ₂ |> MState.M |> HermitianMat.ker ) ≤ ( ρ₁ ⊗ᴹ ρ₂ |> MState.M |> HermitianMat.ker ) › ( by simpa [ HermitianMat.ker ] using ker_prod_le_iff _ _ _ _ |>.2 h_ker ) );
  · have h_ker_prod : ¬((σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker) := by
      simp_all  [ ker_prod_le_iff ]
    rw [not_and_or] at h_ker
    rcases h_ker with h_ker | h_ker
    · simp [SandwichedRelRentropy, h_ker_prod, h_ker, hα0]
    · simp [SandwichedRelRentropy, h_ker_prod, h_ker, hα0]

end additivity

/-- The Sandwiched Renyi Relative entropy is additive when the inputs are product states -/
@[simp]
theorem sandwichedRelRentropy_additive (α) (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ α(ρ₁‖σ₁) + D̃_ α(ρ₂‖σ₂) := by
  rcases eq_or_ne α 1 with rfl | hα
  · exact sandwichedRelRentropy_additive_alpha_one ρ₁ σ₁ ρ₂ σ₂
  · apply sandwichedRelRentropy_additive_alpha_ne_one hα

/-- The quantum relative entropy is additive when the inputs are product states -/
@[simp]
theorem qRelativeEnt_additive (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    𝐃(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂) := by
  --or `simp [SandwichedRelRentropy]`.
  exact sandwichedRelRentropy_additive_alpha_one ρ₁ σ₁ ρ₂ σ₂

@[simp]
theorem sandwichedRelRentropy_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    D̃_ α(ρ.relabel e‖σ.relabel e) = D̃_ α(ρ‖σ) := by
  simp only [SandwichedRelRentropy, MState.relabel_M]
  split_ifs <;> simp_all [HermitianMat.conj_submatrix] <;>
    exact (HermitianMat.ker_reindex_le_iff σ.M ρ.M e.symm).mp ‹_›

@[simp]
theorem sandwichedRelRentropy_self (hα : 0 < α) (ρ : MState d) :
  --Technically this holds for all α except for `-1` and `0`. But those are stupid.
  --TODO: Maybe SandwichedRelRentropy should actually be defined differently for α = 0?
    D̃_ α(ρ‖ρ) = 0 := by
  simp only [SandwichedRelRentropy, hα, ↓reduceDIte, Std.le_refl, sub_self, inner_zero_right,
      ENNReal.coe_eq_zero, NNReal.eq_iff, NNReal.coe_zero]
  simp [NNReal.toReal]
  intro hα1
  left; right; left
  have ht : (1 - α) / (2 * α) ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hα1)) (by positivity)
  have h2 : (1:ℝ) + 2 * ((1 - α) / (2 * α)) = 1 / α := by
    field_simp
    ring
  nth_rw 2 [← HermitianMat.rpow_one (A := ρ.M)]
  rw [HermitianMat.conj_rpow ρ.nonneg ht (h2.symm ▸ one_div_ne_zero hα.ne'),
    ← HermitianMat.rpow_mul ρ.nonneg, h2, one_div_mul_cancel hα.ne', HermitianMat.rpow_one]
  exact ρ.tr

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem sandwichedRelEntropy_ne_top {ρ σ : MState d} [σ.M.NonSingular] : D̃_ α(ρ‖σ) ≠ ⊤ := by
  by_cases 0 < α
  · simp [SandwichedRelRentropy, HermitianMat.nonSingular_ker_bot, *]
  · simp [SandwichedRelRentropy, *]

@[fun_prop]
lemma continuousOn_exponent : ContinuousOn (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 0) := by
  fun_prop (disch := intros; linarith [Set.mem_Ioi.mp ‹_›])

@[fun_prop]
lemma Complex.continuousOn_cpow_const_Ioi (z : ℂ) :
    ContinuousOn (fun r : ℝ => z ^ (r : ℂ)) (Set.Ioi 0) := by
  apply ContinuousOn.const_cpow (f := Complex.ofReal)
  · fun_prop
  · grind [ofReal_ne_zero]

/--
The function α ↦ (1 - α) / (2 * α) maps the interval (1, ∞) to (-∞, 0).
-/
lemma maps_to_Iio_of_Ioi_1 : Set.MapsTo (fun α : ℝ => (1 - α) / (2 * α)) (Set.Ioi 1) (Set.Iio 0) := by
  intro x hx
  rw [Set.mem_Ioi] at hx
  rw [Set.mem_Iio]
  have h1 : 1 - x < 0 := by linarith
  have h2 : 0 < 2 * x := by linarith
  exact div_neg_of_neg_of_pos h1 h2

--PR'ed: #35494
@[simp]
theorem frontier_singleton {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (p : X) : frontier {p} = {p} := by
  simp [frontier]

private theorem sandwichedRelRentropy.continuousOn_Ioi_1_aux (ρ σ : MState d) :
    ContinuousOn (fun (α : ℝ) ↦ ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α)) (Set.Ioi 1) := by
  have h1 : ContinuousOn (fun α : ℝ => (σ.M ^ ((1 - α) / (2 * α))).mat) (Set.Ioi 1) :=
    HermitianMat.continuous_mat.comp_continuousOn <| (σ.M.continuousOn_rpow_neg).comp
      (continuousOn_exponent.mono fun x hx => Set.mem_Ioi.mpr (zero_lt_one.trans hx))
      maps_to_Iio_of_Ioi_1
  exact HermitianMat.continuousOn_rpow_joint_nonneg_pos (by fun_prop) continuousOn_id
    fun x hx => zero_lt_one.trans (Set.mem_Ioi.mp hx)

private theorem sandwichedRelRentropy.continuousOn_Ioi_1 (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 1) := by
  dsimp [SandwichedRelRentropy]
  split_ifs with hρ
  · rw [continuousOn_congr (f := fun α ↦ ENNReal.ofReal
      (Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1)))]
    · apply (ENNReal.continuous_ofReal).comp_continuousOn
      apply ContinuousOn.div₀
      · apply ContinuousOn.log
        · exact HermitianMat.trace_Continuous.comp_continuousOn
            (continuousOn_Ioi_1_aux ρ σ)
        · intro x hx
          apply LT.lt.ne'
          grw [← sandwiched_trace_of_gt_1 hρ hx]
          exact zero_lt_one
      · fun_prop
      · clear hρ; grind
    · intro α (hα : 1 < α)
      dsimp only
      have hα₀ : 0 < α := by linarith
      have hα₁ : α ≠ 1 := by linarith
      simp only [dif_pos hα₀, if_neg hα₁, ENNReal.ofReal]
      rw [Real.toNNReal_of_nonneg]
      rfl
  · rw [continuousOn_congr (f := fun α ↦ ⊤)]
    · fun_prop
    · clear ρ σ hρ;
      grind only [→ Set.EqOn.eq_of_mem, = Set.mem_Ioi, Set.EqOn, cases Or]

private theorem sandwichedRelRentropy.continuousOn_Ioo_0_1_aux (ρ σ : MState d) :
    ContinuousOn (fun (α : ℝ) ↦ ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α)) (Set.Ioo 0 1) := by
  have h1 : ContinuousOn (fun α : ℝ => (σ.M ^ ((1 - α) / (2 * α))).mat) (Set.Ioo 0 1) :=
    HermitianMat.continuous_mat.comp_continuousOn <| (σ.M.continuousOn_rpow_pos).comp
      (continuousOn_exponent.mono fun x hx => Set.mem_Ioi.mpr hx.1)
      fun x hx => Set.mem_Ioi.mpr (div_pos (by linarith [hx.2]) (by linarith [hx.1]))
  exact HermitianMat.continuousOn_rpow_joint_nonneg_pos (by fun_prop) continuousOn_id
    fun x hx => hx.1

/-- Continuity on (0,1): the sandwich relative Rényi entropy is continuous in α on (0,1). -/
private theorem sandwichedRelRentropy.continuousOn_Ioo_0_1 (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioo 0 1) := by
  dsimp [SandwichedRelRentropy]
  split_ifs with hρ
  · rw [continuousOn_congr (f := fun α ↦ ENNReal.ofReal
      (Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1)))]
    · apply (ENNReal.continuous_ofReal).comp_continuousOn
      apply ContinuousOn.div₀
      · apply ContinuousOn.log
        · exact HermitianMat.trace_Continuous.comp_continuousOn
            (continuousOn_Ioo_0_1_aux ρ σ)
        · intro x hx
          exact (sandwiched_trace_pos hρ).ne'
      · fun_prop
      · intro x hx; exact sub_ne_zero.mpr (ne_of_lt hx.2)
    · intro α hα
      dsimp only
      have hα₀ : 0 < α := hα.1
      have hα₁ : α ≠ 1 := ne_of_lt hα.2
      split_ifs
      · norm_cast
      · rw [ENNReal.ofReal, Real.toNNReal_of_nonneg]
        rfl
  · rw [continuousOn_congr (f := fun α ↦ ⊤)]
    · fun_prop
    · intro x hx
      dsimp only
      simp [hx.1]

/-- Continuity at 1: the sandwich relative Rényi entropy is continuous at α = 1. -/
private theorem sandwichedRelRentropy.continuousAt_1 (ρ σ : MState d) :
    ContinuousWithinAt (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 0) 1 := by
  by_cases h : σ.M.ker ≤ ρ.M.ker
  · simp only [ContinuousWithinAt, SandwichedRelRentropy, dif_pos h, zero_lt_one, if_true]
    -- Use the fact that the limit of the real-valued function is the inner product.
    have h_real_limit : Filter.Tendsto (fun α : ℝ => if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫ else Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1)) (nhdsWithin 1 (Set.Ioi 0)) (nhds ⟪ρ.M, ρ.M.log - σ.M.log⟫) := by
      have h_real_limit : Filter.Tendsto (fun α : ℝ => Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1)) (nhdsWithin 1 (Set.Ioi 0 \ {1})) (nhds ⟪ρ.M, ρ.M.log - σ.M.log⟫) := by
        exact sandwichedRelRentropy.limit_at_one ρ σ h
      rw [ Metric.tendsto_nhdsWithin_nhds ] at *
      intro ε hε
      rcases h_real_limit ε hε with ⟨δ, hδ, H⟩
      use δ, hδ
      intro x hx₁ hx₂
      by_cases hx₃ : x = 1 <;> simp [*]
    -- Since the real-valued function tends to the inner product, the ENNReal version should also tend to the same limit because the ENNReal conversion is continuous.
    have h_ennreal_limit : Filter.Tendsto (fun α : ℝ => ENNReal.ofReal (if α = 1 then ⟪ρ.M, ρ.M.log - σ.M.log⟫ else Real.log ((HermitianMat.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ρ.M ^ α).trace / (α - 1))) (nhdsWithin 1 (Set.Ioi 0)) (nhds (ENNReal.ofReal ⟪ρ.M, ρ.M.log - σ.M.log⟫)) := by
      exact (ENNReal.tendsto_ofReal h_real_limit).comp Filter.tendsto_id
    convert h_ennreal_limit.congr' _ using 2
    · symm
      apply ENNReal.ofReal_eq_coe_nnreal
    · filter_upwards [self_mem_nhdsWithin] with α (hα : 0 < α)
      simp only [ENNReal.ofReal, ENNReal.coe_inj, hα, ↓reduceDIte]
      exact Real.toNNReal_of_nonneg _
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with α hα
    simp only [SandwichedRelRentropy, Set.mem_Ioi.mp hα, zero_lt_one, dif_neg h]

@[fun_prop]
theorem sandwichedRelRentropy.continuousOn (ρ σ : MState d) :
    ContinuousOn (fun α => D̃_ α(ρ‖σ)) (Set.Ioi 0) := by
  --If this turns out too hard, we just need `ContinousAt f 1`.
  --If that's still too hard, we really _just_ need that `(𝓝[>] 1).Tendsto f (𝓝 (f 1))`.
  intro α hα
  rcases lt_trichotomy α 1 with hα1 | rfl | hα1
  · have h := sandwichedRelRentropy.continuousOn_Ioo_0_1 ρ σ
    exact (h.continuousAt (Ioo_mem_nhds hα hα1)).continuousWithinAt
  · exact sandwichedRelRentropy.continuousAt_1 ρ σ
  · have h := sandwichedRelRentropy.continuousOn_Ioi_1 ρ σ
    exact (h.continuousAt (Ioi_mem_nhds hα1)).continuousWithinAt

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are contained. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simp [qRelativeEnt, SandwichedRelRentropy, h, EReal.coe_nnreal_eq_coe_real]
  norm_cast

/-- The quantum relative entropy is finite exactly when the support condition
`σ.M.ker ≤ ρ.M.ker` holds. -/
theorem qRelativeEnt_ne_top_iff {ρ σ : MState d} : 𝐃(ρ‖σ) ≠ ⊤ ↔ σ.M.ker ≤ ρ.M.ker := by
  rw [qRelativeEnt, SandwichedRelRentropy]
  simp only [zero_lt_one, ↓reduceDIte]
  split_ifs with h <;> simp [h]

/-- The quantum relative entropy is `⊤` exactly when the support condition fails. -/
theorem qRelativeEnt_eq_top_iff {ρ σ : MState d} : 𝐃(ρ‖σ) = ⊤ ↔ ¬ σ.M.ker ≤ ρ.M.ker := by
  simpa using (not_congr (qRelativeEnt_ne_top_iff (ρ := ρ) (σ := σ)))

open Classical in
theorem qRelativeEnt_eq_neg_Sᵥₙ_add (ρ σ : MState d) :
    (qRelativeEnt ρ σ).toEReal = -(Sᵥₙ ρ : EReal) +
      if σ.M.ker ≤ ρ.M.ker then (-⟪ρ.M, σ.M.log⟫ : EReal) else (⊤ : EReal) := by
  by_cases h : σ.M.ker ≤ ρ.M.ker
  · simp [h, Sᵥₙ_eq_neg_trace_log, qRelativeEnt_ker, inner_sub_right]
    rw [real_inner_comm, sub_eq_add_neg]
  · simp [h, qRelativeEnt, SandwichedRelRentropy]

/-- The quantum relative entropy is unchanged by `MState.relabel` -/
@[simp]
theorem qRelativeEnt_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    𝐃(ρ.relabel e‖σ.relabel e) = 𝐃(ρ‖σ) := by
  simp [qRelativeEnt]

@[simp]
theorem sandwichedRelRentropy_of_unique [Unique d] (ρ σ : MState d) :
    D̃_α(ρ‖σ) = 0 := by
  rcases Subsingleton.allEq ρ default
  rcases Subsingleton.allEq σ default
  simp [SandwichedRelRentropy]
  intro
  rfl

@[simp]
theorem qRelEntropy_of_unique [Unique d] (ρ σ : MState d) :
    𝐃(ρ‖σ) = 0 := by
  exact sandwichedRelRentropy_of_unique ρ σ

theorem sandwichedRelRentropy_heq_congr
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  --Why does this thm need to exist? Why not just `subst d₁` and `simp [heq_eq_eq]`? Well, even though d₁
  --and d₂ are equal, we then end up with two distinct instances of `Fintype d₁` and `DecidableEq d₁`,
  --and ρ₁ and ρ₂ refer to them each and so have different types. And then we'd need to `subst` those away
  --too. This is kind of tedious, so it's better to just have this theorem around.
  rw [heq_iff_exists_eq_cast] at hρ hσ
  obtain ⟨_, rfl⟩ := hρ
  obtain ⟨_, rfl⟩ := hσ
  simp [← MState.relabel_cast _ hd]

theorem sandwichedRelRentropy_congr {α : ℝ}
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂)
        (hρ : ρ₁ = ρ₂.relabel (Equiv.cast hd)) (hσ : σ₁ = σ₂.relabel (Equiv.cast hd)) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  subst ρ₁ σ₁
  simp

theorem qRelEntropy_heq_congr {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    𝐃(ρ₁‖σ₁) = 𝐃(ρ₂‖σ₂) := by
  exact sandwichedRelRentropy_heq_congr hd hρ hσ

/-- Quantum relative entropy when σ has full rank -/
theorem qRelativeEnt_rank {ρ σ : MState d} [σ.M.NonSingular] :
    (𝐃(ρ‖σ) : EReal) = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  apply qRelativeEnt_ker
  simp [HermitianMat.nonSingular_ker_bot]

section lowerSemicontinuous_1

variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped InnerProductSpace RealInnerProductSpace HermitianMat

private def approxLog (N : ℕ) : ℝ → ℝ := fun t => Real.log (max t (Real.exp (-(N : ℝ))))

private lemma approxLog_continuous (N : ℕ) : Continuous (approxLog N) := by
  have h_cont : Continuous (fun t : ℝ => max t (Real.exp (-N))) :=
    Continuous.max continuous_id continuous_const
  exact Continuous.log h_cont (fun x => ne_of_gt (lt_max_of_lt_right (Real.exp_pos _)))

private lemma approxLog_ge_log_pos {t : ℝ} (ht : 0 < t) (N : ℕ) :
    Real.log t ≤ approxLog N t := by
  unfold approxLog
  exact Real.log_le_log ht (le_max_left _ _)

private lemma continuous_inner_cfc_approxLog (ρ : MState d) (N : ℕ) :
    Continuous (fun σ : MState d => ⟪ρ.M, σ.M.cfc (approxLog N)⟫) := by
  refine Continuous.comp ?_ ?_
  · fun_prop (disch := solve_by_elim)
  · exact (HermitianMat.cfc_continuous (approxLog_continuous N)).comp continuous_induced_dom

private lemma approxLog_tendsto_at_pos {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun N : ℕ => approxLog N t) Filter.atTop (nhds (Real.log t)) := by
  refine' Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [Filter.eventually_gt_atTop ⌈-Real.log t⌉₊] with N hN
  unfold approxLog
  rw [max_eq_left (by rw [← Real.log_le_log_iff (by positivity) (by positivity)]; linarith [Nat.le_ceil (-Real.log t), show (N : ℝ) ≥ ⌈-Real.log t⌉₊ + 1 by exact_mod_cast hN, Real.log_exp (-N)])]

open ComplexOrder in
private lemma inner_cfc_approxLog_ge (ρ σ : MState d) (N : ℕ) (hσ : σ.M.ker ≤ ρ.M.ker) :
    ⟪ρ.M, σ.M.log⟫ ≤ ⟪ρ.M, σ.M.cfc (approxLog N)⟫ := by
  rw [inner_cfc_eq_sum_eigenWeight, show σ.M.log = σ.M.cfc Real.log from rfl, inner_cfc_eq_sum_eigenWeight]
  apply Finset.sum_le_sum
  intro i _
  have hpsd : σ.M.mat.PosSemidef := by
    have h := σ.pos.le
    rwa [HermitianMat.le_iff, sub_zero] at h
  have hei_nn : 0 ≤ σ.M.H.eigenvalues i := hpsd.eigenvalues_nonneg i
  by_cases hei : σ.M.H.eigenvalues i = 0
  · rw [eigenWeight_zero_of_eigenvalue_zero hσ hei, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (approxLog_ge_log_pos (lt_of_le_of_ne hei_nn (Ne.symm hei)) N)
      (eigenWeight_nonneg ρ σ i)

open ComplexOrder in
private lemma tendsto_inner_cfc_approxLog (ρ x : MState d) (hx : x.M.ker ≤ ρ.M.ker) :
    Filter.Tendsto (fun N : ℕ => ⟪ρ.M, x.M.cfc (approxLog N)⟫)
      Filter.atTop (nhds ⟪ρ.M, x.M.log⟫) := by
  rw [show x.M.log = x.M.cfc Real.log from rfl, inner_cfc_eq_sum_eigenWeight]
  simp_rw [inner_cfc_eq_sum_eigenWeight]
  apply tendsto_finsetSum
  intro i _
  have hpsd : x.M.mat.PosSemidef := by
    have h := x.pos.le
    rwa [HermitianMat.le_iff, sub_zero] at h
  have hei_nn : 0 ≤ x.M.H.eigenvalues i := hpsd.eigenvalues_nonneg i
  by_cases hei : x.M.H.eigenvalues i = 0
  · simp [eigenWeight_zero_of_eigenvalue_zero hx hei]
  · exact (approxLog_tendsto_at_pos (lt_of_le_of_ne hei_nn (Ne.symm hei))).mul_const _

lemma inner_log_bounded_near (hx : σ.M.ker ≤ ρ.M.ker) {y : ℝ} (hy : ⟪ρ.M, σ.M.log⟫ < y) :
    ∀ᶠ x in nhds σ, x.M.ker ≤ ρ.M.ker → ⟪ρ.M, x.M.log⟫ < y := by
  have h_tendsto := tendsto_inner_cfc_approxLog ρ σ hx
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ⟪ρ.M, σ.M.cfc (approxLog N)⟫ < y := by
    by_contra h
    push Not at h
    exact absurd (lt_of_lt_of_le hy (ge_of_tendsto h_tendsto (Filter.Eventually.of_forall h)))
      (lt_irrefl _)
  have h_cont := continuous_inner_cfc_approxLog ρ N
  have h_lt : ∀ᶠ x in nhds σ, ⟪ρ.M, x.M.cfc (approxLog N)⟫ < y :=
    h_cont.continuousAt.eventually (gt_mem_nhds hN)
  filter_upwards [h_lt] with σ hσ_lt hσ_ker
  exact lt_of_le_of_lt (inner_cfc_approxLog_ge ρ σ N hσ_ker) hσ_lt

end lowerSemicontinuous_1

section lowerSemicontinuous_2

variable {d : Type*} [Fintype d] [DecidableEq d]

open scoped InnerProductSpace RealInnerProductSpace HermitianMat

private lemma eigenWeight_eq_zero_iff (ρ x : MState d) (i : d) :
    eigenWeight ρ x i = 0 ↔ (x.M.H.eigenvectorBasis i : EuclideanSpace ℂ d) ∈ ρ.M.ker := by
  have hpsd := (Matrix.posSemidef_iff_dotProduct_mulVec.mp (HermitianMat.zero_le_iff.mp
    ρ.nonneg)).2 (x.M.H.eigenvectorBasis i)
  constructor
  · intro h0
    refine HermitianMat.mem_ker_of_inner_mulVec_zero ρ.nonneg _ (Complex.ext ?_ ?_)
    · simpa [eigenWeight, Matrix.dotProduct_mulVec] using h0
    · simpa [Complex.le_def, eq_comm] using hpsd.2
  · intro h
    have h0 := (ρ.M.mem_ker_iff_mulVec_zero _).mp h
    simp only [MState.mat_M] at h0
    simp [eigenWeight, ← Matrix.dotProduct_mulVec, h0]

set_option backward.isDefEq.respectTransparency false in
private lemma ker_le_iff_eigenWeight_zero (ρ x : MState d) :
    x.M.ker ≤ ρ.M.ker ↔ ∀ i, x.M.H.eigenvalues i = 0 → eigenWeight ρ x i = 0 := by
  constructor
  · exact fun h i ↦ eigenWeight_zero_of_eigenvalue_zero h
  · intro h v hv
    have hv0 := (x.M.mulVec_eq_zero_iff_inner_eigenvector_zero v).mp
      ((x.M.mem_ker_iff_mulVec_zero v).mp hv)
    rw [← x.M.H.eigenvectorBasis.sum_repr v]
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases eq_or_ne (x.M.H.eigenvalues i) 0 with hi | hi
    · exact Submodule.smul_mem _ _ ((eigenWeight_eq_zero_iff ρ x i).mp (h i hi))
    · rw [OrthonormalBasis.repr_apply_apply, hv0 i hi]
      simp

private lemma neg_ker_exists_eigenWeight_pos (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) :
    ∃ i, x.M.H.eigenvalues i = 0 ∧ 0 < eigenWeight ρ x i := by
  -- By `ker_le_iff_eigenWeight_zero`, ¬(x.M.ker ≤ ρ.M.ker) iff ∃ i, eigenvalue_i = 0 ∧ eigenWeight ≠ 0. Use this fact.
  have h_eigenWeight_ne_zero : ∃ i, x.M.H.eigenvalues i = 0 ∧ eigenWeight ρ x i ≠ 0 := by
    exact Classical.not_forall_not.1 fun h => hx <| by simpa using ker_le_iff_eigenWeight_zero ρ x |>.2 fun i hi => Classical.not_not.1 fun hi' => h i ⟨ hi, hi' ⟩ ;
  exact h_eigenWeight_ne_zero.imp fun i hi => ⟨ hi.1, lt_of_le_of_ne ( eigenWeight_nonneg ρ x i ) hi.2.symm ⟩

private lemma approxLog_at_zero (N : ℕ) : approxLog N 0 = -(N : ℝ) := by
  simp [approxLog, max_eq_right (Real.exp_pos (-N)).le]

private lemma inner_cfc_approxLog_tendsto_bot (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) :
    Filter.Tendsto (fun N : ℕ => ⟪ρ.M, x.M.cfc (approxLog N)⟫) Filter.atTop Filter.atBot := by
  have h_split_sum : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.univ.filter (fun i => x.M.H.eigenvalues i = 0), approxLog N (x.M.H.eigenvalues i) * eigenWeight ρ x i) Filter.atTop Filter.atBot := by
    have h_split_sum : Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.univ.filter (fun i => x.M.H.eigenvalues i = 0), (-↑N) * eigenWeight ρ x i) Filter.atTop Filter.atBot := by
      have h_split_sum : ∑ i ∈ Finset.univ.filter (fun i => x.M.H.eigenvalues i = 0), eigenWeight ρ x i > 0 := by
        obtain ⟨ i, hi, hi' ⟩ := neg_ker_exists_eigenWeight_pos ρ x hx; exact lt_of_lt_of_le hi' ( Finset.single_le_sum ( fun i _ => eigenWeight_nonneg ρ x i ) ( by aesop ) ) ;
      simp_rw [← Finset.mul_sum, neg_mul]
      exact Filter.tendsto_neg_atTop_atBot.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const h_split_sum)
    apply h_split_sum.congr'
    filter_upwards [ Filter.eventually_gt_atTop 0 ] with N hN
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [ show approxLog N ( x.M.H.eigenvalues i ) = -↑N from by rw [ show x.M.H.eigenvalues i = 0 from Finset.mem_filter.mp hi |>.2 ] ; exact approxLog_at_zero N ] ;
  convert h_split_sum.atBot_add ( show Filter.Tendsto ( fun N : ℕ => ∑ i ∈ Finset.univ.filter ( fun i => x.M.H.eigenvalues i ≠ 0 ), approxLog N ( x.M.H.eigenvalues i ) * eigenWeight ρ x i ) Filter.atTop ( nhds ( ∑ i ∈ Finset.univ.filter ( fun i => x.M.H.eigenvalues i ≠ 0 ), Real.log ( x.M.H.eigenvalues i ) * eigenWeight ρ x i ) ) from ?_ ) using 2;
  · rw [ inner_cfc_eq_sum_eigenWeight, Finset.sum_filter_add_sum_filter_not ];
  · apply tendsto_finsetSum
    intro i hi
    exact Filter.Tendsto.mul ((approxLog_tendsto_at_pos ( show 0 < x.M.H.eigenvalues i from lt_of_le_of_ne (x.eigenvalue_nonneg i) (Ne.symm (by aesop))))) tendsto_const_nhds

end lowerSemicontinuous_2

open Classical in
theorem qRelativeEnt_lowerSemicontinuous_2 (ρ x : MState d) (hx : ¬(x.M.ker ≤ ρ.M.ker)) (y : ENNReal) (hy : y < ⊤) :
    ∀ᶠ (x' : MState d) in nhds x,
      y < (if x'.M.ker ≤ ρ.M.ker then ⟪ρ.M, ρ.M.log - x'.M.log⟫ else ⊤ : EReal) := by
  -- Since $y < \top$, we can choose a neighborhood around $x$ where the inner product is less than $y$.
  have h_inner_lt_y : ∀ᶠ x' in nhds x, x'.M.ker ≤ ρ.M.ker → ⟪ρ.M, ρ.M.log - x'.M.log⟫ > y.toReal := by
    have h_inner_lt_y : Filter.Tendsto (fun N : ℕ => ⟪ρ.M, ρ.M.log - x.M.cfc (approxLog N)⟫) Filter.atTop Filter.atTop := by
      have h_inner_lt_y : Filter.Tendsto (fun N : ℕ => ⟪ρ.M, ρ.M.log⟫ - ⟪ρ.M, x.M.cfc (approxLog N)⟫) Filter.atTop Filter.atTop := by
        exact Filter.Tendsto.add_atTop tendsto_const_nhds ( Filter.tendsto_neg_atBot_atTop.comp ( inner_cfc_approxLog_tendsto_bot ρ x hx ) ) |> Filter.Tendsto.congr ( by aesop ) ;
      convert h_inner_lt_y using 1
      ext1 N
      simp [inner_sub_right]
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ⟪ρ.M, ρ.M.log - x.M.cfc (approxLog N)⟫ > y.toReal := by
      exact (h_inner_lt_y.eventually_gt_atTop _ ).exists
    have h_cont : Continuous (fun σ : MState d => ⟪ρ.M, ρ.M.log - σ.M.cfc (approxLog N)⟫) := by
      simp only [inner_sub_right]
      exact continuous_const.sub (continuous_inner_cfc_approxLog ρ N)
    have h_cont : ∀ᶠ x' in nhds x, ⟪ρ.M, ρ.M.log - x'.M.cfc (approxLog N)⟫ > y.toReal := by
      exact h_cont.continuousAt.eventually ( lt_mem_nhds hN ) |> fun h => h.mono fun x' hx' => hx' |> fun hx'' => by simpa using hx'';
    filter_upwards [h_cont] with x' hx' hx''
    apply lt_of_lt_of_le hx'
    have h_inner_le : ⟪ρ.M, x'.M.log⟫ ≤ ⟪ρ.M, x'.M.cfc (approxLog N)⟫ := by
      exact inner_cfc_approxLog_ge ρ x' N hx''
    rw [inner_sub_right, inner_sub_right]
    exact sub_le_sub_left h_inner_le _
  filter_upwards [ h_inner_lt_y ] with x' hx';
  split_ifs <;> simp_all [ ENNReal.toReal ];
  · convert ENNReal.ofReal_lt_ofReal_iff (show 0 < ⟪ρ.M, ρ.M.log - x'.M.log⟫ from lt_of_le_of_lt (by positivity) hx' ) |>.2 hx' using 1
    cases y
    · simp at hy
    simp only [ENNReal.ofReal, ENNReal.toNNReal_coe, Real.toNNReal_coe, ENNReal.coe_lt_coe]
    rw [← NNReal.coe_lt_coe, Real.toNNReal_of_nonneg (le_trans (by positivity) hx'.le)]
    simp [← ENNReal.ofReal_coe_nnreal]
  · rw [lt_top_iff_ne_top, ne_eq] at hy ⊢
    rwa [EReal.coe_ennreal_eq_top_iff]

/-
Relative entropy is lower semicontinuous (in each argument, actually, but we only need in the
latter here). Will need the fact that all the cfc / eigenvalue stuff is continuous, plus
carefully handling what happens with the kernel subspace, which will make this a pain.
-/
@[fun_prop]
theorem qRelativeEnt.lowerSemicontinuous (ρ : MState d) : LowerSemicontinuous fun σ => 𝐃(ρ‖σ) := by
  simp_rw [qRelativeEnt, SandwichedRelRentropy, if_true, lowerSemicontinuous_iff]
  simp only [zero_lt_one, ↓reduceDIte]
  intro x
  by_cases hx : x.M.ker ≤ ρ.M.ker
  · intro y hy
    obtain ⟨y', hy'⟩ : ∃ y' : ℝ, y < ENNReal.ofReal y' ∧ y' < ⟪ρ.M, ρ.M.log - x.M.log⟫ := by
      rcases ENNReal.lt_iff_exists_real_btwn.mp hy with ⟨ y', hy₁, hy₂ ⟩;
      rw [ ENNReal.ofReal_lt_iff_lt_toReal ] at hy₂ <;> aesop;
    simp only [↓reduceDIte, inner_sub_right, hx] at hy hy' ⊢
    have := inner_log_bounded_near hx (y := ⟪ρ.M, ρ.M.log⟫ - y') (by linarith)
    filter_upwards [this] with σ hσ
    split
    · simp_all only [ENNReal.ofReal, forall_const]
      apply lt_of_lt_of_le hy'.1
      refine mod_cast max_le (a := y') (b := 0) (c := ⟪ρ.M, ρ.M.log⟫ - ⟪ρ.M, σ.M.log⟫) ?_ ?_
      · linarith
      · linarith [ show 0 ≤ y' from le_of_not_gt fun h => by norm_num [ Real.toNNReal_of_nonpos h.le ] at hy' ]
    · exact hy'.1.trans_le (by simp)
  · intro y hy
    simp only [hx, ↓reduceDIte] at hy ⊢
    have h₂ := qRelativeEnt_lowerSemicontinuous_2 ρ x hx y hy
    filter_upwards [h₂] with x' hx'
    split_ifs with h₁ junk
    · simp_all only [gt_iff_lt, ← EReal.coe_ennreal_lt_coe_ennreal_iff, EReal.coe_ennreal_top,
      ↓reduceIte]
      exact hx'
    · simp at junk
    · exact hy

@[simp]
theorem qRelEntropy_self (ρ : MState d) : 𝐃(ρ‖ρ) = 0 := by
  simp [qRelativeEnt]

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem qRelativeEnt_ne_top {ρ σ : MState d} [σ.M.NonSingular] : 𝐃(ρ‖σ) ≠ ⊤ := by
  rw [qRelativeEnt]
  finiteness

omit [DecidableEq dA] in
open HermitianMat in
private lemma inner_kron_one_eq_inner_traceRight
    (A : HermitianMat dA ℂ) (M : HermitianMat (dA × dB) ℂ) :
    ⟪A ⊗ₖ (1 : HermitianMat dB ℂ), M⟫ = ⟪A, M.traceRight⟫ := by
  rw [inner_comm, inner_eq_re_trace, inner_eq_re_trace]
  exact (congrArg Complex.re (Matrix.trace_mul_kron_one_right M.mat A.mat)).trans <| by
    simpa using congrArg Complex.re (Matrix.trace_mul_comm M.traceRight.mat A.mat)

omit [DecidableEq dB] in
open HermitianMat in
private lemma inner_one_kron_eq_inner_traceLeft
    (B : HermitianMat dB ℂ) (M : HermitianMat (dA × dB) ℂ) :
    ⟪(1 : HermitianMat dA ℂ) ⊗ₖ B, M⟫ = ⟪B, M.traceLeft⟫ := by
  rw [inner_comm, inner_eq_re_trace, inner_eq_re_trace]
  exact (congrArg Complex.re (Matrix.trace_mul_one_kron_right M.mat B.mat)).trans <| by
    simpa using congrArg Complex.re (Matrix.trace_mul_comm M.traceLeft.mat B.mat)

private lemma fixed_support_kron_right (ρ : MState (dA × dB))
    {x : EuclideanSpace ℂ (dA × dB)} (hx : x ∈ ρ.M.support) :
    (ρ.traceRight.M.supportProj ⊗ₖ (1 : HermitianMat dB ℂ)).lin x = x := by
  set K : HermitianMat (dA × dB) ℂ := ρ.traceRight.M.kerProj ⊗ₖ (1 : HermitianMat dB ℂ) with hKdef
  have hKx : x ∈ K.ker := by
    refine (HermitianMat.inner_zero_iff ρ.nonneg (HermitianMat.kronecker_nonneg
      (by simpa [HermitianMat.kerProj] using
        (HermitianMat.projector_nonneg (S := ρ.traceRight.M.ker)))
      (by rw [HermitianMat.zero_le_iff]; exact Matrix.PosSemidef.one))).1 ?_ hx
    rw [HermitianMat.inner_comm, inner_kron_one_eq_inner_traceRight, HermitianMat.inner_comm]
    simpa [hKdef, MState.exp_val] using
      (ρ.traceRight.exp_val_eq_zero_iff (by simpa [HermitianMat.kerProj] using
        (HermitianMat.projector_nonneg (S := ρ.traceRight.M.ker)))).2 (by simp)
  have hsum : K + ρ.traceRight.M.supportProj ⊗ₖ (1 : HermitianMat dB ℂ) = 1 := by
    rw [hKdef, ← HermitianMat.add_kronecker, ρ.traceRight.M.kerProj_add_supportProj,
      HermitianMat.kronecker_one_one]
  have key := congrArg (fun T : HermitianMat (dA × dB) ℂ => T.lin x) hsum
  simpa [HermitianMat.lin, HermitianMat.mat_add, map_add, LinearMap.add_apply,
    Matrix.toLpLin_apply, (K.mem_ker_iff_mulVec_zero x).1 hKx] using key

private lemma fixed_support_kron_left (ρ : MState (dA × dB))
    {x : EuclideanSpace ℂ (dA × dB)} (hx : x ∈ ρ.M.support) :
    ((1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.supportProj).lin x = x := by
  let K : HermitianMat (dA × dB) ℂ := (1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.kerProj
  let P : HermitianMat (dA × dB) ℂ := (1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.supportProj
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact HermitianMat.kronecker_nonneg
      (by rw [HermitianMat.zero_le_iff]; exact Matrix.PosSemidef.one)
      (by simpa [HermitianMat.kerProj] using
        (HermitianMat.projector_nonneg (S := ρ.traceLeft.M.ker)))
  have hsum : K + P = 1 := by
    simp only [K, P, ← HermitianMat.kronecker_add, ρ.traceLeft.M.kerProj_add_supportProj,
      HermitianMat.kronecker_one_one]
  have hKx : x ∈ K.ker := by
    refine (HermitianMat.inner_zero_iff ρ.nonneg hK_nonneg).1 ?_ hx
    rw [HermitianMat.inner_comm, inner_one_kron_eq_inner_traceLeft, HermitianMat.inner_comm]
    simpa [K, MState.exp_val] using
      (ρ.traceLeft.exp_val_eq_zero_iff (by simpa [HermitianMat.kerProj] using
        (HermitianMat.projector_nonneg (S := ρ.traceLeft.M.ker)))).2 (by simp)
  have key := congrArg (fun T : HermitianMat (dA × dB) ℂ => T.lin x) hsum
  simpa [P, HermitianMat.lin, HermitianMat.mat_add, map_add, LinearMap.add_apply,
    Matrix.toLpLin_apply, (K.mem_ker_iff_mulVec_zero x).1 hKx] using key

/-- `I(A:B) = 𝐃(ρᴬᴮ‖ρᴬ ⊗ ρᴮ)` -/
theorem qMutualInfo_as_qRelativeEnt (ρ : MState (dA × dB)) :
    qMutualInfo ρ = (𝐃(ρ‖ρ.traceRight ⊗ᴹ ρ.traceLeft) : EReal) := by
  have fixed_support_kron_prod : ∀ {x : EuclideanSpace ℂ (dA × dB)},
      x ∈ ρ.M.support →
        (ρ.traceRight.M.supportProj ⊗ₖ ρ.traceLeft.M.supportProj).lin x = x := by
    intro x hx
    let A : Matrix (dA × dB) (dA × dB) ℂ :=
      Matrix.kroneckerMap (· * ·) ρ.traceRight.M.supportProj.mat (1 : Matrix dB dB ℂ)
    let B : Matrix (dA × dB) (dA × dB) ℂ :=
      Matrix.kroneckerMap (· * ·) (1 : Matrix dA dA ℂ) ρ.traceLeft.M.supportProj.mat
    have hxA' : A.toEuclideanLin x = x := by
      simpa [A, HermitianMat.lin, Matrix.toEuclideanLin] using fixed_support_kron_right ρ hx
    have hxB' : B.toEuclideanLin x = x := by
      simpa [B, HermitianMat.lin, Matrix.toEuclideanLin] using fixed_support_kron_left ρ hx
    have hmul : (A * B).toEuclideanLin x = x := by
      simpa [A, B, Matrix.toEuclideanLin, Matrix.mulVec_mulVec] using
        show A.toEuclideanLin (B.toEuclideanLin x) = x by rw [hxB', hxA']
    simpa [HermitianMat.lin, Matrix.toEuclideanLin, A, B, ← Matrix.mul_kronecker_mul] using hmul
  have prod_marginals_ker_le : (ρ.traceRight ⊗ᴹ ρ.traceLeft).M.ker ≤ ρ.M.ker := by
    let P : HermitianMat (dA × dB) ℂ := ρ.traceRight.M.supportProj ⊗ₖ ρ.traceLeft.M.supportProj
    have hP : ρ.M.support ≤ P.support := by
      intro x hx
      exact ⟨x, by simpa [P] using fixed_support_kron_prod hx⟩
    have hkerP : P.ker ≤ ρ.M.ker := by
      simpa [HermitianMat.support_orthogonal_eq_range] using Submodule.orthogonal_le hP
    exact (show (ρ.traceRight ⊗ᴹ ρ.traceLeft).M.ker ≤ P.ker by
      change LinearMap.ker
          ((Matrix.kroneckerMap (· * ·) ρ.traceRight.M.mat ρ.traceLeft.M.mat).toEuclideanLin)
        ≤ LinearMap.ker
          ((Matrix.kroneckerMap (· * ·) ρ.traceRight.M.supportProj.mat
            ρ.traceLeft.M.supportProj.mat).toEuclideanLin)
      exact ker_kron_le_of_le _ _ _ _
        (by
          simpa [HermitianMat.ker, HermitianMat.lin] using
            (show ρ.traceRight.M.ker ≤ ρ.traceRight.M.supportProj.ker by simp))
        (by
          simpa [HermitianMat.ker, HermitianMat.lin] using
            (show ρ.traceLeft.M.ker ≤ ρ.traceLeft.M.supportProj.ker by simp))).trans hkerP
  have right_mul_eq_of_fixed_support {Q ρM : HermitianMat (dA × dB) ℂ}
      (hfix : ∀ x : EuclideanSpace ℂ (dA × dB), x ∈ ρM.support → Q.lin x = x) :
      ρM.mat * Q.mat = ρM.mat := by
    have hleft : Q.mat * ρM.mat = ρM.mat := by
      rw [Matrix.ext_iff_mulVec]
      intro v
      have hv : WithLp.toLp 2 (ρM.mat.mulVec v) ∈ ρM.support :=
        Set.mem_range_self (WithLp.toLp 2 v)
      simpa [Matrix.mulVec_mulVec, HermitianMat.lin, Matrix.toEuclideanLin] using hfix _ hv
    simpa [Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat] using
      congrArg Matrix.conjTranspose hleft
  have inner_kron_support_right_eq (A : HermitianMat dA ℂ) :
      ⟪ρ.M, A ⊗ₖ ρ.traceLeft.M.supportProj⟫ = ⟪ρ.M, A ⊗ₖ (1 : HermitianMat dB ℂ)⟫ := by
    let Q : HermitianMat (dA × dB) ℂ := (1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.supportProj
    have hQ : ρ.M.mat * Q.mat = ρ.M.mat := by
      apply right_mul_eq_of_fixed_support
      intro x hx
      simpa [Q] using fixed_support_kron_left ρ hx
    have hmat : Q.mat * (A ⊗ₖ (1 : HermitianMat dB ℂ)).mat =
        (A ⊗ₖ ρ.traceLeft.M.supportProj).mat := by
      simp [Q, HermitianMat.kronecker_mat, ← Matrix.mul_kronecker_mul]
    rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
    apply congrArg Complex.re
    rw [← hmat, ← Matrix.mul_assoc, hQ]
  have inner_support_kron_left_eq (B : HermitianMat dB ℂ) :
      ⟪ρ.M, ρ.traceRight.M.supportProj ⊗ₖ B⟫ = ⟪ρ.M, (1 : HermitianMat dA ℂ) ⊗ₖ B⟫ := by
    let Q : HermitianMat (dA × dB) ℂ := ρ.traceRight.M.supportProj ⊗ₖ (1 : HermitianMat dB ℂ)
    have hQ : ρ.M.mat * Q.mat = ρ.M.mat := by
      apply right_mul_eq_of_fixed_support
      intro x hx
      simpa [Q] using fixed_support_kron_right ρ hx
    have hmat : Q.mat * ((1 : HermitianMat dA ℂ) ⊗ₖ B).mat =
        (ρ.traceRight.M.supportProj ⊗ₖ B).mat := by
      simp [Q, HermitianMat.kronecker_mat, ← Matrix.mul_kronecker_mul]
    rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
    apply congrArg Complex.re
    rw [← hmat, ← Matrix.mul_assoc, hQ]
  rw [qRelativeEnt_ker prod_marginals_ker_le, qMutualInfo,
    Sᵥₙ_eq_neg_trace_log, Sᵥₙ_eq_neg_trace_log, Sᵥₙ_eq_neg_trace_log]
  rw [show (ρ.traceRight ⊗ᴹ ρ.traceLeft).M.log =
      ρ.traceRight.M.log ⊗ₖ ρ.traceLeft.M.supportProj +
      ρ.traceRight.M.supportProj ⊗ₖ ρ.traceLeft.M.log by
    simpa [MState.prod] using
      (HermitianMat.log_kron_with_proj (A := ρ.traceRight.M) (B := ρ.traceLeft.M)),
    inner_sub_right, inner_add_right]
  rw [show ⟪ρ.M.log, ρ.M⟫ = ⟪ρ.M, ρ.M.log⟫ by rw [HermitianMat.inner_comm]]
  exact congrArg (fun x : ℝ => (x : EReal)) <| by
    rw [show ⟪ρ.M, ρ.traceRight.M.log ⊗ₖ ρ.traceLeft.M.supportProj⟫ =
        ⟪ρ.traceRight.M.log, ρ.traceRight.M⟫ by
      calc
        _ = ⟪ρ.M, ρ.traceRight.M.log ⊗ₖ (1 : HermitianMat dB ℂ)⟫ :=
          inner_kron_support_right_eq ρ.traceRight.M.log
        _ = ⟪ρ.traceRight.M.log, ρ.traceRight.M⟫ := by
          simpa [HermitianMat.inner_comm] using
            inner_kron_one_eq_inner_traceRight ρ.traceRight.M.log ρ.M,
      show ⟪ρ.M, ρ.traceRight.M.supportProj ⊗ₖ ρ.traceLeft.M.log⟫ =
        ⟪ρ.traceLeft.M.log, ρ.traceLeft.M⟫ by
      calc
        _ = ⟪ρ.M, (1 : HermitianMat dA ℂ) ⊗ₖ ρ.traceLeft.M.log⟫ :=
          inner_support_kron_left_eq ρ.traceLeft.M.log
        _ = ⟪ρ.traceLeft.M.log, ρ.traceLeft.M⟫ := by
          simpa [HermitianMat.inner_comm] using
            inner_one_kron_eq_inner_traceLeft ρ.traceLeft.M.log ρ.M]
    ring

/-
Helper: If σ₂ ≤ α • σ₁ for density matrices, then α > 0.
   Proof: σ₂ has trace 1, so it's nonzero. If α ≤ 0, then α • σ₁ ≤ 0 (since σ₁ ≥ 0),
   but σ₂ ≤ α • σ₁ ≤ 0 with σ₂ ≥ 0 forces σ₂ = 0, contradicting trace = 1.
-/
private lemma pos_of_MState_le_smul {σ₁ σ₂ : MState d} (hσ : σ₂.M ≤ α • σ₁.M) : 0 < α := by
  by_contra! h_nonpos
  apply σ₂.pos.ne'
  apply le_antisymm
  · convert ← hσ using 1
    apply le_antisymm
    · exact smul_nonpos_of_nonpos_of_nonneg h_nonpos ( by positivity)
    · exact hσ.trans' ( by positivity );
  · positivity

open ComplexOrder in
private lemma HermitianMat.inner_log_mono_of_posDef_of_le {A B C : HermitianMat d 𝕜}
    (hC : 0 ≤ C) (hA : A.mat.PosDef) (hAB : A ≤ B) :
    ⟪C, A.log⟫ ≤ ⟪C, B.log⟫ := by
  exact inner_mono hC (log_mono hA hAB)

open ComplexOrder in
private lemma posDef_add_eps {A : HermitianMat d ℂ} (hA : 0 ≤ A) {ε : ℝ} (hε : 0 < ε) :
    (A + ε • 1).mat.PosDef := by
  rw [HermitianMat.zero_le_iff] at hA
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · exact HermitianMat.H _
  · intro x hx_ne_zero
    have h_inner : star x ⬝ᵥ (A.val.mulVec x) ≥ 0 := by
      simp [hA]
    have h_eps : star x ⬝ᵥ (ε • 1 : Matrix d d ℂ).mulVec x = ε * star x ⬝ᵥ x := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm, Matrix.one_apply]
    have h_pos : 0 < ε * star x ⬝ᵥ x := by
      simp [*]
    simpa [Matrix.add_mulVec, h_eps] using add_pos_of_nonneg_of_pos h_inner h_pos

private lemma log_add_eps_eq_cfc (A : HermitianMat d 𝕜) (ε : ℝ) :
    (A + ε • 1).log = A.cfc (Real.log <| · + ε) := by
  have h_cfc : A + ε • 1 = A.cfc (· + ε) := by
    have h_add : A.cfc (fun u => u + ε) = A.cfc (fun u => u) + A.cfc (fun _ => ε) := by
      exact A.cfc_add_apply _ _
    simp only [HermitianMat.cfc_id', HermitianMat.cfc_const, h_add]
  rw [h_cfc, HermitianMat.log, A.cfc_comp_apply]

private lemma inner_cfc_eq_sum (A C : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    ⟪C, A.cfc f⟫ = ∑ i, f (A.H.eigenvalues i) *
      RCLike.re ((C.mat * (A.H.eigenvectorUnitary.val * Matrix.single i i 1 * A.H.eigenvectorUnitary.val.conjTranspose)).trace) := by
  apply congr(RCLike.re ((C.val * $(A.cfc_toMat_eq_sum_smul_proj f)).trace)).trans
  simp only [HermitianMat.val_eq_coe, Matrix.mul_sum, Algebra.mul_smul_comm, Matrix.trace_sum,
    Matrix.trace_smul, RCLike.real_smul_eq_coe_mul, map_sum, RCLike.mul_re,
    RCLike.ofReal_re, RCLike.ofReal_im, zero_mul, sub_zero]

private lemma eigenproj_coeff_zero_of_ker_le {A C : HermitianMat d 𝕜}
    (hker : A.ker ≤ C.ker) {i : d} (hi : A.H.eigenvalues i = 0) :
    RCLike.re ((C.mat * (A.H.eigenvectorUnitary.val * Matrix.single i i 1 * A.H.eigenvectorUnitary.val.conjTranspose)).trace) = 0 := by
  have h1 : A.mat.mulVec (A.H.eigenvectorBasis i) = 0 := by
    simpa [hi] using A.H.mulVec_eigenvectorBasis i
  have h0 : C.mat.mulVec (A.H.eigenvectorBasis i) = 0 :=
    congr(WithLp.ofLp $(hker ((A.mem_ker_iff_mulVec_zero _).mpr h1)))
  have h2 := congr_arg (fun v => star ((A.H.eigenvectorBasis i : d → 𝕜)) ⬝ᵥ v) h0
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, Matrix.trace_mul_single]
  simp only [dotProduct_zero] at h2
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Finset.mul_sum,
    mul_comm, mul_left_comm] at h2 ⊢
  rw [Finset.sum_comm] at h2
  simpa using congr_arg RCLike.re h2

open scoped Topology in
private lemma inner_log_shift_tendsto {A C : HermitianMat d 𝕜} (hker : A.ker ≤ C.ker) :
    (𝓝[>] 0).Tendsto (fun (ε : ℝ) ↦ ⟪C, (A + ε • 1).log⟫) (𝓝 ⟪C, A.log⟫) := by
  simp only [log_add_eps_eq_cfc A]
  simp only [inner_cfc_eq_sum, HermitianMat.log]
  refine tendsto_finsetSum _ fun i _ ↦ ?_
  by_cases hi : A.H.eigenvalues i = 0
  · simp [eigenproj_coeff_zero_of_ker_le hker hi]
  · have h := log_add_eps_eq_cfc A
    simp_rw [HermitianMat.log] at h
    refine Filter.Tendsto.mul ?_ tendsto_const_nhds
    conv in 𝓝 (Real.log _) => rw [← add_zero (A.H.eigenvalues i)]
    apply (tendsto_const_nhds.add (Filter.tendsto_id.mono_left inf_le_left)).log
    rwa [add_zero]

private lemma HermitianMat.inner_log_mono_of_psd_of_le {A B C : HermitianMat d ℂ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (hC : 0 ≤ C) (hker : A.ker ≤ C.ker) :
    ⟪C, A.log⟫ ≤ ⟪C, B.log⟫ := by
  open scoped Topology in
  have h_eventually : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ⟪C, (A + ε • 1).log⟫ ≤ ⟪C, (B + ε • 1).log⟫ := by
    refine eventually_nhdsWithin_of_forall fun ε hε ↦ ?_
    exact inner_log_mono_of_posDef_of_le hC (posDef_add_eps hA hε) (add_le_add_left hAB _)
  refine le_of_tendsto_of_tendsto ?_ ?_ h_eventually
  · exact inner_log_shift_tendsto hker
  · apply inner_log_shift_tendsto
    exact (ker_antitone hA hAB).trans hker

private lemma HermitianMat.inner_log_sub_le_log_alpha (ρ : MState d) {σ₁ σ₂ : MState d} {α : ℝ}
    (hσ : σ₂.M ≤ α • σ₁.M)
    (hker₁ : σ₁.M.ker ≤ ρ.M.ker) (hker₂ : σ₂.M.ker ≤ ρ.M.ker) :
    ⟪ρ.M, σ₂.M.log - σ₁.M.log⟫ ≤ Real.log α := by
  have h_log_mono : ⟪ρ.M, σ₂.M.log - (α • σ₁.M).log⟫ ≤ 0 := by
    have h_log_mono : ⟪ρ.M, σ₂.M.log⟫ ≤ ⟪ρ.M, (α • σ₁.M).log⟫ := by
      exact inner_log_mono_of_psd_of_le σ₂.nonneg hσ ρ.nonneg hker₂
    simpa [inner_sub_right] using sub_nonpos_of_le h_log_mono
  have h_log_smul : (α • σ₁.M).log = (Real.log α) • σ₁.M.supportProj + σ₁.M.log := by
    apply HermitianMat.log_smul_of_pos
    rintro rfl
    simpa using pos_of_MState_le_smul hσ
  rw [h_log_smul] at h_log_mono
  simp only [add_comm, sub_eq_add_neg, neg_add_rev] at h_log_mono h_log_smul ⊢
  have h_inner_support : ⟪ρ.M, σ₁.M.supportProj⟫ = 1 := by
    rw [HermitianMat.inner_supportProj_of_ker_le hker₁, ρ.tr]
  simp_all [← add_assoc, inner_add_right, inner_smul_right]

theorem qRelEntropy_le_add_of_le_smul (ρ : MState d) {σ₁ σ₂ : MState d} (hσ : σ₂.M ≤ α • σ₁.M) :
    𝐃(ρ‖σ₁) ≤ 𝐃(ρ‖σ₂) + ENNReal.ofReal (Real.log α)
    := by
  -- Consider two cases: when the kernel of σ₂ is contained in the kernel of ρ and when it is not.
  by_cases hker : σ₂.M.ker ≤ ρ.M.ker;
  · by_cases hker₁ : σ₁.M.ker ≤ ρ.M.ker;
    · -- Using `qRelativeEnt_ker` to get D(ρ‖σ₁).toEReal = ⟪ρ.M, ρ.M.log - σ₁.M.log⟫
      have h_log : ⟪ρ.M, σ₂.M.log - σ₁.M.log⟫ ≤ Real.log α := by
        apply HermitianMat.inner_log_sub_le_log_alpha
        · exact hσ
        · exact hker₁
        · exact hker
      have h_final : (qRelativeEnt ρ σ₁).toEReal ≤ (qRelativeEnt ρ σ₂).toEReal + ENNReal.toEReal (ENNReal.ofReal (Real.log α)) := by
        simp_all only [qRelativeEnt_ker, inner_sub_right, tsub_le_iff_right, EReal.coe_sub, EReal.coe_ennreal_ofReal]
        cases max_cases (Real.log α) 0
        <;> simp only [sup_of_le_left, *]
        <;> norm_cast at *
        <;> linarith [Real.log_nonneg one_le_two]
      have h_final' : qRelativeEnt ρ σ₁ ≤ qRelativeEnt ρ σ₂ + ENNReal.ofReal (Real.log α) := by
        exact_mod_cast h_final
      exact h_final'
    · by_contra h_contra;
      have hker_le : σ₁.M.ker ≤ σ₂.M.ker := by
        apply_rules [ HermitianMat.ker_le_of_le_smul, hσ ];
        · rintro rfl
          apply σ₂.pos.not_ge
          simpa using hσ
        · positivity
      exact hker₁ (hker_le.trans hker)
  · simp [hker, SandwichedRelRentropy, qRelativeEnt]

theorem qRelativeEnt_op_le {ρ σ : MState d} (h : ρ.M ≤ α • σ.M) :
    𝐃(ρ‖σ) ≤ .ofReal (Real.log α) := by
  simpa using qRelEntropy_le_add_of_le_smul ρ h
