/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Entropy.Relative
public import QuantumInfo.ForMathlib.HermitianMat.Sqrt
public import QuantumInfo.ForMathlib.HermitianMat.LiebConcavity

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

open HermitianMat
open scoped InnerProductSpace RealInnerProductSpace Topology

/-!
# DPI (Data Processing Inequality)

The Data Processing Inequality (DPI) for the sandwiched Rényi relative entropy, and
as a consequence, the quantum relative entropy.

## Proof structure (for α > 1)

Following Leditzky–Rouzé–Datta (arXiv:1306.5920), the proof proceeds as follows:

1. Define the **trace functional** `Q̃_α(ρ‖σ) = Tr[(σ^γ ρ σ^γ)^α]` where `γ = (1 - α) / (2α)`.
   The sandwiched Rényi divergence satisfies `D̃_α(ρ‖σ) = log(Q̃_α(ρ‖σ)) / (α - 1)`.

2. The DPI for `D̃_α` reduces to **monotonicity of `Q̃_α` under partial trace**:
   `Q̃_α(ρ_AB‖σ_AB) ≥ Q̃_α(ρ_A‖σ_A)` for `α > 1`.

3. This monotonicity is proved via the **twirling argument**:
   - `Q̃_α` is invariant under joint unitary conjugation.
   - `Q̃_α` is jointly convex for `α > 1` (Frank–Lieb).
   - A twirling set of unitaries `{V_i}` averages any state to a product with the
     maximally mixed state.
   - `Q̃_α` is invariant under tensoring with a fixed state.

4. The general DPI for CPTP maps follows via **Stinespring dilation**:
   any CPTP map can be decomposed as ancilla preparation + unitary + partial trace.
-/

open scoped Matrix ComplexOrder
open BigOperators

/-! ## The Sandwiched Trace Functional -/

/-- The sandwiched trace functional `Q̃_α(ρ‖σ) = Tr[(σ^γ ρ σ^γ)^α]` where `γ = (1-α)/(2α)`.
This is the quantity underlying the sandwiched Rényi divergence:
`D̃_α(ρ‖σ) = log(Q̃_α(ρ‖σ)) / (α - 1)`.

Note: the `conj` operation gives `A.conj B = B * A.mat * B†`, and since `σ^γ` is Hermitian
(self-adjoint), `B† = B`, so `ρ.M.conj (σ.M ^ γ).mat = σ^γ * ρ * σ^γ`. -/
noncomputable def sandwichedTraceFunctional (α : ℝ) (ρ σ : MState d) : ℝ :=
  let γ := (1 - α) / (2 * α)
  ((ρ.M.conj (σ.M ^ γ).mat) ^ α).trace

notation "Q̃_" α "(" ρ "‖" σ ")" => sandwichedTraceFunctional α ρ σ

/-! ## Properties of the Trace Functional -/

/-
The sandwiched Rényi divergence equals `log(Q̃_α) / (α - 1)` for `α > 0`, `α ≠ 1`,
when `σ.M.ker ≤ ρ.M.ker`.
-/
theorem sandwichedRelRentropy_eq_log_traceFunctional (hα₀ : 0 < α) (hα₁ : α ≠ 1)
    (hker : σ.M.ker ≤ ρ.M.ker) :
    D̃_ α(ρ‖σ) = ENNReal.ofReal (Real.log (Q̃_ α(ρ‖σ)) / (α - 1)) := by
  rw [ENNReal.ofReal_eq_coe_nnreal]
  unfold SandwichedRelRentropy sandwichedTraceFunctional
  split
  next h => simp_all only; norm_cast
  next h => rfl

/-
`Q̃_α(ρ‖σ)` is nonneg when `α > 0`.
-/
theorem sandwichedTraceFunctional_nonneg (ρ σ : MState d) :
    0 ≤ Q̃_ α(ρ‖σ) := by
  rw [sandwichedTraceFunctional]
  apply trace_nonneg
  apply rpow_nonneg
  positivity

/-- The trace functional is strictly positive when the kernel condition holds. Under
`σ.M.ker ≤ ρ.M.ker` (i.e. `supp(ρ) ⊆ supp(σ)`), the sandwich `σ^γ ρ σ^γ ≠ 0`
because ρ has support inside σ's support. -/
theorem sandwichedTraceFunctional_pos
    (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    0 < Q̃_ α(ρ‖σ) := by
  rw [sandwichedTraceFunctional]
  apply trace_pos
  apply rpow_pos
  apply conj_pos ρ.pos
  grw [← hker]
  exact ker_rpow_le_of_nonneg σ.nonneg

/-! ## Unitary Invariance

`Q̃_α(UρU†‖UσU†) = Q̃_α(ρ‖σ)` for any unitary `U`.

Here, `conj U.val A` denotes `U * A * U†`, so "conjugating ρ and σ by
the same unitary" means applying `conj U.val` to both. -/

/-
The trace functional is invariant under joint unitary conjugation:
`Tr[(U σ U†)^γ (U ρ U†) (U σ U†)^γ)^α] = Tr[(σ^γ ρ σ^γ)^α]`.
This corresponds to equation (2.3) in the paper.
Proved using `rpow_conj_unitary` (f(UXU†) = U f(X) U†) and `conj_conj`.
-/
theorem sandwichedTraceFunctional_conj_unitary_hermitian
    (U : Matrix.unitaryGroup d ℂ) (A B : HermitianMat d ℂ) :
    let γ := (1 - α) / (2 * α)
    ((A.conj U.val).conj ((B.conj U.val) ^ γ).mat ^ α).trace =
      ((A.conj (B ^ γ).mat) ^ α).trace := by
  intro γ
  rw [rpow_conj_unitary, conj_apply_mat, conj_conj, mul_assoc, mul_assoc]
  simp [← Matrix.star_eq_conjTranspose, ← conj_conj, rpow_conj_unitary, trace_conj_unitary]

/-- The trace functional is invariant under joint unitary conjugation of MStates. -/
theorem sandwichedTraceFunctional_conj_unitary_MState
    (U : Matrix.unitaryGroup d ℂ) (ρ σ : MState d) :
    Q̃_ α(ρ.U_conj U‖σ.U_conj U) = Q̃_ α(ρ‖σ) := by
  unfold sandwichedTraceFunctional MState.U_conj
  exact sandwichedTraceFunctional_conj_unitary_hermitian U ρ.M σ.M

/-! ## Joint Convexity for α > 1

The trace functional `Q̃_α` is jointly convex for `α > 1`. This is proved by
Frank and Lieb via a variational formula and strict convexity of trace functions.

### Trace functions convexity

The following result is used in the proof: for a convex function `g : ℝ → ℝ`,
the map `A ↦ Tr[g(A)]` on Hermitian matrices is convex (Carlen, Theorem 2.10).  -/

namespace HermitianMat

end HermitianMat

/-! ### Variational formula for the trace functional
Following Frank–Lieb, for `α > 1` we define
  `f_α(H, ρ, σ) = α · Tr[ρ · H] − (α−1) · Tr[(σ^{−γ} H σ^{−γ})^{α/(α−1)}]`
where `γ = (1−α)/(2α)` (so `−γ = (α−1)/(2α) > 0`).
Key facts (each stated as a lemma below):
1. `Q̃_α(ρ‖σ) = sup_{H ≥ 0} f_α(H, ρ, σ)` for α > 1.
2. For fixed `H`, `f_α` is linear in `ρ` (hence convex).
3. For fixed `H`, `f_α` is convex in `σ` (uses Lieb concavity).
4. Therefore `f_α` is jointly convex in `(ρ, σ)` for fixed `H`.
5. The supremum of jointly convex functions is jointly convex.
-/

/-- The variational function `f_α(H, ρ, σ) = α · ⟪ρ, H⟫ − (α−1) · Tr[(σ^{−γ} H σ^{−γ})^{α/(α−1)}]`
where `γ = (1−α)/(2α)`. For fixed `H ≥ 0`, this is linear in `ρ` and convex in `σ`.
Frank–Lieb show that `Q̃_α(ρ‖σ) = sup_{H ≥ 0} f_α(H, ρ, σ)` for `α > 1`. -/
noncomputable def f_alpha (α : ℝ) (H : HermitianMat d ℂ) (ρ σ : MState d) : ℝ :=
  let γ : ℝ := (1 - α) / (2 * α)
  α * ⟪ρ.M, H⟫_ℝ - (α - 1) * ((H.conj (σ.M ^ (-γ)).mat) ^ (α / (α - 1))).trace

/-- The optimizer in the variational formula: `H_hat = σ^γ (σ^γ ρ σ^γ)^{α−1} σ^γ`
where `γ = (1−α)/(2α)`. -/
noncomputable def H_hat (α : ℝ) (ρ σ : MState d) : HermitianMat d ℂ :=
  let γ := (1 - α) / (2 * α)
  ((ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1)).conj (σ.M ^ γ).mat

/-
**Step 1a**: The optimizer `H_hat` is PSD.
-/
theorem H_hat_nonneg (ρ σ : MState d) : 0 ≤ H_hat α ρ σ := by
  apply conj_nonneg
  apply rpow_nonneg
  positivity

/--
For a PSD Hermitian matrix B whose kernel contains A's kernel, conjugating B by A's
support projection leaves B unchanged.
-/
private lemma conj_supportProj_eq_of_ker_le (A B : HermitianMat d ℂ) (hker : A.ker ≤ B.ker) :
    B.conj (A.supportProj).mat = B := by
  ext1
  have h' := congrArg Matrix.conjTranspose (mul_supportProj_of_ker_le hker)
  simp only [Matrix.conjTranspose_mul, conjTranspose_mat] at h'
  simp [h', mul_supportProj_of_ker_le hker]

/--
The kernel of σ is contained in the kernel of (ρ.conj (σ^γ))^{α-1} when γ ≠ 0 and α > 1.
-/
private lemma ker_sigma_le_ker_conj_rpow (ρ σ : MState d) {γ : ℝ} (hγ : γ ≠ 0) (hα1 : α - 1 ≠ 0) :
    σ.M.ker ≤ ((ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1)).ker := by
  rw [ker_rpow_eq_of_nonneg (by positivity) hα1]
  intro x hx
  have h_ker_rpow : x ∈ (σ.M ^ γ).ker := by
    rwa [ker_rpow_eq_of_nonneg σ.nonneg hγ]
  simp_all [ker, lin]

/-- Sub-lemma for Step 1b: the conj of H_hat by σ^{−γ} simplifies to (ρ.M.conj (σ^γ).mat)^{α−1}.
This uses σ^{−γ} · σ^γ = identity (on support) to cancel the outer σ^γ factors. -/
theorem H_hat_conj_sigma (hα : 1 < α) (ρ σ : MState d) :
    let γ := (1 - α) / (2 * α)
    (H_hat α ρ σ).conj (σ.M ^ (-γ)).mat = (ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1) := by
  intro γ
  have hγ : γ ≠ 0 := div_ne_zero (sub_ne_zero_of_ne hα.ne) (ne_of_gt (by linarith))
  have hα1 : α - 1 ≠ 0 := by linarith
  show (((ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1)).conj (σ.M ^ γ).mat).conj (σ.M ^ (-γ)).mat =
    (ρ.M.conj (σ.M ^ γ).mat) ^ (α - 1)
  rw [conj_conj, rpow_neg_mul_rpow_eq_supportProj σ.nonneg hγ]
  exact conj_supportProj_eq_of_ker_le σ.M _ (ker_sigma_le_ker_conj_rpow ρ σ hγ hα1)


/-
Sub-lemma for Step 1b: the inner product ⟪ρ.M, H_hat⟫ equals Tr[(σ^γ ρ σ^γ)^α].
By cyclicity of trace: Tr[ρ · σ^γ · (σ^γ ρ σ^γ)^{α−1} · σ^γ] = Tr[(σ^γ ρ σ^γ)^α].
-/
theorem inner_rho_H_hat (hα : 1 < α) (ρ σ : MState d) :
    let γ := (1 - α) / (2 * α)
    ⟪ρ.M, H_hat α ρ σ⟫_ℝ = ((ρ.M.conj (σ.M ^ γ).mat) ^ α).trace := by
  intro γ
  simp only [show γ = (1 - α) / (2 * α) from rfl]
  have hmul := mat_rpow_add (A := ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) (by positivity)
    (p := 1) (q := α - 1) (by linarith)
  simp only [rpow_one, show (1 : ℝ) + (α - 1) = α by ring] at hmul
  rw [inner_eq_re_trace, trace_eq_re_trace, H_hat, hmul]
  congr 1
  simp only [conj_apply_mat, conjTranspose_mat, ← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp [Matrix.mul_assoc]

/-
**Step 1b**: Evaluating `f_α` at the optimizer `H_hat` gives `Q̃_α(ρ‖σ)`.
This is the key computation that verifies the variational formula at the optimizer.
Proof: f_α(H_hat, ρ, σ) = α · Tr[(σ^γ ρ σ^γ)^α] - (α-1) · Tr[(σ^γ ρ σ^γ)^α] = Tr[(σ^γ ρ σ^γ)^α] = Q̃.
-/
theorem f_alpha_at_optimizer (hα : 1 < α) (ρ σ : MState d) :
    f_alpha α (H_hat α ρ σ) ρ σ = Q̃_ α(ρ‖σ) := by
  have h_inner : ⟪ρ.M, H_hat α ρ σ⟫_ℝ =
      ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace := inner_rho_H_hat hα ρ σ
  have h_conj : (H_hat α ρ σ).conj (σ.M ^ ((α - 1) / (2 * α))).mat =
      (ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ (α - 1) := by
    convert H_hat_conj_sigma (hα := hα) (ρ := ρ) (σ := σ) using 1
    ring_nf!
  unfold f_alpha sandwichedTraceFunctional
  simp_all [sub_div]
  rw [← rpow_mul]; norm_num [show α ≠ 0 by positivity, show α - 1 ≠ 0 by linarith]
  · rw [mul_div_cancel₀ _ (by linarith)]; ring
  · exact conj_nonneg _ ρ.nonneg

/--
For PSD `A` and `γ ≠ 0`, the product `A^γ * A^{-γ}` equals the support projection
of `A`. This is because `x^γ * x^{-γ} = if x = 0 then 0 else 1` for `x ≥ 0`.
-/
lemma rpow_mul_neg_rpow_eq_supportProj {A : HermitianMat d ℂ}
    (hA : 0 ≤ A) (γ : ℝ) (hγ : γ ≠ 0) :
    (A ^ γ).mat * (A ^ (-γ)).mat = A.supportProj.mat := by
  simpa using rpow_neg_mul_rpow_eq_supportProj hA (neg_ne_zero.mpr hγ)

/--
The support projection of `A` acts as identity on `B` when `A.ker ≤ B.ker`.
Since `A.supportProj` projects onto `ker(A)⊥` and `B` is zero on `ker(A)`,
the projection preserves `B`.
-/
lemma supportProj_mul_of_ker_le {A B : HermitianMat d ℂ}
    (hker : A.ker ≤ B.ker) :
    A.supportProj.mat * B.mat = B.mat := by
  simpa [Matrix.conjTranspose_mul] using
    congrArg Matrix.conjTranspose (mul_supportProj_of_ker_le hker)

/--
Under the support condition `σ.M.ker ≤ ρ.M.ker` (i.e., supp(ρ) ⊆ supp(σ)),
conjugation by `σ^γ` and `σ^{-γ}` preserves the inner product:
`⟪ρ.M, H⟫ = ⟪σ^γ ρ σ^γ, σ^{-γ} H σ^{-γ}⟫`. This holds because the kernel condition
ensures `ρ` is supported on `supp(σ)`, where `σ^γ σ^{-γ}` acts as the identity.
-/
lemma inner_eq_inner_conj_of_ker_le (ρ σ : MState d)
    (H : HermitianMat d ℂ) (hker : σ.M.ker ≤ ρ.M.ker) (γ : ℝ) (hγ : γ ≠ 0) :
    ⟪ρ.M, H⟫_ℝ = ⟪ρ.M.conj (σ.M ^ γ).mat, H.conj (σ.M ^ (-γ)).mat⟫_ℝ := by
  have h2 : (σ.M ^ (-γ)).mat * (σ.M ^ γ).mat = σ.M.supportProj.mat := by
    simpa using rpow_mul_neg_rpow_eq_supportProj σ.nonneg (-γ) (neg_ne_zero.mpr hγ)
  simp only [inner_eq_re_trace, conj_apply_mat, conjTranspose_mat]
  congr 1
  rw [Matrix.trace_mul_cycle]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ (σ.M ^ (-γ)).mat (σ.M ^ γ).mat, h2,
    Matrix.mul_assoc _ _ ρ.M.mat, supportProj_mul_of_ker_le hker,
    Matrix.trace_mul_cycle, ← Matrix.mul_assoc,
    rpow_mul_neg_rpow_eq_supportProj σ.nonneg γ hγ,
    Matrix.trace_mul_cycle, mul_supportProj_of_ker_le hker]

/-- **Step 1c**: `H_hat` is a maximizer: for all `H ≥ 0`, `f_α(H) ≤ f_α(H_hat)`.
This uses the trace Young inequality: for PSD `A, B` and conjugate exponents `p, q > 1`,
`⟪A, B⟫ ≤ Tr[A^p]/p + Tr[B^q]/q`.
Applied with `A = σ^γ ρ σ^γ`, `B = σ^{-γ} H σ^{-γ}`, `p = α`, `q = α/(α-1)`,
the inner product identity `⟪ρ, H⟫ = ⟪A, B⟫` (under the support condition) yields
`f_α(H) ≤ Tr[A^α] = Q̃_α(ρ‖σ) = f_α(H_hat)`.
Note: the support condition `σ.M.ker ≤ ρ.M.ker` (i.e., supp(ρ) ⊆ supp(σ)) is necessary.
Without it, the theorem is false: taking ρ orthogonal to σ gives Q̃_α = 0 but
`f_α(H) = α · Tr[ρH] > 0` for appropriate H. -/
theorem f_alpha_le_at_optimizer (hα : 1 < α) (ρ σ : MState d)
    (H : HermitianMat d ℂ) (hH : 0 ≤ H) (hker : σ.M.ker ≤ ρ.M.ker) :
    f_alpha α H ρ σ ≤ f_alpha α (H_hat α ρ σ) ρ σ := by
  rw [f_alpha_at_optimizer hα]
  -- Goal: f_alpha α H ρ σ ≤ Q̃_α(ρ‖σ)
  set γ : ℝ := (1 - α) / (2 * α)
  have hγ : γ ≠ 0 := div_ne_zero (sub_ne_zero_of_ne hα.ne) (ne_of_gt (by linarith))
  set A := ρ.M.conj (σ.M ^ γ).mat
  set B := H.conj (σ.M ^ (-γ)).mat
  have hA_nn : 0 ≤ A := conj_nonneg _ ρ.nonneg
  have hB_nn : 0 ≤ B := conj_nonneg _ hH
  have h_inner : ⟪ρ.M, H⟫_ℝ = ⟪A, B⟫_ℝ :=
    inner_eq_inner_conj_of_ker_le ρ σ H hker γ hγ
  have hpq : 1 / α + 1 / (α / (α - 1)) = 1 := by field_simp; ring
  have h_young := trace_young A B hA_nn hB_nn α (α / (α - 1)) hα hpq
  have hα_pos : (0 : ℝ) < α := by linarith
  have hαm1_pos : (0 : ℝ) < α - 1 := by linarith
  change α * ⟪ρ.M, H⟫_ℝ - (α - 1) * (B ^ (α / (α - 1))).trace ≤ (A ^ α).trace
  rw [h_inner]
  have h_simp : α * ((A ^ α).trace / α + (B ^ (α / (α - 1))).trace / (α / (α - 1))) =
      (A ^ α).trace + (α - 1) * (B ^ (α / (α - 1))).trace := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h_young hα_pos.le]

/--
**Step 1 (Variational formula)**: For `α > 1`, the trace functional equals the
supremum of `f_α` over all PSD `H`:
  `Q̃_α(ρ‖σ) = ⨆ (H : HermitianMat d ℂ) (_ : 0 ≤ H), f_alpha α H ρ σ`.
The optimizer is `H_hat = σ^γ (σ^γ ρ σ^γ)^{α−1} σ^γ`.
-/
theorem traceFunctional_eq_iSup_f_alpha (hα : 1 < α) (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    Q̃_ α(ρ‖σ) = ⨆ (H : {H : HermitianMat d ℂ // 0 ≤ H}), f_alpha α H.1 ρ σ := by
  rw [@ciSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · intro i
    rw [← f_alpha_at_optimizer hα ρ σ]
    exact f_alpha_le_at_optimizer hα ρ σ i i.2 hker
  · intro w hw
    exact ⟨⟨H_hat α ρ σ, H_hat_nonneg ρ σ⟩, hw.trans_le (f_alpha_at_optimizer hα ρ σ ▸ le_rfl)⟩

/-- (Convexity in σ): For fixed `H ≥ 0` and `ρ`, and `α > 1`, the map
`σ ↦ f_alpha α H ρ σ` is convex. The key is that for `p = α/(α−1) > 1`:
• `A ↦ Tr[A^p]` is convex on PSD matrices (trace function convexity, Theorem 2.10 of Carlen),
• `σ ↦ σ^{−γ} H σ^{−γ}` is *concave* in `σ` by Lieb concavity (since `−γ = (α−1)/(2α) ∈ (0,½)`),
• The composition of a convex non-decreasing function with a concave function is convex,
  but we actually need the sign: the second term has a factor `−(α−1) < 0` which
  flips concave → convex.
More precisely: `σ ↦ Tr[(σ^{−γ} H σ^{−γ})^p]` is concave (by Lieb + trace function convexity),
so `σ ↦ −(α−1) · Tr[(σ^{−γ} H σ^{−γ})^p]` is convex. -/
theorem f_alpha_convex_in_sigma (hα : 1 < α) (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    (ρ : MState d) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (σs : ι → MState d) (σ_mix : MState d)
    (hσ_mix : σ_mix.M = ∑ i, w i • (σs i).M) :
    f_alpha α H ρ σ_mix ≤ ∑ i, w i * f_alpha α H ρ (σs i) := by
  have hα_pos : 0 < α - 1 := by linarith
  -- Define the σ-dependent trace function on HermitianMat
  let s := (α - 1) / (2 * α)
  let p := α / (α - 1)
  let F : HermitianMat d ℂ → ℝ := fun σ => ((H.conj (σ ^ s).mat) ^ p).trace
  -- f_alpha relates to F via: f_alpha α H ρ σ = α * ⟪ρ.M, H⟫ - (α-1) * F(σ.M)
  -- because -γ = -((1-α)/(2α)) = (α-1)/(2α) = s
  have hf_eq : ∀ σ : MState d, f_alpha α H ρ σ = α * ⟪ρ.M, H⟫_ℝ - (α - 1) * F σ.M := by
    intro σ
    show _ = α * ⟪ρ.M, H⟫_ℝ - (α - 1) *
      ((H.conj (σ.M ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace
    unfold f_alpha; ring_nf
  simp_rw [hf_eq]
  -- Reduce to concavity: ∑ w_i * F(σ_i.M) ≤ F(σ_mix.M)
  suffices h : ∑ i, w i * F (σs i).M ≤ F σ_mix.M by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw_sum, one_mul,
      mul_left_comm _ (α - 1), ← Finset.mul_sum]
    linarith [mul_le_mul_of_nonneg_left h hα_pos.le]
  have h_jensen := (trace_conj_rpow_concave hα H hH).le_map_sum
    (t := Finset.univ) (w := w) (p := fun i => (σs i).M)
    (fun i _ => hw_nonneg i) (by simp [hw_sum]) (fun i _ => (σs i).nonneg)
  rw [← hσ_mix] at h_jensen
  convert! h_jensen using 1

/-
**Step 4 (Joint convexity of f_α)**: For fixed `H ≥ 0` and `α > 1`, the map
`(ρ, σ) ↦ f_alpha α H ρ σ` is jointly convex. This follows from Steps 2 and 3:
f_α decomposes as a function linear in ρ (independent of σ) plus a function convex
in σ (independent of ρ).
-/
theorem f_alpha_jointly_convex (hα : 1 < α) (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (ρs σs : ι → MState d) (ρ_mix σ_mix : MState d)
    (hρ_mix : ρ_mix.M = ∑ i, w i • (ρs i).M)
    (hσ_mix : σ_mix.M = ∑ i, w i • (σs i).M) :
    f_alpha α H ρ_mix σ_mix ≤ ∑ i, w i * f_alpha α H (ρs i) (σs i) := by
  refine (f_alpha_convex_in_sigma hα H hH ρ_mix w hw_nonneg hw_sum σs σ_mix hσ_mix).trans ?_
  unfold f_alpha
  simp [hρ_mix]
  simp [sum_inner, inner_smul_left, mul_sub, sub_mul, mul_comm, mul_left_comm, Finset.mul_sum]
  simp [← Finset.mul_sum, ← Finset.sum_mul, hw_sum]

/-
The range of `H ↦ f_alpha α H ρ σ` over PSD `H` is bounded above.
This follows from the variational formula: the supremum equals `Q̃_α(ρ‖σ)`,
which is a finite real number.
-/
theorem f_alpha_bddAbove (hα : 1 < α) (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    BddAbove (Set.range (fun H : {H : HermitianMat d ℂ // 0 ≤ H} => f_alpha α H.1 ρ σ)) := by
  exact ⟨_, Set.forall_mem_range.mpr fun H => f_alpha_le_at_optimizer hα ρ σ _ H.2 hker⟩

/-
**Step 5 (Sup preserves convexity)**: The supremum over `H ≥ 0` of the jointly
convex `f_alpha α H` is jointly convex. This is a standard fact: for each `H`,
`f_alpha α H (ρ_mix) (σ_mix) ≤ ∑ wᵢ f_alpha α H (ρᵢ) (σᵢ) ≤ ∑ wᵢ sup_H f_alpha ...`,
so taking sup on the left gives the result.
-/
theorem iSup_f_alpha_jointly_convex (hα : 1 < α)
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (ρs σs : ι → MState d) (ρ_mix σ_mix : MState d)
    (hρ_mix : ρ_mix.M = ∑ i, w i • (ρs i).M)
    (hσ_mix : σ_mix.M = ∑ i, w i • (σs i).M)
    (hker : ∀ i, (σs i).M.ker ≤ (ρs i).M.ker) :
    (⨆ (H : {H : HermitianMat d ℂ // 0 ≤ H}), f_alpha α H.1 ρ_mix σ_mix) ≤
      ∑ i, w i * (⨆ (H : {H : HermitianMat d ℂ // 0 ≤ H}), f_alpha α H.1 (ρs i) (σs i)) := by
  refine ciSup_le fun H => (f_alpha_jointly_convex hα H.1 H.2 w hw_nonneg hw_sum ρs σs ρ_mix
    σ_mix hρ_mix hσ_mix).trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (le_ciSup (f_alpha_bddAbove hα (ρs i) (σs i) (hker i)) H) (hw_nonneg i))

/-- If for all i, ker(σs i) ≤ ker(ρs i), then ker(∑ w i • σs i) ≤ ker(∑ w i • ρs i),
provided all weights are nonneg and all matrices are PSD. -/
theorem HermitianMat.ker_weighted_sum_le {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i)
    (ρs σs : ι → HermitianMat d ℂ)
    (hρs_nonneg : ∀ i, 0 ≤ ρs i)
    (hσs_nonneg : ∀ i, 0 ≤ σs i)
    (hker : ∀ i, (σs i).ker ≤ (ρs i).ker) :
    (∑ i, w i • σs i).ker ≤ (∑ i, w i • ρs i).ker := by
  rw [ker_sum, ker_sum]
  · refine iInf_mono fun i ↦ ?_
    by_cases hi : w i = 0
    · simp [hi]
    · simp_all [ker_pos_smul]
  · exact fun i => smul_nonneg (hw_nonneg i) (hρs_nonneg i)
  · exact fun i => smul_nonneg (hw_nonneg i) (hσs_nonneg i)

/-- The trace functional `Q̃_α` is jointly convex for `α > 1`.
This is Proposition 3 of the paper, originally from Frank–Lieb.
The proof uses the variational formula:
  `Q̃_α(ρ‖σ) = sup_{H ≥ 0} f_α(H, ρ, σ)`
where `f_α(H, ρ, σ) = α · Tr[ρ H] - (α-1) · Tr[(σ^{-γ} H σ^{-γ})^{α/(α-1)}]`
is jointly convex in `(ρ, σ)` for fixed `H` (since the first term is linear and
the second uses the convexity of trace functions). The supremum of jointly convex
functions is jointly convex. -/
theorem sandwichedTraceFunctional_jointly_convex (hα : 1 < α) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1)
    (ρs σs : ι → MState d) (ρ_mix σ_mix : MState d)
    (hρ_mix : ρ_mix.M = ∑ i, w i • (ρs i).M)
    (hσ_mix : σ_mix.M = ∑ i, w i • (σs i).M)
    (hker : ∀ i, (σs i).M.ker ≤ (ρs i).M.ker) :
    Q̃_ α(ρ_mix‖σ_mix) ≤ ∑ i, w i * Q̃_ α(ρs i‖σs i) := by
  have hker' : σ_mix.M.ker ≤ ρ_mix.M.ker := by
    rw [hρ_mix, hσ_mix]
    exact ker_weighted_sum_le w hw_nonneg _ _ (fun i => (ρs i).nonneg) (fun i => (σs i).nonneg) hker
  rw [traceFunctional_eq_iSup_f_alpha hα ρ_mix σ_mix hker']
  calc ⨆ H : {H : HermitianMat d ℂ // 0 ≤ H}, f_alpha α H.1 ρ_mix σ_mix
      ≤ ∑ i, w i * (⨆ H : {H : HermitianMat d ℂ // 0 ≤ H}, f_alpha α H.1 (ρs i) (σs i)) :=
        iSup_f_alpha_jointly_convex hα w hw_nonneg hw_sum ρs σs ρ_mix σ_mix hρ_mix hσ_mix hker
    _ = ∑ i, w i * Q̃_ α(ρs i‖σs i) := by
        congr 1; ext i
        rw [traceFunctional_eq_iSup_f_alpha hα (ρs i) (σs i) (hker i)]

/-! ### Twirling Construction Helpers
We construct a twirling set using κ = Perm dB × (dB → Bool).
For each (σ, f), the unitary V(σ,f) is the product of a sign-diagonal matrix
(with entries ±1 determined by f) and a permutation matrix.
The averaging property follows from:
1. Sign averaging: summing over f kills off-diagonal entries
2. Permutation averaging: summing over σ uniformizes diagonal entries
-/

/-
A diagonal matrix with ±1 entries (determined by a Bool function) is unitary.
-/
private lemma signDiag_mem_unitaryGroup (f : dB → Bool) :
    Matrix.diagonal (fun i : dB => (if f i then (-1 : ℂ) else 1)) ∈ Matrix.unitaryGroup dB ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr with i
  split_ifs <;> simp_all

/-- The product of a ±1 diagonal matrix and a permutation matrix is unitary. -/
private lemma twirlingU_mem_unitaryGroup (σ : Equiv.Perm dB) (f : dB → Bool) :
    Matrix.diagonal (fun i : dB => (if f i then (-1 : ℂ) else 1)) * σ.permMatrix ℂ ∈
      Matrix.unitaryGroup dB ℂ :=
  mul_mem (signDiag_mem_unitaryGroup f) (σ.permMatrix_mem_unitaryGroup)

/-- The twirling unitary for a given permutation and sign function. -/
private def twirlingU (σ : Equiv.Perm dB) (f : dB → Bool) : Matrix.unitaryGroup dB ℂ :=
  ⟨Matrix.diagonal (fun i : dB => (if f i then (-1 : ℂ) else 1)) * σ.permMatrix ℂ,
   twirlingU_mem_unitaryGroup σ f⟩

/-
Entry of the conjugation by a twirling unitary:
  (X.conj (twirlingU σ f))_{pq} = sign(f,p) * sign(f,q) * X_{σp, σq}.
-/
private lemma twirlingU_conj_entry (X : HermitianMat dB ℂ) (σ : Equiv.Perm dB) (f : dB → Bool)
    (p q : dB) :
    (X.conj (twirlingU σ f : Matrix dB dB ℂ)) p q =
      (if f p then (-1 : ℂ) else 1) * (if f q then (-1 : ℂ) else 1) * X (σ p) (σ q) := by
  unfold twirlingU
  rw [← mat_apply, conj_apply_mat]
  simp [Matrix.mul_apply, Matrix.diagonal]
  simp [Finset.sum_ite]
  rw [Finset.sum_eq_single (σ q)]
  · split_ifs <;> simp_all
  · aesop
  · simp

/-
Summing the sign product over all Bool functions.
  For p = q, each term is 1, giving 2^(card dB).
  For p ≠ q, terms cancel in pairs (flip f at p).
-/
private lemma sum_sign_prod (p q : dB) :
    ∑ f : dB → Bool, ((if f p then (-1 : ℂ) else 1) * (if f q then (-1 : ℂ) else 1)) =
      if p = q then (2 ^ Fintype.card dB : ℕ) else 0 := by
  split_ifs with h
  · simp +contextual [h]
  · rw [Nat.cast_zero]
    refine Finset.sum_involution (fun f _ => Function.update f p (!f p)) ?_ ?_
      (fun _ _ => Finset.mem_univ _) (by simp)
    · intro g _
      rcases hp : g p <;> rcases hq : g q <;> simp_all [Ne.symm h]
    · intro g _ _
      simp

/-
Summing X_{σ(p), σ(p)} over all permutations σ.
  For each target k, exactly (card dB - 1)! permutations send p to k.
-/
private lemma sum_perm_diag_entry (X : HermitianMat dB ℂ) (p : dB) :
    ∑ σ : Equiv.Perm dB, X (σ p) (σ p) =
      ((Fintype.card dB - 1).factorial : ℂ) * ∑ k : dB, X k k := by
  have hn : 0 < Fintype.card dB := Fintype.card_pos_iff.mpr ⟨p⟩
  have h_eq : ∀ k : dB, (Finset.univ.filter (fun σ : Equiv.Perm dB => σ p = k)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm dB => σ p = p)).card := fun k =>
    Finset.card_bij (fun σ _ => Equiv.swap p k * σ) (by simp +contextual)
      (by simp) (fun b hb => ⟨Equiv.swap p k * b, by simp_all, by simp⟩)
  have h_card (k : dB) : (Finset.univ.filter (fun σ : Equiv.Perm dB => σ p = k)).card =
      (Fintype.card dB - 1).factorial := by
    have hc : ∑ j : dB, (Finset.univ.filter (fun σ : Equiv.Perm dB => σ p = j)).card =
        Finset.card (Finset.univ : Finset (Equiv.Perm dB)) := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_fiberwise]
    simp only [h_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_perm,
      ← Nat.mul_factorial_pred hn.ne'] at hc
    rw [h_eq k]
    exact Nat.eq_of_mul_eq_mul_left hn hc
  rw [Finset.sum_comp (fun k => X k k) (fun σ : Equiv.Perm dB => σ p),
    Finset.image_univ_of_surjective fun k => ⟨Equiv.swap p k, Equiv.swap_apply_left p k⟩]
  simp [h_card, Finset.mul_sum]

/-
The sum formula for twirling: summing the conjugation entries over all (σ, f) pairs.
-/
private lemma twirling_sum_eq [Nonempty dB] (X : HermitianMat dB ℂ) (p q : dB) :
    ∑ i : Equiv.Perm dB × (dB → Bool), (X.conj (twirlingU i.1 i.2 : Matrix dB dB ℂ)) p q =
      if p = q then ((Fintype.card dB - 1).factorial * 2 ^ Fintype.card dB : ℕ) * ∑ k, X k k
      else 0 := by
  -- Rewrite the sum as a double sum over σ and f using Finset.sum_product'.
  have h_double_sum : ∑ i : Equiv.Perm dB × (dB → Bool),
      ((conj (twirlingU i.1 i.2 : Matrix dB dB ℂ)) X) p q =
    ∑ σ : Equiv.Perm dB, ∑ f : dB → Bool, ((if f p then (-1 : ℂ) else 1) *
        (if f q then (-1 : ℂ) else 1) * X (σ p) (σ q)) := by
      simp_rw [Fintype.sum_prod_type, twirlingU_conj_entry]
  split_ifs with h
  · simp_all [← Finset.mul_sum]
    have := sum_perm_diag_entry X q; simp_all [mul_assoc, mul_comm]
  · rw [h_double_sum, Finset.sum_eq_zero]
    intro σ _
    rw [← Finset.sum_mul, sum_sign_prod p q]
    simp [h]

/-
The identity for the twirling set, stated for κ = Perm dB × (dB → Bool).
-/
private lemma twirling_identity [Nonempty dB] (X : HermitianMat dB ℂ) :
    (Fintype.card (Equiv.Perm dB × (dB → Bool)) : ℝ)⁻¹ •
      ∑ i : Equiv.Perm dB × (dB → Bool), X.conj (twirlingU i.1 i.2 : Matrix dB dB ℂ) =
        (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ) := by
  ext p q
  have mat_sum := map_sum
    (⟨⟨(mat : HermitianMat dB ℂ → Matrix dB dB ℂ), rfl⟩, mat_add⟩ :
      HermitianMat dB ℂ →+ Matrix dB dB ℂ)
    (fun i : Equiv.Perm dB × (dB → Bool) => X.conj (twirlingU i.1 i.2 : Matrix dB dB ℂ))
    Finset.univ
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at mat_sum
  rw [mat_smul, mat_smul, mat_sum, mat_one]
  simp only [Matrix.sum_apply, Matrix.smul_apply, mat_apply, twirling_sum_eq X p q,
    Matrix.one_apply, Fintype.card_prod, Fintype.card_perm, Fintype.card_pi, smul_ite, smul_zero]
  split_ifs with h
  · rw [Complex.real_smul, Complex.real_smul, mul_one]
    push_cast [Fintype.card_bool, Finset.prod_const, Finset.card_univ,
      show ((X.trace : ℝ) : ℂ) = ∑ k, X k k from X.trace_eq_trace,
      ← Nat.mul_factorial_pred Fintype.card_ne_zero]
    field_simp [Nat.factorial_ne_zero]
  · rfl

/-! ## Twirling Set

A twirling set for a finite-dimensional system `dB` is a set of unitary matrices
`{V_i}` on `dB` (indexed by some finite type `κ`) such that the average
`(1/|κ|) Σ_i V_i X V_i†` equals `Tr(X) · (1/dim(dB))` for all `X`.
When applied as `1_A ⊗ V_i` on a bipartite system `dA × dB`, this gives:
`(1/|κ|) Σ_i (1_A ⊗ V_i) ρ_AB (1_A ⊗ V_i)† = ρ_A ⊗ π_B`
where `π_B = 1/dim(dB)` is the maximally mixed state.

The standard construction uses the Heisenberg–Weyl (discrete Weyl) operators. -/

/-- A twirling set for the system `dB` exists: there is a finite collection of unitaries
whose average conjugation action twirls any matrix to a multiple of the identity.
Specifically, `(1/|κ|) Σ_i V_i X V_i† = (Tr X / dim dB) · I` for all Hermitian X on dB.
The standard construction uses the discrete Heisenberg-Weyl group of order `|dB|²`. -/
private lemma exists_twirling_unitaries [Nonempty dB] :
    ∃ (κ : Type) (_ : Fintype κ) (_ : Nonempty κ) (V : κ → Matrix.unitaryGroup dB ℂ),
      ∀ (X : HermitianMat dB ℂ),
        (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
          (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ) := by
  use Shrink (Equiv.Perm dB × (dB → Bool)), inferInstance, inferInstance
  use fun i => twirlingU ((equivShrink _).symm i).1 ((equivShrink _).symm i).2
  intro X
  rw [Fintype.card_shrink]
  convert twirling_identity X using 2
  exact Fintype.sum_equiv (equivShrink _).symm _ _ fun i => rfl


-- /-- Twirling on a bipartite system: applying `1_A ⊗ V_i` and averaging produces the
-- partial trace tensored with the maximally mixed state. -/
-- theorem twirling_bipartite [Nonempty dB]
--     (κ : Type) [Fintype κ] (V : κ → Matrix.unitaryGroup dB ℂ)
--     (hV : ∀ (X : HermitianMat dB ℂ),
--       (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
--         (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ))
--     (A : HermitianMat (dA × dB) ℂ) :
--     (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ,
--       A.conj (Matrix.kroneckerMap (· * ·) (1 : Matrix dA dA ℂ) (V i : Matrix dB dB ℂ)) =
--       A.traceRight ⊗ₖ ((Fintype.card dB : ℝ)⁻¹ • (1 : HermitianMat dB ℂ)) := by
--   not needed...

/-! ## Tensor Invariance

`Q̃_α(ρ ⊗ τ ‖ σ ⊗ τ) = Q̃_α(ρ ‖ σ)` for any state `τ`.
This corresponds to equation (2.4) in the paper. -/

/-
The trace functional is multiplicative over tensor products:
`Q̃_α(ρ₁ ⊗ ρ₂ ‖ σ₁ ⊗ σ₂) = Q̃_α(ρ₁‖σ₁) · Q̃_α(ρ₂‖σ₂)`.
-/
theorem sandwichedTraceFunctional_mul
    (ρ₁ σ₁ : MState dA) (ρ₂ σ₂ : MState dB) :
    Q̃_ α(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = Q̃_ α(ρ₁‖σ₁) * Q̃_ α(ρ₂‖σ₂) := by
  exact sandwiched_term_product ρ₁ σ₁ ρ₂ σ₂ α ((1 - α) / (2 * α))

/-
The trace functional of a state with itself equals 1.
This follows from the calculation: `γ = (1-α)/(2α)` gives `2γ + 1 = 1/α`,
so `σ^γ · σ · σ^γ = σ^(2γ+1) = σ^(1/α)`, and `(σ^(1/α))^α = σ^1`,
whose trace equals 1 since σ is a state.
-/
theorem sandwichedTraceFunctional_self (hα : 0 < α) (ρ : MState d) :
    Q̃_ α(ρ‖ρ) = 1 := by
  by_cases h : α = 1
  · subst h; simp [sandwichedTraceFunctional]
  · unfold sandwichedTraceFunctional
    show ((ρ.M.conj (ρ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace = 1
    have hγ : (1 - α) / (2 * α) ≠ 0 :=
      div_ne_zero (sub_ne_zero_of_ne (Ne.symm h)) (by positivity)
    have h1 : 1 + 2 * ((1 - α) / (2 * α)) = 1 / α := by field_simp; ring
    have h2 : ρ.M.conj (ρ.M ^ ((1 - α) / (2 * α))).mat = ρ.M ^ (1 / α) := by
      rw [← h1, ← conj_rpow ρ.pos.le hγ (by rw [h1]; exact one_div_ne_zero hα.ne'), rpow_one]
    rw [h2, ← rpow_mul ρ.pos.le, one_div_mul_cancel hα.ne', rpow_one]
    exact ρ.tr

/-- The trace functional is invariant under tensoring with a fixed state.
This follows from multiplicativity (`sandwichedTraceFunctional_mul`) and
the self-trace-functional being 1 (`sandwichedTraceFunctional_self`). -/
theorem sandwichedTraceFunctional_tensor_invariant (hα : 0 < α)
    (ρ σ : MState dA) (τ : MState dB) :
    Q̃_ α(ρ ⊗ᴹ τ‖σ ⊗ᴹ τ) = Q̃_ α(ρ‖σ) := by
  rw [sandwichedTraceFunctional_mul, sandwichedTraceFunctional_self hα, mul_one]

/-! ## Twirling MState Helpers

Helper lemmas for constructing MStates via the twirling argument. -/

/-- The MState obtained by conjugating a bipartite state by `1_A ⊗ V` where `V` is a unitary
on the `B` system. This is `(1_A ⊗ V) ρ_AB (1_A ⊗ V)†`. -/
def MState.conjTensorUnitary (ρ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ) :
    MState (dA × dB) :=
  ρ.U_conj ((1 : Matrix.unitaryGroup dA ℂ) ⊗ᵤ V)

/-- The twirled MState: averaging conjugation by `1_A ⊗ V_i` over all elements of
the twirling set gives `ρ_A ⊗ uniform_B`. We state the HermitianMat-level
equality needed for the joint convexity argument. -/
theorem MState.conjTensorUnitary_M (ρ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ) :
    (ρ.conjTensorUnitary V).M = ρ.M.conj ((1 : Matrix.unitaryGroup dA ℂ) ⊗ᵤ V).val := by
  rfl

/-- The trace functional is invariant under `1_A ⊗ V` conjugation. -/
theorem sandwichedTraceFunctional_conj_tensorUnitary
    (ρ σ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ) :
    Q̃_ α(ρ.conjTensorUnitary V‖σ.conjTensorUnitary V) = Q̃_ α(ρ‖σ) := by
  exact sandwichedTraceFunctional_conj_unitary_MState _ ρ σ

section twirling

variable {dA dB : Type*}
variable [Fintype dA] [Fintype dB]
variable [DecidableEq dA] [DecidableEq dB]
open scoped InnerProductSpace RealInnerProductSpace HermitianMat Matrix

omit [DecidableEq dB] in
-- The ((a₁,b₁),(a₂,b₂)) entry of (1⊗V)*M*(1⊗V)†
-- equals (V * block_{a₁,a₂} * V†)_{b₁,b₂}.
lemma conj_kron_one_entry (M : Matrix (dA × dB) (dA × dB) ℂ)
    (V : Matrix dB dB ℂ) (a₁ a₂ : dA) (b₁ b₂ : dB) :
    (Matrix.kroneckerMap (· * ·) (1 : Matrix dA dA ℂ) V * M *
     (Matrix.kroneckerMap (· * ·) (1 : Matrix dA dA ℂ) V).conjTranspose) (a₁, b₁) (a₂, b₂) =
    (V * (Matrix.of fun b₁' b₂' => M (a₁, b₁') (a₂, b₂')) * V.conjTranspose) b₁ b₂ := by
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, apply_ite,
    Finset.sum_ite_eq]

/-
For a Hermitian matrix, the twirling identity at the entry level.
Extracts from hV the entry-level equation.
-/
lemma twirling_hermitian_entry
    (κ : Type) [Fintype κ] (V : κ → Matrix.unitaryGroup dB ℂ)
    (hV : ∀ (X : HermitianMat dB ℂ),
      (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
        (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ))
    (X : HermitianMat dB ℂ) (b₁ b₂ : dB) :
    ∑ i : κ, ((V i).val * X.val * (V i).val.conjTranspose) b₁ b₂ =
    (X.val.trace / (Fintype.card dB : ℂ)) * (Fintype.card κ : ℂ) *
      (if b₁ = b₂ then 1 else 0) := by
  replace hV := congr_arg (fun s => s.val b₁ b₂) (hV X); simp_all [div_eq_inv_mul]
  convert congr_arg (fun x : ℂ => x * Fintype.card κ) hV using 1 <;> ring_nf
  · by_cases h : Fintype.card κ = 0 <;> simp_all [conj]
    · rw [Fintype.card_eq_zero_iff] at h
      simp_all only [Finset.univ_eq_empty, Finset.sum_empty]
    · classical induction (Finset.univ : Finset κ) using Finset.induction
      · simp_all [Matrix.mul_assoc]
      · simp_all [Matrix.mul_assoc]
        rfl
  · simp [Matrix.one_apply, mul_assoc, mul_comm]
    simp [Matrix.trace, trace]
    congr! 2
    exact Finset.sum_congr rfl fun _ _ => by simp [Complex.ext_iff]
/-
Extension of the twirling property from HermitianMat to general matrices.
-/
lemma twirling_general_matrix
    (κ : Type) [Fintype κ] (V : κ → Matrix.unitaryGroup dB ℂ)
    (hV : ∀ (X : HermitianMat dB ℂ),
      (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
        (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ))
    (X : Matrix dB dB ℂ) (b₁ b₂ : dB) :
    ∑ i : κ, ((V i).val * X * (V i).val.conjTranspose) b₁ b₂ =
    (X.trace / (Fintype.card dB : ℂ)) * (Fintype.card κ : ℂ) *
      (if b₁ = b₂ then 1 else 0) := by
  -- Decompose X into Hermitian and anti-Hermitian parts.
  set X_herm : Matrix dB dB ℂ := (1 / 2 : ℂ) • (X + X.conjTranspose)
  set X_anti_herm : Matrix dB dB ℂ := (1 / (2 * Complex.I) : ℂ) • (X - X.conjTranspose)
  have h_decomp : X = X_herm + Complex.I • X_anti_herm := by
    ext i j; norm_num [X_herm, X_anti_herm]; ring_nf
    norm_num; ring
  -- Apply thetwirling property to X_herm and X_anti_herm.
  have h_tw_h : ∑ i : κ, ((V i).val * X_herm * (V i).val.conjTranspose) b₁ b₂ =
      (X_herm.trace / (Fintype.card dB)) * (Fintype.card κ) * (if b₁ = b₂ then 1 else 0) := by
    convert twirling_hermitian_entry κ V hV ⟨X_herm, _⟩ b₁ b₂ using 1
    simp +zetaDelta at *
    ext i j; simp [Matrix.conjTranspose_apply]; ring
  have h_tw_a : ∑ i : κ, ((V i).val * X_anti_herm * (V i).val.conjTranspose) b₁ b₂ =
      (X_anti_herm.trace / (Fintype.card dB)) * (Fintype.card κ) * (if b₁ = b₂ then 1 else 0) := by
    convert twirling_hermitian_entry κ V hV ⟨X_anti_herm, ?_⟩ b₁ b₂ using 1
    ext i j; simp [X_anti_herm, Matrix.conjTranspose_apply]; ring
  rw [h_decomp]
  convert congr_arg₂ (· + ·) h_tw_h (congr_arg (fun x : ℂ => Complex.I * x) h_tw_a) using 1
  <;> simp [mul_add, add_mul, mul_assoc, Finset.mul_sum, Finset.sum_add_distrib]
  ring_nf
  split_ifs <;> ring

/-- The MState obtained by conjugating a bipartite state by `1_A ⊗ V`. -/
def MState.conjTensorUnitary' (ρ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ) :
    MState (dA × dB) :=
  ρ.U_conj ((1 : Matrix.unitaryGroup dA ℂ) ⊗ᵤ V)

-- Entry-level form of the conjTensorUnitary.
lemma conjTensorUnitary'_entry (ρ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ)
    (a₁ a₂ : dA) (b₁ b₂ : dB) :
    (ρ.conjTensorUnitary' V).M.val (a₁, b₁) (a₂, b₂) =
    ((V : Matrix dB dB ℂ) * (Matrix.of fun b₁' b₂' => ρ.M.val (a₁, b₁') (a₂, b₂')) *
     (V : Matrix dB dB ℂ).conjTranspose) b₁ b₂ := by
  apply conj_kron_one_entry

-- The RHS entry: (ρ.traceRight ⊗ᴹ uniform).M at ((a₁,b₁),(a₂,b₂)).
lemma prod_traceRight_uniform_entry [Nonempty dB] (ρ : MState (dA × dB))
    (a₁ a₂ : dA) (b₁ b₂ : dB) :
    (ρ.traceRight ⊗ᴹ MState.uniform).M.val (a₁, b₁) (a₂, b₂) =
    ρ.M.val.traceRight a₁ a₂ * ((Fintype.card dB : ℂ)⁻¹ * if b₁ = b₂ then 1 else 0) := by
  simp [MState.traceRight, MState.uniform, MState.ofClassical, diagonal, MState.prod, kronecker]
  rw [← mat_apply, mat_mk]
  simp [Matrix.diagonal_apply, mul_ite, mul_zero]

theorem twirling_average_eq [Nonempty dB]
    (κ : Type) [Fintype κ] (V : κ → Matrix.unitaryGroup dB ℂ)
    (hV : ∀ (X : HermitianMat dB ℂ),
      (Fintype.card κ : ℝ)⁻¹ • ∑ i : κ, X.conj (V i : Matrix dB dB ℂ) =
        (X.trace / Fintype.card dB) • (1 : HermitianMat dB ℂ))
    (ρ : MState (dA × dB)) :
    ∑ i : κ, ((Fintype.card κ : ℝ)⁻¹ • (ρ.conjTensorUnitary' (V i)).M) =
      (ρ.traceRight ⊗ᴹ MState.uniform).M := by
  have hκ : (Fintype.card κ : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    intro h0
    haveI := Fintype.card_eq_zero_iff.mp h0
    have h1 := congrArg HermitianMat.trace (hV 1)
    simp [Fintype.card_ne_zero] at h1
    exact absurd h1.symm (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hn : (Fintype.card dB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have mat_sum := map_sum (⟨⟨(mat : HermitianMat (dA × dB) ℂ → Matrix (dA × dB) (dA × dB) ℂ),
      rfl⟩, mat_add⟩ : HermitianMat (dA × dB) ℂ →+ Matrix (dA × dB) (dA × dB) ℂ)
    (fun i : κ => (Fintype.card κ : ℝ)⁻¹ • (ρ.conjTensorUnitary' (V i)).M) Finset.univ
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at mat_sum
  ext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  have h := twirling_general_matrix κ V hV
    (Matrix.of fun b₁' b₂' => ρ.M.val (a₁, b₁') (a₂, b₂')) b₁ b₂
  have htr : (Matrix.of fun b₁' b₂' => ρ.M.val (a₁, b₁') (a₂, b₂')).trace =
      ρ.M.val.traceRight a₁ a₂ := rfl
  have hprod := prod_traceRight_uniform_entry ρ a₁ a₂ b₁ b₂
  have hconj := fun i => conjTensorUnitary'_entry ρ (V i) a₁ a₂ b₁ b₂
  simp only [val_eq_coe, mat_apply] at h htr hprod hconj
  rw [mat_sum]
  simp only [Matrix.sum_apply, mat_smul, Matrix.smul_apply, mat_apply, hconj, hprod,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, ← Finset.mul_sum, h, htr]
  field_simp

end twirling

/-! ## Monotonicity Under Partial Trace (α > 1)

The main intermediate result: for `α > 1`, the trace functional `Q̃_α` is monotone
under partial trace:
`Q̃_α(ρ_AB ‖ σ_AB) ≥ Q̃_α(ρ_A ‖ σ_A)`.

The proof uses the twirling argument:
1. By unitary invariance, `Q̃_α(ρ_AB‖σ_AB) = Q̃_α(V_i ρ_AB V_i†‖V_i σ_AB V_i†)` for each `i`.
2. Averaging: `Q̃_α(ρ_AB‖σ_AB) = (1/|κ|) Σ_i Q̃_α(V_i ρ_AB V_i†‖V_i σ_AB V_i†)`.
3. By joint convexity (α > 1): `≥ Q̃_α((1/|κ|) Σ_i V_i ρ_AB V_i†‖(1/|κ|) Σ_i V_i σ_AB V_i†)`.
4. By twirling: `= Q̃_α(ρ_A ⊗ π_B ‖ σ_A ⊗ π_B)`.
5. By tensor invariance: `= Q̃_α(ρ_A ‖ σ_A)`. -/

/-- If `σ.M.ker ≤ ρ.M.ker`, then `(σ.conj B).ker ≤ (ρ.conj B).ker` for any matrix `B`.
This follows from `ker_conj` (which expresses `(A.conj B).ker` as a `comap`) and
`Submodule.comap_mono`. -/
lemma ker_conj_le_of_ker_le {n : Type*} [Fintype n] [DecidableEq n]
    {A B : HermitianMat n ℂ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A.ker ≤ B.ker)
    (C : Matrix n n ℂ) : (A.conj C).ker ≤ (B.conj C).ker := by
  rw [ker_conj hA, ker_conj hB]
  exact Submodule.comap_mono h

/-- Unitary conjugation preserves the kernel ordering between MStates.
If `σ.M.ker ≤ ρ.M.ker`, then `(σ.conjTensorUnitary V).M.ker ≤ (ρ.conjTensorUnitary V).M.ker`. -/
lemma MState.ker_conjTensorUnitary_le {dA dB : Type*} [Fintype dA] [Fintype dB]
    [DecidableEq dA] [DecidableEq dB]
    (ρ σ : MState (dA × dB)) (V : Matrix.unitaryGroup dB ℂ)
    (hker : σ.M.ker ≤ ρ.M.ker) :
    (σ.conjTensorUnitary V).M.ker ≤ (ρ.conjTensorUnitary V).M.ker := by
  simp only [MState.conjTensorUnitary_M]
  exact ker_conj_le_of_ker_le σ.nonneg ρ.nonneg hker _

/-- Monotonicity of the trace functional under partial trace for `α > 1`.
Equation (2.8) of the paper (second line). -/
theorem sandwichedTraceFunctional_mono_traceRight [Nonempty dB]
    (hα : 1 < α) (ρ σ : MState (dA × dB)) (hker : σ.M.ker ≤ ρ.M.ker) :
    Q̃_ α(ρ.traceRight‖σ.traceRight) ≤ Q̃_ α(ρ‖σ) := by
  -- Obtain the twirling unitaries
  obtain ⟨κ, hκ_fin, hκ_ne, V, hV⟩ := exists_twirling_unitaries (dB := dB)
  letI : Fintype κ := hκ_fin
  letI : Nonempty κ := hκ_ne
  -- By unitary invariance, Q̃_α(ρ‖σ) = Q̃_α(V_i ρ V_i†‖V_i σ V_i†) for each i
  have h_inv (i) : Q̃_ α(ρ.conjTensorUnitary (V i)‖σ.conjTensorUnitary (V i)) = Q̃_ α(ρ‖σ) :=
    sandwichedTraceFunctional_conj_tensorUnitary ρ σ (V i)
  -- Step 2: Q̃_α(ρ‖σ) = Σ_i (1/|κ|) * Q̃_α(V_i ρ V_i†‖V_i σ V_i†)
  have h_avg : Q̃_ α(ρ‖σ) = ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ *
      Q̃_ α(ρ.conjTensorUnitary (V i)‖σ.conjTensorUnitary (V i)) := by
    simp only [h_inv, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  -- Step 3: By joint convexity (α > 1)
  have hw_sum : ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ = 1 := by
    simp [Finset.card_univ]
  set ρ_mix := ρ.traceRight ⊗ᴹ MState.uniform (d := dB)
  set σ_mix := σ.traceRight ⊗ᴹ MState.uniform (d := dB)
  have hρ_mix : ρ_mix.M = ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ • (ρ.conjTensorUnitary (V i)).M :=
    (twirling_average_eq κ V hV ρ).symm
  have hσ_mix : σ_mix.M = ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ • (σ.conjTensorUnitary (V i)).M :=
    (twirling_average_eq κ V hV σ).symm
  have h_convex := sandwichedTraceFunctional_jointly_convex hα
    (fun (_ : κ) => (Fintype.card κ : ℝ)⁻¹) (by intro; positivity) hw_sum
    (fun i => ρ.conjTensorUnitary (V i)) (fun i => σ.conjTensorUnitary (V i))
    ρ_mix σ_mix hρ_mix hσ_mix
    (fun i => MState.ker_conjTensorUnitary_le ρ σ (V i) hker)
  -- Step 4 + 5: Q̃_α(ρ_A ⊗ π_B‖σ_A ⊗ π_B) = Q̃_α(ρ_A‖σ_A) by tensor invariance
  have h_tensor : Q̃_ α(ρ_mix‖σ_mix) = Q̃_ α(ρ.traceRight‖σ.traceRight) :=
    sandwichedTraceFunctional_tensor_invariant (by linarith) ρ.traceRight σ.traceRight .uniform
  -- Combine
  calc Q̃_ α(ρ.traceRight‖σ.traceRight)
      = Q̃_ α(ρ_mix‖σ_mix) := h_tensor.symm
    _ ≤ ∑ i : κ, (Fintype.card κ : ℝ)⁻¹ *
      Q̃_ α(ρ.conjTensorUnitary (V i)‖σ.conjTensorUnitary (V i)) := h_convex
    _ = Q̃_ α(ρ‖σ) := h_avg.symm

/-! ## DPI for Sandwiched Rényi Divergence Under Partial Trace -/

/-- The "tensor product" of a vector v with basis vector e_b:
    (v ⊗ e_b)(a, b') = v(a) if b' = b, else 0 -/
private def vecTensorBasis (v : dA → ℂ) (b : dB) : (dA × dB) → ℂ :=
  fun ⟨a, b'⟩ => if b' = b then v a else 0

omit [DecidableEq dA] in
/-- Key identity: ⟨v, (Tr_B A)v⟩ = ∑_b ⟨v⊗e_b, A(v⊗e_b)⟩ -/
private lemma inner_traceRight_eq_sum_inner_vecTensorBasis
    (A : Matrix (dA × dB) (dA × dB) ℂ) (v : dA → ℂ) :
    star v ⬝ᵥ A.traceRight *ᵥ v =
    ∑ b : dB, star (vecTensorBasis v b) ⬝ᵥ A *ᵥ (vecTensorBasis v b) := by
  simp [Matrix.traceRight, Matrix.mulVec, dotProduct, vecTensorBasis, Fintype.sum_prod_type,
    Finset.mul_sum, Finset.sum_mul, apply_ite, mul_comm, mul_assoc, mul_left_comm]
  exact (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm

omit [DecidableEq dA] in
/-- If A.mulVec(v⊗e_b) = 0 for all b, then (Tr_B A) *ᵥ v = 0 -/
private lemma traceRight_mulVec_zero_of_vecTensorBasis_zero
    (A : Matrix (dA × dB) (dA × dB) ℂ) (v : dA → ℂ)
    (h : ∀ b : dB, A *ᵥ (vecTensorBasis v b) = 0) :
    A.traceRight *ᵥ v = 0 := by
  ext i
  simp only [Matrix.traceRight, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  have hb := congrFun (h b) (i, b)
  simpa [Matrix.mulVec, dotProduct, vecTensorBasis, Fintype.sum_prod_type] using hb

/-- The kernel condition `σ.M.ker ≤ ρ.M.ker` is preserved under partial trace.
This follows because `supp(ρ) ⊆ supp(σ)` implies `supp(Tr_B ρ) ⊆ supp(Tr_B σ)`:
if `v ∈ supp(Tr_B ρ)`, then `⟨v, (Tr_B ρ) v⟩ > 0`, so for some basis vector `e_b`
we have `v ⊗ e_b ∈ supp(ρ) ⊆ supp(σ)`, hence `⟨v, (Tr_B σ) v⟩ ≥ ⟨v ⊗ e_b, σ (v ⊗ e_b)⟩ > 0`. -/
theorem ker_le_traceRight {ρ σ : MState (dA × dB)}
    (hker : σ.M.ker ≤ ρ.M.ker) :
    σ.traceRight.M.ker ≤ ρ.traceRight.M.ker := by
  simp only [MState.traceRight_M]
  intro v hv
  rw [mem_ker_iff_mulVec_zero, traceRight_mat] at hv
  rw [mem_ker_iff_mulVec_zero, traceRight_mat]
  have hσ_psd := zero_le_iff.mp σ.nonneg
  have hin : star v.ofLp ⬝ᵥ σ.M.mat.traceRight *ᵥ v.ofLp = 0 := by
    rw [hv]
    simp [dotProduct]
  rw [inner_traceRight_eq_sum_inner_vecTensorBasis] at hin
  refine traceRight_mulVec_zero_of_vecTensorBasis_zero ρ.M.mat v.ofLp fun b => ?_
  have h_zero : σ.M.mat *ᵥ vecTensorBasis v.ofLp b = 0 :=
    (hσ_psd.dotProduct_mulVec_zero_iff _).mp <|
      (Finset.sum_eq_zero_iff_of_nonneg fun b _ => hσ_psd.dotProduct_mulVec_nonneg _).mp
        hin b (Finset.mem_univ _)
  exact (mem_ker_iff_mulVec_zero _ (WithLp.toLp 2 (vecTensorBasis v.ofLp b))).mp
    (hker ((mem_ker_iff_mulVec_zero _ (WithLp.toLp 2 (vecTensorBasis v.ofLp b))).mpr h_zero))

/-- The sandwiched Rényi divergence is monotone under partial trace for `α > 1`.
This follows from monotonicity of the trace functional together with the fact that
`D̃_α = log(Q̃_α) / (α - 1)` and both `log` and `1/(α-1)` are order-preserving for α > 1. -/
theorem sandwichedRenyiEntropy_mono_traceRight [Nonempty dB]
    (hα : 1 < α) (ρ σ : MState (dA × dB))
    (hker : σ.M.ker ≤ ρ.M.ker) :
    D̃_ α(ρ.traceRight‖σ.traceRight) ≤ D̃_ α(ρ‖σ) := by
  have hα₀ : 0 < α := by linarith
  have hα₁ : α ≠ 1 := hα.ne'
  have hker_tr := ker_le_traceRight hker
  -- Rewrite both sides as log(Q̃) / (α - 1)
  rw [sandwichedRelRentropy_eq_log_traceFunctional hα₀ hα₁ hker,
      sandwichedRelRentropy_eq_log_traceFunctional hα₀ hα₁ hker_tr]
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (by linarith : 0 < α - 1).le
  exact Real.log_le_log (sandwichedTraceFunctional_pos ρ.traceRight σ.traceRight hker_tr)
    (sandwichedTraceFunctional_mono_traceRight hα ρ σ hker)

/-! ## DPI via Stinespring Dilation -/

/-
The sandwiched Rényi divergence is invariant under unitary conjugation.
-/
set_option maxHeartbeats 400000 in
theorem sandwichedRenyiEntropy_conj_unitary (hα : 0 < α) (ρ σ : MState d)
    (U : Matrix.unitaryGroup d ℂ) :
    D̃_ α(ρ.U_conj U‖σ.U_conj U) = D̃_ α(ρ‖σ) := by
  have hsurj : Function.Surjective ⇑(Matrix.toEuclideanLin U.val.conjTranspose) := fun y =>
    ⟨Matrix.toEuclideanLin U.val y, by
      rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, ← Matrix.star_eq_conjTranspose,
        U.2.1, Matrix.toLpLin_one, LinearMap.id_apply]⟩
  have h_kernel : σ.M.ker ≤ ρ.M.ker ↔ (σ.U_conj U).M.ker ≤ (ρ.U_conj U).M.ker := by
    show _ ↔ (σ.M.conj U.val).ker ≤ (ρ.M.conj U.val).ker
    rw [ker_conj σ.nonneg, ker_conj ρ.nonneg,
      Submodule.comap_le_comap_iff_of_surjective hsurj]
  by_cases h : σ.M.ker ≤ ρ.M.ker <;> simp_all [SandwichedRelRentropy]
  split_ifs <;> simp_all [MState.U_conj]
  · congr 1
    rw [inner_sub_right, inner_sub_right]
    grind only [log_conj_unitary, inner_conj_unitary]
  · ext1
    congr 3
    convert! congr_arg Real.log (sandwichedTraceFunctional_conj_unitary_MState U ρ σ) using 1

/-
The sandwiched Rényi divergence is invariant under tensoring with a fixed pure state:
`D̃_α(ρ ⊗ |ψ⟩⟨ψ| ‖ σ ⊗ |ψ⟩⟨ψ|) = D̃_α(ρ ‖ σ)`.
-/
theorem sandwichedRenyiEntropy_tensor_pure (hα : 0 < α) (ρ σ : MState d₁) (ψ : Ket d₂) :
    D̃_ α(ρ ⊗ᴹ MState.pure ψ‖σ ⊗ᴹ MState.pure ψ) = D̃_ α(ρ‖σ) := by
  simp [hα]

/-- The sandwiched Rényi divergence is invariant under SWAP. -/
@[simp]
theorem sandwichedRenyiEntropy_SWAP (ρ σ : MState (dA × dB)) :
    D̃_ α(ρ.SWAP‖σ.SWAP) = D̃_ α(ρ‖σ) := by
  exact sandwichedRelRentropy_relabel ρ σ _

/-
Monotonicity of the sandwiched Rényi divergence under traceRight for `α > 1`,
without the kernel condition. When the kernel condition fails, `D̃_α = ⊤` and
the inequality is trivial.
-/
theorem sandwichedRenyiEntropy_mono_traceRight' [Nonempty dB]
    (hα : 1 < α) (ρ σ : MState (dA × dB)) :
    D̃_ α(ρ.traceRight‖σ.traceRight) ≤ D̃_ α(ρ‖σ) := by
  by_cases hker : σ.M.ker ≤ ρ.M.ker
  · exact sandwichedRenyiEntropy_mono_traceRight hα ρ σ hker
  · simp only [SandwichedRelRentropy, MState.traceRight_M]
    split <;> simp_all

/-- Monotonicity of the sandwiched Rényi divergence under `traceLeft` for `α > 1`.
Follows from `sandwichedRenyiEntropy_mono_traceRight'` + SWAP invariance. -/
theorem sandwichedRenyiEntropy_mono_traceLeft [Nonempty dA]
    (hα : 1 < α) (ρ σ : MState (dA × dB)) :
    D̃_ α(ρ.traceLeft‖σ.traceLeft) ≤ D̃_ α(ρ‖σ) := by
  -- traceLeft = SWAP.traceRight, and SWAP preserves the SRD
  rw [← MState.traceRight_SWAP, ← MState.traceRight_SWAP]
  calc D̃_ α(ρ.SWAP.traceRight‖σ.SWAP.traceRight)
      ≤ D̃_ α(ρ.SWAP‖σ.SWAP) :=
        sandwichedRenyiEntropy_mono_traceRight' hα ρ.SWAP σ.SWAP
    _ = D̃_ α(ρ‖σ) := sandwichedRenyiEntropy_SWAP ρ σ

/-- Helper: The Stinespring preparation `prep ∘ append` equals tensoring with a fixed pure state.
`append = ofEquiv (Equiv.prodPUnit d₁).symm`.
TODO: PULLOUT to a more reasonable place. -/
theorem prep_append_eq_tensor_pure [Inhabited d₂] (ρ : MState d₁) :
    let ψ₀ : Ket (d₂ × d₂) := Ket.basis default
    let τ := MState.pure ψ₀
    let zero_prep : CPTPMap Unit (d₂ × d₂) := CPTPMap.replacement τ
    let prep := (CPTPMap.id ⊗ᶜᵖ zero_prep)
    let append : CPTPMap d₁ (d₁ × Unit) := CPTPMap.ofEquiv (Equiv.prodPUnit d₁).symm
    (prep ∘ₘ append) ρ = ρ ⊗ᴹ τ := by
  apply MState.ext
  ext1
  funext ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  have h := CPTPMap.prep_append_map_entry ρ.m a₁ b₁ a₂ b₂
  simp only [MState.prod, kronecker]
  exact h

/-- The Data Processing Inequality for the Sandwiched Rényi relative entropy (α > 1).
Every CPTP map `Φ` satisfies `D̃_α(Φρ‖Φσ) ≤ D̃_α(ρ‖σ)`.

The proof uses the Stinespring representation (see `CPTPMap.exists_purify`):
every CPTP map can be written as ancilla preparation + unitary conjugation + partial trace.
Since the sandwiched Rényi divergence is invariant under the first two operations
(by additivity and relabel invariance) and monotone under partial trace
(by `sandwichedRenyiEntropy_mono_traceRight`), the DPI follows. -/
theorem sandwichedRenyiEntropy_DPI_gt_one (hα : 1 < α) (ρ σ : MState d₁) (Φ : CPTPMap d₁ d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  have _ : Nonempty d₁ := ρ.nonempty
  have _ : Nonempty d₂ := (Φ ρ).nonempty
  haveI : Inhabited d₂ := Classical.inhabited_of_nonempty ‹_›
  let ψ₀ : Ket (d₂ × d₂) := Ket.basis default
  let τ := MState.pure ψ₀
  obtain ⟨U, hU⟩ := Φ.purify_IsUnitary
  -- USe the `zero_prep` / `prep` / `append` from `CPTPMap.purify_trace`
  let zero_prep : CPTPMap Unit (d₂ × d₂) := CPTPMap.replacement τ
  let prep := ((CPTPMap.id : CPTPMap d₁ d₁) ⊗ᶜᵖ zero_prep)
  let append : CPTPMap d₁ (d₁ × Unit) := CPTPMap.ofEquiv (Equiv.prodPUnit d₁).symm
  calc D̃_ α(Φ ρ‖Φ σ)
    _ = D̃_ α((Φ.purify ((prep ∘ₘ append) ρ)).traceLeft.traceLeft‖
            (Φ.purify ((prep ∘ₘ append) σ)).traceLeft.traceLeft) := by
        have h_trace (ξ) : Φ ξ = (Φ.purify ((prep ∘ₘ append) ξ)).traceLeft.traceLeft := by
          exact congr($Φ.purify_trace ξ)
        rw [h_trace ρ, h_trace σ]
    _ = D̃_ α(((ρ ⊗ᴹ τ).U_conj U).traceLeft.traceLeft‖
             ((σ ⊗ᴹ τ).U_conj U).traceLeft.traceLeft) := by
        have h_app (ξ) : Φ.purify ξ = ξ.U_conj U := congr($hU ξ)
        rw [prep_append_eq_tensor_pure ρ, prep_append_eq_tensor_pure σ, h_app, h_app]
    _ ≤ D̃_ α(((ρ ⊗ᴹ τ).U_conj U).traceLeft‖((σ ⊗ᴹ τ).U_conj U).traceLeft) :=
        sandwichedRenyiEntropy_mono_traceLeft hα ..
    _ ≤ D̃_ α((ρ ⊗ᴹ τ).U_conj U‖(σ ⊗ᴹ τ).U_conj U) :=
        sandwichedRenyiEntropy_mono_traceLeft hα ..
    _ = D̃_ α(ρ ⊗ᴹ τ‖σ ⊗ᴹ τ) :=
        sandwichedRenyiEntropy_conj_unitary (by positivity) _ _ _
    _ = D̃_ α(ρ‖σ) :=
        sandwichedRenyiEntropy_tensor_pure (by positivity) ρ σ ψ₀

/-
The DPI for the sandwiched Rényi divergence at α = 1 (the quantum relative entropy).
This follows from the α > 1 case by taking a limit, using the continuity of
`α ↦ D̃_α(ρ‖σ)` established in `sandwichedRelRentropy.continuousOn`.
-/
theorem sandwichedRenyiEntropy_DPI_eq_one (ρ σ : MState d₁) (Φ : CPTPMap d₁ d₂) :
    D̃_ 1(Φ ρ‖Φ σ) ≤ D̃_ 1(ρ‖σ) := by
  refine le_of_tendsto_of_tendsto (b := 𝓝[>] (1 : ℝ)) ?_ ?_ (Filter.eventually_of_mem
      self_mem_nhdsWithin fun x hx => sandwichedRenyiEntropy_DPI_gt_one hx ρ σ Φ) <;>
    exact tendsto_nhdsWithin_of_tendsto_nhds
      ((sandwichedRelRentropy.continuousOn _ _).continuousAt (Ioi_mem_nhds zero_lt_one))

/-- The Data Processing Inequality for the Sandwiched Renyi relative entropy.
Proved following the approach of Frank–Lieb and Leditzky–Rouzé–Datta. -/
theorem sandwichedRenyiEntropy_DPI (hα : 1 ≤ α) (ρ σ : MState d₁) (Φ : CPTPMap d₁ d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  rcases hα.lt_or_eq with hα | rfl
  · exact sandwichedRenyiEntropy_DPI_gt_one hα ρ σ Φ
  · exact sandwichedRenyiEntropy_DPI_eq_one ρ σ Φ

/-! ## Joint Convexity of the Relative Entropy

Joint convexity of the (Umegaki) quantum relative entropy is derived from joint convexity
of the trace functional `Q̃_α` (`sandwichedTraceFunctional_jointly_convex`) by letting
`α → 1⁺`, in the same way that `sandwichedRenyiEntropy_DPI_eq_one` follows from the
`α > 1` case.

For `α > 1` and states with compatible kernels, `log x ≤ x - 1` gives
`D̃_α(ρ‖σ) = log (Q̃_α(ρ‖σ)) / (α - 1) ≤ (Q̃_α(ρ‖σ) - 1) / (α - 1)`, and the difference
quotient on the right is jointly convex in `(ρ, σ)` because `Q̃_α` is. As `α → 1⁺`, the
left-hand side tends to `𝐃(ρ‖σ)` (by `sandwichedRelRentropy.continuousOn`), and the
difference quotient tends to `𝐃(ρ‖σ)` as well (since `Q̃_α = exp ((α - 1) D̃_α)` and
`exp x ≤ 1 + x + x²` for `|x| ≤ 1`), so the convex combination passes to the limit.
-/

/-- As `α → 1⁺`, the sandwiched Rényi relative entropy `D̃_α(ρ‖σ)` tends to the relative
entropy `𝐃(ρ‖σ) = D̃_1(ρ‖σ)`, by continuity of `α ↦ D̃_α` on `(0, ∞)`. -/
theorem sandwichedRelRentropy_tendsto_qRelativeEnt (ρ σ : MState d) :
    Filter.Tendsto (fun α : ℝ => D̃_ α(ρ‖σ)) (𝓝[>] 1) (𝓝 𝐃(ρ‖σ)) :=
  tendsto_nhdsWithin_of_tendsto_nhds
    ((sandwichedRelRentropy.continuousOn ρ σ).continuousAt (Ioi_mem_nhds zero_lt_one))

/-- As `α → 1⁺`, the difference quotient `(Q̃_α(ρ‖σ) - 1) / (α - 1)` is eventually bounded
above by a function tending to `𝐃(ρ‖σ).toReal`. This is the key estimate for transferring
joint convexity of the trace functional `Q̃_α` to the relative entropy `𝐃` in
`qRelativeEnt_joint_convexity`. -/
private lemma sandwichedTraceFunctional_sub_one_div_eventually_le
    (ρ σ : MState d) (hker : σ.M.ker ≤ ρ.M.ker) :
    ∃ u : ℝ → ℝ, Filter.Tendsto u (𝓝[>] 1) (𝓝 (𝐃(ρ‖σ)).toReal) ∧
      ∀ᶠ α in 𝓝[>] 1, (Q̃_ α(ρ‖σ) - 1) / (α - 1) ≤ u α := by
  set r : ℝ → ℝ := fun α => Real.log (Q̃_ α(ρ‖σ)) / (α - 1) with hr_def
  have h_ne : 𝐃(ρ‖σ) ≠ ⊤ := qRelativeEnt_ne_top_iff.mpr hker
  have h_r_nonneg : ∀ α : ℝ, 1 < α → 0 ≤ r α := by
    intro α hα
    have h := sandwichedRelRentropy_nonneg (ρ := ρ) (σ := σ) (α := α) (by linarith) hker
    rw [if_neg hα.ne'] at h
    simpa [hr_def, sandwichedTraceFunctional] using h
  have h_eq : ∀ α : ℝ, 1 < α → D̃_ α(ρ‖σ) = ENNReal.ofReal (r α) := fun α hα =>
    sandwichedRelRentropy_eq_log_traceFunctional (by linarith) hα.ne' hker
  -- `r` tends to `𝐃(ρ‖σ).toReal`, by continuity of `α ↦ D̃_α(ρ‖σ)` at `α = 1`.
  have h_r_tendsto : Filter.Tendsto r (𝓝[>] 1) (𝓝 (𝐃(ρ‖σ)).toReal) := by
    refine Filter.Tendsto.congr' ?_ ((ENNReal.tendsto_toReal h_ne).comp
      (sandwichedRelRentropy_tendsto_qRelativeEnt ρ σ))
    filter_upwards [self_mem_nhdsWithin] with α (hα : 1 < α)
    simp only [Function.comp_apply, h_eq α hα, ENNReal.toReal_ofReal (h_r_nonneg α hα)]
  have h_eps : Filter.Tendsto (fun α : ℝ => (α - 1) * r α) (𝓝[>] 1) (𝓝 0) := by
    have h₁ : Filter.Tendsto (fun α : ℝ => α - 1) (𝓝[>] 1) (𝓝 0) := by
      simpa using ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
    simpa using h₁.mul h_r_tendsto
  refine ⟨fun α => r α + ((α - 1) * r α) * r α, ?_, ?_⟩
  · simpa using h_r_tendsto.add (h_eps.mul h_r_tendsto)
  · -- Eventually `|(α - 1) * r α| ≤ 1`, so `exp x - 1 ≤ x + x²` applies with
    -- `x = (α - 1) * r α = log (Q̃_α)`.
    have h_small : ∀ᶠ α in 𝓝[>] 1, |(α - 1) * r α| ≤ 1 :=
      h_eps.eventually (Filter.eventually_of_mem (Metric.closedBall_mem_nhds 0 one_pos)
        fun x hx => by simpa [Real.dist_0_eq_abs] using hx)
    filter_upwards [self_mem_nhdsWithin, h_small] with α (hα : 1 < α) h_abs
    have hα1 : (0 : ℝ) < α - 1 := by linarith
    have hQ_pos : 0 < Q̃_ α(ρ‖σ) := sandwichedTraceFunctional_pos ρ σ hker
    have h_log : Real.log (Q̃_ α(ρ‖σ)) = (α - 1) * r α := by
      simp only [hr_def]
      field_simp
    have h_exp : Q̃_ α(ρ‖σ) = Real.exp ((α - 1) * r α) := by
      rw [← h_log, Real.exp_log hQ_pos]
    have h_bound : Q̃_ α(ρ‖σ) - 1 ≤ (α - 1) * r α + ((α - 1) * r α) ^ 2 := by
      have h₂ := Real.abs_exp_sub_one_sub_id_le h_abs
      have h₃ := le_abs_self (Real.exp ((α - 1) * r α) - 1 - (α - 1) * r α)
      rw [h_exp]
      linarith
    calc (Q̃_ α(ρ‖σ) - 1) / (α - 1)
        ≤ ((α - 1) * r α + ((α - 1) * r α) ^ 2) / (α - 1) :=
          div_le_div_of_nonneg_right h_bound hα1.le
      _ = r α + ((α - 1) * r α) * r α := by
          field_simp

/-- A binary `Mixable` mixture of states, written as a weighted sum of matrices over
`Fin 2` — the form consumed by `sandwichedTraceFunctional_jointly_convex` and
`HermitianMat.ker_weighted_sum_le`. -/
private lemma mix_M_eq_weighted_sum (p : Prob) (τ₁ τ₂ : MState d) :
    (p [τ₁ ↔ τ₂]).M = ∑ i, ![(p : ℝ), 1 - (p : ℝ)] i • (![τ₁, τ₂] i).M := by
  simp only [Mixable.mix, Mixable.mix_ab, MState.instMixable, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Prob.coe_one_minus]
  rfl

/-- A binary mixture preserves the support condition (kernel inclusion) of its
components. -/
private lemma ker_mix_le (p : Prob) {ρ₁ ρ₂ σ₁ σ₂ : MState d}
    (hker₁ : σ₁.M.ker ≤ ρ₁.M.ker) (hker₂ : σ₂.M.ker ≤ ρ₂.M.ker) :
    (p [σ₁ ↔ σ₂]).M.ker ≤ (p [ρ₁ ↔ ρ₂]).M.ker := by
  rw [mix_M_eq_weighted_sum, mix_M_eq_weighted_sum]
  exact HermitianMat.ker_weighted_sum_le _
    (by intro i; fin_cases i <;> simp) _ _
    (fun i => (![ρ₁, ρ₂] i).nonneg) (fun i => (![σ₁, σ₂] i).nonneg)
    (by intro i; fin_cases i <;> [exact hker₁; exact hker₂])

/-- Binary case of the joint convexity of the trace functional `Q̃_α` for `α > 1`
(`sandwichedTraceFunctional_jointly_convex`), stated for a `Mixable` mixture. -/
private lemma sandwichedTraceFunctional_mix_le (hα : 1 < α) (p : Prob)
    {ρ₁ ρ₂ σ₁ σ₂ : MState d}
    (hker₁ : σ₁.M.ker ≤ ρ₁.M.ker) (hker₂ : σ₂.M.ker ≤ ρ₂.M.ker) :
    Q̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤
      (p : ℝ) * Q̃_ α(ρ₁‖σ₁) + (1 - (p : ℝ)) * Q̃_ α(ρ₂‖σ₂) := by
  simpa [Fin.sum_univ_two] using sandwichedTraceFunctional_jointly_convex hα
    ![(p : ℝ), 1 - (p : ℝ)]
    (by intro i; fin_cases i <;> simp)
    (by simp [Fin.sum_univ_two]) ![ρ₁, ρ₂] ![σ₁, σ₂]
    (p [ρ₁ ↔ ρ₂]) (p [σ₁ ↔ σ₂])
    (mix_M_eq_weighted_sum p ρ₁ ρ₂) (mix_M_eq_weighted_sum p σ₁ σ₂)
    (by intro i; fin_cases i <;> [exact hker₁; exact hker₂])

/-- Joint convexity of the quantum relative entropy.

This is stated using `Mixable`, rather than `ConvexOn`, because `MState d`
is not an `AddCommMonoid`.
-/
theorem qRelativeEnt_joint_convexity :
    ∀ (ρ₁ ρ₂ σ₁ σ₂ : MState d), ∀ (p : Prob),
      𝐃(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤ p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
  intro ρ₁ ρ₂ σ₁ σ₂ p
  -- Degenerate mixing weights: the mixture is just one of the two pairs.
  rcases eq_or_ne p 0 with rfl | hp0
  · simp
  rcases eq_or_ne p 1 with rfl | hp1
  · simp
  have hp0' : (0 : ℝ) < p := Prob.zero_lt_coe hp0
  have hp1' : (p : ℝ) < 1 := lt_of_le_of_ne Prob.coe_le_one fun h => hp1 (Subtype.ext h)
  -- If either relative entropy on the right is `⊤`, the bound is trivial.
  by_cases hker₁ : σ₁.M.ker ≤ ρ₁.M.ker
  swap
  · have h_ne : ((p : NNReal) : ENNReal) ≠ 0 := by
      rw [ne_eq, Prob.ofNNReal_toNNReal, ENNReal.ofReal_eq_zero]
      exact not_le.mpr hp0'
    rw [qRelativeEnt_eq_top_iff.mpr hker₁, ENNReal.mul_top h_ne, top_add]
    exact le_top
  by_cases hker₂ : σ₂.M.ker ≤ ρ₂.M.ker
  swap
  · have h_ne : (1 : ENNReal) - ((p : NNReal) : ENNReal) ≠ 0 := by
      rw [ne_eq, tsub_eq_zero_iff_le, Prob.ofNNReal_toNNReal, not_le,
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg hp0'.le |>.mpr hp1'
    rw [qRelativeEnt_eq_top_iff.mpr hker₂, ENNReal.mul_top h_ne, add_top]
    exact le_top
  -- Main case: `0 < p < 1` and both kernel conditions hold, so both `𝐃`s are finite.
  obtain ⟨u₁, hu₁, hb₁⟩ := sandwichedTraceFunctional_sub_one_div_eventually_le ρ₁ σ₁ hker₁
  obtain ⟨u₂, hu₂, hb₂⟩ := sandwichedTraceFunctional_sub_one_div_eventually_le ρ₂ σ₂ hker₂
  have hker_mix : (p [σ₁ ↔ σ₂]).M.ker ≤ (p [ρ₁ ↔ ρ₂]).M.ker := ker_mix_le p hker₁ hker₂
  -- As `α → 1⁺`, `D̃_α` of the mixture tends to `𝐃` of the mixture...
  have h_lhs := sandwichedRelRentropy_tendsto_qRelativeEnt (p [ρ₁ ↔ ρ₂]) (p [σ₁ ↔ σ₂])
  -- ...and the convex combination of the majorants tends to the convex combination of the `𝐃`s.
  have h_rhs : Filter.Tendsto
      (fun α : ℝ => ENNReal.ofReal ((p : ℝ) * u₁ α + (1 - (p : ℝ)) * u₂ α)) (𝓝[>] 1)
      (𝓝 (p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂))) := by
    -- The limit is the `ENNReal`-valued convex combination of the two finite `𝐃`s,
    -- rewritten via `ofReal` of the corresponding real combination.
    have h_id : ENNReal.ofReal ((p : ℝ) * (𝐃(ρ₁‖σ₁)).toReal
        + (1 - (p : ℝ)) * (𝐃(ρ₂‖σ₂)).toReal) = p * 𝐃(ρ₁‖σ₁) + (1 - p) * 𝐃(ρ₂‖σ₂) := by
      have h1p : (0 : ℝ) ≤ 1 - (p : ℝ) := by simp
      rw [ENNReal.ofReal_add (mul_nonneg p.zero_le_coe ENNReal.toReal_nonneg)
          (mul_nonneg h1p ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul p.zero_le_coe, ENNReal.ofReal_mul h1p,
        ENNReal.ofReal_toReal (qRelativeEnt_ne_top_iff.mpr hker₁),
        ENNReal.ofReal_toReal (qRelativeEnt_ne_top_iff.mpr hker₂),
        ENNReal.ofReal_sub 1 p.zero_le_coe, ENNReal.ofReal_one]
      simp only [← Prob.ofNNReal_toNNReal]
    rw [← h_id]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((hu₁.const_mul (p : ℝ)).add (hu₂.const_mul (1 - (p : ℝ))))
  -- The pointwise bound for `α > 1`, from joint convexity of `Q̃_α` and `log x ≤ x - 1`.
  have h_ev : ∀ᶠ α in 𝓝[>] 1, D̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) ≤
      ENNReal.ofReal ((p : ℝ) * u₁ α + (1 - (p : ℝ)) * u₂ α) := by
    filter_upwards [self_mem_nhdsWithin, hb₁, hb₂] with α (hα : 1 < α) h₁ h₂
    have hα1 : (0 : ℝ) < α - 1 := by linarith
    have hQ_pos : 0 < Q̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂]) :=
      sandwichedTraceFunctional_pos _ _ hker_mix
    rw [sandwichedRelRentropy_eq_log_traceFunctional (by linarith) hα.ne' hker_mix]
    apply ENNReal.ofReal_le_ofReal
    calc Real.log (Q̃_ α(p [ρ₁ ↔ ρ₂]‖p [σ₁ ↔ σ₂])) / (α - 1)
        ≤ (((p : ℝ) * Q̃_ α(ρ₁‖σ₁) + (1 - (p : ℝ)) * Q̃_ α(ρ₂‖σ₂)) - 1) / (α - 1) :=
          div_le_div_of_nonneg_right ((Real.log_le_sub_one_of_pos hQ_pos).trans
            (sub_le_sub_right (sandwichedTraceFunctional_mix_le hα p hker₁ hker₂) 1)) hα1.le
      _ = (p : ℝ) * ((Q̃_ α(ρ₁‖σ₁) - 1) / (α - 1)) +
          (1 - (p : ℝ)) * ((Q̃_ α(ρ₂‖σ₂) - 1) / (α - 1)) := by
          field_simp
          ring
      _ ≤ (p : ℝ) * u₁ α + (1 - (p : ℝ)) * u₂ α :=
          add_le_add (mul_le_mul_of_nonneg_left h₁ hp0'.le)
            (mul_le_mul_of_nonneg_left h₂ (by linarith))
  exact le_of_tendsto_of_tendsto h_lhs h_rhs h_ev
