/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LiebAndoTrace
public import QuantumInfo.ForMathlib.HermitianMat.Schatten

@[expose] public section

/-! ## Main result for DPI

We derive the concavity of the trace functional `σ ↦ Tr[(σ^s H σ^s)^p]` from
the Lieb–Ando trace inequalities proved in `LiebAndoTrace.lean`.
-/

variable {d : Type*} [Fintype d] [DecidableEq d]

namespace HermitianMatBridge

/- Bridge lemmas: HermitianMat ↔ L (EuclideanSpace ℂ d)

We use `Matrix.toEuclideanCLM` (a `≃⋆ₐ[ℂ]`) to bridge between `Matrix d d ℂ`
and bounded operators on `EuclideanSpace ℂ d`. This allows us to apply
the Lieb–Ando trace inequalities proved in `LiebAndoTrace.lean` to
`HermitianMat` trace functionals.
-/

open LiebAndoTrace GeneralizedPerspectiveFunction

/-- Abbreviation for the star algebra isomorphism. -/
noncomputable abbrev Φ : Matrix d d ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) :=
  Matrix.toEuclideanCLM (n := d) (𝕜 := ℂ)

/-- `Φ` is continuous (as a linear map between finite-dimensional spaces). -/
lemma Φ_continuous : Continuous (⇑Φ : Matrix d d ℂ → _) :=
  (Φ (d := d)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

/-- `Φ` maps Hermitian matrices to self-adjoint operators. -/
lemma Φ_isSelfAdjoint (A : HermitianMat d ℂ) :
    IsSelfAdjoint (Φ A.mat) :=
  A.H.isSelfAdjoint.map Φ

/-
`Φ` preserves nonneg: PSD HermitianMat maps to nonneg operators.
-/
lemma Φ_nonneg (A : HermitianMat d ℂ) (hA : 0 ≤ A) :
    (0 : EuclideanSpace ℂ d →L[ℂ] EuclideanSpace ℂ d) ≤ Φ A.mat := by
  have h := star_mul_self_nonneg (Φ (A ^ (1/2 : ℝ)).mat)
  rwa [← map_star, ← map_mul, Matrix.star_eq_conjTranspose,
    (A ^ (1/2 : ℝ)).conjTranspose_mat, HermitianMat.pow_half_mul hA] at h

open ComplexOrder in
/-- `Φ` maps PosDef HermitianMat to pdSet. -/
lemma Φ_mem_pdSet [Nonempty d] (A : HermitianMat d ℂ) (hA : A.mat.PosDef) :
    Φ A.mat ∈ pdSet (ℋ := EuclideanSpace ℂ d) := by
  exact ⟨Φ_isSelfAdjoint A, (AlgEquiv.spectrum_eq (Φ.toAlgEquiv.restrictScalars ℝ) A.mat).symm ▸
    HermitianMat.Matrix.PosDef.spectrum_subset_Ioi hA⟩

set_option synthInstance.maxHeartbeats 80000 in
/-- `Φ` commutes with CFC for Hermitian matrices. -/
lemma Φ_cfc (A : HermitianMat d ℂ) (f : ℝ → ℝ) :
    Φ (cfc f A.mat) = cfc f (Φ A.mat) :=
  StarAlgHomClass.map_cfc Φ f A.mat (hφ := Φ_continuous) (ha := A.H.isSelfAdjoint)

set_option synthInstance.maxHeartbeats 80000 in
/-- `Φ` commutes with rpow for PSD matrices. -/
lemma Φ_rpow (A : HermitianMat d ℂ) (hA : 0 ≤ A) (r : ℝ) :
    Φ (A ^ r).mat = (Φ A.mat) ^ r := by
  rw [HermitianMat.rpow_eq_cfc, HermitianMat.mat_cfc]
  rw [Φ_cfc, CFC.rpow_eq_cfc_real (ha := Φ_nonneg A hA)]

/-- General trace bridge: the operator trace of Φ(M) equals the matrix trace of M,
for any matrix M (not just Hermitian). -/
lemma trace_Φ_eq (M : Matrix d d ℂ) :
    (LinearMap.trace ℂ (EuclideanSpace ℂ d)) (Φ M).toLinearMap = M.trace := by
  simp [LinearMap.trace_eq_matrix_trace ℂ (EuclideanSpace.basisFun d ℂ).toBasis, Φ,
    Matrix.toEuclideanCLM, EuclideanSpace.basisFun, Matrix.trace]

/-- `traceRe(Φ(M)) = re(Tr[M])` for any matrix M. -/
lemma traceRe_Φ_general (M : Matrix d d ℂ) :
    traceRe (Φ M) = Complex.re M.trace := by
  simp [traceRe, trace_Φ_eq]

end HermitianMatBridge

namespace HermitianMat

open LiebAndoTrace GeneralizedPerspectiveFunction ComplexOrder

omit [Fintype d] in
/-- The PSD cone is convex. -/
private lemma psd_convex : Convex ℝ {σ : HermitianMat d ℂ | 0 ≤ σ} :=
  convex_Ici 0

/-- The trace of rpow applied to a congruence is continuous in the base matrix. -/
private lemma trace_conj_rpow_continuous {s p : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p)
    (H : HermitianMat d ℂ) :
    Continuous (fun σ : HermitianMat d ℂ ↦
      ((H.conj (σ ^ s).mat) ^ p).trace) := by
  have h_trace : Continuous (fun σ : HermitianMat d ℂ => σ.trace) := by
    simp [HermitianMat.trace]
    fun_prop
  fun_prop

/-! ### Density and continuity lemmas for PD/PSD extension -/

private lemma psd_add_eps_posdef [Nonempty d] (σ : HermitianMat d ℂ) (hσ : 0 ≤ σ)
    (ε : ℝ) (hε : 0 < ε) : (σ + ε • (1 : HermitianMat d ℂ)).mat.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (σ + ε • 1).H fun x hx => ?_
  simp only [mat_add, mat_smul, mat_one, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_add, dotProduct_smul]
  exact add_pos_of_nonneg_of_pos ((zero_le_iff.mp hσ).dotProduct_mulVec_nonneg x)
    (smul_pos hε (Matrix.dotProduct_star_self_pos_iff.mpr hx))

omit [Fintype d] in
/-- σ + εI → σ as ε → 0+. -/
private lemma tendsto_add_eps (σ : HermitianMat d ℂ) :
    Filter.Tendsto (fun ε : ℝ ↦ σ + ε • (1 : HermitianMat d ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds σ) := by
  exact tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by fun_prop) _ _ (by simp))

/-! ### Helper lemmas for the core concavity proof -/

set_option maxHeartbeats 800000 in
/-- **AB/BA trace identity for rpow**: `Tr[(C^*C)^p] = Tr[(CC^*)^p]` for any square C. -/
private lemma trace_rpow_conjTranspose_mul_comm [Nonempty d]
    (C : Matrix d d ℂ) (p : ℝ) :
    let M₁ : HermitianMat d ℂ := ⟨_, Matrix.isHermitian_conjTranspose_mul_self C⟩
    let M₂ : HermitianMat d ℂ := ⟨_, Matrix.isHermitian_mul_conjTranspose_self C⟩
    (M₁ ^ p).trace = (M₂ ^ p).trace := by
  intro M₁ M₂
  rw [trace_rpow_eq_sum M₁ p, trace_rpow_eq_sum M₂ p]
  have h : M₁.mat.charpoly.roots = M₂.mat.charpoly.roots :=
    congr_arg Polynomial.roots (Matrix.charpoly_mul_comm C.conjTranspose C)
  rw [M₁.H.roots_charpoly_eq_eigenvalues, M₂.H.roots_charpoly_eq_eigenvalues] at h
  simpa using congr_arg (fun m => (m.map fun x : ℂ => x.re ^ p).sum) h

/-! ### Core concavity on positive definite matrices -/

section VariationalAndBridge
open InnerProductSpace

/-
Variational lower bound from trace Young inequality:
  `Tr[X^p] ≥ p · ⟪X, Z^r⟫ - (p-1) · Tr[Z]` where r = (p-1)/p.
  Proof: Young says ⟪X, Z^r⟫ ≤ Tr[X^p]/p + Tr[Z]/q (with q=p/(p-1)),
  so p·⟪X, Z^r⟫ ≤ Tr[X^p] + (p-1)·Tr[Z].
-/
private lemma variational_lower_bound
    (X Z : HermitianMat d ℂ) (hX : 0 ≤ X) (hZ : 0 ≤ Z)
    {p : ℝ} (hp : 1 < p) :
    p * ⟪X, Z ^ ((p-1)/p)⟫_ℝ - (p - 1) * Z.trace ≤ (X ^ p).trace := by
  have h := trace_young X (Z ^ ((p - 1) / p)) hX (rpow_nonneg hZ) p (p / (p - 1)) hp (by grind)
  rw [← rpow_mul hZ, show (p - 1) / p * (p / (p - 1)) = 1 from by grind, rpow_one] at h
  field_simp at h
  linarith

/-
At the optimizer Z = X^p, the variational bound is tight.
-/
private lemma variational_eq_optimizer
    (X : HermitianMat d ℂ) (hX : 0 ≤ X)
    {p : ℝ} (hp : 1 < p) :
    p * ⟪X, (X ^ p) ^ ((p-1)/p)⟫_ℝ - (p - 1) * (X ^ p).trace = (X ^ p).trace := by
  -- (X ^ p) ^ ((p - 1) / p) = X ^ (p * ((p - 1) / p)) = X ^ (p - 1)
  have h_exp : (X ^ p) ^ ((p - 1) / p) = X ^ (p - 1) := by
    rw [← rpow_mul hX, mul_div_cancel₀ _ (by positivity)]
  have h_inner : ⟪X, X ^ (p - 1)⟫_ℝ = (X ^ p).trace := by
    rw [inner_eq_re_trace, trace_eq_re_trace, Matrix.trace_mul_comm,
      show (X ^ (p - 1)).mat * X.mat = (X ^ p).mat by
        simpa using (mat_rpow_add hX (p := p - 1) (q := 1) (by linarith)).symm]
  rw [h_exp, h_inner]
  ring

/-
Joint concavity of the Lieb extension trace map on HermitianMat.
  This bridges `liebExtensionTrace_jointlyConcaveOn_pdSet` to HermitianMat.
-/
set_option maxHeartbeats 1600000 in
private lemma liebExtension_bridge [Nonempty d]
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q + r ≤ 1)
    (K : HermitianMat d ℂ)
    (σ₁ σ₂ Z₁ Z₂ : HermitianMat d ℂ)
    (hσ₁ : σ₁.mat.PosDef) (hσ₂ : σ₂.mat.PosDef)
    (hZ₁ : Z₁.mat.PosDef) (hZ₂ : Z₂.mat.PosDef)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) * ⟪(σ₁ ^ q).conj K, Z₁ ^ r⟫_ℝ + θ * ⟪(σ₂ ^ q).conj K, Z₂ ^ r⟫_ℝ ≤
    ⟪(((1 - θ) • σ₁ + θ • σ₂) ^ q).conj K, ((1 - θ) • Z₁ + θ • Z₂) ^ r⟫_ℝ := by
  open HermitianMatBridge GeneralizedPerspectiveFunction in
  -- Rewrite the inequality using the joint concavity result.
  have h_joint_concave :=
    LiebAndoTrace.liebExtensionTrace_jointlyConcaveOn_pdSet hr hq (by linarith) (Φ K.mat)
  have h_rewrite : ∀ σ Z : HermitianMat d ℂ, 0 ≤ σ → 0 ≤ Z →
      ⟪(σ ^ q).conj K, Z ^ r⟫_ℝ = liebExtensionTraceMap q r (Φ K.mat) (Φ σ.mat) (Φ Z.mat) := by
    intros σ Z hσ hZ
    have h_inner : ⟪(σ ^ q).conj K, Z ^ r⟫_ℝ = ((σ ^ q).mat * K * (Z ^ r).mat * K).trace.re := by
      rw [inner_eq_re_trace]
      simp [Matrix.mul_assoc, Matrix.trace_mul_comm K.mat]
    convert h_inner using 1
    rw [← traceRe_Φ_general]
    simp [liebExtensionTraceMap, Φ_rpow, hσ, hZ, (Φ_isSelfAdjoint K).star_eq]
  convert! h_joint_concave (Φ_mem_pdSet σ₁ hσ₁) (Φ_mem_pdSet σ₂ hσ₂)
    (Φ_mem_pdSet Z₁ hZ₁) (Φ_mem_pdSet Z₂ hZ₂) hθ₀ hθ₁ using 1
  · rw [h_rewrite σ₁ Z₁ (zero_le_iff.mpr hσ₁.posSemidef) (zero_le_iff.mpr hZ₁.posSemidef),
      h_rewrite σ₂ Z₂ (zero_le_iff.mpr hσ₂.posSemidef) (zero_le_iff.mpr hZ₂.posSemidef)]
    norm_num [Algebra.smul_def]
  · convert h_rewrite ((1 - θ) • σ₁ + θ • σ₂) ((1 - θ) • Z₁ + θ • Z₂) _ _ using 1
    · congr! 2 <;>
        simp only [mat_add, mat_smul, map_add, RCLike.real_smul_eq_coe_smul (K := ℂ), map_smul]
    all_goals have : 0 ≤ 1 - θ := by linarith
    all_goals positivity

/-
**AB/BA rewrite**: `Tr[(H.conj (σ^s))^p] = Tr[((σ^{2s}).conj (H^{1/2}))^p]` for PSD σ, H.
-/
private lemma trace_conj_rpow_eq_conj_sqrt [Nonempty d]
    (σ H : HermitianMat d ℂ) (hσ : 0 ≤ σ) (hH : 0 ≤ H) (s p : ℝ) (hs : 0 < s) :
    ((H.conj (σ ^ s).mat) ^ p).trace =
    (((σ ^ (2 * s)).conj (H ^ (1/2 : ℝ)).mat) ^ p).trace := by
  have h_exp : (σ ^ (2 * s)).mat = (σ ^ s).mat * (σ ^ s).mat := by
    rw [two_mul]
    exact mat_rpow_add hσ (by positivity)
  have h := trace_rpow_conjTranspose_mul_comm ((σ ^ s).mat * (H ^ (1 / 2 : ℝ)).mat) p
  convert h.symm using 3
  · ext1
    simp [conj_apply_mat, Matrix.conjTranspose_mul, ← pow_half_mul hH, Matrix.mul_assoc]
  · ext1
    simp [conj_apply_mat, Matrix.conjTranspose_mul, h_exp, Matrix.mul_assoc]

/-
Extension of liebExtension_bridge from PD to PSD Z inputs via continuity.
-/
private lemma liebExtension_bridge_psd [Nonempty d]
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q + r ≤ 1)
    (K σ₁ σ₂ Z₁ Z₂ : HermitianMat d ℂ)
    (hσ₁ : σ₁.mat.PosDef) (hσ₂ : σ₂.mat.PosDef)
    (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) * ⟪(σ₁ ^ q).conj K, Z₁ ^ r⟫_ℝ + θ * ⟪(σ₂ ^ q).conj K, Z₂ ^ r⟫_ℝ ≤
    ⟪(((1 - θ) • σ₁ + θ • σ₂) ^ q).conj K, ((1 - θ) • Z₁ + θ • Z₂) ^ r⟫_ℝ := by
  open scoped Topology in
  have h_cont : ∀ (ε : ℝ), 0 < ε → (1 - θ) * ⟪(σ₁ ^ q).conj K, (Z₁ + ε • 1) ^ r⟫_ℝ +
      θ * ⟪(σ₂ ^ q).conj K, (Z₂ + ε • 1) ^ r⟫_ℝ ≤ ⟪(((1 - θ) • σ₁ + θ • σ₂) ^ q).conj K,
      ((1 - θ) • (Z₁ + ε • 1) + θ • (Z₂ + ε • 1)) ^ r⟫_ℝ := by
    intro ε hε_pos
    exact liebExtension_bridge hq hr hqr K σ₁ σ₂ (Z₁ + ε • 1) (Z₂ + ε • 1) hσ₁ hσ₂
      (psd_add_eps_posdef Z₁ hZ₁ ε hε_pos) (psd_add_eps_posdef Z₂ hZ₂ ε hε_pos) θ hθ₀ hθ₁
  have key : ∀ X Z : HermitianMat d ℂ, Filter.Tendsto (fun ε : ℝ ↦ ⟪X, (Z + ε • 1) ^ r⟫_ℝ)
      (𝓝[>] 0) (𝓝 ⟪X, Z ^ r⟫_ℝ) := fun X Z => by
    have hc : Continuous fun ε : ℝ => (Z + ε • 1) ^ r :=
      (rpow_const_continuous hr.le).comp (by fun_prop)
    exact (tendsto_const_nhds.inner (hc.tendsto' 0 _ (by simp))).mono_left nhdsWithin_le_nhds
  have hmix : ∀ ε : ℝ, (1 - θ) • (Z₁ + ε • 1) + θ • (Z₂ + ε • 1) =
      (1 - θ) • Z₁ + θ • Z₂ + ε • 1 := fun ε => by module
  exact le_of_tendsto_of_tendsto
    ((tendsto_const_nhds.mul (key _ Z₁)).add (tendsto_const_nhds.mul (key _ Z₂)))
    (by simpa only [hmix] using key _ ((1 - θ) • Z₁ + θ • Z₂))
    (Filter.eventually_of_mem self_mem_nhdsWithin h_cont)

set_option maxHeartbeats 1600000 in
/-- Core concavity inequality on positive definite matrices. -/
private lemma trace_conj_rpow_concave_pd [Nonempty d] {α : ℝ} (hα : 1 < α)
    (H : HermitianMat d ℂ) (hH : 0 ≤ H)
    (σ₁ σ₂ : HermitianMat d ℂ) (hσ₁ : σ₁.mat.PosDef) (hσ₂ : σ₂.mat.PosDef)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    let s := (α - 1) / (2 * α)
    let p := α / (α - 1)
    a * ((H.conj (σ₁ ^ s).mat) ^ p).trace + b * ((H.conj (σ₂ ^ s).mat) ^ p).trace ≤
      ((H.conj ((a • σ₁ + b • σ₂) ^ s).mat) ^ p).trace := by
  intro s p
  -- Key derived parameters
  have hα_pos : 0 < α := by linarith
  have hαm1_pos : 0 < α - 1 := by linarith
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have hs_pos : 0 < s := by show 0 < (α - 1) / (2 * α); positivity
  have hp_gt1 : 1 < p := (one_lt_div hαm1_pos).mpr (by linarith)
  have hp_pos : 0 < p := by linarith
  -- The exponents for the bridge
  set q := (α - 1) / α with q_def
  set r := 1 / α with r_def
  have hq_pos : 0 < q := div_pos hαm1_pos hα_pos
  have hr_pos : 0 < r := div_pos one_pos hα_pos
  have hqr : q + r ≤ 1 := by
    rw [q_def, r_def, ← add_div, sub_add_cancel, div_self hα_ne]
  have h2s_eq_q : 2 * s = q := by
    show 2 * ((α - 1) / (2 * α)) = (α - 1) / α; field_simp
  have hr_eq : r = (p - 1) / p := by
    show 1 / α = (α / (α - 1) - 1) / (α / (α - 1)); field_simp; ring
  -- K = H^{1/2}
  set K := H ^ (1/2 : ℝ) with K_def
  -- PSD facts for σ_i
  have hσ₁_psd : 0 ≤ σ₁ := HermitianMat.zero_le_iff.mpr hσ₁.posSemidef
  have hσ₂_psd : 0 ≤ σ₂ := HermitianMat.zero_le_iff.mpr hσ₂.posSemidef
  have hσ_mix_psd : 0 ≤ a • σ₁ + b • σ₂ :=
    add_nonneg (smul_nonneg ha hσ₁_psd) (smul_nonneg hb hσ₂_psd)
  -- X_i = (σ_i ^ q).conj K
  set X₁ := (σ₁ ^ q).conj K.mat with X₁_def
  set X₂ := (σ₂ ^ q).conj K.mat with X₂_def
  set X_mix := ((a • σ₁ + b • σ₂) ^ q).conj K.mat with X_mix_def
  have hX₁ : 0 ≤ X₁ := conj_nonneg _ (rpow_nonneg hσ₁_psd)
  have hX₂ : 0 ≤ X₂ := conj_nonneg _ (rpow_nonneg hσ₂_psd)
  have hX_mix : 0 ≤ X_mix := conj_nonneg _ (rpow_nonneg hσ_mix_psd)
  -- Z_i = X_i ^ p
  set Z₁ := X₁ ^ p with Z₁_def
  set Z₂ := X₂ ^ p with Z₂_def
  have hZ₁ : 0 ≤ Z₁ := rpow_nonneg hX₁
  have hZ₂ : 0 ≤ Z₂ := rpow_nonneg hX₂
  have hZ_mix : 0 ≤ a • Z₁ + b • Z₂ :=
    add_nonneg (smul_nonneg ha hZ₁) (smul_nonneg hb hZ₂)
  -- Step 1: Rewrite using AB/BA identity
  have rewrite₁ : ((H.conj (σ₁ ^ s).mat) ^ p).trace = (Z₁).trace := by
    rw [trace_conj_rpow_eq_conj_sqrt σ₁ H hσ₁_psd hH s p hs_pos, h2s_eq_q]
  have rewrite₂ : ((H.conj (σ₂ ^ s).mat) ^ p).trace = (Z₂).trace := by
    rw [trace_conj_rpow_eq_conj_sqrt σ₂ H hσ₂_psd hH s p hs_pos, h2s_eq_q]
  have rewrite_mix : ((H.conj ((a • σ₁ + b • σ₂) ^ s).mat) ^ p).trace = (X_mix ^ p).trace := by
    rw [trace_conj_rpow_eq_conj_sqrt (a • σ₁ + b • σ₂) H hσ_mix_psd hH s p hs_pos, h2s_eq_q]
  rw [rewrite₁, rewrite₂, rewrite_mix]
  -- Step 2a: Use variational_eq_optimizer
  have var_opt₁ := variational_eq_optimizer X₁ hX₁ hp_gt1
  have var_opt₂ := variational_eq_optimizer X₂ hX₂ hp_gt1
  rw [← hr_eq] at var_opt₁ var_opt₂
  -- Step 2b: Rewrite LHS
  rw [show Z₁.trace = p * ⟪X₁, Z₁ ^ r⟫_ℝ - (p - 1) * Z₁.trace from var_opt₁.symm,
      show Z₂.trace = p * ⟪X₂, Z₂ ^ r⟫_ℝ - (p - 1) * Z₂.trace from var_opt₂.symm]
  -- Goal: a*(p*⟪X₁,Z₁^r⟫-(p-1)*Z₁.trace) + b*(p*⟪X₂,Z₂^r⟫-(p-1)*Z₂.trace) ≤ (X_mix^p).trace
  -- Step 2c-f: Chain inequality
  calc a * (p * ⟪X₁, Z₁ ^ r⟫_ℝ - (p - 1) * Z₁.trace) +
       b * (p * ⟪X₂, Z₂ ^ r⟫_ℝ - (p - 1) * Z₂.trace)
      = p * (a * ⟪X₁, Z₁ ^ r⟫_ℝ + b * ⟪X₂, Z₂ ^ r⟫_ℝ) -
        (p - 1) * (a * Z₁.trace + b * Z₂.trace) := by ring
    _ ≤ p * ⟪X_mix, (a • Z₁ + b • Z₂) ^ r⟫_ℝ -
        (p - 1) * (a • Z₁ + b • Z₂).trace := by
        have bridge := liebExtension_bridge_psd hq_pos hr_pos hqr K
          σ₁ σ₂ Z₁ Z₂ hσ₁ hσ₂ hZ₁ hZ₂ b hb (by linarith)
        rw [show (1 : ℝ) - b = a from by linarith] at bridge
        rw [trace_add, trace_smul, trace_smul]
        linarith [mul_le_mul_of_nonneg_left bridge hp_pos.le]
    _ ≤ (X_mix ^ p).trace := by
        rw [hr_eq]
        exact variational_lower_bound X_mix (a • Z₁ + b • Z₂) hX_mix hZ_mix hp_gt1

end VariationalAndBridge

/-
**Concavity of the trace functional for DPI**: For `α > 1`, `H ≥ 0`, the map
  `σ ↦ Tr[(σ^s H σ^s)^p]` is concave on PSD matrices,
  where `s = (α-1)/(2α)` and `p = α/(α-1)`.
-/
theorem trace_conj_rpow_concave {α : ℝ} (hα : 1 < α)
    (H : HermitianMat d ℂ) (hH : 0 ≤ H) :
    ConcaveOn ℝ {σ : HermitianMat d ℂ | 0 ≤ σ}
      (fun σ ↦ ((H.conj (σ ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace) := by
  refine' ⟨psd_convex, fun σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab => _⟩
  by_cases hd : Nonempty d
  · simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    have hcont : Continuous (fun σ : HermitianMat d ℂ ↦ ((H.conj (σ ^ ((α - 1) / (2 * α))).mat) ^
        (α / (α - 1))).trace) :=
      trace_conj_rpow_continuous (div_nonneg (sub_nonneg.2 hα.le) (by positivity))
        (div_nonneg (by positivity) (by linarith)) H
    open scoped Topology in
    refine' le_of_tendsto_of_tendsto (b := 𝓝[>] (0 : ℝ))
      (f := fun ε ↦ a * ((H.conj ((σ₁ + ε • 1) ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace +
        b * ((H.conj ((σ₂ + ε • 1) ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace)
      (g := fun ε ↦ ((H.conj ((a • (σ₁ + ε • 1) + b • (σ₂ + ε • 1)) ^ ((α - 1) / (2 * α))).mat) ^
        (α / (α - 1))).trace)
      ?_ ?_ _
    · exact (tendsto_const_nhds.mul (hcont.continuousAt.tendsto.comp (tendsto_add_eps _))).add
        (tendsto_const_nhds.mul (hcont.continuousAt.tendsto.comp (tendsto_add_eps _)))
    · exact hcont.continuousAt.tendsto.comp (tendsto_nhdsWithin_of_tendsto_nhds
        (Continuous.tendsto' (by fun_prop) _ (a • σ₁ + b • σ₂) (by simp)))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact trace_conj_rpow_concave_pd hα H hH _ _ (psd_add_eps_posdef σ₁ hσ₁ ε hε)
        (psd_add_eps_posdef σ₂ hσ₂ ε hε) a b ha hb hab
  · simp_all [HermitianMat.trace]

end HermitianMat
