/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Rpow
import QuantumInfo.ForMathlib.HermitianMat.Schatten
import QuantumInfo.ForMathlib.HermitianMat.LiebConcavityBridge
import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LiebAndoTrace
import Mathlib

/-! ## Main result for DPI

We derive the concavity of the trace functional `σ ↦ Tr[(σ^s H σ^s)^p]` from
the Lieb–Ando trace inequalities proved in `LiebAndoTrace.lean`.
-/

variable {d : Type*} [Fintype d] [DecidableEq d]

namespace HermitianMat

open LiebAndoTrace GeneralizedPerspectiveFunction ComplexOrder

set_option maxHeartbeats 400000 in
/-- The PSD cone is convex. -/
private lemma psd_convex : Convex ℝ {σ : HermitianMat d ℂ | 0 ≤ σ} := by
  intro σ₁ hσ₁ σ₂ hσ₂ a b ha hb _
  simp only [Set.mem_setOf_eq] at *
  exact add_nonneg (smul_nonneg ha hσ₁) (smul_nonneg hb hσ₂)

/-- The trace of rpow applied to a congruence is continuous in the base matrix. -/
private lemma trace_conj_rpow_continuous {s p : ℝ} (hs : 0 ≤ s) (hp : 0 ≤ p)
    (H : HermitianMat d ℂ) :
    Continuous (fun σ : HermitianMat d ℂ ↦
      ((H.conj (σ ^ s).mat) ^ p).trace) := by
  have h_rpow_cont : Continuous (fun σ : HermitianMat d ℂ => σ ^ s) :=
    rpow_const_continuous hs
  have h_conj_cont : Continuous (fun σ : HermitianMat d ℂ => (σ ^ s).mat) :=
    Continuous.subtype_val h_rpow_cont
  have h_trace_cont : Continuous (fun σ : HermitianMat d ℂ => σ.trace) := by
    simp [HermitianMat.trace]; fun_prop
  have h_comp_cont : Continuous (fun σ : Matrix d d ℂ => ((conj σ H) ^ p).trace) := by
    have h_conj_cont : Continuous (fun σ : Matrix d d ℂ => conj σ H) :=
      continuous_conj H
    exact h_trace_cont.comp (rpow_const_continuous hp |>.comp h_conj_cont)
  exact h_comp_cont.comp h_conj_cont

/-! ### Density and continuity lemmas for PD/PSD extension -/

private lemma psd_add_eps_posdef [Nonempty d] (σ : HermitianMat d ℂ) (hσ : 0 ≤ σ)
    (ε : ℝ) (hε : 0 < ε) : (σ + ε • (1 : HermitianMat d ℂ)).mat.PosDef := by
  refine' ⟨ _, _ ⟩;
  · exact H (σ + ε • 1);
  · intro x hx_ne_zero
    have h_pos : 0 < ∑ i, ∑ j, star (x i) * (σ.mat i j + ε * (if i = j then 1 else 0)) * x j := by
      have h_pos : 0 ≤ ∑ i, ∑ j, star (x i) * σ i j * x j := by
        have := hσ.2;
        simpa [ Finsupp.sum_fintype, Finset.sum_mul _ _ _ ] using this x;
      simp_all [ mul_add, add_mul, Finset.sum_add_distrib ];
      refine' add_pos_of_nonneg_of_pos h_pos _;
      simp_all [ mul_assoc, mul_comm, mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq ];
      contrapose! hx_ne_zero;
      ext i; simp_all [ Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ;
      exact not_not.mp fun hi => hx_ne_zero <| lt_of_lt_of_le ( by positivity ) <| Finset.single_le_sum ( fun i _ => by positivity ) <| Finset.mem_univ i;
    simp [ Finsupp.sum, Matrix.add_apply, Matrix.smul_apply ];
    convert h_pos using 1;
    rw [ Finset.sum_subset ( Finset.subset_univ x.support ) ];
    · exact Finset.sum_congr rfl fun i hi => Finset.sum_subset ( Finset.subset_univ _ ) fun j hj₁ hj₂ => by aesop;
    · aesop

/-- σ + εI → σ as ε → 0+. -/
private lemma tendsto_add_eps (σ : HermitianMat d ℂ) :
    Filter.Tendsto (fun ε : ℝ ↦ σ + ε • (1 : HermitianMat d ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds σ) := by
  exact tendsto_nhdsWithin_of_tendsto_nhds
    (Continuous.tendsto' (by continuity) _ _ (by simp))

/-! ### Helper lemmas for the core concavity proof -/

set_option maxHeartbeats 800000 in
/-- **AB/BA trace identity for rpow**: `Tr[(C^*C)^p] = Tr[(CC^*)^p]` for any square C. -/
private lemma trace_rpow_conjTranspose_mul_comm [Nonempty d]
    (C : Matrix d d ℂ) (p : ℝ) :
    let M₁ : HermitianMat d ℂ := ⟨C.conjTranspose * C, Matrix.isHermitian_conjTranspose_mul_self C⟩
    let M₂ : HermitianMat d ℂ := ⟨C * C.conjTranspose, Matrix.isHermitian_mul_conjTranspose_self C⟩
    (M₁ ^ p).trace = (M₂ ^ p).trace := by
  intro M₁ M₂
  rw [trace_rpow_eq_sum M₁ p, trace_rpow_eq_sum M₂ p]
  have hcharpoly : M₁.mat.charpoly = M₂.mat.charpoly :=
    Matrix.charpoly_mul_comm C.conjTranspose C
  rw [M₁.H.charpoly_eq, M₂.H.charpoly_eq] at hcharpoly
  have hmultiset : Finset.univ.val.map (fun i => (M₁.H.eigenvalues i : ℂ)) =
                   Finset.univ.val.map (fun i => (M₂.H.eigenvalues i : ℂ)) := by
    have h1 := Polynomial.roots_multiset_prod_X_sub_C
      (Finset.univ.val.map (fun i => (M₁.H.eigenvalues i : ℂ)))
    have h2 := Polynomial.roots_multiset_prod_X_sub_C
      (Finset.univ.val.map (fun i => (M₂.H.eigenvalues i : ℂ)))
    simp only [Multiset.map_map] at h1 h2
    rw [← h1, ← h2]; congr 1
  have hmap : Finset.univ.val.map (fun i => M₁.H.eigenvalues i ^ p) =
              Finset.univ.val.map (fun i => M₂.H.eigenvalues i ^ p) := by
    have := congr_arg (Multiset.map (fun x : ℂ => x.re ^ p)) hmultiset
    simp [Multiset.map_map, Function.comp, Complex.ofReal_re] at this
    exact this
  simpa using congr_arg Multiset.sum hmap

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
  have := @HermitianMat.trace_young d _ _ X ( Z ^ ( ( p - 1 ) / p ) ) hX ( ?_ ) p ( p / ( p - 1 ) ) hp ?_;
  · -- Using the fact that $Z$ is positive semi-definite, we can simplify the expression.
    have hZ_pow : ((Z ^ ((p - 1) / p)) ^ (p / (p - 1))) = Z := by
      rw [ ← HermitianMat.rpow_mul ];
      · field_simp;
        rw [ div_self ( by linarith ), HermitianMat.rpow_one ];
      · exact hZ;
    simp_all [ ne_of_gt ( zero_lt_one.trans hp ), mul_div_cancel₀ ];
    field_simp at this;
    exact this;
  · exact rpow_nonneg hZ;
  · grind

/-
At the optimizer Z = X^p, the variational bound is tight.
-/
private lemma variational_eq_optimizer
    (X : HermitianMat d ℂ) (hX : 0 ≤ X)
    {p : ℝ} (hp : 1 < p) :
    p * ⟪X, (X ^ p) ^ ((p-1)/p)⟫_ℝ - (p - 1) * (X ^ p).trace = (X ^ p).trace := by
  -- By definition of exponentiation, we know that $(X ^ p) ^ ((p - 1) / p) = X ^ (p * ((p - 1) / p)) = X ^ (p - 1)$.
  have h_exp : (X ^ p) ^ ((p - 1) / p) = X ^ (p - 1) := by
    rw [ ← rpow_mul hX, mul_div_cancel₀ _ ( by positivity ) ];
  have h_inner : ⟪X, X ^ (p - 1)⟫_ℝ = (X ^ p).trace := by
    have h_inner : ⟪X, X ^ (p - 1)⟫_ℝ = (X * (X ^ (p - 1)).mat).trace.re := by
      exact Real.ext_cauchy rfl;
    convert h_inner using 1;
    have h_exp : (X ^ p).mat = X.mat * (X ^ (p - 1)).mat := by
      convert mat_rpow_add hX _;
      rotate_left;
      rotate_left;
      exacts [ 1, by linarith, by ring, by simp ];
    exact h_exp ▸ rfl;
  rw [ h_exp, h_inner ] ; ring

/-
Joint concavity of the Lieb extension trace map on HermitianMat.
  This bridges `liebExtensionTrace_jointlyConcaveOn_pdSet` to HermitianMat.
-/
set_option maxHeartbeats 1600000 in
private lemma liebExtension_bridge [Nonempty d]
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q + r ≤ 1)
    (K : HermitianMat d ℂ) (hK : 0 ≤ K)
    (σ₁ σ₂ Z₁ Z₂ : HermitianMat d ℂ)
    (hσ₁ : σ₁.mat.PosDef) (hσ₂ : σ₂.mat.PosDef)
    (hZ₁ : Z₁.mat.PosDef) (hZ₂ : Z₂.mat.PosDef)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) * ⟪(σ₁ ^ q).conj K, Z₁ ^ r⟫_ℝ + θ * ⟪(σ₂ ^ q).conj K, Z₂ ^ r⟫_ℝ ≤
    ⟪(((1 - θ) • σ₁ + θ • σ₂) ^ q).conj K, ((1 - θ) • Z₁ + θ • Z₂) ^ r⟫_ℝ := by
  -- By the properties of the trace and the Lieb extension trace map, we can rewrite the inequality using the joint concavity result.
  have h_joint_concave : GeneralizedPerspectiveFunction.JointlyConcaveOn (pdSet (ℋ := EuclideanSpace ℂ d)) (pdSet (ℋ := EuclideanSpace ℂ d)) (LiebAndoTrace.liebExtensionTraceMap q r (HermitianMatBridge.Φ K.mat)) := by
    apply_rules [ LiebAndoTrace.liebExtensionTrace_jointlyConcaveOn_pdSet ];
    linarith;
  have h_rewrite : ∀ σ Z : HermitianMat d ℂ, 0 ≤ σ → 0 ≤ Z → ⟪(σ ^ q).conj K, Z ^ r⟫_ℝ = liebExtensionTraceMap q r (HermitianMatBridge.Φ K.mat) (HermitianMatBridge.Φ σ.mat) (HermitianMatBridge.Φ Z.mat) := by
    intros σ Z hσ hZ
    have h_inner : ⟪(σ ^ q).conj K, Z ^ r⟫_ℝ = Complex.re ((σ ^ q).mat * K.mat * (Z ^ r).mat * K.mat).trace := by
      rw [ inner_eq_re_trace ];
      simp [ Matrix.mul_assoc, Matrix.trace_mul_comm K.mat ];
    convert h_inner using 1;
    rw [ ← HermitianMatBridge.traceRe_Φ_general ];
    simp [ liebExtensionTraceMap, HermitianMatBridge.Φ_rpow, hσ, hZ ];
    rw [ show star ( HermitianMatBridge.Φ K.mat ) = HermitianMatBridge.Φ K.mat from ?_ ];
    have h_rewrite : IsSelfAdjoint (HermitianMatBridge.Φ K.mat) := by
      exact HermitianMatBridge.Φ_isSelfAdjoint K;
    exact h_rewrite;
  nontriviality;
  convert h_joint_concave (HermitianMatBridge.Φ_mem_pdSet σ₁ hσ₁) (HermitianMatBridge.Φ_mem_pdSet σ₂ hσ₂) (HermitianMatBridge.Φ_mem_pdSet Z₁ hZ₁) (HermitianMatBridge.Φ_mem_pdSet Z₂ hZ₂) hθ₀ hθ₁ using 1;
  · rw [ h_rewrite σ₁ Z₁ ( by
      constructor;
      · simp [ Matrix.IsHermitian ];
      · intro x; have := hσ₁.2; simp_all [ Matrix.mulVec, dotProduct ] ;
        exact if hx : x = 0 then by simp [ hx ] else le_of_lt ( this hx ) ) ( by
      finiteness ), h_rewrite σ₂ Z₂ ( by
      finiteness ) ( by
      finiteness ) ];
    norm_num [ Algebra.smul_def ];
  · convert h_rewrite ( ( 1 - θ ) • σ₁ + θ • σ₂ ) ( ( 1 - θ ) • Z₁ + θ • Z₂ ) _ _ using 1;
    · congr! 2;
      · ext; simp [ HermitianMatBridge.Φ ] ;
        simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_add_distrib ];
      · ext; simp [ HermitianMatBridge.Φ ] ;
        simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _ ];
        simp only [mul_assoc];
    · nontriviality;
      have h_pos_def : ∀ (A : HermitianMat d ℂ), A.mat.PosDef → 0 ≤ A := by
        intro A hA;
        have := hA.2;
        constructor;
        · simp [ Matrix.IsHermitian, A.2 ];
        · intro x; by_cases hx : x = 0 <;> simp_all [ Matrix.PosDef ] ;
          exact le_of_lt ( hA.2 hx );
      exact add_nonneg ( smul_nonneg ( sub_nonneg.2 hθ₁ ) ( h_pos_def σ₁ hσ₁ ) ) ( smul_nonneg hθ₀ ( h_pos_def σ₂ hσ₂ ) );
    · constructor <;> norm_num;
      · simp [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul ];
      · intro x;
        have h_pos_def : ∀ (x : d →₀ ℂ), 0 ≤ x.sum (fun i xi => x.sum (fun j xj => (starRingEnd ℂ) xi * Z₁ i j * xj)) ∧ 0 ≤ x.sum (fun i xi => x.sum (fun j xj => (starRingEnd ℂ) xi * Z₂ i j * xj)) := by
          intro x
          have h_pos_def : ∀ (x : d →₀ ℂ), 0 ≤ x.sum (fun i xi => x.sum (fun j xj => (starRingEnd ℂ) xi * Z₁ i j * xj)) := by
            intro x
            have h_pos_def : ∀ (x : d →₀ ℂ), 0 ≤ x.sum (fun i xi => x.sum (fun j xj => (starRingEnd ℂ) xi * Z₁ i j * xj)) := by
              intro x
              have h_pos_def : ∀ (x : d → ℂ), 0 ≤ ∑ i, ∑ j, (starRingEnd ℂ) (x i) * Z₁ i j * x j := by
                intro x
                have h_pos_def : ∀ (x : d → ℂ), 0 ≤ ∑ i, ∑ j, (starRingEnd ℂ) (x i) * Z₁ i j * x j := by
                  intro x
                  have h_pos_def : ∀ (x : d → ℂ), 0 ≤ ∑ i, ∑ j, (starRingEnd ℂ) (x i) * Z₁ i j * x j := by
                    intro x
                    exact (by
                    have := hZ₁.2;
                    contrapose! this;
                    refine' ⟨ Finsupp.equivFunOnFinite.symm x, _, _ ⟩ <;> simp_all [ Finsupp.sum_fintype ];
                    · intro h; simp_all [ Finsupp.ext_iff ] ;
                    · exact fun h => this <| le_of_lt h)
                  exact h_pos_def x;
                exact h_pos_def x
              convert h_pos_def ( fun i => x i ) using 1;
              simp [ Finsupp.sum_fintype ]
            exact h_pos_def x;
          have := hZ₂.2;
          exact ⟨ h_pos_def x, if hx : x = 0 then by simp [ hx ] else le_of_lt ( this hx ) ⟩;
        simp_all [ mul_add, add_mul, mul_assoc, mul_left_comm, Finset.sum_add_distrib ];
        simp_all [ Finsupp.sum, mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ];
        simp_all [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
        exact add_nonneg ( mul_nonneg ( sub_nonneg.2 <| mod_cast hθ₁ ) <| h_pos_def x |>.1 ) ( mul_nonneg ( mod_cast hθ₀ ) <| h_pos_def x |>.2 )

/-
**AB/BA rewrite**: `Tr[(H.conj (σ^s))^p] = Tr[((σ^{2s}).conj (H^{1/2}))^p]` for PSD σ, H.
-/
private lemma trace_conj_rpow_eq_conj_sqrt [Nonempty d]
    (σ H : HermitianMat d ℂ) (hσ : 0 ≤ σ) (hH : 0 ≤ H) (s p : ℝ) (hs : 0 < s) :
    ((H.conj (σ ^ s).mat) ^ p).trace =
    (((σ ^ (2 * s)).conj (H ^ (1/2 : ℝ)).mat) ^ p).trace := by
  norm_num [ conj_apply_mat, Matrix.mul_assoc ];
  -- By definition of exponentiation for Hermitian matrices, we know that $(σ^{2s}).mat = (σ^s).mat * (σ^s).mat$.
  have h_exp : (σ ^ (2 * s)).mat = (σ ^ s).mat * (σ ^ s).mat := by
    convert mat_rpow_add hσ _ using 1 <;> ring_nf
    positivity;
  have h_exp' : (H ^ (1 / 2 : ℝ)).mat * (H ^ (1 / 2 : ℝ)).mat = H.mat := by
    apply HermitianMat.pow_half_mul hH;
  -- Apply the lemma that states the equality of the traces of the conjugates.
  have := trace_rpow_conjTranspose_mul_comm ((σ ^ s).mat * (H ^ (1 / 2 : ℝ)).mat) p;
  convert this.symm using 3 <;> simp [ h_exp, h_exp', mul_assoc ];
  · ext; simp [ ← mul_assoc, h_exp' ] ;
    simp [ conj_apply, h_exp' ];
    simp_all [ mul_assoc, pow_two ];
  · ext; simp [ ← mul_assoc, h_exp ] ;
    simp [ conj, h_exp ];
    simp [ mul_assoc ]

/-
Extension of liebExtension_bridge from PD to PSD Z inputs via continuity.
-/
private lemma liebExtension_bridge_psd [Nonempty d]
    {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q + r ≤ 1)
    (K : HermitianMat d ℂ) (hK : 0 ≤ K)
    (σ₁ σ₂ Z₁ Z₂ : HermitianMat d ℂ)
    (hσ₁ : σ₁.mat.PosDef) (hσ₂ : σ₂.mat.PosDef)
    (hZ₁ : 0 ≤ Z₁) (hZ₂ : 0 ≤ Z₂)
    (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    (1 - θ) * ⟪(σ₁ ^ q).conj K, Z₁ ^ r⟫_ℝ + θ * ⟪(σ₂ ^ q).conj K, Z₂ ^ r⟫_ℝ ≤
    ⟪(((1 - θ) • σ₁ + θ • σ₂) ^ q).conj K, ((1 - θ) • Z₁ + θ • Z₂) ^ r⟫_ℝ := by
  have h_cont : ∀ (ε : ℝ), 0 < ε → (1 - θ) * ⟪(σ₁ ^ q).conj K, (Z₁ + ε • (1 : HermitianMat d ℂ)) ^ r⟫_ℝ + θ * ⟪(σ₂ ^ q).conj K, (Z₂ + ε • (1 : HermitianMat d ℂ)) ^ r⟫_ℝ ≤ ⟪(((1 - θ) • σ₁ + θ • σ₂) ^ q).conj K, ((1 - θ) • (Z₁ + ε • (1 : HermitianMat d ℂ)) + θ • (Z₂ + ε • (1 : HermitianMat d ℂ))) ^ r⟫_ℝ := by
    intro ε hε_pos
    apply liebExtension_bridge hq hr hqr K hK σ₁ σ₂ (Z₁ + ε • (1 : HermitianMat d ℂ)) (Z₂ + ε • (1 : HermitianMat d ℂ)) hσ₁ hσ₂ (by
    convert psd_add_eps_posdef Z₁ hZ₁ ε hε_pos using 1) (by
    convert psd_add_eps_posdef Z₂ hZ₂ ε hε_pos using 1) θ hθ₀ hθ₁;
  -- Apply the continuity results to take the limit as ε approaches 0.
  have h_lim : Filter.Tendsto (fun ε : ℝ => ⟪(σ₁ ^ q).conj K, (Z₁ + ε • (1 : HermitianMat d ℂ)) ^ r⟫_ℝ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (⟪(σ₁ ^ q).conj K, Z₁ ^ r⟫_ℝ)) ∧ Filter.Tendsto (fun ε : ℝ => ⟪(σ₂ ^ q).conj K, (Z₂ + ε • (1 : HermitianMat d ℂ)) ^ r⟫_ℝ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (⟪(σ₂ ^ q).conj K, Z₂ ^ r⟫_ℝ)) := by
    constructor <;> refine' Filter.Tendsto.mono_left _ nhdsWithin_le_nhds;
    · have h_cont : Continuous (fun ε : ℝ => (Z₁ + ε • (1 : HermitianMat d ℂ)) ^ r) := by
        have h_cont : Continuous (fun ε : ℝ => (Z₁ + ε • (1 : HermitianMat d ℂ))) := by
          fun_prop;
        exact HermitianMat.rpow_const_continuous ( show 0 ≤ r by positivity ) |> Continuous.comp <| h_cont;
      convert Filter.Tendsto.inner tendsto_const_nhds ( h_cont.tendsto 0 ) using 2 ; norm_num;
    · have h_inner_cont : Continuous (fun ε : ℝ => (Z₂ + ε • (1 : HermitianMat d ℂ)) ^ r) := by
        have h_cont : Continuous (fun ε : HermitianMat d ℂ => ε ^ r) := by
          apply_rules [ HermitianMat.rpow_const_continuous ];
          positivity;
        fun_prop (disch := solve_by_elim);
      convert Filter.Tendsto.inner tendsto_const_nhds ( h_inner_cont.tendsto 0 ) using 2 ; simp;
  have h_lim_rhs : Filter.Tendsto (fun ε : ℝ => ⟪(conj K) (((1 - θ) • σ₁ + θ • σ₂) ^ q), ((1 - θ) • (Z₁ + ε • (1 : HermitianMat d ℂ)) + θ • (Z₂ + ε • (1 : HermitianMat d ℂ))) ^ r⟫_ℝ) (nhdsWithin 0 (Set.Ioi 0)) (nhds (⟪(conj K) (((1 - θ) • σ₁ + θ • σ₂) ^ q), ((1 - θ) • Z₁ + θ • Z₂) ^ r⟫_ℝ)) := by
    have h_lim_rhs : Filter.Tendsto (fun ε : ℝ => ((1 - θ) • (Z₁ + ε • (1 : HermitianMat d ℂ)) + θ • (Z₂ + ε • (1 : HermitianMat d ℂ))) ^ r) (nhdsWithin 0 (Set.Ioi 0)) (nhds (((1 - θ) • Z₁ + θ • Z₂) ^ r)) := by
      convert ( rpow_const_continuous _ |> Continuous.continuousAt |> fun h => h.tendsto.comp ( show Filter.Tendsto ( fun ε : ℝ => ( 1 - θ ) • ( Z₁ + ε • 1 ) + θ • ( Z₂ + ε • 1 ) ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds ( ( 1 - θ ) • Z₁ + θ • Z₂ ) ) from ?_ ) ) using 2;
      · positivity;
      · refine' tendsto_nhdsWithin_of_tendsto_nhds _;
        refine' Continuous.tendsto' _ _ _ _ <;> norm_num;
        fun_prop;
    convert Filter.Tendsto.inner tendsto_const_nhds h_lim_rhs using 1;
  exact le_of_tendsto_of_tendsto ( Filter.Tendsto.add ( tendsto_const_nhds.mul h_lim.1 ) ( tendsto_const_nhds.mul h_lim.2 ) ) h_lim_rhs ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_cont ε hε )

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
  have hαm1_ne : α - 1 ≠ 0 := ne_of_gt hαm1_pos
  have hs_pos : 0 < s := by show 0 < (α - 1) / (2 * α); positivity
  have hp_gt1 : 1 < p := by
    show 1 < α / (α - 1); rw [lt_div_iff₀ hαm1_pos]; linarith
  have hp_pos : 0 < p := by linarith
  -- The exponents for the bridge
  set q := (α - 1) / α with q_def
  set r := 1 / α with r_def
  have hq_pos : 0 < q := by simp only [q_def]; positivity
  have hr_pos : 0 < r := by simp only [r_def]; positivity
  have hqr : q + r ≤ 1 := by
    simp only [q_def, r_def]; rw [div_add_div_same, sub_add_cancel, div_self hα_ne]
  have h2s_eq_q : 2 * s = q := by
    show 2 * ((α - 1) / (2 * α)) = (α - 1) / α; field_simp
  have hr_eq : r = (p - 1) / p := by
    show 1 / α = (α / (α - 1) - 1) / (α / (α - 1)); field_simp; ring
  -- K = H^{1/2}
  set K := H ^ (1/2 : ℝ) with K_def
  have hK : 0 ≤ K := rpow_nonneg hH
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
        have bridge := liebExtension_bridge_psd hq_pos hr_pos hqr K hK
          σ₁ σ₂ Z₁ Z₂ hσ₁ hσ₂ hZ₁ hZ₂ b hb (by linarith)
        rw [show (1 : ℝ) - b = a from by linarith] at bridge
        have trace_lin : (a • Z₁ + b • Z₂).trace = a * Z₁.trace + b * Z₂.trace := by
          rw [trace_add, trace_smul, trace_smul]
        rw [trace_lin]
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
  refine' ⟨ psd_convex, fun σ₁ hσ₁ σ₂ hσ₂ a b ha hb hab => _ ⟩;
  by_cases hd : Nonempty d <;> simp_all [ ConcaveOn ];
  · have h_cont : Filter.Tendsto (fun ε : ℝ => a * ((H.conj ((σ₁ + ε • (1 : HermitianMat d ℂ)) ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace + b * ((H.conj ((σ₂ + ε • (1 : HermitianMat d ℂ)) ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace) (nhdsWithin 0 (Set.Ioi 0)) (nhds (a * ((H.conj (σ₁ ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace + b * ((H.conj (σ₂ ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace)) := by
      have h_cont : Continuous (fun σ : HermitianMat d ℂ => ((H.conj (σ ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace) := by
        convert trace_conj_rpow_continuous ( show 0 ≤ ( α - 1 ) / ( 2 * α ) by exact div_nonneg ( sub_nonneg.2 hα.le ) ( by positivity ) ) ( show 0 ≤ α / ( α - 1 ) by exact div_nonneg ( by positivity ) ( by linarith ) ) H using 1;
      exact Filter.Tendsto.add ( tendsto_const_nhds.mul ( h_cont.continuousAt.tendsto.comp ( tendsto_add_eps _ ) ) ) ( tendsto_const_nhds.mul ( h_cont.continuousAt.tendsto.comp ( tendsto_add_eps _ ) ) ) |> fun h => h.trans ( by simp [ hab ] );
    have h_cont : Filter.Tendsto (fun ε : ℝ => ((H.conj ((a • (σ₁ + ε • (1 : HermitianMat d ℂ)) + b • (σ₂ + ε • (1 : HermitianMat d ℂ))) ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace) (nhdsWithin 0 (Set.Ioi 0)) (nhds (((H.conj ((a • σ₁ + b • σ₂) ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace)) := by
      have h_cont : Continuous (fun σ : HermitianMat d ℂ => ((H.conj (σ ^ ((α - 1) / (2 * α))).mat) ^ (α / (α - 1))).trace) := by
        convert trace_conj_rpow_continuous ( show 0 ≤ ( α - 1 ) / ( 2 * α ) by exact div_nonneg ( sub_nonneg.2 hα.le ) ( by positivity ) ) ( show 0 ≤ α / ( α - 1 ) by exact div_nonneg ( by positivity ) ( by linarith ) ) H using 1;
      convert h_cont.continuousAt.tendsto.comp ( show Filter.Tendsto ( fun ε : ℝ => a • ( σ₁ + ε • 1 ) + b • ( σ₂ + ε • 1 ) ) ( nhdsWithin 0 ( Set.Ioi 0 ) ) ( nhds ( a • σ₁ + b • σ₂ ) ) from ?_ ) using 2;
      refine' tendsto_nhdsWithin_of_tendsto_nhds _;
      refine' Continuous.tendsto' _ _ _ _ <;> norm_num [ Continuous ];
      fun_prop (disch := solve_by_elim);
    refine' le_of_tendsto_of_tendsto ‹_› ‹_› _;
    filter_upwards [ self_mem_nhdsWithin ] with ε hε;
    convert trace_conj_rpow_concave_pd hα H hH ( σ₁ + ε • 1 ) ( σ₂ + ε • 1 ) _ _ a b ha hb hab using 1 <;> norm_num [ hε.out ];
    · convert psd_add_eps_posdef σ₁ hσ₁ ε hε using 1;
    · convert psd_add_eps_posdef σ₂ hσ₂ ε hε using 1;
  · simp_all [ HermitianMat.trace ]

end HermitianMat
