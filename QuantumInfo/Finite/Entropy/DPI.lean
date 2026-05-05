/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Finite.Entropy.Relative
public import QuantumInfo.Finite.CPTPMap.Dual
public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.HermitianMat.Sqrt
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

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

open scoped InnerProductSpace RealInnerProductSpace HermitianMat

/-!
# DPI (Data Processing Inequality)

The Data Processing Inequality (DPI) for the sandwiched Rényi relative entropy, and
as a consequence, the quantum relative entropy.
-/

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra
open BigOperators

/-- The weighted norm `‖X‖_{p,σ}` used internally in the interpolation proof.
This definition is only used below for `p = 1` and `p > 1`; at `p = 0` it is just Lean's
totalized expression, not a mathematical norm. -/
private noncomputable def weighted_norm (p : ℝ) (σ : MState d) (X : Matrix d d ℂ) : ℝ :=
  let σ_pow : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (1 / (2 * p)))
  schattenNorm (σ_pow.mat * X * σ_pow.mat) p

/-- The weighted norm for p = \infty. -/
private noncomputable def weighted_norm_infty (_ : MState d) (X : Matrix d d ℂ) : ℝ :=
  ‖X‖

/-- The map Γ_σ(X) = σ^{1/2} X σ^{1/2}. -/
private noncomputable def Gamma (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  let σ_half : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (1/2 : ℝ))
  σ_half.mat * X * σ_half.mat

/-- The support inverse of `Γ_σ`, given by `σ^{-1/2} X σ^{-1/2}`.
For singular `σ` this is a pseudoinverse: composing with `Gamma σ` compresses to
`σ.M.supportProj`, not to the identity. -/
private noncomputable def Gamma_inv (σ : MState d) (X : Matrix d d ℂ) : Matrix d d ℂ :=
  let σ_inv_half : HermitianMat d ℂ := σ.M.cfc (fun x => x ^ (-1/2 : ℝ))
  σ_inv_half.mat * X * σ_inv_half.mat

/-- The operator T = Γ_{Φ(σ)}^{-1} ∘ Φ ∘ Γ_σ. -/
private noncomputable def T_op (Φ : CPTPMap d d₂) (σ : MState d)
    (X : Matrix d d ℂ) : Matrix d₂ d₂ ℂ :=
  Gamma_inv (Φ σ) (Φ.map (Gamma σ X))

/-- The operator `Γ_{Φ(σ)}^{-1} ∘ Φ ∘ Γ_σ` as a linear map. -/
private noncomputable def T_map (σ : MState d) (Φ : CPTPMap d d₂) : MatrixMap d d₂ ℂ :=
  { toFun := fun X => T_op Φ σ X,
    map_add' := fun X Y => by
      unfold T_op Gamma Gamma_inv
      simp [Matrix.mul_add, Matrix.add_mul]
    map_smul' := fun c X => by
      unfold T_op
      simp
      unfold Gamma Gamma_inv
      simp [mul_assoc]
  }

/-- `Gamma` as a matrix map: conjugation by the square root of `σ`. -/
private noncomputable def Gamma_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M.cfc (fun x => x ^ (1/2 : ℝ))).mat

/-- `Gamma_inv` as a matrix map: conjugation by the inverse square root on the support. -/
private noncomputable def Gamma_inv_map (σ : MState d) : MatrixMap d d ℂ :=
  MatrixMap.conj (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat

/-- `T_map` is the composition of `Gamma_inv_map`, `Φ`, and `Gamma_map`. -/
private lemma T_map_eq_comp (σ : MState d) (Φ : CPTPMap d d₂) :
    T_map σ Φ = (Gamma_inv_map (Φ σ)).comp (Φ.map.comp (Gamma_map σ)) := by
  ext
  unfold T_map
  simp [T_op]
  congr! 1
  · exact funext fun _ => by
      simp [Gamma_inv_map, Gamma_inv]
      congr
      symm
      apply IsSelfAdjoint.cfc
  · ext
    simp [Gamma_map, Gamma]
    all_goals symm
    apply_rules [IsSelfAdjoint.cfc]

/-- `T_map` is completely positive. -/
private lemma T_is_CP (σ : MState d) (Φ : CPTPMap d d₂) :
    (T_map σ Φ).IsCompletelyPositive := by
  rw [T_map_eq_comp]
  exact
    ((MatrixMap.conj_isCompletelyPositive _ : (Gamma_map σ).IsCompletelyPositive).comp
      Φ.cp).comp (MatrixMap.conj_isCompletelyPositive _)

/-- The weighted `1`-norm of `X` is the trace norm of `Gamma σ X`. -/
private lemma weighted_norm_one_eq_trace_norm_Gamma (σ : MState d) (X : Matrix d d ℂ) :
    weighted_norm 1 σ X = schattenNorm (Gamma σ X) 1 := by
  unfold weighted_norm Gamma
  norm_num

/-- `Gamma` sends the identity to `σ`. -/
private lemma Gamma_one (σ : MState d) : Gamma σ 1 = σ.M.mat := by
  have h_gamma_one : (σ.M.cfc (fun x => x^(1/2 : ℝ))).mat * (σ.M.cfc (fun x => x^(1/2 : ℝ))).mat = σ.M.cfc (fun x => x^(1/2 : ℝ) * x^(1/2 : ℝ)) := by
    symm
    exact HermitianMat.mat_cfc_mul σ.M ( fun x => x ^ ( 1 / 2 : ℝ ) ) ( fun x => x ^ ( 1 / 2 : ℝ ) )
  convert h_gamma_one using 1
  · unfold Gamma; aesop
  · norm_num [ ← Real.sqrt_eq_rpow, Real.sqrt_mul_self ( show 0 ≤ _ from _ ) ]
    have h_gamma_one : ∀ x ∈ spectrum ℝ σ.m, Real.sqrt x * Real.sqrt x = x := by
      intro x hx; rw [ Real.mul_self_sqrt ] ; exact (by
      rw [ spectrum.mem_iff ] at hx
      exact Matrix.PosSemidef.pos_of_mem_spectrum σ.psd x hx)
    rw [ cfc ]
    split_ifs <;> simp_all
    · convert rfl
      convert cfcHom_id _
      ext x; aesop
    · exact False.elim ( ‹IsSelfAdjoint σ.m → ¬ContinuousOn ( fun x => Real.sqrt x * Real.sqrt x ) ( spectrum ℝ σ.m ) › σ.M.prop <| ContinuousOn.mul ( Real.continuous_sqrt.continuousOn ) ( Real.continuous_sqrt.continuousOn ) )

/-- For full-support `σ`, the support inverse sends `σ` to the identity. -/
private lemma Gamma_inv_self (σ : MState d) (hσ : σ.m.PosDef) :
    Gamma_inv σ σ.M.mat = 1 := by
  -- We use functional calculus and the fact that $x^{-1/2} * x * x^{-1/2} = 1$ for $x > 0$.
  have h_gamma_inv_sigma : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => x ^ (-1/2 : ℝ) * x * x ^ (-1/2 : ℝ))).mat := by
    have h_gamma_inv_sigma : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.cfc id).mat * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => x ^ (-1/2 : ℝ) * x * x ^ (-1/2 : ℝ))).mat := by
      have h_gamma_inv_sigma : ∀ (f g h : ℝ → ℝ), ContinuousOn f (spectrum ℝ σ.M.mat) → ContinuousOn g (spectrum ℝ σ.M.mat) → ContinuousOn h (spectrum ℝ σ.M.mat) → (σ.M.cfc f).mat * (σ.M.cfc g).mat * (σ.M.cfc h).mat = (σ.M.cfc (fun x => f x * g x * h x)).mat := by
        intro f g h hf hg hh
        have h_gamma_inv_sigma : (σ.M.cfc f).mat * (σ.M.cfc g).mat = (σ.M.cfc (fun x => f x * g x)).mat := by
          symm
          convert HermitianMat.mat_cfc_mul σ.M f g using 1
        rw [ h_gamma_inv_sigma, ← HermitianMat.mat_cfc_mul ]
        congr! 2
      have h : ∀ x ∈ spectrum ℝ σ.M.mat, x ≠ 0 := by
        norm_num
        intro x hx h_zero
        have h_eigenvalue : ∃ v : d → ℂ, v ≠ 0 ∧ σ.m.mulVec v = x • v := by
          simp_all [ spectrum.mem_iff]
          contrapose! hx
          exact Matrix.PosDef.isUnit hσ
        obtain ⟨ v, hv_ne_zero, hv_eigenvalue ⟩ := h_eigenvalue
        rw [Matrix.posDef_iff_dotProduct_mulVec] at hσ
        have := hσ.2 hv_ne_zero
        simp [hv_eigenvalue, h_zero] at this
      apply h_gamma_inv_sigma
      · fun_prop
      · fun_prop
      · fun_prop
    convert h_gamma_inv_sigma using 1
    ext i j ; simp [ Matrix.mul_apply]
  -- Since $x^{-1/2} * x * x^{-1/2} = 1$ for $x > 0$, we have $(σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => 1)).mat$.
  have h_gamma_inv_sigma_simplified : (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat * (σ.M.mat) * (σ.M.cfc (fun x => x ^ (-1/2 : ℝ))).mat = (σ.M.cfc (fun x => 1)).mat := by
    convert h_gamma_inv_sigma using 1
    congr! 1
    -- Since $x^{-1/2} * x * x^{-1/2} = 1$ for all $x > 0$, the functions are equal.
    have h_eq : ∀ x : ℝ, 0 < x → x ^ (-1 / 2 : ℝ) * x * x ^ (-1 / 2 : ℝ) = 1 := by
      intro x hx
      ring_nf
      norm_num [ hx.ne' ]
      rw [ ← Real.rpow_natCast, ← Real.rpow_mul hx.le ] ; norm_num [ hx.ne' ]
      rw [ Real.rpow_neg_one, inv_mul_cancel₀ hx.ne' ]
    exact Eq.symm (HermitianMat.cfc_congr_of_posDef hσ h_eq)
  convert h_gamma_inv_sigma_simplified using 1
  ext i j
  simp

private lemma Gamma_inv_self_supportProj (σ : MState d) :
    Gamma_inv σ σ.M.mat = σ.M.supportProj.mat := by
  change ((σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat * σ.M.mat *
      (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat) = σ.M.supportProj.mat
  rw [show σ.M.mat = (σ.M.cfc id).mat from by simp,
    ← HermitianMat.mat_cfc_mul σ.M (fun x => x ^ (-1 / 2 : ℝ)) id,
    show (σ.M.cfc ((fun x => x ^ (-1 / 2 : ℝ)) * id)).mat
      = (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ) * x)).mat from rfl,
    ← HermitianMat.mat_cfc_mul σ.M _ (fun x => x ^ (-1 / 2 : ℝ)),
    HermitianMat.supportProj_eq_cfc]
  refine congrArg _ <| HermitianMat.cfc_congr_of_nonneg σ.nonneg fun x hx => ?_
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hxpos : 0 < x := hx.lt_of_ne (Ne.symm hx0)
    show x ^ (-1 / 2 : ℝ) * x * x ^ (-1 / 2 : ℝ) = if x = 0 then 0 else 1
    simp only [hx0, if_false]
    nth_rw 2 [← Real.rpow_one x]
    rw [← Real.rpow_add hxpos, ← Real.rpow_add hxpos]
    norm_num

/-- For full-support `σ`, `Gamma σ` composed with `Gamma_inv σ` is the identity. -/
private lemma Gamma_Gamma_inv (σ : MState d) (hσ : σ.m.PosDef) (X : Matrix d d ℂ) :
    Gamma σ (Gamma_inv σ X) = X := by
  -- By definition of Gamma and Gamma_inv, we can simplify the expression.
  have h_simp : (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat * (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat = 1 := by
    symm
    convert HermitianMat.mat_cfc_mul _ _ _ using 1
    · have h_gamma_gamma_inv : ∀ x ∈ spectrum ℝ σ.M.mat, x ^ (1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) = 1 := by
        intro x hx
        have hx_pos : 0 < x := by
          have := (Matrix.posDef_iff_dotProduct_mulVec.mp hσ).2
          obtain ⟨v, hv⟩ : ∃ v : d → ℂ, v ≠ 0 ∧ σ.m.mulVec v = x • v := by
            rw [ spectrum.mem_iff ] at hx
            simp_all [ Matrix.isUnit_iff_isUnit_det ]
            obtain ⟨ v, hv ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hx
            simp_all [ sub_eq_iff_eq_add, Matrix.sub_mulVec ]
            exact ⟨ v, hv.1, hv.2.symm.trans ( by ext i; erw [ Matrix.mulVec_diagonal ] ; aesop ) ⟩
          specialize this hv.1
          simp_all [ dotProduct]
          simp_all [ mul_assoc, mul_comm]
          simp_all [ mul_left_comm ( v _ ), Complex.mul_conj, Complex.normSq_eq_norm_sq ]
          norm_cast at this
          exact lt_of_not_ge fun hx' => this.not_ge <| Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg hx' <| sq_nonneg _
        rw [ ← Real.rpow_add hx_pos ] ; norm_num
      rw [HermitianMat.cfc_congr (g := fun x ↦ 1)]
      · rw [ HermitianMat.cfc_const ]
        norm_num
      · exact fun x hx => h_gamma_gamma_inv x hx
  unfold Gamma Gamma_inv; simp_all [ ← mul_assoc ]
  simp_all [ mul_assoc, mul_eq_one_comm.mp h_simp ]

private lemma Gamma_Gamma_inv_supportProj (σ : MState d) (X : Matrix d d ℂ) :
    Gamma σ (Gamma_inv σ X) = σ.M.supportProj.mat * X * σ.M.supportProj.mat := by
  have key (p : ℝ) (hp : p ≠ 0) :
      (σ.M.cfc (fun x => x ^ p)).mat * (σ.M.cfc (fun x => x ^ (-p))).mat = σ.M.supportProj.mat ∧
      (σ.M.cfc (fun x => x ^ (-p))).mat * (σ.M.cfc (fun x => x ^ p)).mat = σ.M.supportProj.mat := by
    refine ⟨?_, ?_⟩
    · simpa [HermitianMat.rpow_eq_cfc] using
        HermitianMat.rpow_neg_mul_rpow_eq_supportProj (A := σ.M) σ.nonneg
          (p := -p) (neg_ne_zero.mpr hp)
    · simpa [HermitianMat.rpow_eq_cfc] using
        HermitianMat.rpow_neg_mul_rpow_eq_supportProj (A := σ.M) σ.nonneg (p := p) hp
  have hneg_half :
      (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat =
        (σ.M.cfc (fun x => x ^ (-(1 / 2 : ℝ)))).mat := by congr 1; ext x; norm_num
  obtain ⟨h1, h2⟩ := key (1 / 2 : ℝ) (by norm_num)
  unfold Gamma Gamma_inv
  calc _ = ((σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat *
            (σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat) * X *
          ((σ.M.cfc (fun x => x ^ (-1 / 2 : ℝ))).mat *
            (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat) := by simp [Matrix.mul_assoc]
    _ = _ := by rw [hneg_half, h1, h2]

private def spectralProj (A : HermitianMat d ℂ) (i : d) : Matrix d d ℂ :=
  A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose

private def supportCpow (A : HermitianMat d ℂ) (z : ℂ) : Matrix d d ℂ :=
  ∑ i, (if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ z)) • spectralProj A i

private lemma spectralProj_mul (A : HermitianMat d ℂ) (i j : d) :
    spectralProj A i * spectralProj A j = if i = j then spectralProj A i else 0 := by
  classical
  have hU : A.H.eigenvectorUnitary.val.conjTranspose * A.H.eigenvectorUnitary.val =
      (1 : Matrix d d ℂ) := by simp [Matrix.IsHermitian.eigenvectorUnitary]
  unfold spectralProj
  have heq : A.H.eigenvectorUnitary.val * Matrix.single i i (1 : ℂ) *
        A.H.eigenvectorUnitary.val.conjTranspose *
        (A.H.eigenvectorUnitary.val * Matrix.single j j (1 : ℂ) *
          A.H.eigenvectorUnitary.val.conjTranspose) =
      A.H.eigenvectorUnitary.val *
        (Matrix.single i i (1 : ℂ) * Matrix.single j j 1) *
        A.H.eigenvectorUnitary.val.conjTranspose := by
    rw [show A.H.eigenvectorUnitary.val * Matrix.single i i (1 : ℂ) *
          A.H.eigenvectorUnitary.val.conjTranspose *
          (A.H.eigenvectorUnitary.val * Matrix.single j j (1 : ℂ) *
            A.H.eigenvectorUnitary.val.conjTranspose) =
        A.H.eigenvectorUnitary.val * Matrix.single i i 1 *
          (A.H.eigenvectorUnitary.val.conjTranspose * A.H.eigenvectorUnitary.val) *
          Matrix.single j j 1 * A.H.eigenvectorUnitary.val.conjTranspose
        from by simp [Matrix.mul_assoc], hU, Matrix.mul_one]
    simp [Matrix.mul_assoc]
  rw [heq]
  by_cases hij : i = j
  · subst j; simp [Matrix.single_mul_single_same]
  · simp [hij]

private lemma supportCpow_zero (A : HermitianMat d ℂ) :
    supportCpow A 0 = A.supportProj.mat := by
  rw [A.supportProj_eq_cfc, HermitianMat.cfc_toMat_eq_sum_smul_proj]
  simp [supportCpow, spectralProj]

private lemma supportCpow_ofReal
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) {r : ℝ} (hr : 0 < r) :
    supportCpow A (r : ℂ) = (A ^ r).mat := by
  rw [HermitianMat.rpow_eq_cfc, HermitianMat.cfc_toMat_eq_sum_smul_proj]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h0 : A.H.eigenvalues i = 0
  · simp [spectralProj, h0, hr.ne']
  · simp [spectralProj, h0]
    rw [← Complex.ofReal_cpow ((HermitianMat.zero_le_iff.mp hA).eigenvalues_nonneg i) r]
    rfl

private lemma supportCpow_ofReal_ne_zero (A : HermitianMat d ℂ) (hA : 0 ≤ A) {r : ℝ}
    (hr : r ≠ 0) :
    supportCpow A (r : ℂ) = (A ^ r).mat := by
  rw [HermitianMat.rpow_eq_cfc, HermitianMat.cfc_toMat_eq_sum_smul_proj]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h0 : A.H.eigenvalues i = 0
  · simp [h0, spectralProj, Real.zero_rpow hr]
  · simp [h0, spectralProj]
    rw [← Complex.ofReal_cpow ((HermitianMat.zero_le_iff.mp hA).eigenvalues_nonneg i) r]
    rfl

private lemma supportCpow_mul (A : HermitianMat d ℂ) (z w : ℂ) :
    supportCpow A z * supportCpow A w = supportCpow A (z + w) := by
  unfold supportCpow
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · by_cases h0 : A.H.eigenvalues i = 0
    · simp [h0]
    · simp [h0, spectralProj_mul, smul_smul, add_comm,
        ← Complex.cpow_add _ _ (by exact_mod_cast h0 : (A.H.eigenvalues i : ℂ) ≠ 0)]
  · intro j _ hij
    simp [spectralProj_mul, hij]
  · simp

private lemma Gamma_supportCpow_shift
    (σ : MState d) (a : ℂ) (X : Matrix d d ℂ) :
    Gamma σ (supportCpow σ.M a * X * supportCpow σ.M a) =
      supportCpow σ.M (((1 / 2 : ℝ) : ℂ) + a) * X *
        supportCpow σ.M (((1 / 2 : ℝ) : ℂ) + a) := by
  calc
    Gamma σ (supportCpow σ.M a * X * supportCpow σ.M a)
      = supportCpow σ.M (((1 / 2 : ℝ) : ℂ)) *
          (supportCpow σ.M a * X * supportCpow σ.M a) *
          supportCpow σ.M (((1 / 2 : ℝ) : ℂ)) := by
            rw [supportCpow_ofReal σ.M σ.nonneg (r := 1 / 2) (by positivity)]
            simp [Gamma, HermitianMat.rpow_eq_cfc]
    _ = (supportCpow σ.M (((1 / 2 : ℝ) : ℂ)) * supportCpow σ.M a) * X *
          (supportCpow σ.M a * supportCpow σ.M (((1 / 2 : ℝ) : ℂ))) := by
            simp [Matrix.mul_assoc]
    _ = supportCpow σ.M ((((1 / 2 : ℝ) : ℂ) + a)) * X *
          supportCpow σ.M (a + (((1 / 2 : ℝ) : ℂ))) := by
            rw [supportCpow_mul, supportCpow_mul]
    _ = supportCpow σ.M ((((1 / 2 : ℝ) : ℂ) + a)) * X *
          supportCpow σ.M ((((1 / 2 : ℝ) : ℂ) + a)) := by
            rw [add_comm a (((1 / 2 : ℝ) : ℂ))]

private lemma supportCpow_conjTranspose (A : HermitianMat d ℂ) (hA : 0 ≤ A) (z : ℂ) :
    (supportCpow A z)ᴴ = supportCpow A (star z) := by
  classical
  unfold supportCpow
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases h0 : A.H.eigenvalues i = 0
  · simp [h0]
  · have hpos : 0 < A.H.eigenvalues i := by
      exact lt_of_le_of_ne (HermitianMat.eigenvalues_nonneg hA i) (Ne.symm h0)
    have hcpow :
        star (((A.H.eigenvalues i : ℂ) ^ z)) = ((A.H.eigenvalues i : ℂ) ^ (star z)) := by
      simpa [Complex.conj_ofReal] using
        (Complex.cpow_conj (x := (A.H.eigenvalues i : ℂ)) (n := z)
          (by
            simpa [Complex.arg_ofReal_of_nonneg hpos.le] using
              (show (0 : ℝ) ≠ Real.pi by positivity))).symm
    rw [Matrix.conjTranspose_smul, show (spectralProj A i)ᴴ = spectralProj A i from by
      unfold spectralProj; simp [Matrix.mul_assoc]]
    simp [h0, hcpow]

private lemma supportCpow_diffContOnCl_strip (A : HermitianMat d ℂ) (l u : ℝ) :
    DiffContOnCl ℂ (fun z : ℂ => supportCpow A z)
      (Complex.HadamardThreeLines.verticalStrip l u) := by
  classical
  unfold supportCpow
  refine Finset.induction_on Finset.univ ?_ ?_
  · simpa using (diffContOnCl_const : DiffContOnCl ℂ (fun _ : ℂ => (0 : Matrix d d ℂ))
      (Complex.HadamardThreeLines.verticalStrip l u))
  · intro a s ha hs
    simp only [Finset.sum_insert ha]
    by_cases h0 : A.H.eigenvalues a = 0
    · simpa [h0] using hs
    · have hterm :
          DiffContOnCl ℂ
            (fun z : ℂ =>
              ((A.H.eigenvalues a : ℂ) ^ z) • spectralProj A a)
            (Complex.HadamardThreeLines.verticalStrip l u) := by
          simpa [h0] using
            (((differentiable_id.const_cpow (Or.inl (by exact_mod_cast h0))).diffContOnCl).smul_const
              (spectralProj A a))
      simpa [h0] using hterm.add hs

private lemma supportProj_le_one (A : HermitianMat d ℂ) :
    A.supportProj ≤ (1 : HermitianMat d ℂ) := by
  rw [show (1 : HermitianMat d ℂ) = A.supportProj + A.kerProj by simp [add_comm]]
  exact le_add_of_nonneg_right (a := A.supportProj) (by
    simpa [HermitianMat.kerProj] using HermitianMat.projector_nonneg A.ker)

private lemma traceNorm_le_of_dual_opNorm_le
    {M : MatrixMap d d₂ ℂ}
    (hdual : ∀ Z : Matrix d₂ d₂ ℂ, ‖M.dual Z‖ ≤ ‖Z‖)
    (Y : Matrix d d ℂ) :
    (M Y).traceNorm ≤ Y.traceNorm := by
  obtain ⟨U, hU⟩ := (Matrix.traceNorm_eq_max_re_tr_U (M Y)).left
  calc
    (M Y).traceNorm = Complex.re ((U.val * M Y).trace) := by
      simpa using hU.symm
    _ = Complex.re ((M.dual U.val * Y).trace) := by
      rw [Matrix.trace_mul_comm, MatrixMap.Dual.trace_eq, Matrix.trace_mul_comm]
    _ ≤ ‖(M.dual U.val * Y).trace‖ := Complex.re_le_norm _
    _ ≤ (M.dual U.val * Y).traceNorm := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖M.dual U.val‖ * Y.traceNorm := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ ≤ ‖U.val‖ * Y.traceNorm :=
      mul_le_mul_of_nonneg_right (hdual U.val) (Matrix.traceNorm_nonneg Y)
    _ ≤ 1 * Y.traceNorm := by
      refine mul_le_mul_of_nonneg_right ?_ (Matrix.traceNorm_nonneg Y)
      by_cases h : IsEmpty d₂
      · have hU0 : U.val = 0 := Subsingleton.elim _ _
        simpa only [hU0, norm_zero] using (zero_le_one : (0 : ℝ) ≤ 1)
      · letI : Nonempty d₂ := not_isEmpty_iff.mp h
        have hU : U.valᴴ * U.val = (1 : Matrix d₂ d₂ ℂ) := by
          ext i j
          by_cases hij : i = j
          · simpa [Matrix.one_apply, Matrix.star_eq_conjTranspose, hij] using
              congrFun (congrFun U.prop.1 i) j
          · simpa [Matrix.one_apply, Matrix.star_eq_conjTranspose, hij] using
              congrFun (congrFun U.prop.1 i) j
        have hU_sq : ‖U.val‖ * ‖U.val‖ = 1 := by
          rw [← CStarRing.norm_star_mul_self (x := U.val), Matrix.star_eq_conjTranspose, hU]
          simp
        nlinarith [norm_nonneg U.val]
    _ = Y.traceNorm := by simp

private lemma norm_supportCpow_im_le_one (A : HermitianMat d₂ ℂ) (hA : 0 ≤ A) (t : ℝ) :
    ‖supportCpow A (Complex.I * t)‖ ≤ 1 := by
  let C := supportCpow A (Complex.I * t)
  have hsq : ‖C‖ * ‖C‖ = ‖A.supportProj.mat‖ := by
    rw [← CStarRing.norm_star_mul_self (x := C)]
    simp [C, Matrix.star_eq_conjTranspose, supportCpow_conjTranspose _ hA, supportCpow_mul,
      supportCpow_zero]
  have hproj : ‖A.supportProj.mat‖ ≤ 1 :=
    (Matrix.norm_le_norm_of_nonneg_of_le
      (by
        simpa [HermitianMat.supportProj] using
          (HermitianMat.projector_nonneg (S := A.support)).nonneg)
      (by simpa using supportProj_le_one A)).trans Matrix.norm_one_le_one
  nlinarith [norm_nonneg C]

private lemma norm_supportCpow_mem_verticalClosedStrip_le_one
    (σ : MState d) {z : ℂ}
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    ‖supportCpow σ.M z‖ ≤ 1 := by
  have hz' : 0 ≤ z.re ∧ z.re ≤ 1 := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  rw [show z = (z.re : ℂ) + Complex.I * z.im by apply Complex.ext <;> simp,
    ← supportCpow_mul]
  calc
    ‖supportCpow σ.M (z.re : ℂ) * supportCpow σ.M (Complex.I * z.im)‖
      ≤ ‖supportCpow σ.M (z.re : ℂ)‖ * ‖supportCpow σ.M (Complex.I * z.im)‖ :=
        norm_mul_le _ _
    _ ≤ ‖supportCpow σ.M (z.re : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_supportCpow_im_le_one σ.M σ.nonneg z.im)
          (norm_nonneg _)
    _ = ‖supportCpow σ.M (z.re : ℂ)‖ := by simp
    _ ≤ 1 := by
          by_cases hr0 : z.re = 0
          · simpa [hr0, supportCpow_zero] using
              (Matrix.norm_le_norm_of_nonneg_of_le
                (by
                  simpa [HermitianMat.supportProj] using
                    (HermitianMat.projector_nonneg (S := σ.M.support)).nonneg)
                (by simpa using supportProj_le_one σ.M)).trans Matrix.norm_one_le_one
          · have hr : 0 < z.re := lt_of_le_of_ne hz'.1 (Ne.symm hr0)
            rw [supportCpow_ofReal σ.M σ.nonneg hr]
            exact (Matrix.norm_le_norm_of_nonneg_of_le
              (HermitianMat.zero_le_iff.mp (HermitianMat.rpow_nonneg σ.nonneg)).nonneg
              (MState.rpow_le_one' (σ := σ) hr)).trans Matrix.norm_one_le_one

private lemma exists_norm_supportCpow_le_on_verticalClosedStrip
    (A : HermitianMat d ℂ) (hA : 0 ≤ A) (l u : ℝ) :
    ∃ K : ℝ, ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip l u,
      ‖supportCpow A z‖ ≤ K := by
  classical
  let K : ℝ := ∑ i,
    max
      (if h0 : A.H.eigenvalues i = 0 then 0 else A.H.eigenvalues i ^ l)
      (if h0 : A.H.eigenvalues i = 0 then 0 else A.H.eigenvalues i ^ u) *
        ‖spectralProj A i‖
  refine ⟨K, ?_⟩
  intro z hz
  have hz' : l ≤ z.re ∧ z.re ≤ u := by
    simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
  rw [show z = (z.re : ℂ) + Complex.I * z.im by apply Complex.ext <;> simp,
    ← supportCpow_mul]
  calc
    ‖supportCpow A (z.re : ℂ) * supportCpow A (Complex.I * z.im)‖
      ≤ ‖supportCpow A (z.re : ℂ)‖ * ‖supportCpow A (Complex.I * z.im)‖ :=
        norm_mul_le _ _
    _ ≤ ‖supportCpow A (z.re : ℂ)‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_supportCpow_im_le_one A hA z.im) (norm_nonneg _)
    _ = ‖supportCpow A (z.re : ℂ)‖ := by simp
    _ ≤ ∑ i,
          ‖(if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ (z.re : ℂ))) •
            spectralProj A i‖ := by
          simpa [supportCpow] using norm_sum_le (s := Finset.univ)
            (f := fun i =>
              (if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ (z.re : ℂ))) •
                spectralProj A i)
    _ ≤ K := by
          unfold K
          refine Finset.sum_le_sum ?_
          intro i _
          by_cases h0 : A.H.eigenvalues i = 0
          · simp [h0]
          · have hpos : 0 < A.H.eigenvalues i :=
              lt_of_le_of_ne ((HermitianMat.zero_le_iff.mp hA).eigenvalues_nonneg i)
                (Ne.symm (by simpa using h0))
            rw [norm_smul, show
                ‖if A.H.eigenvalues i = 0 then 0 else ((A.H.eigenvalues i : ℂ) ^ (z.re : ℂ))‖ =
                  A.H.eigenvalues i ^ z.re by
              simp [h0, Complex.norm_cpow_eq_rpow_re_of_pos hpos]]
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            by_cases hle1 : A.H.eigenvalues i ≤ 1
            · simpa [h0] using
                (Real.rpow_le_rpow_of_exponent_ge hpos hle1 hz'.1).trans
                  (le_max_left (A.H.eigenvalues i ^ l) (A.H.eigenvalues i ^ u))
            · simpa [h0] using
                (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hle1) hz'.2).trans
                  (le_max_right (A.H.eigenvalues i ^ l) (A.H.eigenvalues i ^ u))

private lemma weighted_norm_one_T_map_le
    (σ : MState d) (Φ : CPTPMap d d₂) (X : Matrix d d ℂ) :
    weighted_norm 1 (Φ σ) ((T_map σ Φ) X) ≤ weighted_norm 1 σ X := by
  let P : Matrix d₂ d₂ ℂ := (Φ σ).M.supportProj.mat
  let Mcomp : MatrixMap d d₂ ℂ := (MatrixMap.conj P) ∘ₗ Φ.map
  have hP : Pᴴ = P := by
    simp [P]
  have hMcomp_dual : Mcomp.dual = Φ.map.dual ∘ₗ MatrixMap.conj P := by
    dsimp [Mcomp]
    rw [show MatrixMap.dual (MatrixMap.conj P ∘ₗ Φ.map) =
        Φ.map.dual ∘ₗ (MatrixMap.conj P).dual by
      exact MatrixMap.dual_unique _ _ fun A B => by
        change (MatrixMap.conj P (Φ.map A) * B).trace =
          (A * Φ.map.dual ((MatrixMap.conj P).dual B)).trace
        rw [MatrixMap.Dual.trace_eq (MatrixMap.conj P) (Φ.map A) B,
          MatrixMap.Dual.trace_eq Φ.map A ((MatrixMap.conj P).dual B)],
      show (MatrixMap.conj P).dual = MatrixMap.conj P by
      exact MatrixMap.dual_unique _ _ fun A B => by
        rw [show ((MatrixMap.conj P) A * B).trace =
            ((A * Pᴴ * B) * P).trace by
          simp [MatrixMap.conj, Matrix.mul_assoc]
          rw [Matrix.trace_mul_comm]
          simp [Matrix.mul_assoc]]
        simp only [MatrixMap.conj, hP]
        simp [Matrix.mul_assoc]]
  have hconj1 : (MatrixMap.conj P) 1 ≤ (1 : Matrix d₂ d₂ ℂ) := by
    dsimp [P]
    simpa [MatrixMap.conj, hP, Matrix.mul_assoc,
      show (Φ σ).M.supportProj.mat * (Φ σ).M.supportProj.mat =
          (Φ σ).M.supportProj.mat by
        rw [← pow_two, ← HermitianMat.mat_pow]
        congr 1
        rw [HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_pow, ← HermitianMat.cfc_comp]
        exact HermitianMat.cfc_congr fun x _ => by by_cases hx0 : x = 0 <;> simp [hx0]] using
      (supportProj_le_one (Φ σ).M)
  have hMcomp_dual1 : Mcomp.dual 1 ≤ (1 : Matrix d d ℂ) := by
    rw [hMcomp_dual, ← Φ.TP.dual.map_1]
    simpa [map_sub, sub_nonneg] using
      (MatrixMap.IsPositive.dual Φ.cp.IsPositive
        (by simpa [sub_nonneg] using hconj1 :
          (1 - (MatrixMap.conj P) 1).PosSemidef)).nonneg
  have hMcomp_cp : Mcomp.IsCompletelyPositive := by
    dsimp [Mcomp]; exact Φ.cp.comp (MatrixMap.conj_isCompletelyPositive P)
  have hnorm_one (A : Matrix d d ℂ) : schattenNorm A 1 = A.traceNorm := by
    rw [schattenNorm_eq_sum_singularValues_rpow _ zero_lt_one, Matrix.traceNorm_eq_sum_singularValues]; simp
  have hnorm_one' (A : Matrix d₂ d₂ ℂ) : schattenNorm A 1 = A.traceNorm := by
    rw [schattenNorm_eq_sum_singularValues_rpow _ zero_lt_one, Matrix.traceNorm_eq_sum_singularValues]; simp
  calc
    weighted_norm 1 (Φ σ) ((T_map σ Φ) X)
      = (Gamma (Φ σ) ((T_map σ Φ) X)).traceNorm := by
          simpa [hnorm_one'] using
            weighted_norm_one_eq_trace_norm_Gamma (Φ σ) ((T_map σ Φ) X)
    _ = (Mcomp (Gamma σ X)).traceNorm := by
      simpa [Mcomp, MatrixMap.conj, P, hP, Matrix.mul_assoc] using
        congrArg Matrix.traceNorm (by
          unfold T_map T_op
          simpa [Matrix.mul_assoc] using
            Gamma_Gamma_inv_supportProj (σ := Φ σ) (X := Φ.map (Gamma σ X)))
    _ ≤ (Gamma σ X).traceNorm :=
      traceNorm_le_of_dual_opNorm_le
        (fun Z => MatrixMap.cp_subunital_opNorm_le_one (M := Mcomp.dual)
          hMcomp_cp.dual hMcomp_dual1 Z) _
    _ = weighted_norm 1 σ X := by
      simpa [hnorm_one] using (weighted_norm_one_eq_trace_norm_Gamma σ X).symm

private lemma abs_trace_weighted_pair_le_right
    (σ : MState d) (X Y : Matrix d d ℂ) :
    ‖(Y * Gamma σ X).trace‖ ≤ weighted_norm 1 σ Y * weighted_norm_infty σ X := by
  let S : Matrix d d ℂ := (σ.M.cfc (fun x => x ^ (1 / 2 : ℝ))).mat
  calc
    ‖(Y * Gamma σ X).trace‖ = ‖(X * Gamma σ Y).trace‖ := by
      congr 1
      calc
        (Y * Gamma σ X).trace = (Y * S * X * S).trace := by
          simp [Gamma, S, Matrix.mul_assoc]
        _ = ((S * Y * S) * X).trace := by
          rw [show Y * S * X * S = ((Y * S * X) * S) by simp [Matrix.mul_assoc]]
          rw [Matrix.trace_mul_comm]
          simp [Matrix.mul_assoc]
        _ = (X * Gamma σ Y).trace := by
          rw [Matrix.trace_mul_comm]
          simp [Gamma, S, Matrix.mul_assoc]
    _ ≤ (X * Gamma σ Y).traceNorm := Matrix.abs_trace_le_traceNorm _
    _ ≤ ‖X‖ * (Gamma σ Y).traceNorm := Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
    _ = weighted_norm 1 σ Y * weighted_norm_infty σ X := by
      rw [weighted_norm_infty, weighted_norm_one_eq_trace_norm_Gamma]
      simp [schattenNorm_eq_sum_singularValues_rpow _ zero_lt_one,
        Matrix.traceNorm_eq_sum_singularValues, mul_comm]

private lemma Gamma_Gamma_inv_density
    {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    Gamma σ (Gamma_inv σ ρ.M.mat) = ρ.M.mat := by
  have hleft : ρ.M.mat * σ.M.supportProj.mat = ρ.M.mat := by
    simpa using HermitianMat.mul_supportProj_of_ker_le (A := ρ.M) (B := σ.M) h
  rw [Gamma_Gamma_inv_supportProj,
    show σ.M.supportProj.mat * ρ.M.mat = ρ.M.mat by
      simpa only [Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat] using
        congrArg Matrix.conjTranspose hleft,
    hleft]

private lemma exists_le_exp_of_ker_le {ρ σ : MState d} (hker : σ.M.ker ≤ ρ.M.ker) :
    ∃ x : ℝ, ρ.M ≤ Real.exp x • σ.M := by
  open ComplexOrder in
  let P := σ.M.supportProj
  have hright : ρ.M.mat * P.mat = ρ.M.mat := by
    simpa [P] using HermitianMat.mul_supportProj_of_ker_le (A := ρ.M) (B := σ.M) hker
  have hleft : P.mat * ρ.M.mat = ρ.M.mat := by
    simpa only [Matrix.conjTranspose_mul, HermitianMat.conjTranspose_mat] using
      congrArg Matrix.conjTranspose hright
  have hP_idem : P.mat * P.mat = P.mat := by
    rw [← pow_two, ← HermitianMat.mat_pow]
    congr 1
    dsimp [P]
    rw [HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_pow,
      ← HermitianMat.cfc_comp_apply]
    exact HermitianMat.cfc_congr_of_nonneg σ.nonneg fun x _ => by
      by_cases hx : x = 0 <;> simp [hx]
  have hρ_le_P : ρ.M ≤ P := calc
    ρ.M = ρ.M.conj P.mat := by
      ext
      simp only [HermitianMat.conj_apply_mat, HermitianMat.conjTranspose_mat, hright, hleft]
    _ ≤ (1 : HermitianMat d ℂ).conj P.mat := HermitianMat.conj_mono ρ.le_one
    _ = P := by
      apply HermitianMat.ext
      simp [HermitianMat.conj_apply_mat, hP_idem]
  let α0 : ℝ := ∑ i, if σ.M.H.eigenvalues i = 0 then 0 else (σ.M.H.eigenvalues i)⁻¹
  have hterm j : 0 ≤ if σ.M.H.eigenvalues j = 0 then 0 else (σ.M.H.eigenvalues j)⁻¹ := by
    split_ifs
    · rfl
    · exact inv_nonneg.mpr (HermitianMat.eigenvalues_nonneg σ.nonneg j)
  have hα0_nonneg : 0 ≤ α0 := Finset.sum_nonneg fun i _ => hterm i
  have hP_le : P ≤ α0 • σ.M := by
    dsimp [P]
    rw [← sub_nonneg, show α0 • σ.M = σ.M.cfc (fun x => α0 * x) from by simp [α0],
      HermitianMat.supportProj_eq_cfc, ← HermitianMat.cfc_sub_apply, HermitianMat.cfc_nonneg_iff]
    intro i
    set y := σ.M.H.eigenvalues i
    by_cases hy0 : y = 0
    · simp [hy0]
    · have hy_pos := lt_of_le_of_ne (HermitianMat.eigenvalues_nonneg σ.nonneg i) (Ne.symm hy0)
      have hsingle : y⁻¹ ≤ α0 := by
        dsimp [α0]
        have hith : (if σ.M.H.eigenvalues i = 0 then 0 else (σ.M.H.eigenvalues i)⁻¹) = y⁻¹ := by
          rw [if_neg hy0]
        rw [← hith]
        exact Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_univ i)
      have hmul := mul_le_mul_of_nonneg_right hsingle hy_pos.le
      simp [hy0] at hmul ⊢
      change y⁻¹ * y ≤ α0 * y at hmul
      nlinarith [inv_mul_cancel₀ hy0]
  refine ⟨Real.log (α0 + 1), ?_⟩
  rw [Real.exp_log (by positivity : (0 : ℝ) < α0 + 1)]
  exact hρ_le_P.trans <| hP_le.trans <|
    smul_le_smul_of_nonneg_right (by linarith) σ.nonneg

private lemma weighted_norm_Gamma_inv_density_eq
    (α : ℝ) (hα : 1 < α) (ρ σ : MState d) :
    weighted_norm α σ (Gamma_inv σ ρ.M.mat) =
      ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace ^ (1 / α) := by
  let t : ℝ := (1 - α) / (2 * α)
  have hα0 : α ≠ 0 := by linarith
  have hsum_ne : (1 / (2 * α : ℝ)) + (-(1 / 2 : ℝ)) ≠ 0 := by
    intro h0
    field_simp [hα0] at h0
    linarith
  have hmul (p q : ℝ) (hpq : p + q ≠ 0) (ht : p + q = t) :
      (σ.M ^ p).mat * (σ.M ^ q).mat = (σ.M ^ t).mat := by
    rw [← ht]
    simpa using (HermitianMat.mat_rpow_add (A := σ.M) σ.nonneg (p := p) (q := q) hpq).symm
  have hleft := hmul (1 / (2 * α : ℝ)) (-(1 / 2 : ℝ)) hsum_ne
    (by dsimp [t]; field_simp [hα0]; ring)
  have hright := hmul (-(1 / 2 : ℝ)) (1 / (2 * α : ℝ))
    (by simpa [add_comm] using hsum_ne) (by dsimp [t]; field_simp [hα0]; ring)
  calc
    weighted_norm α σ (Gamma_inv σ ρ.M.mat)
      = schattenNorm
          (((σ.M ^ (1 / (2 * α : ℝ))).mat * (σ.M ^ (-(1 / 2 : ℝ))).mat) *
            (ρ.M.mat * ((σ.M ^ (-(1 / 2 : ℝ))).mat * (σ.M ^ (1 / (2 * α : ℝ))).mat))) α := by
            unfold weighted_norm Gamma_inv
            simp only [HermitianMat.rpow_eq_cfc]
            ring_nf
            simp [Matrix.mul_assoc]
    _ = schattenNorm ((σ.M ^ t).mat * (ρ.M.mat * (σ.M ^ t).mat)) α := by
          rw [hleft, hright]
    _ = schattenNorm ((ρ.M.conj (σ.M ^ t).mat).mat) α := by
          simp [HermitianMat.conj_apply_mat, Matrix.mul_assoc]
    _ = ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace ^ (1 / α) := by
          simpa [t] using schattenNorm_hermitian_pow
            (A := ρ.M.conj (σ.M ^ t).mat) (HermitianMat.conj_nonneg _ ρ.nonneg)
            (p := α) (by linarith)

private lemma weighted_norm_Gamma_inv_density_pos
    (α : ℝ) (hα : 1 < α) {ρ σ : MState d} (hker : σ.M.ker ≤ ρ.M.ker) :
    0 < weighted_norm α σ (Gamma_inv σ ρ.M.mat) := by
  have hcore_pos :
      0 < ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat := by
    exact HermitianMat.conj_pos ρ.pos (by
      grw [← hker]
      exact HermitianMat.ker_rpow_le_of_nonneg σ.nonneg)
  rw [weighted_norm_Gamma_inv_density_eq α hα ρ σ]
  exact Real.rpow_pos_of_pos (HermitianMat.trace_pos (HermitianMat.rpow_pos hcore_pos)) _

private lemma sandwich_core_trace_eq_weighted_norm_rpow
    (α : ℝ) (hα : 1 < α) (ρ σ : MState d) :
    ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace =
      weighted_norm α σ (Gamma_inv σ ρ.M.mat) ^ α := by
  rw [weighted_norm_Gamma_inv_density_eq α hα ρ σ]
  rw [← Real.rpow_mul
    (HermitianMat.trace_nonneg (HermitianMat.rpow_nonneg (HermitianMat.conj_nonneg _ ρ.nonneg)))]
  field_simp [show α ≠ 0 by linarith]
  rw [Real.rpow_one]

private lemma normalized_sandwich_core_trace_eq_one
    (α : ℝ) (hα : 1 < α) {ρ σ : MState d} (hker : σ.M.ker ≤ ρ.M.ker) :
    ((((weighted_norm α σ (Gamma_inv σ ρ.M.mat))⁻¹) •
        (ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat)) ^ α).trace = 1 := by
  let N := weighted_norm α σ (Gamma_inv σ ρ.M.mat)
  let A := ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat
  have hpos := weighted_norm_Gamma_inv_density_pos α hα hker
  have hcore_nonneg : 0 ≤ A := by
    simpa [A] using HermitianMat.conj_nonneg _ ρ.nonneg
  have hsmul_rpow_eq :
      (N⁻¹ • A) ^ α = N⁻¹ ^ α • (A ^ α) := by
    set c := N⁻¹
    have hc_nonneg : 0 ≤ c := by dsimp [c]; simpa [N] using inv_nonneg.mpr hpos.le
    rw [show c • A = A.cfc (fun x => c * x) from
      (HermitianMat.cfc_const_mul_id (A := A) (r := c)).symm]
    rw [HermitianMat.rpow_eq_cfc, ← HermitianMat.cfc_comp]
    calc
      A.cfc (((fun x => x ^ α) : ℝ → ℝ) ∘ fun x => c * x)
        = A.cfc (fun x => c ^ α * x ^ α) := by
            apply HermitianMat.cfc_congr_of_nonneg hcore_nonneg
            intro x hx
            rw [Function.comp_apply, Real.mul_rpow hc_nonneg hx]
      _ = c ^ α • (A ^ α) := by
            rw [HermitianMat.cfc_const_mul, HermitianMat.rpow_eq_cfc]
  change ((N⁻¹ • A) ^ α).trace = 1
  rw [hsmul_rpow_eq, HermitianMat.trace_smul]
  change N⁻¹ ^ α * (A ^ α).trace = 1
  rw [show (A ^ α).trace = N ^ α by
    change ((ρ.M.conj (σ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace = N ^ α
    rw [sandwich_core_trace_eq_weighted_norm_rpow α hα ρ σ]]
  rw [Real.inv_rpow (by simpa [N] using hpos.le)]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos (by simpa [N] using hpos) α).ne'

private lemma traceNorm_supportCpow_beta_add_im_le_one
    {A : HermitianMat d ℂ} (β : ℝ) (hβ : 1 < β) (hA : 0 ≤ A)
    (htrace : (A ^ β).trace = 1) (t : ℝ) :
    (supportCpow A ((β : ℂ) + Complex.I * t)).traceNorm ≤ 1 := by
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  calc
    (supportCpow A ((β : ℂ) + Complex.I * t)).traceNorm
      = (supportCpow A (β : ℂ) * supportCpow A (Complex.I * t)).traceNorm := by
          rw [← supportCpow_mul]
    _ ≤ (supportCpow A (β : ℂ)).traceNorm * ‖supportCpow A (Complex.I * t)‖ :=
          Matrix.traceNorm_mul_le_traceNorm_opNorm _ _
    _ ≤ (supportCpow A (β : ℂ)).traceNorm * 1 :=
          mul_le_mul_of_nonneg_left
            (norm_supportCpow_im_le_one A hA t) (Matrix.traceNorm_nonneg _)
    _ = (supportCpow A (β : ℂ)).traceNorm := by simp
    _ = ((A ^ β).mat).traceNorm := by rw [supportCpow_ofReal A hA hβ0]
    _ = 1 := by
          have htraceC : ((A ^ β).trace : ℂ) = 1 := by exact_mod_cast htrace
          have hnormC : (((A ^ β).mat).traceNorm : ℂ) = 1 :=
            (Matrix.PosSemidef.traceNorm_PSD_eq_trace
              (HermitianMat.zero_le_iff.mp (HermitianMat.rpow_nonneg hA))).trans
              ((HermitianMat.trace_eq_trace_rc (A := A ^ β)).symm.trans htraceC)
          exact_mod_cast hnormC

private lemma traceNorm_supportCpow_im_beta_add_sandwich_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (β : ℝ) (hβ : 1 < β) (σ : MState n) (A : HermitianMat n ℂ)
    (hA_nonneg : 0 ≤ A) (hA_trace1 : (A ^ β).trace = 1) (t s : ℝ) :
    (supportCpow σ.M (Complex.I * t) *
        supportCpow A ((β : ℂ) + Complex.I * s) *
        supportCpow σ.M (Complex.I * t)).traceNorm ≤ 1 := by
  calc
    (supportCpow σ.M (Complex.I * t) *
        supportCpow A ((β : ℂ) + Complex.I * s) *
        supportCpow σ.M (Complex.I * t)).traceNorm
      ≤ (supportCpow A ((β : ℂ) + Complex.I * s)).traceNorm := Matrix.traceNorm_sandwich_le
          (norm_supportCpow_im_le_one σ.M σ.nonneg t)
    _ ≤ 1 := traceNorm_supportCpow_beta_add_im_le_one β hβ hA_nonneg hA_trace1 s

private lemma opNorm_supportCpow_im_sandwich_le_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (σ : MState n) (A : HermitianMat n ℂ) (hA_nonneg : 0 ≤ A) (t s : ℝ) :
    ‖supportCpow σ.M (Complex.I * t) *
        supportCpow A (Complex.I * s) *
        supportCpow σ.M (Complex.I * t)‖ ≤ 1 := by
  calc
    ‖supportCpow σ.M (Complex.I * t) *
        supportCpow A (Complex.I * s) *
        supportCpow σ.M (Complex.I * t)‖
      ≤ ‖supportCpow A (Complex.I * s)‖ := by
          have hS := norm_supportCpow_im_le_one σ.M σ.nonneg t
          calc ‖supportCpow σ.M (Complex.I * t) * supportCpow A (Complex.I * s) *
                supportCpow σ.M (Complex.I * t)‖
              ≤ ‖supportCpow σ.M (Complex.I * t)‖ *
                  ‖supportCpow A (Complex.I * s) * supportCpow σ.M (Complex.I * t)‖ := by
                rw [Matrix.mul_assoc]; exact norm_mul_le _ _
            _ ≤ 1 * ‖supportCpow A (Complex.I * s) * supportCpow σ.M (Complex.I * t)‖ :=
                mul_le_mul_of_nonneg_right hS (norm_nonneg _)
            _ = ‖supportCpow A (Complex.I * s) * supportCpow σ.M (Complex.I * t)‖ := one_mul _
            _ ≤ ‖supportCpow A (Complex.I * s)‖ * ‖supportCpow σ.M (Complex.I * t)‖ :=
                norm_mul_le _ _
            _ ≤ ‖supportCpow A (Complex.I * s)‖ * 1 :=
                mul_le_mul_of_nonneg_left hS (norm_nonneg _)
            _ = ‖supportCpow A (Complex.I * s)‖ := mul_one _
    _ ≤ 1 := norm_supportCpow_im_le_one A hA_nonneg s

private lemma weighted_norm_infty_supportCpow_sandwich_bound {n : Type*}
    [Fintype n] [DecidableEq n] {β Kσneg KA : ℝ} (hβ : 1 < β) (σ : MState n)
    (A : HermitianMat n ℂ)
    (hKσneg : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1 / 2) 0,
      ‖supportCpow σ.M z‖ ≤ Kσneg)
    (hKA : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 β,
      ‖supportCpow A z‖ ≤ KA)
    {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    weighted_norm_infty σ
        (supportCpow σ.M (-z / 2) * supportCpow A ((β : ℂ) * z) *
          supportCpow σ.M (-z / 2)) ≤
      Kσneg * KA * Kσneg := by
  have hzL : -z / 2 ∈ Complex.HadamardThreeLines.verticalClosedStrip (-1 / 2) 0 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage] at hz ⊢
    constructor <;> linarith
  have hzC : (β : ℂ) * z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 β := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage] at hz ⊢
    constructor <;> nlinarith [hz.1, hz.2, hβ]
  let L : Matrix n n ℂ := supportCpow σ.M (-z / 2)
  let M : Matrix n n ℂ := supportCpow A ((β : ℂ) * z)
  dsimp [weighted_norm_infty, L, M]
  have hL_nonneg : 0 ≤ ‖L‖ := norm_nonneg L
  have hM_nonneg : 0 ≤ ‖M‖ := norm_nonneg M
  have hL_bound : ‖L‖ ≤ Kσneg := hKσneg (-z / 2) hzL
  have hM_bound : ‖M‖ ≤ KA := hKA ((β : ℂ) * z) hzC
  have hKσneg_nonneg : 0 ≤ Kσneg := hL_nonneg.trans hL_bound
  have hKA_nonneg : 0 ≤ KA := hM_nonneg.trans hM_bound
  have hML : ‖M * L‖ ≤ ‖M‖ * ‖L‖ := norm_mul_le M L
  have hLM : ‖L‖ * ‖M * L‖ ≤ ‖L‖ * (‖M‖ * ‖L‖) :=
    mul_le_mul_of_nonneg_left hML hL_nonneg
  have hMK : ‖M‖ * ‖L‖ ≤ KA * Kσneg :=
    mul_le_mul hM_bound hL_bound hL_nonneg hKA_nonneg
  have hright : ‖L‖ * (‖M‖ * ‖L‖) ≤ Kσneg * (KA * Kσneg) :=
    mul_le_mul hL_bound hMK (mul_nonneg hM_nonneg hL_nonneg) hKσneg_nonneg
  calc
    ‖L * M * L‖ ≤ ‖L‖ * ‖M * L‖ := by
            rw [Matrix.mul_assoc]; exact norm_mul_le _ _
        _ ≤ ‖L‖ * (‖M‖ * ‖L‖) := hLM
        _ ≤ Kσneg * (KA * Kσneg) := hright
        _ = Kσneg * KA * Kσneg := by ring

private lemma weighted_norm_one_supportCpow_sandwich_bound {n : Type*}
    [Fintype n] [DecidableEq n] {β KA : ℝ} (hβ : 1 < β)
    (σ : MState n) (A : HermitianMat n ℂ)
    (hKA : ∀ z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 β,
      ‖supportCpow A z‖ ≤ KA)
    {z : ℂ} (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1) :
    weighted_norm 1 σ
        (supportCpow σ.M ((z - 1) / 2) * supportCpow A ((β : ℂ) * (1 - z)) *
          supportCpow σ.M ((z - 1) / 2)) ≤
      Fintype.card n * KA := by
  have hzhalf : z / 2 ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage] at hz ⊢
    constructor <;> linarith
  have hzC : (β : ℂ) * (1 - z) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 β := by
    have hβpos : 0 < β := by linarith
    have hzre : z.re ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Complex.HadamardThreeLines.verticalClosedStrip] using hz
    have hre : ((β : ℂ) * (1 - z)).re = β * (1 - z.re) := by
      simp [Complex.mul_re, Complex.sub_re]
    change ((β : ℂ) * (1 - z)).re ∈ Set.Icc (0 : ℝ) β
    rw [hre]
    constructor
    · exact mul_nonneg hβpos.le (sub_nonneg.mpr hzre.2)
    · exact mul_le_of_le_one_right hβpos.le (sub_le_self 1 hzre.1)
  rw [weighted_norm_one_eq_trace_norm_Gamma,
    show schattenNorm (Gamma σ
      (supportCpow σ.M ((z - 1) / 2) * supportCpow A ((β : ℂ) * (1 - z)) *
        supportCpow σ.M ((z - 1) / 2))) 1 =
        (Gamma σ (supportCpow σ.M ((z - 1) / 2) *
          supportCpow A ((β : ℂ) * (1 - z)) *
          supportCpow σ.M ((z - 1) / 2))).traceNorm from by
      rw [schattenNorm_eq_sum_singularValues_rpow _ (by norm_num),
        Matrix.traceNorm_eq_sum_singularValues]; simp]
  let S : Matrix n n ℂ := supportCpow σ.M (z / 2)
  let M : Matrix n n ℂ := supportCpow A ((β : ℂ) * (1 - z))
  have hGammaY :
      Gamma σ (supportCpow σ.M ((z - 1) / 2) * M *
          supportCpow σ.M ((z - 1) / 2)) = S * M * S := by
    dsimp [S, M]
    rw [Gamma_supportCpow_shift]
    congr 1 <;> push_cast <;> ring_nf
  rw [hGammaY]
  dsimp [S, M]
  calc (S * M * S).traceNorm
      ≤ M.traceNorm := Matrix.traceNorm_sandwich_le
        (norm_supportCpow_mem_verticalClosedStrip_le_one (σ := σ) hzhalf)
    _ ≤ Fintype.card n * ‖M‖ := by
          classical
          rw [Matrix.traceNorm_eq_sum_singularValues]
          calc
            ∑ i : n, singularValues M i ≤ ∑ _i : n, ‖M‖ :=
              Finset.sum_le_sum fun i _ => Matrix.singularValues_le_opNorm M i
            _ = Fintype.card n * ‖M‖ := by simp
    _ ≤ Fintype.card n * KA :=
        mul_le_mul_of_nonneg_left (hKA _ hzC) (by positivity)

private def interpXin (β : ℝ) (σ : MState d) (A : HermitianMat d ℂ) :
    ℂ → Matrix d d ℂ :=
  fun z => supportCpow σ.M (-z / 2) * supportCpow A ((β : ℂ) * z) *
    supportCpow σ.M (-z / 2)

private def interpYout (β : ℝ) (τ : MState d₂) (A : HermitianMat d₂ ℂ) :
    ℂ → Matrix d₂ d₂ ℂ :=
  fun z => supportCpow τ.M ((z - 1) / 2) * supportCpow A ((β : ℂ) * (1 - z)) *
    supportCpow τ.M ((z - 1) / 2)

private def interpTrace (τ : MState d₂) (T : MatrixMap d d₂ ℂ)
    (Xin : ℂ → Matrix d d ℂ) (Yout : ℂ → Matrix d₂ d₂ ℂ) : ℂ → ℂ :=
  fun z => (Yout z * Gamma τ (T (Xin z))).trace

private lemma interpTrace_diffContOnCl {β : ℝ} (hβ : 1 < β)
    (σ : MState d) (τ : MState d₂) (T : MatrixMap d d₂ ℂ)
    (Ain : HermitianMat d ℂ) (Aout : HermitianMat d₂ ℂ) :
    DiffContOnCl ℂ (interpTrace τ T (interpXin β σ Ain) (interpYout β τ Aout))
      (Complex.HadamardThreeLines.verticalStrip 0 1) := by
  have hXinL_dc :
      DiffContOnCl ℂ (fun z : ℂ => supportCpow σ.M (-z / 2))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine (supportCpow_diffContOnCl_strip σ.M (-1 / 2) 0).comp ?_ ?_
    · exact (by fun_prop : Differentiable ℂ (fun z : ℂ => -z / 2)).diffContOnCl
    · intro z hz
      simp [Complex.HadamardThreeLines.verticalStrip] at hz ⊢
      constructor <;> linarith
  have hXinC_dc :
      DiffContOnCl ℂ (fun z : ℂ => supportCpow Ain ((β : ℂ) * z))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine (supportCpow_diffContOnCl_strip Ain 0 β).comp ?_ ?_
    · exact (by fun_prop : Differentiable ℂ (fun z : ℂ => (β : ℂ) * z)).diffContOnCl
    · intro z hz
      simp [Complex.HadamardThreeLines.verticalStrip] at hz ⊢
      constructor <;> nlinarith [hz.1, hz.2, hβ]
  have hYoutL_dc :
      DiffContOnCl ℂ (fun z : ℂ => supportCpow τ.M ((z - 1) / 2))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine (supportCpow_diffContOnCl_strip τ.M (-1 / 2) 0).comp ?_ ?_
    · exact (by fun_prop : Differentiable ℂ (fun z : ℂ => (z - 1) / 2)).diffContOnCl
    · intro z hz
      simp [Complex.HadamardThreeLines.verticalStrip] at hz ⊢
      constructor <;> linarith
  have hYoutC_dc :
      DiffContOnCl ℂ (fun z : ℂ => supportCpow Aout ((β : ℂ) * (1 - z)))
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    refine (supportCpow_diffContOnCl_strip Aout 0 β).comp ?_ ?_
    · exact (by fun_prop : Differentiable ℂ (fun z : ℂ => (β : ℂ) * (1 - z))).diffContOnCl
    · intro z hz
      simp [Complex.HadamardThreeLines.verticalStrip] at hz ⊢
      constructor <;> nlinarith [hz.1, hz.2, hβ]
  have hXin_dc :
      DiffContOnCl ℂ (interpXin β σ Ain) (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    dsimp [interpXin]
    exact
      ⟨(hXinL_dc.1.mul hXinC_dc.1).mul hXinL_dc.1,
        (hXinL_dc.2.mul hXinC_dc.2).mul hXinL_dc.2⟩
  have hYout_dc :
      DiffContOnCl ℂ (interpYout β τ Aout)
        (Complex.HadamardThreeLines.verticalStrip 0 1) := by
    dsimp [interpYout]
    exact
      ⟨(hYoutL_dc.1.mul hYoutC_dc.1).mul hYoutL_dc.1,
        (hYoutL_dc.2.mul hYoutC_dc.2).mul hYoutL_dc.2⟩
  let L : Matrix d d ℂ →ₗ[ℂ] Matrix d₂ d₂ ℂ :=
    { toFun := fun X => Gamma τ (T X)
      map_add' := by
        intro X Y
        simp only [Gamma, map_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c X
        simp only [Gamma, map_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  let G : Matrix d d ℂ →L[ℂ] Matrix d₂ d₂ ℂ :=
    { toLinearMap := L
      cont := L.continuous_of_finiteDimensional }
  let hGX_dc := G.differentiable.comp_diffContOnCl hXin_dc
  let trCLM : Matrix d₂ d₂ ℂ →L[ℂ] ℂ :=
    { toLinearMap := Matrix.traceLinearMap d₂ ℂ ℂ
      cont := (Matrix.traceLinearMap d₂ ℂ ℂ).continuous_of_finiteDimensional }
  exact trCLM.differentiable.comp_diffContOnCl
    ⟨hYout_dc.1.mul hGX_dc.1, hYout_dc.2.mul hGX_dc.2⟩

private lemma interpTrace_left_boundary_le_one {β : ℝ} (hβ : 1 < β)
    (σ : MState d) (τ : MState d₂) (T : MatrixMap d d₂ ℂ)
    (Ain : HermitianMat d ℂ) (Aout : HermitianMat d₂ ℂ)
    (hAin_nonneg : 0 ≤ Ain) (hAout_nonneg : 0 ≤ Aout)
    (hAout_trace1 : (Aout ^ β).trace = 1)
    (hInf : ∀ X, weighted_norm_infty τ (T X) ≤ weighted_norm_infty σ X) :
    ∀ z ∈ Complex.re ⁻¹' ({0} : Set ℝ),
      ‖interpTrace τ T (interpXin β σ Ain) (interpYout β τ Aout) z‖ ≤ 1 := by
  intro z hz
  have hz0 : z.re = 0 := by simpa using hz
  have hY1 : weighted_norm 1 τ (interpYout β τ Aout z) ≤ 1 := by
    rw [weighted_norm_one_eq_trace_norm_Gamma,
      show schattenNorm (Gamma τ (interpYout β τ Aout z)) 1 =
          (Gamma τ (interpYout β τ Aout z)).traceNorm from by
      rw [schattenNorm_eq_sum_singularValues_rpow _ (by norm_num),
        Matrix.traceNorm_eq_sum_singularValues]; simp]
    dsimp [interpYout]
    rw [show Gamma τ
        (supportCpow τ.M ((z - 1) / 2) * supportCpow Aout ((β : ℂ) * (1 - z)) *
          supportCpow τ.M ((z - 1) / 2)) =
        supportCpow τ.M (z / 2) * supportCpow Aout ((β : ℂ) * (1 - z)) *
          supportCpow τ.M (z / 2) from by
      have hz : (((2 : ℂ)⁻¹) + (z - 1) / 2) = z / 2 := by
        apply Complex.ext <;> simp; ring
      simpa [hz] using Gamma_supportCpow_shift (σ := τ) (a := (z - 1) / 2)
        (X := supportCpow Aout ((β : ℂ) * (1 - z)))]
    rw [show z / 2 = Complex.I * (z.im / 2) from by
        apply Complex.ext <;> simp [hz0, div_eq_mul_inv],
      show (β : ℂ) * (1 - z) = (β : ℂ) + Complex.I * (-β * z.im) from by
        apply Complex.ext <;> simp [hz0]]
    simpa using
      (traceNorm_supportCpow_im_beta_add_sandwich_le_one β hβ τ Aout
        hAout_nonneg hAout_trace1 (z.im / 2) (-β * z.im))
  have hX1 : weighted_norm_infty τ (T (interpXin β σ Ain z)) ≤ 1 := by
    refine (hInf (interpXin β σ Ain z)).trans ?_
    dsimp [weighted_norm_infty, interpXin]
    rw [show -z / 2 = Complex.I * (-(z.im / 2)) from by
        apply Complex.ext <;> simp [hz0, div_eq_mul_inv],
      show (β : ℂ) * z = Complex.I * (β * z.im) from by
        apply Complex.ext <;> simp [hz0]]
    simpa using
      (opNorm_supportCpow_im_sandwich_le_one σ Ain hAin_nonneg (-(z.im / 2)) (β * z.im))
  exact (show ‖interpTrace τ T (interpXin β σ Ain) (interpYout β τ Aout) z‖
      ≤ weighted_norm 1 τ (interpYout β τ Aout z) *
          weighted_norm_infty τ (T (interpXin β σ Ain z)) from by
    simpa [interpTrace] using
      abs_trace_weighted_pair_le_right (σ := τ)
        (X := T (interpXin β σ Ain z)) (Y := interpYout β τ Aout z)).trans
    (mul_le_one₀ hY1 (by dsimp [weighted_norm_infty]; exact norm_nonneg _) hX1)

private lemma interpTrace_right_boundary_le_one {β : ℝ} (hβ : 1 < β)
    (σ : MState d) (τ : MState d₂) (T : MatrixMap d d₂ ℂ)
    (Ain : HermitianMat d ℂ) (Aout : HermitianMat d₂ ℂ)
    (hAin_nonneg : 0 ≤ Ain) (hAout_nonneg : 0 ≤ Aout)
    (hAin_trace1 : (Ain ^ β).trace = 1)
    (h1 : ∀ X, weighted_norm 1 τ (T X) ≤ weighted_norm 1 σ X) :
    ∀ z ∈ Complex.re ⁻¹' ({1} : Set ℝ),
      ‖interpTrace τ T (interpXin β σ Ain) (interpYout β τ Aout) z‖ ≤ 1 := by
  intro z hz
  have hz1 : z.re = 1 := by simpa using hz
  have hY1 : weighted_norm_infty τ (interpYout β τ Aout z) ≤ 1 := by
    dsimp [weighted_norm_infty, interpYout]
    rw [show (z - 1) / 2 = Complex.I * (z.im / 2) from by
        apply Complex.ext <;> simp [hz1, div_eq_mul_inv],
      show (β : ℂ) * (1 - z) = Complex.I * (-β * z.im) from by
        apply Complex.ext <;> simp [hz1]]
    simpa using
      (opNorm_supportCpow_im_sandwich_le_one τ Aout hAout_nonneg (z.im / 2) (-β * z.im))
  have hX1 : weighted_norm 1 σ (interpXin β σ Ain z) ≤ 1 := by
    rw [weighted_norm_one_eq_trace_norm_Gamma,
      show schattenNorm (Gamma σ (interpXin β σ Ain z)) 1 =
          (Gamma σ (interpXin β σ Ain z)).traceNorm from by
      rw [schattenNorm_eq_sum_singularValues_rpow _ (by norm_num),
        Matrix.traceNorm_eq_sum_singularValues]; simp]
    dsimp [interpXin]
    rw [show Gamma σ
        (supportCpow σ.M (-z / 2) * supportCpow Ain ((β : ℂ) * z) *
          supportCpow σ.M (-z / 2)) =
        supportCpow σ.M (((1 : ℂ) - z) / 2) * supportCpow Ain ((β : ℂ) * z) *
          supportCpow σ.M (((1 : ℂ) - z) / 2) from by
      have hz : (((2 : ℂ)⁻¹) + (-z / 2)) = (((1 : ℂ) - z) / 2) := by
        apply Complex.ext <;> simp; ring
      simpa [hz] using Gamma_supportCpow_shift (σ := σ) (a := (-z / 2))
        (X := supportCpow Ain ((β : ℂ) * z))]
    rw [show (((1 : ℂ) - z) / 2) = Complex.I * (-(z.im / 2)) from by
        apply Complex.ext <;> simp [hz1, div_eq_mul_inv],
      show (β : ℂ) * z = (β : ℂ) + Complex.I * (β * z.im) from by
        apply Complex.ext <;> simp [hz1]]
    simpa using
      (traceNorm_supportCpow_im_beta_add_sandwich_le_one β hβ σ Ain
        hAin_nonneg hAin_trace1 (-(z.im / 2)) (β * z.im))
  have hTX1 : weighted_norm 1 τ (T (interpXin β σ Ain z)) ≤ 1 :=
    (h1 (interpXin β σ Ain z)).trans hX1
  exact (show ‖interpTrace τ T (interpXin β σ Ain) (interpYout β τ Aout) z‖
      ≤ weighted_norm_infty τ (interpYout β τ Aout z) *
          weighted_norm 1 τ (T (interpXin β σ Ain z)) from by
    calc
      ‖interpTrace τ T (interpXin β σ Ain) (interpYout β τ Aout) z‖
          ≤ (interpYout β τ Aout z *
              Gamma τ (T (interpXin β σ Ain z))).traceNorm := by
            simpa [interpTrace] using Matrix.abs_trace_le_traceNorm
              (interpYout β τ Aout z * Gamma τ (T (interpXin β σ Ain z)))
      _ ≤ ‖interpYout β τ Aout z‖ *
            (Gamma τ (T (interpXin β σ Ain z))).traceNorm :=
          Matrix.traceNorm_mul_le_opNorm_traceNorm _ _
      _ = weighted_norm_infty τ (interpYout β τ Aout z) *
            weighted_norm 1 τ (T (interpXin β σ Ain z)) := by
          rw [weighted_norm_one_eq_trace_norm_Gamma,
            show schattenNorm (Gamma τ (T (interpXin β σ Ain z))) 1
              = (Gamma τ (T (interpXin β σ Ain z))).traceNorm from by
            rw [schattenNorm_eq_sum_singularValues_rpow _ (by norm_num),
              Matrix.traceNorm_eq_sum_singularValues]; simp]
          rfl).trans
    (mul_le_one₀ hY1 (by unfold weighted_norm; exact schattenNorm_nonneg _ _) hTX1)

private lemma weighted_norm_density_contraction_of_interpolation {β : ℝ} (hβ : 1 < β)
    (ρ σ : MState d) (ω τ : MState d₂) (T : MatrixMap d d₂ ℂ)
    (hker : σ.M.ker ≤ ρ.M.ker) (hker_out : τ.M.ker ≤ ω.M.ker)
    (hTρ : Gamma τ (T (Gamma_inv σ ρ.M.mat)) = ω.M.mat)
    (hInf : ∀ X, weighted_norm_infty τ (T X) ≤ weighted_norm_infty σ X)
    (h1 : ∀ X, weighted_norm 1 τ (T X) ≤ weighted_norm 1 σ X) :
    weighted_norm β τ (Gamma_inv τ ω.M.mat) ≤
      weighted_norm β σ (Gamma_inv σ ρ.M.mat) := by
  have hβne : β ≠ 0 := by linarith
  have hr_ne : ((1 - β) / (2 * β) : ℝ) ≠ 0 := by
    exact div_ne_zero (sub_ne_zero.mpr hβ.ne) (mul_ne_zero two_ne_zero hβne)
  set cin := weighted_norm β σ (Gamma_inv σ ρ.M.mat)
  set cout := weighted_norm β τ (Gamma_inv τ ω.M.mat)
  have hcin_pos : 0 < cin := by simpa [cin] using weighted_norm_Gamma_inv_density_pos β hβ hker
  have hcout_pos : 0 < cout := by simpa [cout] using weighted_norm_Gamma_inv_density_pos β hβ hker_out
  set Ain : HermitianMat d ℂ := (cin⁻¹) • (ρ.M.conj (σ.M ^ ((1 - β) / (2 * β))).mat)
  set Aout : HermitianMat d₂ ℂ := (cout⁻¹) • (ω.M.conj (τ.M ^ ((1 - β) / (2 * β))).mat)
  have hAin_nonneg : 0 ≤ Ain := by
    simp only [Ain]
    exact smul_nonneg (inv_nonneg.mpr hcin_pos.le) (HermitianMat.conj_nonneg _ ρ.nonneg)
  have hAout_nonneg : 0 ≤ Aout := by
    simp only [Aout]
    exact smul_nonneg (inv_nonneg.mpr hcout_pos.le) (HermitianMat.conj_nonneg _ ω.nonneg)
  have hAin_trace1 : (Ain ^ β).trace = 1 := by
    simpa [Ain, cin] using normalized_sandwich_core_trace_eq_one β hβ hker
  have hAout_trace1 : (Aout ^ β).trace = 1 := by
    simpa [Aout, cout] using normalized_sandwich_core_trace_eq_one β hβ hker_out
  let Xin : ℂ → Matrix d d ℂ := interpXin β σ Ain
  let Yout : ℂ → Matrix d₂ d₂ ℂ := interpYout β τ Aout
  let f : ℂ → ℂ := interpTrace τ T Xin Yout
  have hθeval : f (((1 / β : ℝ) : ℂ)) = cout / cin := by
    let r : ℝ := (1 - β) / (2 * β)
    have hs_add :
        ((-(1 / (2 * β : ℝ)) : ℂ)) + (r : ℂ) = ((-1 / 2 : ℝ) : ℂ) := by
      exact_mod_cast (by
        dsimp [r]
        field_simp [hβne]
        ring_nf : (-(1 / (2 * β : ℝ))) + r = (-1 / 2 : ℝ))
    have hs_add' :
        (r : ℂ) + ((-(1 / (2 * β : ℝ)) : ℂ)) = ((-1 / 2 : ℝ) : ℂ) := by
      simpa [add_comm] using hs_add
    let Sneg : Matrix d d ℂ := supportCpow σ.M (((-1 / 2 : ℝ) : ℂ))
    have hXinθ :
        Xin (((1 / β : ℝ) : ℂ)) =
          cin⁻¹ • (Sneg * ρ.M.mat * Sneg) := by
      calc
        Xin (((1 / β : ℝ) : ℂ))
          = supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) *
              Ain.mat *
              supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) := by
                dsimp [Xin, interpXin]
                rw [show ((β : ℂ) * (((1 / β : ℝ) : ℂ))) = 1 from by
                  exact_mod_cast (by field_simp [hβne] : β * (1 / β : ℝ) = 1),
                  show supportCpow Ain (1 : ℂ) = Ain.mat from by
                  simpa using supportCpow_ofReal Ain hAin_nonneg zero_lt_one]
                simp [div_eq_mul_inv]
        _ = supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) *
              ((cin⁻¹) • (((σ.M ^ ((1 - β) / (2 * β))).mat) * ρ.M.mat *
                ((σ.M ^ ((1 - β) / (2 * β))).mat)ᴴ)) *
              supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) := by
                simp [Ain, HermitianMat.conj_apply_mat]
        _ = cin⁻¹ •
              (supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)) *
                supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) *
                ρ.M.mat *
                (supportCpow σ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) *
                  supportCpow σ.M ((-(1 / (2 * β : ℝ)) : ℂ)))) := by
                rw [HermitianMat.conjTranspose_mat,
                  ← supportCpow_ofReal_ne_zero (A := σ.M) (hA := σ.nonneg)
                    (r := (1 - β) / (2 * β)) hr_ne]
                simp [Matrix.mul_assoc]
        _ = cin⁻¹ •
              (supportCpow σ.M (((-1 / 2 : ℝ) : ℂ)) *
                ρ.M.mat *
                supportCpow σ.M (((-1 / 2 : ℝ) : ℂ))) := by
                rw [supportCpow_mul, supportCpow_mul, hs_add, hs_add']
        _ = cin⁻¹ • (Sneg * ρ.M.mat * Sneg) := by
              rfl
    have hTθ :
        Gamma τ (T (Xin (((1 / β : ℝ) : ℂ)))) = (cin⁻¹) • ω.M.mat := by
      calc
        Gamma τ (T (Xin (((1 / β : ℝ) : ℂ))))
          = Gamma τ (T (cin⁻¹ • (Sneg * ρ.M.mat * Sneg))) := by
              rw [hXinθ]
        _ = (cin⁻¹) • Gamma τ (T (Sneg * ρ.M.mat * Sneg)) := by
              simp [Gamma, Matrix.mul_assoc]
        _ = (cin⁻¹) • Gamma τ (T (Gamma_inv σ ρ.M.mat)) := by
              rw [show Sneg * ρ.M.mat * Sneg = Gamma_inv σ ρ.M.mat by
                dsimp [Sneg]
                rw [supportCpow_ofReal_ne_zero σ.M σ.nonneg (by norm_num), Gamma_inv,
                  HermitianMat.rpow_eq_cfc]]
        _ = (cin⁻¹) • ω.M.mat := by
              rw [hTρ]
    have hYθ :
        Yout (((1 / β : ℝ) : ℂ)) =
          supportCpow τ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) *
            (Aout ^ (β - 1)).mat *
            supportCpow τ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) := by
      dsimp [Yout, interpYout]
      rw [show ((((1 / β : ℝ) : ℂ) - 1) / 2) = ((((1 - β) / (2 * β) : ℝ) : ℂ)) by
        exact_mod_cast (by field_simp [hβne] :
          (((1 / β : ℝ) - 1) / 2) = ((1 - β) / (2 * β) : ℝ))]
      rw [show ((β : ℂ) * (1 - (((1 / β : ℝ) : ℂ)))) = (β - 1 : ℂ) from by
        exact_mod_cast (by field_simp [hβne] : β * (1 - (1 / β : ℝ)) = β - 1)]
      rw [show supportCpow Aout ((β : ℂ) - 1) = (Aout ^ (β - 1)).mat from by
        simpa using supportCpow_ofReal Aout hAout_nonneg (show 0 < β - 1 by linarith)]
    have hBout :
        supportCpow τ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) * ω.M.mat *
          supportCpow τ.M ((((1 - β) / (2 * β) : ℝ) : ℂ)) =
            cout • Aout.mat := by
      rw [supportCpow_ofReal_ne_zero (A := τ.M) (hA := τ.nonneg)
        (r := (1 - β) / (2 * β)) hr_ne]
      simp [Aout, HermitianMat.conj_apply_mat, Matrix.mul_assoc, smul_smul,
        show cout * cout⁻¹ = (1 : ℝ) by field_simp [hcout_pos.ne']]
    have hpowmul :
        (Aout ^ (β - 1)).mat * Aout.mat = (Aout ^ β).mat := by
      calc
        (Aout ^ (β - 1)).mat * Aout.mat =
            supportCpow Aout (((β - 1 : ℝ) : ℂ)) * supportCpow Aout (1 : ℂ) := by
          rw [supportCpow_ofReal Aout hAout_nonneg (by linarith),
            show supportCpow Aout (1 : ℂ) = Aout.mat from by
              simpa using supportCpow_ofReal Aout hAout_nonneg zero_lt_one]
        _ = supportCpow Aout (β : ℂ) := by
              rw [supportCpow_mul]
              congr 1
              simp
        _ = (Aout ^ β).mat := by
              symm
              rw [supportCpow_ofReal Aout hAout_nonneg (show 0 < β by linarith)]
    let Sout : Matrix d₂ d₂ ℂ :=
      supportCpow τ.M ((((1 - β) / (2 * β) : ℝ) : ℂ))
    calc
      f (((1 / β : ℝ) : ℂ))
          = ((Yout (((1 / β : ℝ) : ℂ))) * ((cin⁻¹) • ω.M.mat)).trace := by
              dsimp [f, interpTrace]
              rw [hTθ]
      _ = cin⁻¹ * (Yout (((1 / β : ℝ) : ℂ)) * ω.M.mat).trace := by
              simp
      _ = cin⁻¹ * (((Sout * (Aout ^ (β - 1)).mat * Sout) * ω.M.mat).trace) := by
              rw [hYθ]
      _ = cin⁻¹ * (((Aout ^ (β - 1)).mat * (Sout * ω.M.mat * Sout)).trace) := by
              congr 1
              let A : Matrix d₂ d₂ ℂ := (Aout ^ (β - 1)).mat
              let R : Matrix d₂ d₂ ℂ := ω.M.mat
              have hcyc : ((Sout * A * Sout) * R).trace = (A * (Sout * R * Sout)).trace := by
                calc
                  ((Sout * A * Sout) * R).trace = (Sout * A * (Sout * R)).trace := by
                    rw [Matrix.mul_assoc]
                  _ = ((Sout * R) * Sout * A).trace := by
                    rw [Matrix.trace_mul_cycle]
                  _ = (A * (Sout * R) * Sout).trace := by
                    rw [Matrix.trace_mul_cycle]
                  _ = (A * ((Sout * R) * Sout)).trace := by
                    rw [Matrix.mul_assoc]
                  _ = (A * (Sout * R * Sout)).trace := rfl
              simpa [A, R] using hcyc
      _ = cin⁻¹ * (((Aout ^ (β - 1)).mat * (cout • Aout.mat)).trace) := by rw [hBout]
      _ = cin⁻¹ * (cout * ((Aout ^ β).mat).trace) := by
              rw [Matrix.mul_smul, Matrix.trace_smul]
              simp [hpowmul]
      _ = cin⁻¹ * (cout * 1) := by
              rw [show ((Aout ^ β).mat).trace = (1 : ℂ) from by
                exact (HermitianMat.trace_eq_trace_rc (A := Aout ^ β)).symm.trans
                  (show (((Aout ^ β).trace : ℂ) = 1) from by exact_mod_cast hAout_trace1)]
      _ = cout / cin := by
              calc
                (((cin⁻¹ : ℝ) : ℂ) * (cout * 1))
                    = ((cin : ℂ)⁻¹ * ((cout : ℂ) * 1)) := by simp
                _ = (cout : ℂ) / cin := by simp [div_eq_mul_inv, mul_comm]
  obtain ⟨Kσneg, hKσneg⟩ :=
    exists_norm_supportCpow_le_on_verticalClosedStrip σ.M σ.nonneg (-1 / 2) 0
  obtain ⟨KAin, hKAin⟩ :=
    exists_norm_supportCpow_le_on_verticalClosedStrip Ain hAin_nonneg 0 β
  obtain ⟨KAout, hKAout⟩ :=
    exists_norm_supportCpow_le_on_verticalClosedStrip Aout hAout_nonneg 0 β
  let KXin : ℝ := Kσneg * KAin * Kσneg
  let KYout : ℝ := Fintype.card d₂ * KAout
  have hB :
      BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨KYout * KXin, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simpa [f, interpTrace] using
      (abs_trace_weighted_pair_le_right (σ := τ) (X := T (Xin z)) (Y := Yout z)).trans
        (mul_le_mul
          (by
            simpa [Yout, interpYout, KYout] using
              (weighted_norm_one_supportCpow_sandwich_bound (β := β) hβ τ Aout hKAout hz))
          ((hInf (Xin z)).trans
            (by
              simpa [Xin, interpXin, KXin] using
                (weighted_norm_infty_supportCpow_sandwich_bound (β := β) hβ σ Ain hKσneg
                  hKAin hz)))
          (by dsimp [weighted_norm_infty]; exact norm_nonneg _)
          (by
            exact mul_nonneg (by positivity) <| le_trans (norm_nonneg _) <| hKAout 0 <| by
              simp [Complex.HadamardThreeLines.verticalClosedStrip, show 0 ≤ β by linarith]))
  have hfθ :
      ‖f (((1 / β : ℝ) : ℂ))‖ ≤ 1 := by
    simpa using
      (Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
        (f := f) (l := 0) (u := 1) (a := 1) (b := 1) zero_lt_one
        (by
          have hβpos : 0 < β := by linarith
          simp [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage]
          constructor
          · positivity
          · simpa [one_div] using (div_le_one hβpos).2 (le_of_lt hβ))
        (by simpa [f, Xin, Yout] using interpTrace_diffContOnCl hβ σ τ T Ain Aout) hB
        (by
          simpa [f, Xin, Yout] using
            interpTrace_left_boundary_le_one hβ σ τ T Ain Aout hAin_nonneg hAout_nonneg
              hAout_trace1 hInf)
        (by
          simpa [f, Xin, Yout] using
            interpTrace_right_boundary_le_one hβ σ τ T Ain Aout hAin_nonneg hAout_nonneg
              hAin_trace1 h1))
  exact (div_le_one hcin_pos).mp <| by
    have hnorm_ratio : ‖cout / cin‖ ≤ 1 := by
      have hnorm_ratioC : ‖(((cout / cin : ℝ) : ℂ))‖ ≤ 1 := by
        have hθeval' : f (((1 / β : ℝ) : ℂ)) = (((cout / cin : ℝ) : ℂ) : ℂ) := by
          simpa using hθeval
        rw [← hθeval']
        exact hfθ
      simpa using hnorm_ratioC
    rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ cout / cin)] at hnorm_ratio

private lemma sandwichedRenyiEntropy_DPI_hnorm {β : ℝ} (hβ : 1 < β)
    (ρ σ : MState d) (Φ : CPTPMap d d₂)
    (hker : σ.M.ker ≤ ρ.M.ker) (hker_map : (Φ σ).M.ker ≤ (Φ ρ).M.ker) :
    weighted_norm β (Φ σ) (Gamma_inv (Φ σ) (Φ ρ).M.mat) ≤
      weighted_norm β σ (Gamma_inv σ ρ.M.mat) := by
  refine weighted_norm_density_contraction_of_interpolation hβ ρ σ (Φ ρ) (Φ σ)
    (T_map σ Φ) hker hker_map ?_ ?_ ?_
  · calc
      Gamma (Φ σ) ((T_map σ Φ) (Gamma_inv σ ρ.M.mat))
        = Gamma (Φ σ) (Gamma_inv (Φ σ) (Φ ρ).M.mat) := by
            rw [show (T_map σ Φ) (Gamma_inv σ ρ.M.mat) =
              Gamma_inv (Φ σ) (Φ ρ).M.mat from by
              dsimp [T_map, T_op]
              rw [Gamma_Gamma_inv_density hker]
              rfl]
      _ = (Φ ρ).M.mat := Gamma_Gamma_inv_density hker_map
  · intro X
    dsimp [weighted_norm_infty]
    exact MatrixMap.cp_subunital_opNorm_le_one (M := T_map σ Φ) (T_is_CP σ Φ)
      (by
        dsimp [T_map, T_op]
        rw [Gamma_one]
        change Gamma_inv (Φ σ) (Φ σ).M.mat ≤ 1
        rw [Gamma_inv_self_supportProj]
        simpa using supportProj_le_one (Φ σ).M) X
  · intro X
    exact weighted_norm_one_T_map_le σ Φ X

private lemma sandwichedRenyiEntropy_DPI_ker {β : ℝ} (hβ : 1 < β)
    (ρ σ : MState d) (Φ : CPTPMap d d₂) (hker : σ.M.ker ≤ ρ.M.ker) :
    D̃_ β(Φ ρ‖Φ σ) ≤ D̃_ β(ρ‖σ) := by
  have hker_map : (Φ σ).M.ker ≤ (Φ ρ).M.ker := by
    rcases exists_le_exp_of_ker_le hker with ⟨x, hx⟩
    have hmap : (Φ ρ).M ≤ Real.exp x • (Φ σ).M := by
      have hdiff : (0 : Matrix d d ℂ) ≤ Real.exp x • σ.M.mat - ρ.M.mat := by
        simpa [sub_nonneg] using hx
      have h : (0 : Matrix d₂ d₂ ℂ) ≤ Φ.map (Real.exp x • σ.M.mat - ρ.M.mat) :=
        (Φ.cp.IsPositive (by simpa [Matrix.nonneg_iff_posSemidef] using hdiff)).nonneg
      simpa [sub_nonneg, map_sub, map_smul] using h
    exact HermitianMat.ker_le_of_le_smul (by positivity) (Φ ρ).nonneg hmap
  set cin : ℝ := weighted_norm β σ (Gamma_inv σ ρ.M.mat)
  set cout : ℝ := weighted_norm β (Φ σ) (Gamma_inv (Φ σ) (Φ ρ).M.mat)
  have hcin_pos : 0 < cin := by
    dsimp [cin]; exact weighted_norm_Gamma_inv_density_pos β hβ hker
  have hcout_pos : 0 < cout := by
    dsimp [cout]; exact weighted_norm_Gamma_inv_density_pos β hβ hker_map
  have hnorm : cout ≤ cin :=
    sandwichedRenyiEntropy_DPI_hnorm hβ ρ σ Φ hker hker_map
  have hβ0 : 0 < β := lt_trans zero_lt_one hβ
  have hout :
      D̃_ β(Φ ρ‖Φ σ) = ENNReal.ofReal (Real.log (cout ^ β) / (β - 1)) := by
    have hnonneg :
        0 ≤ Real.log (cout ^ β) / (β - 1) := by
      simpa [hβ.ne', cout, sandwich_core_trace_eq_weighted_norm_rpow β hβ (Φ ρ) (Φ σ)] using
        (sandwichedRelRentropy_nonneg hβ0 hker_map)
    unfold SandwichedRelRentropy
    simpa [hβ0, hβ.ne', hker_map, cout,
      sandwich_core_trace_eq_weighted_norm_rpow β hβ (Φ ρ) (Φ σ)] using
      (ENNReal.ofReal_eq_coe_nnreal hnonneg).symm
  have hin :
      D̃_ β(ρ‖σ) = ENNReal.ofReal (Real.log (cin ^ β) / (β - 1)) := by
    have hnonneg :
        0 ≤ Real.log (cin ^ β) / (β - 1) := by
      simpa [hβ.ne', cin, sandwich_core_trace_eq_weighted_norm_rpow β hβ ρ σ] using
        (sandwichedRelRentropy_nonneg hβ0 hker)
    unfold SandwichedRelRentropy
    simpa [hβ0, hβ.ne', hker, cin,
      sandwich_core_trace_eq_weighted_norm_rpow β hβ ρ σ] using
      (ENNReal.ofReal_eq_coe_nnreal hnonneg).symm
  rw [hout, hin]
  apply ENNReal.ofReal_le_ofReal
  have hpow_le : cout ^ β ≤ cin ^ β := by
    exact Real.rpow_le_rpow hcout_pos.le hnorm (by linarith)
  have hpow_pos_out : 0 < cout ^ β := by
    exact Real.rpow_pos_of_pos hcout_pos _
  have hpow_pos_in : 0 < cin ^ β := by
    exact Real.rpow_pos_of_pos hcin_pos _
  have hlog_le : Real.log (cout ^ β) ≤ Real.log (cin ^ β) := by
    exact Real.strictMonoOn_log.monotoneOn hpow_pos_out hpow_pos_in hpow_le
  exact div_le_div_of_nonneg_right hlog_le (by linarith)

/-- The high-parameter branch of the data processing inequality for sandwiched Rényi relative
entropy: for `1 ≤ α`, applying a CPTP map cannot increase `D̃_α`.

The proof follows the Hadamard three-lines/interpolation argument for the sandwiched Rényi DPI
from Müller-Lennert et al. and Beigi, with the `α = 1` case obtained by right-continuity from
`α > 1`. -/
theorem sandwichedRenyiEntropy_DPI_of_one_le
    (hα : 1 ≤ α) (ρ σ : MState d) (Φ : CPTPMap d d₂) :
    D̃_ α(Φ ρ‖Φ σ) ≤ D̃_ α(ρ‖σ) := by
  have hstrict : ∀ {β : ℝ}, 1 < β → D̃_ β(Φ ρ‖Φ σ) ≤ D̃_ β(ρ‖σ) := by
    intro β hβ
    by_cases hker : σ.M.ker ≤ ρ.M.ker
    · exact sandwichedRenyiEntropy_DPI_ker hβ ρ σ Φ hker
    · have : D̃_ β(ρ‖σ) = ⊤ := by
        unfold SandwichedRelRentropy; simp [show 0 < β from lt_trans zero_lt_one hβ, hker]
      rw [this]; exact le_top
  rcases eq_or_lt_of_le hα with rfl | hgt
  · have hmono := nhdsWithin_mono (1 : ℝ) (Set.Ioi_subset_Ioi zero_le_one)
    exact le_of_tendsto_of_tendsto
      (((sandwichedRelRentropy.continuousOn (Φ ρ) (Φ σ)) 1 (by norm_num)).mono_left
        hmono)
      (((sandwichedRelRentropy.continuousOn ρ σ) 1 (by norm_num)).mono_left
        hmono)
      (by
        filter_upwards [self_mem_nhdsWithin] with β hβ
        exact hstrict hβ)
  · exact hstrict hgt
