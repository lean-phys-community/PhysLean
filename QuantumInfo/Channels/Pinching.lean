/-
Copyright (c) 2025 Leonardo A Lessa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo A Lessa, Alex Meiburg
-/
module

public import QuantumInfo.Channels.Bundled
public import QuantumInfo.Channels.CPTP
public import QuantumInfo.Channels.Dual
public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.Channels.Unbundled
public import QuantumInfo.States.Mixed.MState
public import QuantumInfo.Entropy.VonNeumann
public import QuantumInfo.Entropy.SSA
public import QuantumInfo.Entropy.Relative
public import QuantumInfo.Entropy.DPI
public import QuantumInfo.ForMathlib.HermitianMat.CFC

/-! # Pinching channels
A pinching channel decoheres in the eigenspaces of a given state.
More precisely, given a state ρ, the pinching channel with respect to ρ is defined as
  E(σ) = ∑ Pᵢ σ Pᵢ
where the P_i are the projectors onto the i-th eigenspaces of ρ = ∑ᵢ pᵢ Pᵢ, with i ≠ j → pᵢ ≠ pⱼ.

TODO: Generalize to pinching with respect to arbitrary P(O)VM.
-/

@[expose] public section

noncomputable section
open scoped Matrix RealInnerProductSpace

variable {d : Type*} [Fintype d] [DecidableEq d]

def pinching_kraus (ρ : MState d) : spectrum ℝ ρ.m → HermitianMat d ℂ :=
  fun x ↦ ρ.M.cfc (fun y ↦ if y = x then 1 else 0)

theorem pinching_kraus_commutes (ρ : MState d) (i : spectrum ℝ ρ.m) :
    Commute (pinching_kraus ρ i).mat ρ.m :=
  (Commute.refl ρ.M.mat).cfc_left _

theorem pinching_kraus_mul_self (ρ : MState d) (i : spectrum ℝ ρ.m) :
    (pinching_kraus ρ i).mat * ρ.m = i.val • pinching_kraus ρ i := by
  dsimp only [MState.m]
  nth_rw 1 [← ρ.M.cfc_id]
  rw [pinching_kraus, ← ρ.M.mat_cfc_mul, ← HermitianMat.mat_smul, ← ρ.M.cfc_const_mul]
  congr! 3
  simp +contextual

instance finite_spectrum_inst (ρ : MState d) : Fintype (spectrum ℝ ρ.m) :=
  Fintype.ofFinite (spectrum ℝ ρ.m)

theorem pinching_kraus_orthogonal (ρ : MState d) {i j : spectrum ℝ ρ.m} (h : i ≠ j) :
    (pinching_kraus ρ i).mat * (pinching_kraus ρ j).mat = 0 := by
  convert! (HermitianMat.mat_cfc_mul ρ.M _ _).symm
  convert! congr($((ρ.M.cfc_const 0).symm).mat)
  · simp
  · grind [Pi.mul_apply]

/-- The Kraus operators of the pinching channelare projectors: they square to themselves. -/
@[simp]
theorem pinching_sq_eq_self (ρ : MState d) (k) : (pinching_kraus ρ k) ^ 2  = pinching_kraus ρ k := by
  rw [pinching_kraus, ← HermitianMat.cfc_pow, ← ρ.M.cfc_comp]
  simp [Function.comp_def]

/-- The Kraus operators of the pinching channel are orthogonal projectors. -/
theorem pinching_kraus_ortho (ρ : MState d) (i j : spectrum ℝ ρ.m) :
    (pinching_kraus ρ i).mat * (pinching_kraus ρ j).mat = if i = j then (pinching_kraus ρ i).mat else 0 := by
  split_ifs with hij
  · grind [sq, HermitianMat.mat_pow, pinching_sq_eq_self]
  · exact pinching_kraus_orthogonal ρ hij

theorem pinching_sum (ρ : MState d) : ∑ k, pinching_kraus ρ k = 1 := by
  ext1
  have heq : Set.EqOn (fun x => ∑ i : spectrum ℝ ρ.m, if x = ↑i then (1 : ℝ) else 0) 1
      (spectrum ℝ ρ.m) := fun x hx ↦ by
    simp [Finset.sum_set_coe (f := fun i => if x = i then (1 : ℝ) else 0), Set.mem_toFinset.2 hx]
  simp only [pinching_kraus, HermitianMat.mat_finset_sum, HermitianMat.mat_cfc,
    HermitianMat.mat_one, MState.mat_M]
  rw [← cfc_sum, Finset.sum_fn, cfc_congr heq]
  exact cfc_one (R := ℝ) (ha := ρ.M.isSelfAdjoint)

def pinching_map (ρ : MState d) : CPTPMap d d ℂ :=
  CPTPMap.of_kraus_CPTPMap (HermitianMat.mat ∘ pinching_kraus ρ) (by
  simp [pinching_kraus_ortho, ← HermitianMat.mat_finset_sum, pinching_sum])

theorem pinchingMap_apply_M (σ ρ : MState d) : (pinching_map σ ρ).M =
  ⟨_, (MatrixMap.of_kraus_isCompletelyPositive
    (HermitianMat.mat ∘ pinching_kraus σ)).IsPositive.IsHermitianPreserving ρ.M.H⟩ :=
  rfl

theorem pinching_eq_sum_conj (σ ρ : MState d) : (pinching_map σ ρ).M =
    ∑ k, (pinching_kraus σ k).mat * ρ.M * (pinching_kraus σ k).mat := by
  rw [pinchingMap_apply_M]
  simp [MatrixMap.of_kraus, Matrix.mul_assoc]

theorem pinching_commutes_kraus (σ ρ : MState d) (i : spectrum ℝ σ.m) :
    Commute (pinching_map σ ρ).m (pinching_kraus σ i).mat := by
  simp only [Commute, SemiconjBy, ← MState.mat_M, pinching_eq_sum_conj, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  congr! 1 with x
  by_cases h : x = i <;> simp [h, ← mul_assoc, pinching_kraus_ortho]
  grind

theorem pinching_commutes (ρ σ : MState d) :
    Commute (pinching_map σ ρ).m σ.m := by
  have h_expand := pinching_eq_sum_conj σ ρ
  simp only [MState.mat_M] at h_expand
  rw [h_expand]
  refine Commute.sum_left _ _ _ fun i _ ↦ ?_
  have hl := pinching_kraus_mul_self σ i
  have hr := hl ▸ (pinching_kraus_commutes σ i).symm.eq
  simp only [Commute, SemiconjBy, mul_assoc, hl]
  simp only [← mul_assoc, hr]
  simp

@[simp]
theorem pinching_self (ρ : MState d) : pinching_map ρ ρ = ρ := by
  ext1
  ext1
  rw [pinching_eq_sum_conj]
  simp [MState.mat_M, (pinching_kraus_commutes ρ _).eq, mul_assoc, pinching_kraus_ortho,
    ← Finset.mul_sum, ← HermitianMat.mat_finset_sum, pinching_sum]

set_option backward.isDefEq.respectTransparency false in
/-- Lemma 3.10 of Hayashi's book "Quantum Information Theory - Mathematical Foundations".
Also, Lemma 5 in https://arxiv.org/pdf/quant-ph/0107004.
-- Used in (S60) -/
theorem pinching_bound (ρ σ : MState d) : ρ.M ≤ (↑(Fintype.card (spectrum ℝ σ.m)) : ℝ) • (pinching_map σ ρ).M := by
  suffices ρ.M ≤ (Fintype.card (spectrum ℝ σ.m) : ℝ) • ∑ c, ρ.M.conj (pinching_kraus σ c) by
    convert this
    ext1
    simp [pinchingMap_apply_M, MatrixMap.of_kraus, HermitianMat.conj]
  --Rewrite ρ as its spectral decomposition
  obtain ⟨ψs, hρm⟩ := ρ.spectralDecomposition
  simp only [hρm, map_sum, Finset.smul_sum]
  rw [Finset.sum_comm (α := d)]
  gcongr with i _
  --
  open ComplexOrder in
  rw [HermitianMat.le_iff_mulVec_le_mulVec]
  intro v
  simp [← Finset.smul_sum, smul_comm _ (ρ.spectrum i : ℝ), Matrix.smul_mulVec, dotProduct_smul]
  gcongr
  · exact_mod_cast (ρ.spectrum i).zero_le
  have h1 : (1 : Matrix d d ℂ) = (1 : HermitianMat d ℂ) := by exact selfAdjoint.val_one
  conv_lhs =>
    enter [2, 1]
    rw [← one_mul (MState.m _), h1, ← congr(HermitianMat.mat $(pinching_sum σ))]
    enter [2]
    rw [← mul_one (MState.m _), h1, ← congr(HermitianMat.mat $(pinching_sum σ))]
  simp only [HermitianMat.mat_finset_sum]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_mulVec, dotProduct_sum]
  simp only [MState.pure]
  dsimp [MState.m]
  --This out to be Cauchy-Schwarz.
  have hschwarz := inner_mul_inner_self_le (𝕜 := ℂ) (E := EuclideanSpace ℂ (↑(spectrum ℝ σ.m)))
    (x := .toLp 2 fun i ↦ 1) (y := .toLp 2 fun k ↦ (
      star v ⬝ᵥ ((pinching_kraus σ k).mat *ᵥ (ψs i))
    ))
  rw [← Complex.real_le_real] at hschwarz
  simp only [PiLp.inner_apply] at hschwarz
  simp only [RCLike.inner_apply, map_one, mul_one, one_mul, Complex.ofReal_mul, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, RCLike.natCast_re, map_sum, RCLike.re_to_complex,
    Complex.ofReal_natCast, Complex.ofReal_sum] at hschwarz
  simp only [HermitianMat.mat_mk] at ⊢
  have h_mul (x y : spectrum ℝ σ.m) :
      star v ⬝ᵥ ((pinching_kraus σ y).mat *
        (Matrix.vecMulVec ⇑(ψs i) ((ψs i).to_bra) : Matrix d d ℂ)
        * (pinching_kraus σ x).mat) *ᵥ v =
      star v ⬝ᵥ (pinching_kraus σ y).mat *ᵥ (ψs i)
        * (starRingEnd ℂ) (star v ⬝ᵥ (pinching_kraus σ x).mat *ᵥ (ψs i)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_comm]
    congr
    rw [starRingEnd_apply, ← Matrix.star_dotProduct, Matrix.star_mulVec]
    rw [← Matrix.dotProduct_mulVec, HermitianMat.conjTranspose_mat]
    --Uses the defeq of `star (_ : Bra)` and `(_ : Ket)`. Would be good to have a lemma
    -- so that we don't 'abuse' this defeq, TODO. (Maybe even make the coercions between
    -- kets and bras irreducible?)
    rfl
  convert hschwarz with x <;> clear hschwarz
  · rw [← map_sum, ← Complex.ofReal_mul, ← norm_mul]
    rw [Complex.mul_conj, Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _)]
    simp_rw [← Complex.mul_conj, map_sum, Finset.mul_sum, Finset.sum_mul]
    congr! with x _ y _
    rw [← Matrix.mul_assoc]
    exact h_mul x y
  · simp
  · have hc (c d : ℂ) : d = starRingEnd ℂ d  → c = d → c = d.re := by
      rintro h rfl; simp [Complex.ext_iff] at h ⊢; linarith
    apply hc <;> clear hc
    · simpa using mul_comm _ _
    · exact h_mul x x

open ComplexOrder in
theorem ker_le_ker_pinching_of_PosDef (ρ σ : MState d) (hpos : σ.m.PosDef) : σ.M.ker ≤ (pinching_map σ ρ).M.ker := by
  have h_ker : σ.M.ker = ⊥ := by
    have := hpos.toLin_ker_eq_bot
    simp [LinearMap.ker_eq_bot', HermitianMat.ker] at this ⊢
    intro m hm
    simpa only [WithLp.ofLp_eq_zero] using this m congr($hm)
  exact h_ker ▸ bot_le

theorem pinching_idempotent (ρ σ : MState d) :
    (pinching_map σ) (pinching_map σ ρ) = (pinching_map σ ρ) := by
  ext1
  ext1
  rw [pinching_eq_sum_conj, pinching_eq_sum_conj]
  simp only [Matrix.mul_sum, Matrix.sum_mul, ← mul_assoc, pinching_kraus_ortho]
  simp [mul_assoc, pinching_kraus_ortho]

theorem inner_cfc_pinching (ρ σ : MState d) (f : ℝ → ℝ) :
    ⟪ρ.M, (pinching_map σ ρ).M.cfc f⟫ = ⟪(pinching_map σ ρ).M, (pinching_map σ ρ).M.cfc f⟫ := by
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
  congr 1
  rw [pinching_eq_sum_conj, Finset.sum_mul, Matrix.trace_sum]
  simp_rw [mul_assoc, ((pinching_commutes_kraus σ ρ _).symm.cfc_right (f := f)).eq,
    Matrix.trace_mul_comm (pinching_kraus σ _).mat]
  simp [mul_assoc, pinching_kraus_ortho, ← Finset.mul_sum, ← Matrix.trace_sum,
    ← HermitianMat.mat_finset_sum, pinching_sum]

theorem inner_cfc_pinching_right (ρ σ : MState d) (f : ℝ → ℝ) :
    ⟪(pinching_map σ ρ).M, σ.M.cfc f⟫ = ⟪ρ.M, σ.M.cfc f⟫ := by
  rw [HermitianMat.inner_eq_re_trace, HermitianMat.inner_eq_re_trace]
  congr 1
  rw [pinching_eq_sum_conj, Finset.sum_mul, Matrix.trace_sum]
  have hC (x) : Commute (pinching_kraus σ x).mat (σ.M.cfc f).mat := σ.M.cfc_self_commute _ f
  simp_rw [mul_assoc, (hC _).eq, Matrix.trace_mul_comm (pinching_kraus σ _).mat]
  simp [mul_assoc, pinching_kraus_ortho, ← Finset.mul_sum, ← Matrix.trace_sum,
    ← HermitianMat.mat_finset_sum, pinching_sum]

open ComplexOrder in
theorem pinching_map_eq_sum_conj_hermitian (σ ρ : MState d) :
    (pinching_map σ ρ).M = ∑ k, ρ.M.conj (pinching_kraus σ k).mat := by
  ext1
  simp [pinching_eq_sum_conj σ ρ]

theorem pinching_map_ker_le (ρ σ : MState d) : (pinching_map σ ρ).M.ker ≤ ρ.M.ker := by
  intro v hv
  rw [pinching_map_eq_sum_conj_hermitian σ ρ,
    HermitianMat.ker_sum _ fun i ↦ HermitianMat.conj_nonneg (pinching_kraus σ i).mat ρ.nonneg,
    Submodule.mem_iInf] at hv
  have hv_sum : ∑ k : (spectrum ℝ σ.m), (pinching_kraus σ k).mat *ᵥ v = v := by
    rw [← Matrix.sum_mulVec, ← HermitianMat.mat_finset_sum, pinching_sum σ,
      HermitianMat.mat_one, Matrix.one_mulVec]
  replace hv_sum := congr(WithLp.toLp 2 $(hv_sum))
  simp only [WithLp.toLp_sum, WithLp.toLp_ofLp] at hv_sum
  rw [← hv_sum]
  refine Submodule.sum_mem _ fun k _ ↦ ?_
  have h1 := hv k
  simp only [HermitianMat.ker_conj ρ.nonneg, HermitianMat.conjTranspose_mat,
    Submodule.mem_comap] at h1 ⊢
  exact h1


noncomputable section AristotleLemmas

/-
If v is in the kernel of σ, then for any non-zero eigenvalue k, the projection of v onto the k-eigenspace is 0.
-/
theorem pinching_kraus_ker_of_ne_zero {d : Type*} [Fintype d] [DecidableEq d]
    (σ : MState d) (v : d → ℂ) (hv : σ.m.mulVec v = 0)
    (k : spectrum ℝ σ.m) (hk : k.val ≠ 0) :
    (pinching_kraus σ k).mat *ᵥ v = 0 := by
  have h := congr($(pinching_kraus_mul_self σ k) *ᵥ v)
  rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero] at h
  simpa [Matrix.smul_mulVec, smul_eq_zero, hk] using h.symm

end AristotleLemmas

theorem ker_le_ker_pinching_map_ker (ρ σ : MState d) (h : σ.M.ker ≤ ρ.M.ker) :
    σ.M.ker ≤ (pinching_map σ ρ).M.ker := by
  intro v hv
  have hρv := (HermitianMat.mem_ker_iff_mulVec_zero _ _).mp (h hv)
  rw [HermitianMat.mem_ker_iff_mulVec_zero] at hv ⊢
  have h_expand := congr($(pinching_eq_sum_conj σ ρ) *ᵥ v)
  simp only [Matrix.sum_mulVec, ← Matrix.mulVec_mulVec] at h_expand
  rw [h_expand]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  by_cases hk : k.val = 0
  · have hsum : ∑ j : spectrum ℝ σ.m, (pinching_kraus σ j).mat *ᵥ v.ofLp = v.ofLp := by
      rw [← Matrix.sum_mulVec, ← HermitianMat.mat_finset_sum, pinching_sum,
        HermitianMat.mat_one, Matrix.one_mulVec]
    rw [Finset.sum_eq_single k (fun j _ hj ↦ pinching_kraus_ker_of_ne_zero σ _ hv j
      fun h0 ↦ hj (Subtype.ext (h0.trans hk.symm))) (by simp)] at hsum
    rw [hsum, hρv, Matrix.mulVec_zero]
  · rw [pinching_kraus_ker_of_ne_zero σ _ hv k hk, Matrix.mulVec_zero, Matrix.mulVec_zero]

/-- Exercise 2.8 of Hayashi's book "A group theoretic approach to Quantum Information". -/
theorem pinching_pythagoras (ρ σ : MState d) :
    𝐃(ρ‖σ) = 𝐃(ρ‖pinching_map σ ρ) + 𝐃(pinching_map σ ρ‖σ) := by
  by_cases h_ker : σ.M.ker ≤ ρ.M.ker
  · rw [← EReal.coe_ennreal_eq_coe_ennreal_iff, EReal.coe_ennreal_add,
      qRelativeEnt_ker h_ker, qRelativeEnt_ker (pinching_map_ker_le ρ σ),
      qRelativeEnt_ker (ker_le_ker_pinching_map_ker ρ σ h_ker)]
    have h_eq₁ := inner_cfc_pinching_right ρ σ Real.log
    have h_eq₂ := inner_cfc_pinching ρ σ Real.log
    rw [← HermitianMat.log] at h_eq₁ h_eq₂
    simp only [inner_sub_right, EReal.coe_sub]
    rw [h_eq₂, h_eq₁, ← add_sub_assoc, EReal.sub_add_cancel]
  · have h2 : ¬σ.M.ker ≤ (pinching_map σ ρ).M.ker :=
      fun h2 ↦ h_ker (h2.trans (pinching_map_ker_le ρ σ))
    simp only [qRelativeEnt, SandwichedRelRentropy, dif_pos zero_lt_one, dif_neg h_ker,
      dif_neg h2, add_top]
