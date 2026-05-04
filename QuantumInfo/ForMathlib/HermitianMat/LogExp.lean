/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Proj
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Properties of the matrix logarithm and exponential

In particular, operator monotonicity and concavity of the matrix logarithm.
These are proved using `inv_antitone`, so, first showing that the matrix inverse
is operator antitone for positive definite matrices.
-/

@[expose] public section

variable {d d₂ 𝕜 : Type*}
variable [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂]
variable [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {x : ℝ}

noncomputable section

set_option backward.isDefEq.respectTransparency false in
theorem Matrix.IsHermitian.log_smul_of_ne_zero {A : Matrix d d 𝕜} (hA : A.IsHermitian) (hx : x ≠ 0) :
    cfc Real.log (x • A) = (Real.log x) • cfc (if · = 0 then (0 : ℝ) else 1) A + cfc Real.log A := by
  have hCFC : cfc (Real.log ∘ (x * ·)) A = cfc Real.log (x • A) := by
    exact cfc_comp_smul x Real.log _ (by fun_prop) hA
  rw [← hCFC, ← cfc_smul, ← cfc_add]
  apply cfc_congr
  intro t ht
  by_cases h : t = 0
  · simp [*]
  · simp [*, Real.log_mul]

namespace HermitianMat

section exp

/-- Matrix exponential of a Hermitian matrix, as given by the continuous
functional calculus with `Real.exp` -/
def exp (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.exp

/-- Primed because `Commute.exp_left` refers to `NormedSpace.exp` instead of `HermitianMat.exp`. -/
@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem _root_.Commute.exp_left' (hAB : Commute A.mat B.mat) :
    Commute (A.exp).mat B.mat := by
  rw [exp]; commutes

/-- Primed because `Commute.exp_right` refers to `NormedSpace.exp` instead of `HermitianMat.exp`. -/
@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem _root_.Commute.exp_right' (hAB : Commute A.mat B.mat) :
    Commute A.mat (B.exp).mat := by
  rw [exp]; commutes

@[simp]
theorem reindex_exp (e : d ≃ d₂) : (A.reindex e).exp = A.exp.reindex e :=
  cfc_reindex A Real.exp e

variable (A) in
instance nonSingular_exp : NonSingular A.exp := by
  exact cfc_nonSingular A Real.exp (fun i ↦ by positivity)

/-- The matrix exponential of a Hermitian matrix is nonnegative. -/
theorem exp_nonneg (A : HermitianMat d 𝕜) : 0 ≤ A.exp := by
  rw [exp, HermitianMat.cfc_nonneg_iff]
  exact fun i ↦ le_of_lt (Real.exp_pos _)

/-- The matrix exponential of a Hermitian matrix is strictly positive (Loewner order).
Requires `Nonempty` since over an empty index type every matrix equals zero and `0 < 0`
is false. -/
theorem exp_pos [i : Nonempty d] (A : HermitianMat d 𝕜) : 0 < A.exp := by
  apply A.exp_nonneg.lt_of_ne'
  intro h
  simpa [h] using A.nonSingular_exp.isUnit

open Lean Meta Mathlib.Meta.Positivity in
/-- Positivity extension for `HermitianMat.exp`: always strictly positive if `Nonempty d`.
TODO: We could add a fallback to give `nonnegative` if `Nonempty d` is not available,
possibly also print a warning. (Users might often not have `Nonempty d` in context, and
they probably want to.) -/
@[positivity HermitianMat.exp _]
meta def evalHermitianMatExp : PositivityExt where eval {_u _α} _zα _pα e := do
  let .app _exp (A : Expr) ← whnfR e | throwError "not HermitianMat.exp"
  pure (.positive (← mkAppM ``HermitianMat.exp_pos #[A]))

end exp

/-- Matrix logarithm (base e) of a Hermitian matrix, as given by the elementwise
  real logarithm of the diagonal in a diagonalized form, using `Real.log`

  Note that this means that the nullspace of the image includes all of the nullspace of the
  original matrix. This contrasts to the standard definition, which is typically defined for
  positive *definite* matrices, and the nullspace of the image is exactly the
  (λ=1)-eigenspace of the original matrix. (We also get the (λ=-1)-eigenspace here!)

  It coincides with a standard definition if A is positive definite. -/
def log (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.log

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem _root_.Commute.log_left (hAB : Commute A.mat B.mat) :
    Commute (A.log).mat B.mat := by
  rw [log]; commutes

@[aesop unsafe apply 50% (rule_sets := [Commutes])]
theorem _root_.Commute.log_right (hAB : Commute A.mat B.mat) :
    Commute A.mat (B.log).mat := by
  rw [log]; commutes

@[simp]
theorem reindex_log (e : d ≃ d₂) : (A.reindex e).log = A.log.reindex e :=
  cfc_reindex A Real.log e

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem log_zero : (0 : HermitianMat d 𝕜).log = 0 := by
  simp [log]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem log_one : (1 : HermitianMat d 𝕜).log = 0 := by
  simp [log]

theorem log_smul_of_pos (A : HermitianMat d 𝕜) (hx : x ≠ 0) :
    (x • A).log = Real.log x • A.supportProj + A.log := by
  ext1
  convert A.H.log_smul_of_ne_zero hx
  simp [cfc, log, supportProj_eq_cfc]

theorem log_smul {A : HermitianMat d 𝕜} {x : ℝ} (hx : x ≠ 0) [NonSingular A] :
    (x • A).log = Real.log x • 1 + A.log := by
  simp [log_smul_of_pos A hx]

/-
The inverse function is operator antitone for positive definite matrices.
-/
set_option backward.isDefEq.respectTransparency false in
open ComplexOrder MatrixOrder in
theorem inv_antitone (hA : A.mat.PosDef) (h : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  -- Since $B - A$ is positive semidefinite, we can write it as $C^*C$ for some matrix $C$.
  obtain ⟨C, hC⟩ : ∃ C : Matrix d d 𝕜, B.mat - A.mat = C.conjTranspose * C := by
    classical
    apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
    simpa using h
  -- Using the fact that $B = A + C^*C$, we can write $B^{-1}$ as $(A + C^*C)^{-1}$.
  have h_inv_posDef : (1 + C * A.mat⁻¹ * C.conjTranspose).PosDef := by
    exact Matrix.PosDef.one.add_posSemidef (hA.inv.posSemidef.mul_mul_conjTranspose_same C)
  have hB_inv : B.mat⁻¹ = A.mat⁻¹ - A.mat⁻¹ * C.conjTranspose * (1 + C * A.mat⁻¹ * C.conjTranspose)⁻¹ * C * A.mat⁻¹ := by
    have hB_inv : (A.mat + C.conjTranspose * C)⁻¹ = A.mat⁻¹ - A.mat⁻¹ * C.conjTranspose * (1 + C * A.mat⁻¹ * C.conjTranspose)⁻¹ * C * A.mat⁻¹ := by
      have hB_inv : (A.mat + C.conjTranspose * C) * (A.mat⁻¹ - A.mat⁻¹ * C.conjTranspose * (1 + C * A.mat⁻¹ * C.conjTranspose)⁻¹ * C * A.mat⁻¹) = 1 := by
        have h_inv : (1 + C * A.mat⁻¹ * C.conjTranspose) * (1 + C * A.mat⁻¹ * C.conjTranspose)⁻¹ = 1 := by
          exact Matrix.mul_nonsing_inv _ ( show IsUnit _ from by simpa [ Matrix.isUnit_iff_isUnit_det ] using h_inv_posDef.det_pos.ne' );
        simp only [mul_assoc, Matrix.mul_sub] at *
        simp only [← Matrix.mul_assoc, add_mul, one_mul] at *
        simp only [isUnit_iff_ne_zero, ne_eq, hA.det_pos.ne', not_false_eq_true,
          Matrix.mul_nonsing_inv, one_mul, ← add_mul] at *
        simp only [mul_assoc, add_mul] at *
        simp_all only [← Matrix.mul_assoc, ← eq_sub_iff_add_eq']
        grind only [cases eager Subtype]
      rw [ Matrix.inv_eq_right_inv hB_inv ];
    rw [ ← hB_inv, ← hC, add_sub_cancel ];
  -- Since $(1 + C * A⁻¹ * C.conjTranspose)$ is positive definite, its inverse is also positive definite.
  have h_inv_pos : (A.mat⁻¹ * C.conjTranspose * (1 + C * A.mat⁻¹ * C.conjTranspose)⁻¹ * C * A.mat⁻¹).PosSemidef := by
    have h_inv_pos : (C * A.mat⁻¹).conjTranspose * (1 + C * A.mat⁻¹ * C.conjTranspose)⁻¹ * (C * A.mat⁻¹) = A.mat⁻¹ * C.conjTranspose * (1 + C * A.mat⁻¹ * C.conjTranspose)⁻¹ * C * A.mat⁻¹ := by
      simp [ Matrix.mul_assoc, Matrix.conjTranspose_mul ];
      rw [ Matrix.conjTranspose_nonsing_inv, A.H ];
    rw [ ← h_inv_pos ];
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same h_inv_posDef.inv.posSemidef _
  have h_inv_pos : (A.mat⁻¹ - B.mat⁻¹).PosSemidef := by
    simp_all [ Matrix.PosSemidef ];
  exact h_inv_pos

/-
The integral of $1/(1+t) - 1/(x+t)$ from 0 to T is $\log x + \log((1+T)/(x+T))$.
-/
lemma Real.integral_inv_sub_inv_finite (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    ∫ t in (0)..T, (1 / (1 + t) - 1 / (x + t)) = Real.log x + Real.log ((1 + T) / (x + T)) := by
  rw [ intervalIntegral.integral_sub, intervalIntegral.integral_comp_add_left, intervalIntegral.integral_comp_add_left ];
  · rw [ ← Real.log_mul, intervalIntegral.integral_deriv_eq_sub' ];
    field_simp;
    rw [ intervalIntegral.integral_deriv_eq_sub' ];
    any_goals intro t ht; exact Real.differentiableAt_log ( by cases Set.mem_uIcc.mp ht <;> linarith );
    any_goals positivity;
    · rw [ Real.log_div ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ) ] ; norm_num;
      ring;
    · exact funext fun x => by simp [ div_eq_inv_mul ] ;
    · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const continuousAt_id ( by cases Set.mem_uIcc.mp ht <;> linarith );
    · exact funext fun x => by simp [ div_eq_inv_mul ] ;
    · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const continuousAt_id <| by cases Set.mem_uIcc.mp ht <;> linarith;
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const ( continuousAt_const.add continuousAt_id ) ( by linarith [ Set.mem_Icc.mp ( by simpa [ hT.le ] using ht ) ] ) );
  · exact ContinuousOn.intervalIntegrable ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div continuousAt_const ( continuousAt_const.add continuousAt_id ) ( by linarith [ Set.mem_Icc.mp ( by simpa [ hT.le ] using ht ) ] ) )

set_option backward.isDefEq.respectTransparency false in
/--
The limit of $\log((1+T)/(x+T))$ as $T \to \infty$ is 0, for $x > 0$.
-/
lemma Real.tendsto_log_div_add_atTop (x : ℝ) :
    Filter.Tendsto (fun T => Real.log ((1 + T) / (x + T))) .atTop (nhds 0) := by
  -- We can divide the numerator and the denominator by $b$ and then take the limit as $b$ approaches infinity.
  suffices h_div : Filter.Tendsto (fun b => Real.log ((1 / b + 1) / (x / b + 1))) Filter.atTop (nhds 0) by
    refine h_div.congr' ( by filter_upwards [ Filter.eventually_gt_atTop 0 ] with b hb using by rw [ show ( 1 + b ) / ( x + b ) = ( 1 / b + 1 ) / ( x / b + 1 ) by rw [ div_add_one, div_add_one, div_div_div_cancel_right₀ ] <;> positivity ] );
  exact le_trans ( Filter.Tendsto.log ( Filter.Tendsto.div ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) tendsto_const_nhds ) ( Filter.Tendsto.add ( tendsto_const_nhds.div_atTop Filter.tendsto_id ) tendsto_const_nhds ) ( by positivity ) ) ( by positivity ) ) ( by norm_num )

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
open ComplexOrder MeasureTheory intervalIntegral in
/--
Monotonicity of the finite integral approximation of the logarithm.
-/
theorem logApprox_mono {x y : HermitianMat d 𝕜} (hx : x.mat.PosDef) (hy : y.mat.PosDef)
    (hxy : x ≤ y) (T : ℝ) (hT : 0 < T) :
    ∫ t in (0)..T, ((1 + t)⁻¹ • (1 : HermitianMat d 𝕜) - (x + t • 1)⁻¹) ≤
    ∫ t in (0)..T, ((1 + t)⁻¹ • (1 : HermitianMat d 𝕜) - (y + t • 1)⁻¹) := by
  -- By the properties of the integral, we can bring the limit inside, so we have:
  have h_integrable : ContinuousOn (fun t : ℝ => (1 + t)⁻¹ • (1 : HermitianMat d 𝕜)) (Set.Icc 0 T) ∧ ContinuousOn (fun t : ℝ => (x + t • 1)⁻¹) (Set.Icc 0 T) ∧ ContinuousOn (fun t : ℝ => (y + t • 1)⁻¹) (Set.Icc 0 T) := by
    refine' ⟨ ContinuousOn.smul ( ContinuousOn.inv₀ ( continuousOn_const.add continuousOn_id ) fun t ht => by linarith [ ht.1 ] ) continuousOn_const, _, _ ⟩;
    · refine' ContinuousOn.comp ( show ContinuousOn ( fun m : HermitianMat d 𝕜 => m⁻¹ ) ( { m : HermitianMat d 𝕜 | m.mat.PosDef } ) from _ ) _ _;
      · intro m hm;
        refine' ContinuousAt.continuousWithinAt _;
        have h_inv_cont : ContinuousAt (fun m : Matrix d d 𝕜 => m⁻¹) m.mat := by
          have h_inv_cont : ContinuousAt (fun m : Matrix d d 𝕜 => m⁻¹) m.mat := by
            have h_det_cont : ContinuousAt (fun m : Matrix d d 𝕜 => m.det) m.mat := by
              exact Continuous.continuousAt ( continuous_id.matrix_det )
            have h_adj_cont : ContinuousAt (fun m : Matrix d d 𝕜 => m.adjugate) m.mat := by
              exact Continuous.continuousAt ( continuous_id.matrix_adjugate )
            simp_all [ Matrix.inv_def ];
            exact ContinuousAt.smul ( h_det_cont.inv₀ ( by simpa using hm.det_pos.ne' ) ) h_adj_cont;
          exact h_inv_cont;
        rw [ ContinuousAt ] at *;
        rw [ tendsto_subtype_rng ] at *;
        exact h_inv_cont.comp ( continuous_subtype_val.tendsto _ );
      · fun_prop;
      · intro t ht;
        simp only [Set.mem_setOf_eq, mat_add, mat_smul, mat_one]
        rw [Matrix.posDef_iff_dotProduct_mulVec] at hx ⊢
        refine' ⟨ _, _ ⟩;
        · exact H ((fun t => x + t • 1) t);
        · intro v hv_ne_zero
          have h_pos : 0 < star v ⬝ᵥ x.mat.mulVec v + t * star v ⬝ᵥ (1 : Matrix d d 𝕜).mulVec v := by
            have := hx.2 hv_ne_zero;
            refine' add_pos_of_pos_of_nonneg this _;
            exact mul_nonneg ( mod_cast ht.1 ) ( Finset.sum_nonneg fun i _ => by simp [ mul_comm, RCLike.mul_conj ] );
          simp_all [ Matrix.add_mulVec ];
          simp_all [ Matrix.mulVec, dotProduct ];
          simp_all [ Matrix.one_apply, Finset.mul_sum, mul_left_comm,];
          convert h_pos using 3 ; simp [ mul_left_comm, Algebra.smul_def ];
    · have h_cont : ContinuousOn (fun t : ℝ => (y + t • 1 : Matrix d d 𝕜)⁻¹) (Set.Icc 0 T) := by
        have h_inv : ∀ t ∈ Set.Icc 0 T, (y + t • 1 : Matrix d d 𝕜).det ≠ 0 := by
          intro t ht;
          have h_det_pos : ∀ t ∈ Set.Icc (0 : ℝ) T, Matrix.PosDef (y.mat + t • 1) := by
            intro t ht;
            rw [Matrix.posDef_iff_dotProduct_mulVec] at hy ⊢
            refine' ⟨ _, _ ⟩;
            · simp [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul ];
            · intro x hx_ne_zero
              have h_pos : 0 < star x ⬝ᵥ y.mat.mulVec x + t * star x ⬝ᵥ x := by
                have := hy.2 hx_ne_zero;
                exact add_pos_of_pos_of_nonneg this ( mul_nonneg ( mod_cast ht.1 ) ( by simp [ dotProduct_comm ] ) );
              simp_all [ Matrix.add_mulVec ]
              simp_all [ Matrix.mulVec, dotProduct ]
              simp_all [ Matrix.one_apply, Finset.mul_sum, mul_left_comm ]
              convert h_pos using 1;
              simp [ mul_assoc, mul_comm, mul_left_comm, Algebra.smul_def ];
          exact ne_of_gt ( h_det_pos t ht |> fun h => h.det_pos )
        have h_cont_inv : ContinuousOn (fun t : ℝ => (y + t • 1 : Matrix d d 𝕜)⁻¹) (Set.Icc 0 T) := by
          have h_cont_det : ContinuousOn (fun t : ℝ => (y + t • 1 : Matrix d d 𝕜).det) (Set.Icc 0 T) := by
            fun_prop
          have h_cont_adj : ContinuousOn (fun t : ℝ => (y + t • 1 : Matrix d d 𝕜).adjugate) (Set.Icc 0 T) := by
            fun_prop;
          simp_all [ Matrix.inv_def ];
          exact ContinuousOn.smul ( h_cont_det.inv₀ fun t ht => h_inv t ht.1 ht.2 ) h_cont_adj;
        convert h_cont_inv using 1;
      rw [ continuousOn_iff_continuous_restrict ] at *;
      exact continuous_induced_rng.mpr h_cont
  rw [ intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le ];
  apply_rules [ MeasureTheory.integral_mono_ae ];
  · exact ContinuousOn.integrableOn_Icc (ContinuousOn.sub h_integrable.1 h_integrable.2.1) |> fun h => h.mono_set (Set.Ioc_subset_Icc_self);
  · exact ContinuousOn.integrableOn_Icc (ContinuousOn.sub h_integrable.1 h_integrable.2.2) |> fun h => h.mono_set (Set.Ioc_subset_Icc_self);
  have h_integral_limit : ∀ t ∈ Set.Icc (0 : ℝ) T, (y + t • 1)⁻¹ ≤ (x + t • 1)⁻¹ := by
    intro t ht;
    apply inv_antitone;
    · rw [Matrix.posDef_iff_dotProduct_mulVec] at hx ⊢
      constructor;
      · simp [ Matrix.IsHermitian];
      · intro v hv_ne_zero
        have h_pos : 0 < star v ⬝ᵥ x.mat.mulVec v + t * star v ⬝ᵥ v := by
          have := hx.2 hv_ne_zero
          exact add_pos_of_pos_of_nonneg this ( mul_nonneg ( mod_cast ht.1 ) ( dotProduct_star_self_nonneg v ) );
        simp_all [ Matrix.add_mulVec ];
        convert h_pos using 2 ; simp [ Matrix.mulVec, dotProduct ];
        simp [ Matrix.one_apply, Finset.mul_sum, mul_left_comm ];
        simp [ mul_left_comm, Algebra.smul_def ];
    · exact add_le_add_left hxy _;
  have h_integral_limit : ∀ t ∈ Set.Ioc 0 T, (1 + t)⁻¹ • 1 - (x + t • 1)⁻¹ ≤ (1 + t)⁻¹ • 1 - (y + t • 1)⁻¹ := by
    exact fun t ht => sub_le_sub_left ( h_integral_limit t <| Set.Ioc_subset_Icc_self ht ) _;
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  exact h_integral_limit t ht

/-
Definition of the finite integral approximation of the logarithm.
-/
noncomputable def logApprox {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    (x : HermitianMat n 𝕜) (T : ℝ) : HermitianMat n 𝕜 :=
  ∫ t in (0)..T, ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (x + t • 1)⁻¹)

/-
Definition of the scalar log approximation and its value.
-/
noncomputable def scalarLogApprox (T : ℝ) (u : ℝ) : ℝ :=
  ∫ t in (0)..T, ((1 + t)⁻¹ - (u + t)⁻¹)

theorem scalarLogApprox_eq (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    scalarLogApprox T x = Real.log x + Real.log ((1 + T) / (x + T)) := by
  convert Real.integral_inv_sub_inv_finite x T hx hT using 1;
  unfold scalarLogApprox; norm_num

open ComplexOrder in
/--
The integrand in the log approximation is the CFC of the scalar integrand.
-/
private lemma integrand_eq
    (x : HermitianMat d 𝕜) (hx : x.mat.PosDef) (t : ℝ) (ht : 0 ≤ t) :
    ((1 + t)⁻¹ • (1 : HermitianMat d 𝕜) - (x + t • 1)⁻¹) = x.cfc (fun u => (1 + t)⁻¹ - (u + t)⁻¹) := by
  have h_cfc_add : x.cfc (fun u => u + t) = x.cfc (fun u => u) + x.cfc (fun u => t) :=
    x.cfc_add id _
  have h_cfc_sub : (x + t • 1)⁻¹ = x.cfc (fun u => (u + t)⁻¹) := by
    convert inv_cfc_eq_cfc_inv (fun u => u + t) ?_ using 1;
    · simp [h_cfc_add]
    · exact fun i => ne_of_gt ( add_pos_of_pos_of_nonneg ( hx.eigenvalues_pos i ) ht );
  rw [← cfc_const x (1 + t)⁻¹, h_cfc_sub, ← cfc_sub ];
  rfl

open ComplexOrder MeasureTheory intervalIntegral in
/--
The matrix log approximation is the CFC of the scalar log approximation.
-/
theorem logApprox_eq_cfc_scalar
    (x : HermitianMat d 𝕜) (hx : x.mat.PosDef) (T : ℝ) (hT : 0 < T) :
    logApprox x T = x.cfc (scalarLogApprox T) := by
  unfold scalarLogApprox logApprox;
  rw [ intervalIntegral.integral_congr fun t ht => ?_ ];
  convert integral_cfc_eq_cfc_integral 0 T ( fun t u => ( 1 + t ) ⁻¹ - ( u + t ) ⁻¹ ) ?_ using 1;
  · intro i;
    apply_rules [ ContinuousOn.intervalIntegrable ];
    field_simp;
    apply_rules [ ContinuousOn.sub, ContinuousOn.div, continuousOn_const, continuousOn_id ];
    · fun_prop;
    · exact fun x hx => by cases Set.mem_uIcc.mp hx <;> linarith;
    · fun_prop;
    · have := hx.eigenvalues_pos i;
      exact fun t ht => ne_of_gt ( add_pos_of_pos_of_nonneg this ( by cases Set.mem_uIcc.mp ht <;> linarith ) );
  · apply integrand_eq x hx t
    cases Set.mem_uIcc.mp ht <;> linarith

open ComplexOrder in
/--
The log approximation is the log plus an error term.
-/
theorem logApprox_eq_log_add_error
    (x : HermitianMat d 𝕜) (hx : x.mat.PosDef) (T : ℝ) (hT : 0 < T) :
    logApprox x T = x.log + x.cfc (fun u => Real.log ((1 + T) / (u + T))) := by
  have h_logApprox : ∫ t in (0)..T, ((1 + t)⁻¹ • (1 : HermitianMat d 𝕜) - (x + t • 1)⁻¹) = x.cfc (fun u => Real.log u + Real.log ((1 + T) / (u + T))) := by
    convert logApprox_eq_cfc_scalar x hx T hT using 1;
    apply cfc_congr_of_posDef hx;
    exact fun u hu => Eq.symm ( scalarLogApprox_eq u T hu.out hT );
  have h_cfc_add : x.cfc (fun u => Real.log u + Real.log ((1 + T) / (u + T))) = x.cfc Real.log + x.cfc (fun u => Real.log ((1 + T) / (u + T))) := by
    apply cfc_add;
  exact h_logApprox.trans h_cfc_add

open ComplexOrder Filter Topology in
open scoped Matrix.Norms.Frobenius in
set_option backward.isDefEq.respectTransparency false in
/--
The error term in the log approximation tends to 0 as T goes to infinity.
-/
lemma tendsto_cfc_log_div_add_atTop (x : HermitianMat d 𝕜) :
    Tendsto (fun T => x.cfc (fun u => Real.log ((1 + T) / (u + T)))) atTop (nhds 0) := by
  -- Expand `(cfc x ...).mat` using `cfc_toMat_eq_sum_smul_proj`.
  have h_expand : ∀ T : ℝ, (x.cfc (fun u => Real.log ((1 + T) / (u + T)))).mat = ∑ i, Real.log ((1 + T) / (x.H.eigenvalues i + T)) • (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose) := by
    exact fun T => cfc_toMat_eq_sum_smul_proj x fun u => Real.log ((1 + T) / (u + T));
  -- The limit of a sum is the sum of the limits.
  have h_sum : Filter.Tendsto (fun T : ℝ => ∑ i, Real.log ((1 + T) / (x.H.eigenvalues i + T)) • (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose)) Filter.atTop (nhds (∑ i, 0 • (x.H.eigenvectorUnitary.val * (Matrix.single i i 1) * x.H.eigenvectorUnitary.val.conjTranspose))) := by
    refine' tendsto_finset_sum _ fun i _ => _;
    convert Filter.Tendsto.smul_const ( Real.tendsto_log_div_add_atTop ( x.H.eigenvalues i ) ) _ using 1;
    all_goals try infer_instance;
    norm_num +zetaDelta at *
  rw [ tendsto_iff_norm_sub_tendsto_zero ] at *;
  convert h_sum using 2 ; simp [ ← h_expand]
  rfl

open ComplexOrder Filter in
/--
The log approximation converges to the matrix logarithm.
-/
lemma tendsto_logApprox {x : HermitianMat d 𝕜} (hx : x.mat.PosDef) :
  Tendsto (fun T => logApprox x T) atTop (nhds x.log) := by
    have h_log_approx_eq : ∀ᶠ T in Filter.atTop, x.logApprox T = x.log + x.cfc (fun u => Real.log ((1 + T) / (u + T))) := by
      filter_upwards [ Filter.eventually_gt_atTop 0 ] with T hT using logApprox_eq_log_add_error x hx T hT;
    rw [ Filter.tendsto_congr' h_log_approx_eq ];
    simpa using tendsto_const_nhds.add ( tendsto_cfc_log_div_add_atTop x )

--PULLOUT
open ComplexOrder in
omit [DecidableEq d] [Fintype d] in
theorem posDef_of_posDef_le (hA : A.mat.PosDef) (hAB : A ≤ B) : B.mat.PosDef := by
  rw [le_iff] at hAB
  convert hA.add_posSemidef hAB
  simp

open ComplexOrder in
/--
The matrix logarithm is operator monotone.
-/
theorem log_mono (hA : A.mat.PosDef) (hAB : A ≤ B) : A.log ≤ B.log := by
  have hB : B.mat.PosDef := posDef_of_posDef_le hA hAB
  apply le_of_tendsto_of_tendsto (tendsto_logApprox hA) (tendsto_logApprox hB)
  rw [Filter.EventuallyLE, Filter.eventually_atTop]
  exact ⟨1, fun T hT => by simpa using logApprox_mono hA hB hAB T ( zero_lt_one.trans_le hT )⟩

/-- Monotonicity of exp on commuting operators. -/
theorem le_of_exp_commute (hAB₂ : A.exp ≤ B.exp) :
    A ≤ B := by
  have hA : A = (A.exp).log := by simp [exp, log, ← HermitianMat.cfc_comp]
  have hB : B = (B.exp).log := by simp [exp, log, ← HermitianMat.cfc_comp]
  rw [hA, hB]
  apply HermitianMat.log_mono
  · rw [exp, HermitianMat.cfc_posDef]
    intro
    positivity
  · exact hAB₂

set_option maxHeartbeats 10000000 in
open ComplexOrder Matrix in
/--
The inverse function is operator convex on positive definite matrices.
-/
lemma inv_convex {x y : HermitianMat d 𝕜} (hx : x.mat.PosDef) (hy : y.mat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • x + b • y)⁻¹ ≤ a • x⁻¹ + b • y⁻¹ := by
  -- Using the fact that the set of positive semidefinite matrices is a convex cone, we can show that the matrix
  -- $\begin{pmatrix} a \bullet x + b \bullet y & I \\ I & a \bullet x^{-1} + b \bullet y^{-1} \end{pmatrix}$
  -- is positive semidefinite.
  have h_pos_semidef :
    (Matrix.fromBlocks (a • x.mat + b • y.mat) (1 : Matrix d d 𝕜) (1 : Matrix d d 𝕜) (a • (x.mat)⁻¹ + b • (y.mat)⁻¹)).PosSemidef := by
      -- Since $a + b = 1$, we can use the fact that the block matrix $\begin{pmatrix} A & I \\ I & A^{-1} \end{pmatrix}$ is positive semidefinite for any positive definite $A$.
      have h_block_pos : ∀ A : Matrix d d 𝕜, A.PosDef → (Matrix.fromBlocks A 1 1 A⁻¹).PosSemidef := by
        intro A hA
        have h_block_pos : (Matrix.fromBlocks A (1 : Matrix d d 𝕜) (1 : Matrix d d 𝕜) (A⁻¹)).PosSemidef := by
          have h_inv_pos : A⁻¹.PosSemidef := by
            exact hA.inv.posSemidef
          have h_block_pos : (Matrix.fromBlocks A (1 : Matrix d d 𝕜) (1 : Matrix d d 𝕜) (A⁻¹)) = (Matrix.fromBlocks 1 0 A⁻¹ 1) * (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * A * A⁻¹)) * (Matrix.fromBlocks 1 A⁻¹ 0 1) := by
            simp [ Matrix.fromBlocks_multiply ];
            have := hA.det_pos;
            exact ⟨ by rw [ Matrix.mul_nonsing_inv _ ( show IsUnit A.det from isUnit_iff_ne_zero.mpr this.ne' ) ], by rw [ Matrix.nonsing_inv_mul _ ( show IsUnit A.det from isUnit_iff_ne_zero.mpr this.ne' ) ] ⟩;
          have h_block_pos : (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * A * A⁻¹)).PosSemidef := by
            have h_block_pos : (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * A * A⁻¹)) = (Matrix.fromBlocks A 0 0 0) := by
              have h_inv : A⁻¹ * A = 1 := by
                rw [ Matrix.nonsing_inv_mul _ ];
                exact isUnit_iff_ne_zero.mpr hA.det_pos.ne';
              simp [ h_inv ];
            rw [h_block_pos];
            rw [Matrix.posDef_iff_dotProduct_mulVec] at hA
            rw [Matrix.posSemidef_iff_dotProduct_mulVec]
            constructor;
            · ext i j ; simp [ Matrix.fromBlocks ];
              cases i <;> cases j <;> simp
              exact hA.1.apply _ _;
            · intro x
              simp [Matrix.mulVec, dotProduct];
              have := @hA.2 ( fun i => x ( Sum.inl i ) );
              by_cases h : ( fun i => x ( Sum.inl i ) ) = 0
              · simp_all [ dotProduct, Matrix.mulVec ];
                simp_all [ funext_iff ];
              · exact le_of_lt (this h)
          rw [ Matrix.posSemidef_iff_dotProduct_mulVec ] at *;
          simp_all [ Matrix.IsHermitian, Matrix.mul_assoc ];
          refine' ⟨ _, _ ⟩;
          · simp [Matrix.fromBlocks_conjTranspose, h_inv_pos.1 ];
          · intro x
            set y : d ⊕ d → 𝕜 := (Matrix.fromBlocks 1 A⁻¹ 0 1).mulVec x
            have h_y : star x ⬝ᵥ (Matrix.fromBlocks 1 0 A⁻¹ 1 * (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * (A * A⁻¹)) * Matrix.fromBlocks 1 A⁻¹ 0 1)).mulVec x = star y ⬝ᵥ (Matrix.fromBlocks A 0 0 (A⁻¹ - A⁻¹ * (A * A⁻¹))).mulVec y := by
              simp +zetaDelta at *;
              simp [Matrix.dotProduct_mulVec ];
              simp [ Matrix.star_mulVec ];
              congr! 2;
              ext i j ; simp [ Matrix.mul_apply, Matrix.fromBlocks ];
              cases i <;> cases j <;> simp [ Matrix.one_apply];
              · rw [ ← Matrix.ext_iff ] at * ; aesop;
              · rw [ ← Matrix.ext_iff ] at * ; aesop;
            exact h_y.symm ▸ h_block_pos.2 y;
        exact h_block_pos;
      -- Since $a + b = 1$, we can use the fact that the block matrix $\begin{pmatrix} a \bullet x + b \bullet y & I \\ I & a \bullet x^{-1} + b \bullet y^{-1} \end{pmatrix}$ is positive semidefinite.
      have h_convex : Matrix.PosSemidef ((a • Matrix.fromBlocks (x.mat) (1 : Matrix d d 𝕜) (1 : Matrix d d 𝕜) (x.mat)⁻¹) + (b • Matrix.fromBlocks (y.mat) (1 : Matrix d d 𝕜) (1 : Matrix d d 𝕜) (y.mat)⁻¹)) := by
        apply_rules [ Matrix.PosSemidef.add, Matrix.PosSemidef.smul ];
      convert h_convex using 1;
      ext i j ; simp [ Matrix.fromBlocks ];
      rcases i with ( i | i ) <;> rcases j with ( j | j ) <;> simp [ Matrix.one_apply ];
      · split_ifs <;> simp_all [ ← add_smul ];
      · split_ifs <;> simp_all [ ← add_smul ];
  have h_schur : (a • x.mat + b • y.mat).PosDef := by
    by_cases ha' : a = 0 <;> by_cases hb' : b = 0 <;> simp_all [ Matrix.posSemidef_iff_dotProduct_mulVec ];
    rw [Matrix.posDef_iff_dotProduct_mulVec] at hx hy ⊢
    constructor;
    · simp_all [ Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_smul ];
    · intro v hv_ne_zero
      have h_pos : 0 < a * (star v ⬝ᵥ x.mat.mulVec v) + b * (star v ⬝ᵥ y.mat.mulVec v) := by
        have := hx.2 hv_ne_zero; have := hy.2 hv_ne_zero
        clear hx hy
        simp_all [ Matrix.mulVec, dotProduct ] ;
        exact add_pos_of_nonneg_of_pos ( mul_nonneg ( mod_cast ha ) ( le_of_lt ‹_› ) ) ( mul_pos ( mod_cast lt_of_le_of_ne hb ( Ne.symm hb' ) ) ( mod_cast this ) );
      convert h_pos using 1 ; simp [ Matrix.add_mulVec]
      ring_nf
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm];
      simp [mul_left_comm, Algebra.smul_def ];
  change (a • (x.mat)⁻¹ + b • (y.mat)⁻¹ - (a • x.mat + b • y.mat)⁻¹).PosSemidef
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h_pos_semidef ⊢
  refine' ⟨ _, fun v => _ ⟩;
  · simp_all [ Matrix.IsHermitian, Matrix.conjTranspose_nonsing_inv ];
  · have := h_pos_semidef.2;
    specialize this (Sum.elim (- (a • x.mat + b • y.mat)⁻¹.mulVec v) v);
    simp_all [ Matrix.fromBlocks_mulVec ];
    simp_all [ Matrix.mul_nonsing_inv _ ( show IsUnit (a • x.mat + b • y.mat).det from isUnit_iff_ne_zero.mpr <| h_schur.det_pos.ne' ), Matrix.mulVec_neg];
    simp_all [ dotProduct, Matrix.sub_mulVec ];
    refine this.trans_eq (Finset.sum_congr rfl fun _ _ => by ring );

open ComplexOrder in
set_option backward.isDefEq.respectTransparency false in
/--
The shifted inverse function is operator convex on positive definite matrices.
-/
lemma inv_shift_convex {x y : HermitianMat d 𝕜} (hx : x.mat.PosDef) (hy : y.mat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (t : ℝ) (ht : 0 ≤ t) :
    (a • x + b • y + t • 1)⁻¹ ≤ a • (x + t • 1)⁻¹ + b • (y + t • 1)⁻¹ := by
  have hx' : (x + t • 1).mat.PosDef := hx.add_posSemidef (.smul .one ht)
  have hy' : (y + t • 1).mat.PosDef := hy.add_posSemidef (.smul .one ht)
  convert inv_convex hx' hy' ha hb hab using 1
  ext
  simp [add_assoc, add_left_comm, hab, ← add_smul]

open MeasureTheory intervalIntegral ComplexOrder Matrix in
open scoped Matrix.Norms.Frobenius in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of the approximation of the matrix logarithm.
-/
lemma integrable_inv_shift {A : HermitianMat d 𝕜} (hA : A.mat.PosDef) (b : ℝ) (hb : 0 ≤ b) :
    IntervalIntegrable (fun t => (A + t • 1)⁻¹) volume 0 b := by
  -- Since A is positive definite, for any t ≥ 0, A + t • 1 is also positive definite, hence invertible.
  have h_inv : ∀ t : ℝ, 0 ≤ t → IsUnit (A + t • 1).mat := by
    intro t ht
    have h_pos_def : (A + t • 1).mat.PosDef := by
      convert hA.add_posSemidef _ using 1
      constructor <;> simp [*]
      · simp [ Matrix.IsHermitian];
      · simp [ Matrix.one_apply, Finsupp.sum ];
        intro x
        refine Finset.sum_nonneg fun i _ => ?_
        split_ifs <;> simp [ *, mul_comm, RCLike.mul_conj ]
        positivity
    exact Matrix.PosDef.isUnit h_pos_def
  have h_inv_cont : ContinuousOn (fun t : ℝ => (A + t • 1).mat⁻¹) (Set.Icc 0 b) := by
    intro t ht
    have h_inv : IsUnit (A + t • 1).mat := h_inv t ht.1
    have h_inv_cont : ContinuousAt (fun t : ℝ => (A + t • 1).mat⁻¹) t := by
      have h_det_cont : ContinuousAt (fun t : ℝ => (A + t • 1).mat.det) t := by
        fun_prop (disch := solve_by_elim)
      have h_adj_cont : ContinuousAt (fun t : ℝ => (A + t • 1).mat.adjugate) t := by
        exact Continuous.continuousAt ( by exact Continuous.matrix_adjugate <| by continuity )
      simp_all [ Matrix.inv_def ];
      exact ContinuousAt.smul ( h_det_cont.inv₀ <| by simpa [ Matrix.isUnit_iff_isUnit_det ] using h_inv t ht.1 ) h_adj_cont
    exact h_inv_cont.continuousWithinAt
  have h_inv_cont : ContinuousOn (fun t : ℝ => (A + t • 1)⁻¹) (Set.Icc 0 b) := by
    exact (continuousOn_iff_coe fun t => (A + t • 1)⁻¹).mpr h_inv_cont
  exact h_inv_cont.intervalIntegrable_of_Icc hb

open ComplexOrder in
set_option backward.isDefEq.respectTransparency false in
/--
The finite integral approximation of the matrix logarithm is operator concave.
-/
theorem logApprox_concave {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {x y : HermitianMat n 𝕜} (hx : x.mat.PosDef) (hy : y.mat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (T : ℝ) (hT : 0 ≤ T) :
    a • x.logApprox T + b • y.logApprox T ≤ (a • x + b • y).logApprox T := by
  have h_integrable {z : HermitianMat n 𝕜} : z.mat.PosDef → IntervalIntegrable (fun t => (1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (z + t • 1)⁻¹) MeasureTheory.volume 0 T := by
    intro hz
    have h_integrable := integrable_inv_shift hz T hT
    rw [ intervalIntegrable_iff_integrableOn_Ioc_of_le hT ] at *
    refine MeasureTheory.Integrable.sub ?_ h_integrable
    exact ContinuousOn.integrableOn_Icc ( by exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.smul ( ContinuousAt.inv₀ ( continuousAt_const.add continuousAt_id ) ( by linarith [ ht.1 ] ) ) continuousAt_const ) |> fun h => h.mono_set ( Set.Ioc_subset_Icc_self );
  have h_int2 : IntervalIntegrable (fun t => (1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - ((a • x + b • y) + t • 1)⁻¹) MeasureTheory.volume 0 T := by
    exact h_integrable (Matrix.PosDef.Convex hx hy ha hb hab)
  have h_integral_mono : ∫ t in (0)..T, a • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (x + t • 1)⁻¹) + b • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (y + t • 1)⁻¹) ≤ ∫ t in (0)..T, (1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - ((a • x + b • y) + t • 1)⁻¹ := by
    have h_integral_mono : ∀ t ∈ Set.Icc 0 T, a • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (x + t • 1)⁻¹) + b • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (y + t • 1)⁻¹) ≤ (1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - ((a • x + b • y) + t • 1)⁻¹ := by
      intros t ht
      have h_inv_shift_convex : ((a • x + b • y) + t • 1)⁻¹ ≤ a • (x + t • 1)⁻¹ + b • (y + t • 1)⁻¹ := by
        convert inv_shift_convex hx hy ha hb hab t ht.1 using 1;
      simp_all [smul_sub, ← smul_assoc ];
      rw [ show ( 1 + t ) ⁻¹ • ( 1 : HermitianMat n 𝕜 ) = ( a * ( 1 + t ) ⁻¹ ) • ( 1 : HermitianMat n 𝕜 ) + ( b * ( 1 + t ) ⁻¹ ) • ( 1 : HermitianMat n 𝕜 ) by rw [ ← add_smul, ← add_mul, hab, one_mul ] ];
      convert sub_le_sub_left h_inv_shift_convex _ using 1 ; abel_nf;
    rw [ intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT ];
    apply MeasureTheory.integral_mono_ae
    · exact ( (h_integrable hx).1.smul a |> fun h => h.add ( (h_integrable hy).1.smul b ) ) |> fun h => h.mono_measure ( MeasureTheory.Measure.restrict_mono ( Set.Ioc_subset_Ioc le_rfl le_rfl ) le_rfl );
    · exact h_int2.1.mono_set (Set.Ioc_subset_Ioc le_rfl le_rfl)
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with t ht using h_integral_mono t <| Set.Ioc_subset_Icc_self ht;
  convert h_integral_mono using 1;
  rw [ intervalIntegral.integral_add ( by exact (h_integrable hx).smul a ) ( by exact (h_integrable hy).smul b ), intervalIntegral.integral_smul, intervalIntegral.integral_smul ]
  rw [logApprox, logApprox]

open ComplexOrder in
/--
The matrix logarithm is operator concave.
-/
theorem log_concave {x y : HermitianMat d 𝕜} (hx : x.mat.PosDef) (hy : y.mat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x.log + b • y.log ≤ (a • x + b • y).log := by
  apply le_of_tendsto_of_tendsto (b := .atTop) (f := fun T => a • x.logApprox T + b • y.logApprox T) (g := (a • x + b • y).logApprox)
  · exact ((tendsto_const_nhds.smul (tendsto_logApprox hx)).add (tendsto_const_nhds.smul (y.tendsto_logApprox hy)))
  · apply tendsto_logApprox
    exact Matrix.PosDef.Convex hx hy ha hb hab
  · rw [Filter.EventuallyLE, Filter.eventually_atTop]
    exact ⟨0, logApprox_concave hx hy ha hb hab⟩

/-
The logarithm of the Kronecker product of two diagonal Hermitian matrices is the sum of the Kronecker products of their logarithms with the identity matrix.
-/
lemma log_kron_diagonal {m n 𝕜 : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {d₁ : m → ℝ} {d₂ : n → ℝ} (h₁ : ∀ i, 0 < d₁ i) (h₂ : ∀ j, 0 < d₂ j) :
    (diagonal 𝕜 d₁ ⊗ₖ diagonal 𝕜 d₂).log =
    (diagonal 𝕜 d₁).log ⊗ₖ 1 + 1 ⊗ₖ (diagonal 𝕜 d₂).log := by
  have h_eq : (diagonal 𝕜 d₁ ⊗ₖ diagonal 𝕜 d₂) = (diagonal 𝕜 (fun (i : m × n) => d₁ i.1 * d₂ i.2)) := by
    exact kronecker_diagonal d₁ d₂
  convert congr_arg _ h_eq using 1;
  -- By definition of logarithm, we can rewrite the right-hand side.
  have h_rhs : (diagonal 𝕜 (fun (i : m × n) => d₁ i.1 * d₂ i.2)).log =
    (diagonal 𝕜 (fun (i : m × n) => Real.log (d₁ i.1) + Real.log (d₂ i.2))) := by
      rw [log, cfc_diagonal ];
      exact congr_arg _ ( funext fun i => Real.log_mul ( ne_of_gt ( h₁ i.1 ) ) ( ne_of_gt ( h₂ i.2 ) ) );
  rw [ h_rhs ];
  have h_rhs : (diagonal 𝕜 (fun (i : m × n) => Real.log (d₁ i.1) + Real.log (d₂ i.2))) =
    (diagonal 𝕜 (fun (i : m × n) => Real.log (d₁ i.1))) + (diagonal 𝕜 (fun (i : m × n) => Real.log (d₂ i.2))) := by
      ext1
      simp [ diagonal ]
  rw [ h_rhs ];
  congr! 1;
  · rw [ show ( diagonal 𝕜 d₁ |> log ) = diagonal 𝕜 ( Real.log ∘ d₁ ) from ?_ ];
    · rw [← diagonal_one, kronecker_diagonal]
      simp
    · exact cfc_diagonal Real.log d₁
  · have h_rhs : (diagonal 𝕜 d₂).log = (diagonal 𝕜 (fun (i : n) => Real.log (d₂ i))) := by
      exact cfc_diagonal Real.log d₂
    rw [ h_rhs ];
    convert kronecker_diagonal 1 ( fun i => Real.log ( d₂ i ) ) using 1;
    all_goals try infer_instance;
    · exact congr_arg₂ _ ( diagonal_one.symm ) rfl;
    · simp

/--
The logarithm of a Hermitian matrix conjugated by a unitary matrix is the conjugate of the logarithm.
-/
lemma log_conj_unitary (A : HermitianMat d 𝕜) (U : Matrix.unitaryGroup d 𝕜) :
    (A.conj U.val).log = A.log.conj U.val :=
  cfc_conj_unitary _ Real.log U

open RealInnerProductSpace in
set_option backward.isDefEq.respectTransparency false in
theorem inner_log_smul_of [NonSingular A] {x : ℝ} (hx : x ≠ 0) :
    ⟪(x • A).log, B⟫ = Real.log x * B.trace + ⟪A.log, B⟫ := by
  simp [log_smul hx, inner_add_left]

section kron

lemma log_kron_diagonal_with_proj {f : d → ℝ} {g : d₂ → ℝ}  :
    (diagonal 𝕜 f ⊗ₖ diagonal 𝕜 g).log =
    (diagonal 𝕜 f).log ⊗ₖ (diagonal 𝕜 g).supportProj +
    (diagonal 𝕜 f).supportProj ⊗ₖ (diagonal 𝕜 g).log := by
  have h_diag_kron : (diagonal 𝕜 f ⊗ₖ diagonal 𝕜 g).log = diagonal 𝕜 (fun i ↦ Real.log (f i.1 * g i.2)) := by
    rw [kronecker_diagonal, log]
    exact cfc_diagonal _ _
  simp_all [ HermitianMat.ext_iff, cfc_diagonal, log, supportProj_eq_cfc ];
  ext ⟨i, j⟩ ⟨i', j'⟩
  by_cases hi' : i = i'; swap
  · simp [hi']
  by_cases hj' : j = j'; swap
  · simp [hj']
  simp [hi', hj']
  split_ifs <;> simp_all [Real.log_mul]

variable {B : HermitianMat d₂ 𝕜}

/--
Generalization of `HermitianMat.log_kron` for possibly singular matrices.
-/
lemma log_kron_with_proj : (A ⊗ₖ B).log = A.log ⊗ₖ B.supportProj + A.supportProj ⊗ₖ B.log := by
  obtain ⟨UA, DA, rfl⟩ : ∃ UA : Matrix.unitaryGroup d 𝕜, ∃ DA, A = (diagonal 𝕜 DA).conj UA.val :=
    ⟨_, _, eq_conj_diagonal A⟩
  obtain ⟨UB, DB, rfl⟩ : ∃ UB : Matrix.unitaryGroup d₂ 𝕜, ∃ DB , B = (diagonal 𝕜 DB).conj UB.val :=
    ⟨_, _, eq_conj_diagonal B⟩
  rw [← kronecker_conj, log_conj_unitary _ ⟨_, Matrix.kronecker_mem_unitary UA.2 UB.2⟩]
  rw [log_kron_diagonal_with_proj, map_add (conj _)]
  congr 1
  <;> rw [supportProj_eq_cfc, supportProj_eq_cfc, cfc_conj_unitary, log_conj_unitary, kronecker_conj]

/--
The matrix logarithm of the Kronecker product of two nonsingular Hermitian matrices is
the sum of the Kronecker products of their logarithms with the identity matrix.
-/
theorem log_kron [NonSingular A] [NonSingular B] : (A ⊗ₖ B).log = A.log ⊗ₖ 1 + 1 ⊗ₖ B.log := by
  simp [log_kron_with_proj]

end kron
