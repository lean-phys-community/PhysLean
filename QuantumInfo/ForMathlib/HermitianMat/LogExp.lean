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

theorem Matrix.IsHermitian.log_smul_of_ne_zero {A : Matrix d d 𝕜} (hA : A.IsHermitian) (hx : x ≠ 0) :
    cfc Real.log (x • A) = (Real.log x) • cfc (if · = 0 then (0 : ℝ) else 1) A + cfc Real.log A := by
  have hCFC : cfc (Real.log ∘ (x * ·)) A = cfc Real.log (x • A) :=
    cfc_comp_smul x Real.log _ (by fun_prop) hA
  rw [← hCFC, ← cfc_smul, ← cfc_add]
  refine cfc_congr fun t ht => ?_
  rcases eq_or_ne t 0 with h | h <;> simp [*, Real.log_mul]

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
instance nonSingular_exp : NonSingular A.exp :=
  cfc_nonSingular A Real.exp (fun i ↦ by positivity)

/-- The matrix exponential of a Hermitian matrix is nonnegative. -/
theorem exp_nonneg (A : HermitianMat d 𝕜) : 0 ≤ A.exp :=
  (HermitianMat.cfc_nonneg_iff _ _).mpr fun _ ↦ (Real.exp_pos _).le

/-- The matrix exponential of a Hermitian matrix is strictly positive (Loewner order).
Requires `Nonempty` since over an empty index type every matrix equals zero and `0 < 0`
is false. -/
theorem exp_pos [i : Nonempty d] (A : HermitianMat d 𝕜) : 0 < A.exp :=
  A.exp_nonneg.lt_of_ne' fun h ↦ by simpa [h] using A.nonSingular_exp.isUnit

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

@[simp]
theorem log_zero : (0 : HermitianMat d 𝕜).log = 0 := by
  simp [log]

@[simp]
theorem log_one : (1 : HermitianMat d 𝕜).log = 0 := by
  simp [log]

theorem log_smul_of_pos (A : HermitianMat d 𝕜) (hx : x ≠ 0) :
    (x • A).log = Real.log x • A.supportProj + A.log := by
  ext1
  convert! A.H.log_smul_of_ne_zero hx
  simp [cfc, log, supportProj_eq_cfc]

theorem log_smul {A : HermitianMat d 𝕜} {x : ℝ} (hx : x ≠ 0) [NonSingular A] :
    (x • A).log = Real.log x • 1 + A.log := by
  simp [log_smul_of_pos A hx]

/-
The inverse function is operator antitone for positive definite matrices.
-/
open ComplexOrder MatrixOrder in
theorem inv_antitone (hA : A.mat.PosDef) (h : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  rw [HermitianMat.le_iff] at h ⊢
  have hB : B.mat.PosDef := by simpa using hA.add_posSemidef h
  have := hA.isUnit.invertible
  have := hB.isUnit.invertible
  have := hA.inv.isUnit.invertible
  have h1 : (Matrix.fromBlocks B.mat 1 (1 : Matrix d d 𝕜).conjTranspose A.mat⁻¹).PosSemidef :=
    (Matrix.PosDef.fromBlocks₂₂ _ _ hA.inv).mpr (by simpa [Matrix.inv_inv_of_invertible] using h)
  simpa using (Matrix.PosDef.fromBlocks₁₁ _ _ hB).mp h1

/-
The integral of $1/(1+t) - 1/(x+t)$ from 0 to T is $\log x + \log((1+T)/(x+T))$.
-/
lemma Real.integral_inv_sub_inv_finite (x T : ℝ) (hx : 0 < x) (hT : 0 < T) :
    ∫ t in (0)..T, (1 / (1 + t) - 1 / (x + t)) = Real.log x + Real.log ((1 + T) / (x + T)) := by
  have key : ∀ {c : ℝ}, 0 < c → ∀ u ∈ Set.uIcc c (c + T), u ≠ 0 := fun {c} hc u hu =>
    (hc.trans_le ((Set.uIcc_of_le (le_add_of_nonneg_right hT.le)) ▸ hu).1).ne'
  have h1 : ∀ {c : ℝ}, 0 < c → ∫ t in (0)..T, 1 / (c + t) = Real.log (c + T) - Real.log c := by
    intro c hc
    rw [intervalIntegral.integral_comp_add_left (1 / ·) c, add_zero]
    exact intervalIntegral.integral_deriv_eq_sub' _ (funext fun u => by simp [Real.deriv_log])
      (fun u hu => Real.differentiableAt_log (key hc u hu))
      (continuousOn_const.div continuousOn_id (key hc))
  have hi : ∀ {c : ℝ}, 0 < c →
      IntervalIntegrable (fun t => 1 / (c + t)) MeasureTheory.volume 0 T := fun {c} hc =>
    (continuousOn_const.div (by fun_prop) fun t ht =>
      (add_pos_of_pos_of_nonneg hc ht.1).ne').intervalIntegrable_of_Icc hT.le
  rw [intervalIntegral.integral_sub (hi one_pos) (hi hx), h1 one_pos, h1 hx,
    Real.log_div (by positivity) (by positivity), Real.log_one]
  ring

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
  have key : ∀ {z : HermitianMat d 𝕜}, z.mat.PosDef →
      ContinuousOn (fun t : ℝ => (1 + t)⁻¹ • (1 : HermitianMat d 𝕜) - (z + t • 1)⁻¹)
        (Set.Icc 0 T) := by
    intro z hz
    have h2 : ContinuousOn (fun t : ℝ => (z.mat + t • 1)⁻¹) (Set.Icc 0 T) := by
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact ((by fun_prop : ContinuousOn (fun t : ℝ => (z.mat + t • 1).det)
        (Set.Icc 0 T)).inv₀ fun t ht =>
        (hz.add_posSemidef (.smul .one ht.1)).det_pos.ne').smul (by fun_prop)
    refine ContinuousOn.sub ?_ ((continuousOn_iff_coe fun t : ℝ => (z + t • 1)⁻¹).mpr h2)
    exact ((continuousOn_const.add continuousOn_id).inv₀ fun t ht =>
      (add_pos_of_pos_of_nonneg one_pos ht.1).ne').smul continuousOn_const
  rw [intervalIntegral.integral_of_le hT.le, intervalIntegral.integral_of_le hT.le]
  refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
  · exact ((key hx).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · exact ((key hy).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have h1 : (y + t • 1)⁻¹ ≤ (x + t • 1)⁻¹ :=
      inv_antitone (hx.add_posSemidef (.smul .one ht.1.le)) (add_le_add hxy le_rfl)
    exact sub_le_sub_left h1 _

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
  simpa [scalarLogApprox, one_div] using Real.integral_inv_sub_inv_finite x T hx hT

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
    convert inv_cfc_eq_cfc_inv (fun u => u + t)
      (fun i => (add_pos_of_pos_of_nonneg (hx.eigenvalues_pos i) ht).ne') using 1
    simp [h_cfc_add]
  rw [← cfc_const x (1 + t)⁻¹, h_cfc_sub, ← cfc_sub]
  rfl

open ComplexOrder MeasureTheory intervalIntegral in
/--
The matrix log approximation is the CFC of the scalar log approximation.
-/
theorem logApprox_eq_cfc_scalar
    (x : HermitianMat d 𝕜) (hx : x.mat.PosDef) (T : ℝ) (hT : 0 < T) :
    logApprox x T = x.cfc (scalarLogApprox T) := by
  unfold scalarLogApprox logApprox
  rw [intervalIntegral.integral_congr fun t ht =>
    integrand_eq x hx t (by cases Set.mem_uIcc.mp ht <;> linarith)]
  refine integral_cfc_eq_cfc_integral 0 T _ fun i => ?_
  refine (ContinuousOn.sub ?_ ?_).intervalIntegrable_of_Icc hT.le
  · exact (continuousOn_const.add continuousOn_id).inv₀ fun t ht =>
      (add_pos_of_pos_of_nonneg one_pos ht.1).ne'
  · exact (continuousOn_const.add continuousOn_id).inv₀ fun t ht =>
      (add_pos_of_pos_of_nonneg (hx.eigenvalues_pos i) ht.1).ne'

open ComplexOrder in
/--
The log approximation is the log plus an error term.
-/
theorem logApprox_eq_log_add_error
    (x : HermitianMat d 𝕜) (hx : x.mat.PosDef) (T : ℝ) (hT : 0 < T) :
    logApprox x T = x.log + x.cfc (fun u => Real.log ((1 + T) / (u + T))) := by
  rw [logApprox_eq_cfc_scalar x hx T hT, log, ← cfc_add_apply]
  exact cfc_congr_of_posDef hx fun u hu => scalarLogApprox_eq u T hu.out hT

open ComplexOrder Filter Topology in
open scoped Matrix.Norms.Frobenius in
set_option backward.isDefEq.respectTransparency false in
/--
The error term in the log approximation tends to 0 as T goes to infinity.
-/
lemma tendsto_cfc_log_div_add_atTop (x : HermitianMat d 𝕜) :
    Tendsto (fun T => x.cfc (fun u => Real.log ((1 + T) / (u + T)))) atTop (nhds 0) := by
  refine tendsto_subtype_rng.mpr ?_
  refine Tendsto.congr (fun T => (cfc_toMat_eq_sum_smul_proj x _).symm) ?_
  convert tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) =>
    (Real.tendsto_log_div_add_atTop (x.H.eigenvalues i)).smul_const
      (x.H.eigenvectorUnitary.val * Matrix.single i i 1 * x.H.eigenvectorUnitary.val.conjTranspose)
  simp

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
  simpa using hA.add_posSemidef (le_iff.mp hAB)

open ComplexOrder in
/--
The matrix logarithm is operator monotone.
-/
theorem log_mono (hA : A.mat.PosDef) (hAB : A ≤ B) : A.log ≤ B.log := by
  have hB : B.mat.PosDef := posDef_of_posDef_le hA hAB
  apply le_of_tendsto_of_tendsto (tendsto_logApprox hA) (tendsto_logApprox hB)
  rw [Filter.EventuallyLE, Filter.eventually_atTop]
  exact ⟨1, fun T hT => logApprox_mono hA hB hAB T (zero_lt_one.trans_le hT)⟩

/-- Monotonicity of exp on commuting operators. -/
theorem le_of_exp_commute (hAB₂ : A.exp ≤ B.exp) :
    A ≤ B := by
  have hA : A = (A.exp).log := by simp [exp, log, ← HermitianMat.cfc_comp]
  have hB : B = (B.exp).log := by simp [exp, log, ← HermitianMat.cfc_comp]
  rw [hA, hB]
  exact log_mono ((HermitianMat.cfc_posDef _ _).mpr fun _ => Real.exp_pos _) hAB₂

set_option maxHeartbeats 10000000 in
open ComplexOrder Matrix in
/--
The inverse function is operator convex on positive definite matrices.
-/
lemma inv_convex {x y : HermitianMat d 𝕜} (hx : x.mat.PosDef) (hy : y.mat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • x + b • y)⁻¹ ≤ a • x⁻¹ + b • y⁻¹ := by
  have hs : (a • x.mat + b • y.mat).PosDef := Matrix.PosDef.Convex hx hy ha hb hab
  have key : ∀ z : Matrix d d 𝕜, z.PosDef →
      (Matrix.fromBlocks z 1 (1 : Matrix d d 𝕜).conjTranspose z⁻¹).PosSemidef := fun z hz => by
    have := hz.isUnit.invertible
    exact (hz.fromBlocks₁₁ 1 z⁻¹).mpr (by simpa using Matrix.PosSemidef.zero)
  have h2 : (Matrix.fromBlocks (a • x.mat + b • y.mat) 1 (1 : Matrix d d 𝕜).conjTranspose
      (a • x.mat⁻¹ + b • y.mat⁻¹)).PosSemidef := by
    have h3 := ((key _ hx).smul ha).add ((key _ hy).smul hb)
    simpa [Matrix.fromBlocks_smul, Matrix.fromBlocks_add, ← add_smul, hab] using h3
  have := hs.isUnit.invertible
  rw [HermitianMat.le_iff]
  simpa using (hs.fromBlocks₁₁ _ _).mp h2

open ComplexOrder in
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
  have h2 : ContinuousOn (fun t : ℝ => (A.mat + t • 1)⁻¹) (Set.Icc 0 b) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact ((by fun_prop : ContinuousOn (fun t : ℝ => (A.mat + t • 1).det)
      (Set.Icc 0 b)).inv₀ fun t ht =>
      (hA.add_posSemidef (.smul .one ht.1)).det_pos.ne').smul (by fun_prop)
  exact ((continuousOn_iff_coe fun t : ℝ => (A + t • 1)⁻¹).mpr h2).intervalIntegrable_of_Icc hb

open ComplexOrder in
set_option backward.isDefEq.respectTransparency false in
/--
The finite integral approximation of the matrix logarithm is operator concave.
-/
theorem logApprox_concave {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]
    {x y : HermitianMat n 𝕜} (hx : x.mat.PosDef) (hy : y.mat.PosDef)
    ⦃a b : ℝ⦄ (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (T : ℝ) (hT : 0 ≤ T) :
    a • x.logApprox T + b • y.logApprox T ≤ (a • x + b • y).logApprox T := by
  have h_integrable : ∀ {z : HermitianMat n 𝕜}, z.mat.PosDef →
      IntervalIntegrable (fun t => (1 + t)⁻¹ • (1 : HermitianMat n 𝕜) - (z + t • 1)⁻¹)
        MeasureTheory.volume 0 T := by
    intro z hz
    refine IntervalIntegrable.sub ?_ (integrable_inv_shift hz T hT)
    exact (((continuousOn_const.add continuousOn_id).inv₀ fun t ht =>
      (add_pos_of_pos_of_nonneg one_pos ht.1).ne').smul
      continuousOn_const).intervalIntegrable_of_Icc hT
  have hax : IntervalIntegrable (fun t => a • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) -
      (x + t • 1)⁻¹)) MeasureTheory.volume 0 T := (h_integrable hx).smul a
  have hby : IntervalIntegrable (fun t => b • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜) -
      (y + t • 1)⁻¹)) MeasureTheory.volume 0 T := (h_integrable hy).smul b
  rw [logApprox, logApprox, logApprox, ← intervalIntegral.integral_smul,
    ← intervalIntegral.integral_smul, ← intervalIntegral.integral_add hax hby,
    intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
  refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
  · exact (hax.add hby).1
  · exact (h_integrable (z := a • x + b • y) (Matrix.PosDef.Convex hx hy ha hb hab)).1
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    refine le_trans (le_of_eq ?_)
      (sub_le_sub_left (inv_shift_convex hx hy ha hb hab t ht.1.le) _)
    linear_combination (norm := module) hab • ((1 + t)⁻¹ • (1 : HermitianMat n 𝕜))

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
  simp only [log, ← diagonal_one (𝕜 := 𝕜), kronecker_diagonal, cfc_diagonal, ← diagonal_add]
  refine congrArg _ (funext fun i => ?_)
  simp [Real.log_mul (h₁ i.1).ne' (h₂ i.2).ne']

/--
The logarithm of a Hermitian matrix conjugated by a unitary matrix is the conjugate of the logarithm.
-/
lemma log_conj_unitary (A : HermitianMat d 𝕜) (U : Matrix.unitaryGroup d 𝕜) :
    (A.conj U.val).log = A.log.conj U.val :=
  cfc_conj_unitary _ Real.log U

open RealInnerProductSpace in
theorem inner_log_smul_of [NonSingular A] {x : ℝ} (hx : x ≠ 0) :
    ⟪(x • A).log, B⟫ = Real.log x * B.trace + ⟪A.log, B⟫ := by
  simp [log_smul hx, inner_add_left]

section kron

lemma log_kron_diagonal_with_proj {f : d → ℝ} {g : d₂ → ℝ}  :
    (diagonal 𝕜 f ⊗ₖ diagonal 𝕜 g).log =
    (diagonal 𝕜 f).log ⊗ₖ (diagonal 𝕜 g).supportProj +
    (diagonal 𝕜 f).supportProj ⊗ₖ (diagonal 𝕜 g).log := by
  simp only [log, supportProj_eq_cfc, kronecker_diagonal, cfc_diagonal, ← diagonal_add]
  refine congrArg _ (funext fun i => ?_)
  rcases eq_or_ne (f i.1) 0 with h | h <;> rcases eq_or_ne (g i.2) 0 with h' | h' <;>
    simp [h, h', Real.log_mul]

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
