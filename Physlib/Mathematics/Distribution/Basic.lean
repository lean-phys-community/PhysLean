/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joseph Tooby-Smith
-/
module

public import Physlib.Meta.TODO.Basic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Topology.Algebra.Module.PointwiseConvergence
/-!

# Distributions

## i. Overview of distributions

Distributions are often used implicitly in physics, for example the correct way to handle
a dirac delta function is to treat it as a distribution. In this file we will
define distributions and some properties on them.

The distributions from a space `E` to space `F` can be thought of as a generalization of
functions from `E` to `F`. We give a more precise definition of distributions below.

## ii. Key results

- `E →d[𝕜] F` is the type of distributions from `E` to `F`.
- `Distribution.derivative` and `Distribution.fourierTransform` allow us to make sense of these
  operations that might not make sense a priori on general functions.

## iii. Table of Content

- A. The definition of a distribution
- B. Construction of distributions from linear maps
- C. Derivatives of distributions
- D. Fourier transform of distributions
- E. Specific distributions

## iv. Implementation notes

- In this file we will define distributions generally, in `Physlib.SpaceAndTime.Distributions`
  we define properties of distributions directly related to `Space`.

-/

@[expose] public section

open SchwartzMap NNReal
noncomputable section

/-!

## A. The definition of a distribution

In physics, we often encounter mathematical objects like the Dirac delta function `δ(x)`
that are not functions in the traditional sense.
Distributions provide a rigorous framework for handling such objects.

The core idea is to define a "generalized function" not by its value at each point,
but by how it acts on a set of well-behaved "test functions".

These test functions, typically denoted `η`. The choice of test functions depends on the application
here we choose test functions which are smooth and decay
rapidly at infinity (called Schwartz maps). Thus really the distributions we are defining here
are called tempered distributions.

A distribution `u` is a linear map that takes a test function `η` and produces a value,
which can be a scalar or a vector. This action is written as `⟪u,η⟫`.

Two key examples illustrate this concept:

1. **Ordinary Functions:** Any well-behaved function `f(x)` can be viewed as a distribution.
  Its action on a test function `η` is defined by integration:
  `u_f(η) = ∫ f(x) η(x) dx`
  This integral "tests" the function `f` using `η`.

2. **Dirac Delta:** The Dirac delta `δ_a` (centered at `a`) is a distribution whose action is to
  simply evaluate the test function at `a`:
  `δ_a(η) = η(a)`

Formally, a distribution is a *continuous linear map* from the space of Schwartz functions
`𝓢(E, 𝕜)` to a
vector space `F` over `𝕜`. This definition allows us to rigorously define concepts
like derivatives and Fourier transforms for these generalized functions, as we will see below.

We use the notation `E →d[𝕜] F` to denote the space of distributions from `E` to `F`
where `E` is a normed vector space over `ℝ` and `F` is a normed vector space over `𝕜`.

-/

/-- An `F`-valued distribution on `E` (where `E` is a normed vector space over `ℝ` and `F` is a
normed vector space over `𝕜`) is a continuous linear map `𝓢(E, 𝕜) →L[𝕜] F` where `𝒮(E, 𝕜)` is
the Schwartz space of smooth functions `E → 𝕜` with rapidly decreasing iterated derivatives. This
is notated as `E →d[𝕜] F`.

This should be seen as a generalisation of functions `E → F`. -/
abbrev Distribution (𝕜 E F : Type) [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace 𝕜 F] : Type :=
  𝓢(E, 𝕜) →L[𝕜] F

@[inherit_doc] notation:25 E:arg "→d[" 𝕜:25 "] " F:0 => Distribution 𝕜 E F

variable (𝕜 : Type) {E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]

namespace Distribution

section NormedSpace

variable [NormedSpace ℝ E] [NormedSpace 𝕜 F]

/-!

## B. Construction of distributions from linear maps

Distributions are defined as **continuous** linear maps from `𝓢(E, 𝕜)` to `F`.
It is possible to define a constructor of distributions from just linear maps
`𝓢(E, 𝕜) →ₗ[𝕜] F` (without the continuity requirement) by imposing a condition
on the size of `u` applied to `η`.

-/

set_option backward.isDefEq.respectTransparency false in
/-- The construction of a distribution from the following data:
1. We take a finite set `s` of pairs `(k, n) ∈ ℕ × ℕ` that will be explained later.
2. We take a linear map `u` that evaluates the given Schwartz function `η`. At this stage we don't
  need `u` to be continuous.
3. Recall that a Schwartz function `η` satisfies a bound
  `‖x‖ᵏ * ‖(dⁿ/dxⁿ) η‖ < Mₙₖ` where `Mₙₖ : ℝ` only depends on `(k, n) : ℕ × ℕ`.
4. This step is where `s` is used: for each test function `η`, the norm `‖u η‖` is required to be
  bounded by `C * (‖x‖ᵏ * ‖(dⁿ/dxⁿ) η‖)` for some `x : ℝ` and for some `(k, n) ∈ s`, where
  `C ≥ 0` is a global scalar.
-/
def ofLinear (s : Finset (ℕ × ℕ)) (u : 𝓢(E, 𝕜) →ₗ[𝕜] F)
    (hu : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : 𝓢(E, 𝕜), ∃ (k : ℕ) (n : ℕ) (x : E), (k, n) ∈ s ∧
      ‖u η‖ ≤ C * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n η x‖)) : E →d[𝕜] F :=
  mkCLMtoNormedSpace u (by simp) (by simp) <| by
    obtain ⟨C, hC, hu⟩ := hu
    refine ⟨s, C, hC, fun η ↦ ?_⟩
    obtain ⟨k, n, x, hkn, hη⟩ := hu η
    refine hη.trans <| mul_le_mul_of_nonneg_left ((le_seminorm 𝕜 k n η x).trans ?_) hC
    rw [Seminorm.finset_sup_apply]
    refine (NNReal.coe_le_coe (r₁ := ⟨SchwartzMap.seminorm 𝕜 k n η, apply_nonneg _ _⟩)).2 ?_
    convert s.le_sup hkn
      (f := fun kn : ℕ × ℕ ↦ (⟨SchwartzMap.seminorm 𝕜 kn.1 kn.2 η, apply_nonneg _ _⟩ : ℝ≥0))

@[simp] lemma ofLinear_apply (s : Finset (ℕ × ℕ)) (u : 𝓢(E, 𝕜) →ₗ[𝕜] F)
    (hu : ∃ C : ℝ, 0 ≤ C ∧ ∀ η : 𝓢(E, 𝕜), ∃ (k : ℕ) (n : ℕ) (x : E), (k, n) ∈ s ∧
      ‖u η‖ ≤ C * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n η x‖))
    (η : 𝓢(E, 𝕜)) :
    ofLinear 𝕜 s u hu η = u η :=
  rfl

end NormedSpace

/-!

## C. Derivatives of distributions

Given a distribution `u : E →d[𝕜] F`, we can define the derivative of that distribution.
In general when defining an operation on a distribution, we do it by applying a similar
operation instead to the Schwartz maps it acts on.

Thus the derivative of `u` is the distribution which takes `η` to `⟪u, - η'⟫`
where `η'` is the derivative of `η`.

-/

section fderiv

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The Fréchet derivative of a distribution.

Informally, for a distribution `u : E →d[𝕜] F`,
the Fréchet derivative `fderiv u x v` corresponds to the derivative of `u` at the
point `x` in the direction `v`. For example, if `F = ℝ³`
then `fderiv u x v` is a vector in `ℝ³` corresponding to
`(v₁ ∂u₁/∂x₁ + v₂ ∂u₁/∂x₂ + v₃ ∂u₁/∂x₃, v₁ ∂u₂/∂x₁ + v₂ ∂u₂/∂x₂ + v₃ ∂u₂/∂x₃,...)`.

Formally, for a distribution `u : E →d[𝕜] F`, this is actually defined
the distribution which takes test function `η : E → 𝕜` to
`- u (SchwartzMap.evalCLM v (SchwartzMap.fderivCLM 𝕜 η))`.

Note that, unlike for functions, the Fréchet derivative of a distribution always exists.
-/
def fderivD [FiniteDimensional ℝ E] : (E →d[𝕜] F) →ₗ[𝕜] (E →d[𝕜] (E →L[ℝ] F)) where
  toFun u := {
    toFun η := LinearMap.toContinuousLinearMap {
      toFun v := ContinuousLinearEquiv.neg 𝕜 <| u <|
        SchwartzMap.evalCLM (𝕜 := 𝕜) E 𝕜 v <|
        SchwartzMap.fderivCLM 𝕜 (E := E) (F := 𝕜) η
      map_add' v1 v2 := by
        simp only [ContinuousLinearEquiv.neg_apply]
        trans -u ((SchwartzMap.evalCLM (𝕜 := 𝕜) E 𝕜 v1) ((fderivCLM 𝕜) E 𝕜 η) +
          (SchwartzMap.evalCLM (𝕜 := 𝕜) E 𝕜 v2) ((fderivCLM 𝕜) E 𝕜 η))
        swap
        · simp only [map_add, neg_add_rev]
          abel
        congr
        ext x
        simp only [SchwartzMap.evalCLM, mkCLM, mkLM, map_add, ContinuousLinearMap.coe_mk',
          LinearMap.coe_mk, AddHom.coe_mk, fderivCLM_apply, add_apply]
        rfl
      map_smul' a v1 := by
        simp only [ContinuousLinearEquiv.neg_apply, RingHom.id_apply, smul_neg, neg_inj]
        trans u (a • (SchwartzMap.evalCLM (𝕜 := 𝕜) E 𝕜 v1) ((fderivCLM 𝕜) E 𝕜 η))
        swap
        · simp
        congr
        ext x
        simp only [SchwartzMap.evalCLM, mkCLM, mkLM, map_smul, ContinuousLinearMap.coe_mk',
          LinearMap.coe_mk, AddHom.coe_mk, fderivCLM_apply, smul_apply]
        rfl}
    map_add' η1 η2 := by
      ext x
      simp only [map_add, ContinuousLinearEquiv.neg_apply,
        LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousLinearMap.add_apply]
    map_smul' a η := by
      ext x
      simp
    cont := by
      refine continuous_clm_apply.mpr ?_
      intro y
      simp only [ContinuousLinearEquiv.neg_apply, LinearMap.coe_toContinuousLinearMap',
        LinearMap.coe_mk, AddHom.coe_mk]
      fun_prop
  }
  map_add' u₁ u₂ := by
    ext η
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearEquiv.neg_apply, neg_add_rev,
      ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coe_toContinuousLinearMap']
    abel
  map_smul' c u := by
    ext
    simp

lemma fderivD_apply [FiniteDimensional ℝ E] (u : E →d[𝕜] F) (η : 𝓢(E, 𝕜)) (v : E) :
    fderivD 𝕜 u η v = - u (SchwartzMap.evalCLM (𝕜 := 𝕜) E 𝕜 v (SchwartzMap.fderivCLM 𝕜 E 𝕜 η)) := by
  rfl

TODO "01-09-25-JTS" "For distributions, prove that the derivative fderivD commutes with
  integrals and sums. This may require defining the integral of families of distributions
  although it is expected this will follow from the definition of a distribution."

end fderiv

/-!

## D. Fourier transform of distributions

As with derivatives of distributions we can define the fourier transform of a distribution
by taking the fourier transform of the underlying Schwartz maps. Thus the fourier transform
of the distribution `u` is the distribution which takes `η` to `⟪u, F[η]⟫` where `F[η]` is the
fourier transform of `η`.

-/

section Complex

variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedSpace ℂ F]

variable (E F) in
/-- Definition of Fourier transform of distribution: Let `u` be a distribution. Then its Fourier
transform is `F{u}` where given a test function `η`, `F{u}(η) := u(F{η})`. -/
def fourierTransform : (E →d[ℂ] F) →ₗ[ℂ] (E →d[ℂ] F) where
  toFun u := u.comp <| fourierTransformCLM ℂ (E := ℂ) (V := E)
  map_add' u₁ u₂ := by simp
  map_smul' c u := by simp

@[simp] lemma fourierTransform_apply (u : E →d[ℂ] F) (η : 𝓢(E, ℂ)) :
    u.fourierTransform E F η = u (fourierTransformCLM ℂ η) :=
  rfl

end Complex

/-!

## E. Specific distributions

We now define specific distributions, which are used throughout physics. In particular, we define:
- The constant distribution.
- The dirac delta distribution.
- The heaviside step function.

-/

section constant
/-!

### E.1. The constant distribution

The constant distribution is the distribution which corresponds to a constant function,
it takes `η` to the integral of `η` over the volume measure.

-/
open MeasureTheory
section
variable (E : Type) [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace ℝ F]
  [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]

set_option backward.isDefEq.respectTransparency false in
/-- The constant distribution `E →d[𝕜] F`, for a given `c : F` this corresponds
  to the integral `∫ x, η x • c ∂MeasureTheory.volume`. -/
def const [hμ : Measure.HasTemperateGrowth (volume (α := E))] (c : F) : E →d[𝕜] F := by
  refine mkCLMtoNormedSpace
    (fun η => ∫ x, η x • c ∂MeasureTheory.volume) ?_
    ?_ ?_
  · intro η1 η2
    simp [add_smul]
    by_cases hc : c = 0
    · subst hc
      simp
    rw [MeasureTheory.integral_add]
    · refine (integrable_smul_const hc).mpr ?_
      exact integrable η1
    · refine (integrable_smul_const hc).mpr ?_
      exact integrable η2
  · intro a η
    simp only [smul_apply, RingHom.id_apply, smul_assoc]
    rw [MeasureTheory.integral_smul]
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, ‖c‖ * (2 ^ n * ∫ x, (1 + ‖x‖) ^ (- (n : ℝ)) ∂(volume (α := E)))
  refine ⟨by positivity, fun η ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  have h' : ∀ x, ‖η x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
    (2 ^ n * ((Finset.Iic m).sup (fun m' => SchwartzMap.seminorm 𝕜 m'.1 m'.2) η)) := by
    intro x
    rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
      le_div_iff₀' (by positivity), Real.rpow_natCast]
    simpa using one_add_le_sup_seminorm_apply (m := m) (k := n) (n := 0) le_rfl le_rfl η x
  conv_lhs =>
    enter [2, x]
    rw [norm_smul, mul_comm]
  conv_lhs =>
    rw [MeasureTheory.integral_const_mul]
  rw [mul_assoc]
  by_cases hc : c = 0
  · subst hc
    simp
  refine (mul_le_mul_iff_of_pos_left ?_).mpr ?_
  · positivity
  apply (integral_mono (by simpa using η.integrable_pow_mul ((volume)) 0) _ h').trans
  · unfold schwartzSeminormFamily
    rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]
  apply h.mul_const

lemma const_apply [hμ : Measure.HasTemperateGrowth (volume (α := E))] (c : F)
    (η : 𝓢(E, 𝕜)) :
    const 𝕜 E c η = ∫ x, η x • c ∂MeasureTheory.volume := by rfl
end
section

variable [NormedSpace ℝ E] [NormedSpace ℝ F]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]

@[simp]
lemma fderivD_const [hμ : Measure.IsAddHaarMeasure (volume (α := E))]
    [FiniteDimensional ℝ E] (c : F) :
    fderivD ℝ (const ℝ E c) = 0 := by
  ext η v
  rw [fderivD_apply, const_apply]
  simp only [ContinuousLinearMap.zero_apply, neg_eq_zero]
  trans -∫ (x : E), η x • (fderiv ℝ (fun y => c) x) v ∂volume
  swap
  · simp
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable]
  simp only [evalCLM_apply_apply, fderivCLM_apply, neg_neg]
  · apply MeasureTheory.Integrable.smul_const
    change Integrable (SchwartzMap.evalCLM (𝕜 := ℝ) E ℝ v (SchwartzMap.fderivCLM ℝ E ℝ η)) volume
    exact integrable ((SchwartzMap.evalCLM ℝ E ℝ v) ((fderivCLM ℝ) E ℝ η))
  · simp
  · apply MeasureTheory.Integrable.smul_const
    exact integrable η
  · fun_prop
  · simp

end
end constant

/-!

### E.2. The dirac delta distribution

The dirac delta distribution centered at `a : E` is the distribution which takes
`η` to `η a`. We also define `diracDelta'` which takes in an element of `v` of `F` and
outputs `η a • v`.

-/

section DiracDelta

open ContinuousLinearMap

variable [NormedSpace ℝ E] [NormedSpace 𝕜 F]

/-- Dirac delta distribution `diracDelta 𝕜 a : E →d[𝕜] 𝕜` takes in a test function `η : 𝓢(E, 𝕜)`
and outputs `η a`. Intuitively this is an infinite density at a single point `a`. -/
def diracDelta (a : E) : E →d[𝕜] 𝕜 :=
  toPointwiseConvergenceCLM _ _ _ _ <|
    (BoundedContinuousFunction.evalCLM 𝕜 a).comp (toBoundedContinuousFunctionCLM 𝕜 E 𝕜)

@[simp] lemma diracDelta_apply (a : E) (η : 𝓢(E, 𝕜)) :
    diracDelta 𝕜 a η = η a :=
  rfl

/-- Dirac delta in a given direction `v : F`. `diracDelta' 𝕜 a v` takes in a test function
`η : 𝓢(E, 𝕜)` and outputs `η a • v`. Intuitively this is an infinitely intense vector field
at a single point `a` pointing at the direction `v`. -/
def diracDelta' (a : E) (v : F) : E →d[𝕜] F :=
  ContinuousLinearMap.smulRight (diracDelta 𝕜 a) v

@[simp] lemma diracDelta'_apply (a : E) (v : F) (η : 𝓢(E, 𝕜)) :
    diracDelta' 𝕜 a v η = η a • v :=
  rfl

end DiracDelta
/-!

### E.3. The heviside step function

The heaviside step function on `EuclideanSpace ℝ (Fin d.succ)` is the distribution
from `EuclideanSpace ℝ (Fin d.succ)` to `ℝ` which takes a `η` to the integral of `η` in the
upper-half plane (determined by the last coordinate in `EuclideanSpace ℝ (Fin d.succ)`).

-/
open MeasureTheory

set_option backward.isDefEq.respectTransparency false in
/-- The Heaviside step distribution defined on `(EuclideanSpace ℝ (Fin d.succ)) `
  equal to `1` in the positive `z`-direction and `0` in the negative `z`-direction. -/
def heavisideStep (d : ℕ) : (EuclideanSpace ℝ (Fin d.succ)) →d[ℝ] ℝ := by
  refine mkCLMtoNormedSpace
    (fun η =>
    ∫ x in {x : EuclideanSpace ℝ (Fin d.succ) | 0 < x (Fin.last d)}, η x ∂MeasureTheory.volume) ?_
    ?_ ?_
  · intro η1 η2
    simp only [Nat.succ_eq_add_one, add_apply]
    rw [MeasureTheory.integral_add]
    · apply MeasureTheory.Integrable.restrict
      exact integrable η1
    · apply MeasureTheory.Integrable.restrict
      exact integrable η2
  · intro a η
    simp only [smul_apply, RingHom.id_apply]
    rw [MeasureTheory.integral_smul]
  haveI hμ : (volume (α := EuclideanSpace ℝ (Fin d.succ))).HasTemperateGrowth := by
    infer_instance
  rcases hμ.exists_integrable with ⟨n, h⟩
  let m := (n, 0)
  use Finset.Iic m, 2 ^ n *
    ∫ x, (1 + ‖x‖) ^ (- (n : ℝ)) ∂(volume (α := EuclideanSpace ℝ (Fin d.succ)))
  refine ⟨by positivity, fun η ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  trans ∫ x, ‖η x‖ ∂(volume (α := EuclideanSpace ℝ (Fin d.succ)))
  · refine setIntegral_le_integral ?_ ?_
    · have hi := integrable η (μ := volume)
      fun_prop
    · filter_upwards with x
      simp
  · have h' : ∀ x, ‖η x‖ ≤ (1 + ‖x‖) ^ (-(n : ℝ)) *
      (2 ^ n * ((Finset.Iic m).sup (fun m' => SchwartzMap.seminorm ℝ m'.1 m'.2) η)) := by
      intro x
      rw [Real.rpow_neg (by positivity), ← div_eq_inv_mul,
        le_div_iff₀' (by positivity), Real.rpow_natCast]
      simpa using one_add_le_sup_seminorm_apply (m := m) (k := n) (n := 0) le_rfl le_rfl η x
    apply (integral_mono (by simpa using η.integrable_pow_mul ((volume)) 0) _ h').trans
    · unfold schwartzSeminormFamily
      rw [integral_mul_const, ← mul_assoc, mul_comm (2 ^ n)]
    apply h.mul_const

lemma heavisideStep_apply (d : ℕ) (η : 𝓢(EuclideanSpace ℝ (Fin d.succ), ℝ)) :
    heavisideStep d η = ∫ x in {x : EuclideanSpace ℝ (Fin d.succ) | 0 < x (Fin.last d)},
      η x ∂MeasureTheory.volume := by
  rfl

end Distribution
