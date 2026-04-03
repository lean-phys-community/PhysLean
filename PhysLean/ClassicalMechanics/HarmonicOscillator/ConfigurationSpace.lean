/-
Copyright (c) 2026 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini, Joseph Tooby-Smith
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import PhysLean.SpaceAndTime.Time.Basic
/-!
# Configuration space of the harmonic oscillator

The configuration space is defined as a one-dimensional smooth manifold,
modeled on `ℝ`, with a chosen coordinate.
-/

@[expose] public section

namespace ClassicalMechanics

namespace HarmonicOscillator

TODO "4DLL5" "The API around this should be improved to allow further development of a proper
    geometric model of the Harmonic Oscillator (see TODO item 4DK2M)."

/-- The configuration space of the harmonic oscillator. -/
structure ConfigurationSpace where
  /-- The underlying real coordinate. -/
  val : ℝ

namespace ConfigurationSpace

open Manifold ContDiff

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))

@[ext]
lemma ext {x y : ConfigurationSpace} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  simp at h
  simp [h]


/-!

## The manifold structure on the configuration space

On `ConfigurationSpace`, we induce an instance of a topological space,
a charted space, and a smooth manifold structure from the equivalence `toEuclid` with
`EuclideanSpace ℝ (Fin 1)`.

-/

/-- Linear map sending a configuration space element to its underlying real value. -/
noncomputable def toEuclid : ConfigurationSpace ≃ EuclideanSpace ℝ (Fin 1) where
    toFun x := WithLp.toLp 2 fun _ => x.val
    invFun x := ⟨x 0⟩
    right_inv x := by
      ext i
      fin_cases i
      rfl
    left_inv x := rfl

/-- The structure of a topological space on ConfigurationSpace induced
  by `toEuclid`. -/
instance : TopologicalSpace ConfigurationSpace :=
  TopologicalSpace.induced toEuclid (PiLp.topologicalSpace 2 fun _ => ℝ)

lemma toEuclid_isInducing : Topology.IsInducing toEuclid := { eq_induced := rfl }

/-- The homeomorphism between `ConfigurationSpace` and `EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def toEuclidHomeo : ConfigurationSpace ≃ₜ EuclideanSpace ℝ (Fin 1) :=
  toEuclid.toHomeomorphOfIsInducing toEuclid_isInducing

noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ConfigurationSpace where
  atlas := { toEuclidHomeo.toOpenPartialHomeomorph }
  chartAt _ := toEuclidHomeo.toOpenPartialHomeomorph
  mem_chart_source := by simp
  chart_mem_atlas x := by simp

instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ω ConfigurationSpace where
  compatible := by
    intro e1 e2 h1 h2
    simp [atlas, ChartedSpace.atlas] at h1 h2
    subst h1 h2
    exact symm_trans_mem_contDiffGroupoid toEuclidHomeo.toOpenPartialHomeomorph

/-- The diffeomorphism between ℝ and ConfigurationSpace. -/
noncomputable def toEuclidDiffeo :
    Diffeomorph I I ConfigurationSpace (EuclideanSpace ℝ (Fin 1)) ω where
  toFun := toEuclidHomeo
  invFun := toEuclidHomeo.symm
  left_inv t := by rfl
  right_inv t := by simp
  contMDiff_toFun := by
    refine contMDiff_iff.mpr ⟨toEuclidHomeo.continuous, fun x y => ?_⟩
    simpa using contDiffOn_id
  contMDiff_invFun := by
    refine contMDiff_iff.mpr ⟨toEuclidHomeo.symm.continuous, fun x y => ?_⟩
    simpa using contDiffOn_id

lemma toEuclidHomeo_mem_atlas : toEuclidHomeo.toOpenPartialHomeomorph ∈
    atlas (EuclideanSpace ℝ (Fin 1)) ConfigurationSpace := by simp [atlas, ChartedSpace.atlas]

@[simp]
lemma chartAt_eq_toEuclidDiffeo (x : ConfigurationSpace) :
    chartAt (EuclideanSpace ℝ (Fin 1)) x  = toEuclidHomeo.toOpenPartialHomeomorph := rfl

lemma achart_eq_toEuclidDiffeo (x : ConfigurationSpace) :
    achart (EuclideanSpace ℝ (Fin 1)) x  =
    ⟨toEuclidHomeo.toOpenPartialHomeomorph, toEuclidHomeo_mem_atlas⟩ := rfl

/-!

## The tangent bundle of the configuration space

We show that the tangent bundle of `ConfigurationSpace` is equivalent to the product
`EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)`. We do this by
constructing first an equivalence, then a homeomorphism, and finally a diffeomorphism
between these two spaces.

-/

/-!

### The equivalence

-/

/-- The equivalence between the tangent space of `ConfigurationSpace` and the
  product `EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def toEuclidTangent :
    TangentBundle I ConfigurationSpace ≃ EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) where
  toFun x :=  ⟨toEuclidDiffeo x.1, x.2⟩
  invFun x := ⟨toEuclidDiffeo.symm x.1, x.2⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp

lemma toEuclidTangent_eq :
    (toEuclidTangent : _ → _) = fun x => (toEuclidDiffeo x.1, x.2) := rfl

lemma chartAt_tangent_eq_toEuclidTangent (x : TangentBundle I ConfigurationSpace) :
    (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) x).toFun =
    toEuclidTangent := by
  ext1 p
  simp only [FiberBundle.chartedSpace_chartAt, Homeomorph.toOpenPartialHomeomorph_source,
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq,
    OpenPartialHomeomorph.trans_toPartialEquiv, OpenPartialHomeomorph.prod_toPartialEquiv,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.coe_trans, PartialEquiv.prod_coe,
    OpenPartialHomeomorph.toFun_eq_coe, Homeomorph.toOpenPartialHomeomorph_apply,
    PartialEquiv.refl_coe, id_eq, Trivialization.coe_coe, Function.comp_apply,
    TangentBundle.trivializationAt_apply, OpenPartialHomeomorph.extend,
    modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl, OpenPartialHomeomorph.coe_coe_symm,
    Homeomorph.toOpenPartialHomeomorph_symm_apply, Homeomorph.self_comp_symm,
    modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ, fderiv_id,
    ContinuousLinearMap.coe_id']
  rfl

lemma chartAt_tangent_apply_eq_toEuclidTangent (x p : TangentBundle I ConfigurationSpace) :
    (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) x) p =
    toEuclidTangent p := by
  change (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) x).toFun p  = _
  rw [chartAt_tangent_eq_toEuclidTangent x]

lemma chartAt_invFun_tangent_eq_toEuclidTangent (x : TangentBundle I ConfigurationSpace) :
    (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) x).symm.toFun =
    toEuclidTangent.symm := by
  ext1 p
  obtain ⟨p', rfl⟩ := toEuclidTangent.surjective p
  simp only [OpenPartialHomeomorph.symm_toPartialEquiv, OpenPartialHomeomorph.coe_coe_symm,
    Equiv.symm_apply_apply]
  refine (OpenPartialHomeomorph.eq_symm_apply _ ?_ ?_).mp ?_
  · simp only [OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.symm_source]
    rw [TangentBundle.mem_chart_target_iff]
    simp
  · simp
  · simp [chartAt_tangent_apply_eq_toEuclidTangent]

@[fun_prop]
lemma toEuclidTangent_continuous : Continuous toEuclidTangent := by
  let x : TangentBundle I ConfigurationSpace := ⟨⟨0⟩, 0⟩
  let chart := chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) x
  have h_cont := chart.continuousOn_toFun
  simp at h_cont
  rw [← continuousOn_univ]
  convert h_cont
  · rw [← chartAt_tangent_eq_toEuclidTangent x]
    rfl
  · ext a
    simp [chart]

@[fun_prop]
lemma toEuclidTangent_symm_continuous : Continuous toEuclidTangent.symm := by
  let x : TangentBundle I ConfigurationSpace := ⟨⟨0⟩, 0⟩
  let chart := chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) x
  have h_cont := chart.continuousOn_invFun
  simp at h_cont
  rw [← continuousOn_univ]
  convert h_cont
  · rw [← chartAt_invFun_tangent_eq_toEuclidTangent x]
    rfl
  · ext a
    simp only [Set.mem_univ, true_iff, chart]
    rw [TangentBundle.mem_chart_target_iff]
    simp

/-!

### The homeomorphism

-/

/-- The homeomorphism between the tangent space of `ConfigurationSpace` and the
  product `EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def toEuclidTangentHomeo : TangentBundle I ConfigurationSpace ≃ₜ
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) where
  toEquiv := toEuclidTangent
  continuous_toFun := toEuclidTangent_continuous
  continuous_invFun := toEuclidTangent_symm_continuous

@[simp]
lemma chartAt_tangent_eq_toEuclidTangentHomeo {x : TangentBundle I ConfigurationSpace} :
    (chartAt (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) x) =
    toEuclidTangentHomeo.toOpenPartialHomeomorph := by
  ext1
  · exact congrFun (chartAt_tangent_eq_toEuclidTangent x) _
  · exact congrFun (chartAt_invFun_tangent_eq_toEuclidTangent x) _
  · ext a
    simp

/-!

### The diffeomorphism

-/

/-- The diffeomorphism between the tangent space of `ConfigurationSpace` and the
  product `EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)`. -/
noncomputable def toEuclidTangentDiffeo :
    Diffeomorph (.tangent I) (.prod I I)
      (TangentBundle I ConfigurationSpace)
      (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ω where
  toFun := toEuclidTangentHomeo
  invFun := toEuclidTangentHomeo.symm
  left_inv t := by rfl
  right_inv t := by simp
  contMDiff_toFun := by
    refine contMDiff_iff.mpr ⟨toEuclidTangent_continuous, fun x y => ?_⟩
    convert contDiffOn_id
    ext1 p
    simp [toEuclidTangentHomeo]
    exact toEuclidTangent.apply_symm_apply _
  contMDiff_invFun := by
    refine contMDiff_iff.mpr ⟨toEuclidTangent_symm_continuous, fun x y => ?_⟩
    convert contDiffOn_id
    ext1 p
    simp [toEuclidTangentHomeo]
    change toEuclidTangent _ = _
    simp

end ConfigurationSpace

end HarmonicOscillator

end ClassicalMechanics
