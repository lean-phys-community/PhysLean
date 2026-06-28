/-
Copyright (c) 2026 Nicola Bernini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Bernini, Nathaneal Sajan
-/
module

public import Physlib.SpaceAndTime.Space.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
/-!
# Configuration space of the harmonic oscillator

## i. Overview

The configuration space `Q` of the one-dimensional harmonic oscillator is the space of
possible positions of the oscillator, formalised here as a one-dimensional smooth manifold.

`Q` carries a single chosen global coordinate, modeled by `EuclideanSpace ℝ (Fin 1)`, from
which it inherits its algebraic, metric, inner-product and smooth-manifold structure.

## ii. Key results

- `ConfigurationSpace` : the configuration space, wrapping the chosen
  `EuclideanSpace ℝ (Fin 1)` coordinate.
- `ConfigurationSpace.valLinearIsometryEquiv` : the linear isometry identifying `Q` with
  its coordinate.
- the `InnerProductSpace ℝ ConfigurationSpace` and `IsManifold` instances, exhibiting `Q`
  as a one-dimensional real inner-product space and an analytic manifold.
- `ConfigurationSpace.toSpace` : the point of physical `Space 1` determined by a
  configuration.

## iii. Table of contents

- A. The configuration space type
- B. Algebraic structure
- C. Norm and metric structure
- D. Inner product structure
  - D.1. The inner product and inner-product-space instance
  - D.2. Smoothness of the inner product
- E. The coordinate isometry
- F. Smooth manifold structure
- G. Map to physical space
-/

@[expose] public section

namespace ClassicalMechanics

namespace HarmonicOscillator

TODO "The API around the configuration space
    should be improved to allow further development of a proper
    geometric model of the Harmonic Oscillator."

/-!
## A. The configuration space type

`ConfigurationSpace` wraps a single chosen global coordinate valued in
`EuclideanSpace ℝ (Fin 1)`. We record extensionality in this coordinate together with a
function-like coordinate access mirroring that of `EuclideanSpace ℝ (Fin 1)`.
-/

/-- The one-dimensional configuration space `Q` of the harmonic oscillator: the space of
possible positions of the oscillator, equipped with a single chosen global coordinate
modeled by `EuclideanSpace ℝ (Fin 1)`. -/
structure ConfigurationSpace where
  /-- The chosen global coordinate of the configuration, valued in
  `EuclideanSpace ℝ (Fin 1)`. -/
  val : EuclideanSpace ℝ (Fin 1)

namespace ConfigurationSpace

@[ext]
lemma ext {x y : ConfigurationSpace} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  subst h
  rfl

/-- A configuration may be applied like a function `Fin 1 → ℝ`, evaluating its
underlying coordinate. This mirrors the function-like use of `EuclideanSpace ℝ (Fin 1)`. -/
instance : CoeFun ConfigurationSpace (fun _ => Fin 1 → ℝ) where
  coe x := fun i => x.val i

lemma coe_apply (x : ConfigurationSpace) (i : Fin 1) : x i = x.val i := rfl

/-!
## B. Algebraic structure

The additive group, real scalar action and `Module ℝ` structure, each defined
coordinatewise on the underlying `EuclideanSpace ℝ (Fin 1)` value. Physically this is the
vector-space structure on displacements of the oscillator about a reference configuration.
-/

instance : Zero ConfigurationSpace := { zero := ⟨0⟩ }

instance : OfNat ConfigurationSpace 0 := { ofNat := ⟨0⟩ }

@[simp]
lemma zero_val : (0 : ConfigurationSpace).val = 0 := rfl

instance : Add ConfigurationSpace where
  add x y := ⟨x.val + y.val⟩

@[simp]
lemma add_val (x y : ConfigurationSpace) : (x + y).val = x.val + y.val := rfl

instance : Neg ConfigurationSpace where
  neg x := ⟨-x.val⟩

@[simp]
lemma neg_val (x : ConfigurationSpace) : (-x).val = -x.val := rfl

instance : Sub ConfigurationSpace where
  sub x y := ⟨x.val - y.val⟩

@[simp]
lemma sub_val (x y : ConfigurationSpace) : (x - y).val = x.val - y.val := rfl

instance : SMul ℝ ConfigurationSpace where
  smul r x := ⟨r • x.val⟩

@[simp]
lemma smul_val (r : ℝ) (x : ConfigurationSpace) : (r • x).val = r • x.val := rfl

instance : AddGroup ConfigurationSpace where
  add_assoc x y z := by ext; simp [add_assoc]
  zero_add x := by ext; simp [zero_add]
  add_zero x := by ext; simp [add_zero]
  neg_add_cancel x := by ext; simp [neg_add_cancel]
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : AddCommGroup ConfigurationSpace where
  add_comm x y := by ext; simp [add_comm]

instance : Module ℝ ConfigurationSpace where
  one_smul x := by ext; simp
  smul_add r x y := by ext; simp [smul_add]
  smul_zero r := by ext; simp
  add_smul r s x := by ext; simp [add_smul]
  mul_smul r s x := by ext; simp [mul_smul]
  zero_smul x := by ext; simp

/-!
## C. Norm and metric structure

The norm, distance and resulting `NormedAddCommGroup`/`NormedSpace ℝ` structure, all
inherited from the underlying Euclidean coordinate. The norm corresponds to a choice of
length unit on configuration space.
-/

noncomputable instance : Norm ConfigurationSpace where
  norm x := ‖x.val‖

@[simp]
lemma norm_val (x : ConfigurationSpace) : ‖x‖ = ‖x.val‖ := rfl

noncomputable instance : Dist ConfigurationSpace where
  dist x y := dist x.val y.val

@[simp]
lemma dist_val (x y : ConfigurationSpace) : dist x y = dist x.val y.val := rfl

noncomputable instance : SeminormedAddCommGroup ConfigurationSpace where
  dist_self x := by simp
  dist_comm x y := by simpa using dist_comm x.val y.val
  dist_triangle x y z := by simpa using dist_triangle x.val y.val z.val
  dist_eq x y := by
    rw [dist_val, dist_eq_norm, norm_val, add_val, neg_val,
      show -x.val + y.val = -(x.val - y.val) by abel, norm_neg]

noncomputable instance : NormedAddCommGroup ConfigurationSpace where
  eq_of_dist_eq_zero := by
    intro a b h
    have h' : dist a.val b.val = 0 := by simpa using h
    exact ext (dist_eq_zero.mp h')
  dist_eq x y := by
    rw [dist_val, dist_eq_norm, norm_val, add_val, neg_val,
      show -x.val + y.val = -(x.val - y.val) by abel, norm_neg]

instance : NormedSpace ℝ ConfigurationSpace where
  norm_smul_le r x := by
    simp [norm_val, smul_val, norm_smul]

/-!
## D. Inner product structure

### D.1. The inner product and inner-product-space instance

The inner product is that of the underlying Euclidean coordinate, making
`ConfigurationSpace` a real inner-product space. Physically this is the metric used to form
kinetic energy and to identify configuration space with its dual.
-/

open InnerProductSpace

noncomputable instance : Inner ℝ ConfigurationSpace where
  inner x y := ⟪x.val, y.val⟫_ℝ

@[simp]
lemma inner_def (x y : ConfigurationSpace) : ⟪x, y⟫_ℝ = ⟪x.val, y.val⟫_ℝ := rfl

noncomputable instance : InnerProductSpace ℝ ConfigurationSpace where
  norm_sq_eq_re_inner x := by
    simp [inner_def, norm_val]
  conj_inner_symm x y := by
    simpa [inner_def] using inner_conj_symm (𝕜 := ℝ) x.val y.val
  add_left x y z := by
    simpa [inner_def, add_val] using inner_add_left (𝕜 := ℝ) x.val y.val z.val
  smul_left x y r := by
    simpa [inner_def, smul_val] using inner_smul_left (𝕜 := ℝ) x.val y.val r

/-!
### D.2. Smoothness of the inner product

The self-inner-product `q ↦ ⟪q, q⟫` is differentiable and smooth of every order. These
lemmas are tagged `@[fun_prop]` so the `fun_prop` automation can discharge differentiability
side-goals about it.
-/

@[fun_prop]
lemma differentiable_inner_self :
    Differentiable ℝ (fun x : ConfigurationSpace => ⟪x, x⟫_ℝ) := by
  have h_id : Differentiable ℝ (fun x : ConfigurationSpace => x) := differentiable_id
  simpa using (Differentiable.inner (𝕜:=ℝ) (f:=fun x : ConfigurationSpace => x)
    (g:=fun x : ConfigurationSpace => x) h_id h_id)

@[fun_prop]
lemma differentiableAt_inner_self (x : ConfigurationSpace) :
    DifferentiableAt ℝ (fun y : ConfigurationSpace => ⟪y, y⟫_ℝ) x := by
  have h_id : DifferentiableAt ℝ (fun y : ConfigurationSpace => y) x := differentiableAt_id
  simpa using (DifferentiableAt.inner (𝕜:=ℝ) (f:=fun y : ConfigurationSpace => y)
    (g:=fun y : ConfigurationSpace => y) h_id h_id)

@[fun_prop]
lemma contDiff_inner_self (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : ConfigurationSpace => ⟪x, x⟫_ℝ) := by
  have h_id : ContDiff ℝ n (fun x : ConfigurationSpace => x) := contDiff_id
  simpa using (ContDiff.inner (𝕜:=ℝ) (f:=fun x : ConfigurationSpace => x)
    (g:=fun x : ConfigurationSpace => x) h_id h_id)

/-!
## E. The coordinate isometry

`ConfigurationSpace` is linearly isometric to its `EuclideanSpace ℝ (Fin 1)` coordinate.
Because the norm is defined to be that of the coordinate, the identification is
definitional, and it supplies the homeomorphism underlying the manifold chart.
-/

/-- The configuration space is linearly isometric to its `EuclideanSpace ℝ (Fin 1)`
coordinate, with the isometry given by `ConfigurationSpace.val`. Because the norm on
configuration space is defined to be that of the underlying coordinate, this isometry
is definitional. -/
noncomputable def valLinearIsometryEquiv : ConfigurationSpace ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun := ConfigurationSpace.val
  invFun v := ⟨v⟩
  map_add' x y := rfl
  map_smul' r x := rfl
  left_inv x := by cases x; rfl
  right_inv v := rfl
  norm_map' x := rfl

/-- Homeomorphism between configuration space and its `EuclideanSpace ℝ (Fin 1)`
coordinate, induced by the linear isometry `valLinearIsometryEquiv`. This underlies the
chart used to give `ConfigurationSpace` its smooth-manifold structure. -/
noncomputable def valHomeomorphism : ConfigurationSpace ≃ₜ EuclideanSpace ℝ (Fin 1) :=
  valLinearIsometryEquiv.toHomeomorph

/-!
## F. Smooth manifold structure

`ConfigurationSpace` is an analytic manifold modeled on `EuclideanSpace ℝ (Fin 1)`, via the
single global chart `valHomeomorphism`. With one chart the only coordinate change is the
chart's self-transition, which is analytic, so chart compatibility is immediate. We also
record that `Q` is finite-dimensional and complete.
-/

/-- The structure of a charted space on `ConfigurationSpace`, modeled on its
`EuclideanSpace ℝ (Fin 1)` coordinate via the single global chart `valHomeomorphism`. -/
noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) ConfigurationSpace where
  atlas := { valHomeomorphism.toOpenPartialHomeomorph }
  chartAt _ := valHomeomorphism.toOpenPartialHomeomorph
  mem_chart_source := by
    simp
  chart_mem_atlas := by
    intro x
    simp

open Manifold ContDiff

/-- The structure of a smooth manifold on `ConfigurationSpace`. With a single global
chart, the only coordinate change is the chart's self-transition, which is analytic. -/
noncomputable instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ω ConfigurationSpace where
  compatible := by
    intro e1 e2 h1 h2
    simp [atlas, ChartedSpace.atlas] at h1 h2
    subst h1 h2
    exact symm_trans_mem_contDiffGroupoid valHomeomorphism.toOpenPartialHomeomorph

instance : FiniteDimensional ℝ ConfigurationSpace :=
  LinearEquiv.finiteDimensional valLinearIsometryEquiv.symm.toLinearEquiv

instance : CompleteSpace ConfigurationSpace := by
  classical
  simpa using (FiniteDimensional.complete ℝ ConfigurationSpace)

/-!
## G. Map to physical space

The point of one-dimensional physical `Space 1` determined by a configuration, obtained by
reading off the underlying coordinate. This links the abstract configuration space to the
concrete coordinate model.
-/

/-- The position in one-dimensional space associated to the configuration. -/
def toSpace (q : ConfigurationSpace) : Space 1 := ⟨fun i => q.val i⟩

lemma toSpace_apply (q : ConfigurationSpace) (i : Fin 1) : q.toSpace i = q.val i := rfl

end ConfigurationSpace

end HarmonicOscillator

end ClassicalMechanics
