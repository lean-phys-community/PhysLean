/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Pseudo-inner product spaces

A `PseudoInnerProductSpace E` is a real topological vector space carrying a continuous symmetric
nondegenerate bilinear form. Dropping positivity from `InnerProductSpace ℝ E` has a structural
consequence: an indefinite form induces no norm, so it does not determine the topology of `E`.
The class can therefore be attached to a space that already carries one — `TangentSpace I x`, or
the fibres of a vector bundle — without creating a diamond.

Inheritance runs `InnerProductSpace ℝ E → PseudoInnerProductSpace E` and never the other way; see
`InnerProductSpace.toPseudoInnerProductSpace`.

## Main definitions

* `PseudoInnerProductSpace E` and `pseudoInner v w`.
* `PseudoInnerProductSpace.flatL`, `flatEquiv`, `sharpEquiv`, `sharpL`: the musical isomorphisms
  `♭ : E ≃L[ℝ] E⋆` and `♯ : E⋆ ≃L[ℝ] E`.
* `PseudoInnerProductSpace.dualPseudoInnerSL`: the induced form on `E⋆`, i.e. the inverse metric.

## Implementation notes

Nothing here mentions manifolds: the musical isomorphisms are linear algebra, proved once and
reused for tangent, normal and gauge bundles alike. Surjectivity of `♭` uses `[T2Space E]` and
`[FiniteDimensional ℝ E]`, under which every linear map out of `E` is continuous; in infinite
dimensions nondegeneracy does not make `♭` surjective.

## Acknowledgements

The design follows a proposal of Sébastien Gouëzel on Zulip: introduce a fibrewise class for a
continuous nondegenerate bilinear form, register an instance from `InnerProductSpace`, and weaken
`IsContMDiffRiemannianBundle` to it, so that Riemannian geometry is subsumed rather than
duplicated. See [Zulip](https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/The.20future.20of.20pseudo-Riemannian.20manifolds/with/619509253).

## Tags

pseudo-inner product, bilinear form, nondegenerate, musical isomorphism, index raising
-/

@[expose] public section

open Module

/-! ## Bilinear and quadratic forms of a continuous bilinear map -/

namespace ContinuousLinearMap

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The quadratic form `v ↦ b v v` of a continuous bilinear map. No symmetry is required: the
companion is `(v, w) ↦ b v w + b w v`. -/
noncomputable def toQuadraticForm (b : E →L[ℝ] E →L[ℝ] ℝ) : QuadraticForm ℝ E :=
  b.toBilinForm.toQuadraticMap

@[simp]
lemma toQuadraticForm_apply (b : E →L[ℝ] E →L[ℝ] ℝ) (v : E) : b.toQuadraticForm v = b v v := rfl

@[simp]
lemma toQuadraticForm_neg (b : E →L[ℝ] E →L[ℝ] ℝ) :
    (-b).toQuadraticForm = -b.toQuadraticForm := by
  ext v; simp

end ContinuousLinearMap

/-! ## The class -/

/-- A real topological vector space with a continuous symmetric nondegenerate bilinear form.

Positivity is not assumed, so the form induces no norm and the topology of `E` is independent
data. Every real inner product space is an instance, via
`InnerProductSpace.toPseudoInnerProductSpace`. -/
class PseudoInnerProductSpace (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] where
  /-- The pseudo-inner product, as a continuous bilinear map. -/
  pseudoInnerSL : E →L[ℝ] E →L[ℝ] ℝ
  /-- The pseudo-inner product is symmetric. -/
  pseudoInner_symm : ∀ v w : E, pseudoInnerSL v w = pseudoInnerSL w v
  /-- The pseudo-inner product is nondegenerate: a vector pairing to zero with everything is
  itself zero. -/
  pseudoInner_nondegenerate : ∀ v : E, (∀ w : E, pseudoInnerSL v w = 0) → v = 0

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The pseudo-inner product `⟪v, w⟫` of two vectors of a pseudo-inner product space. -/
noncomputable def pseudoInner [PseudoInnerProductSpace E] (v w : E) : ℝ :=
  PseudoInnerProductSpace.pseudoInnerSL v w

namespace PseudoInnerProductSpace

section Basic

variable [PseudoInnerProductSpace E]

lemma pseudoInnerSL_apply (v w : E) : pseudoInnerSL v w = pseudoInner v w := rfl

lemma pseudoInner_comm (v w : E) : pseudoInner v w = pseudoInner w v :=
  pseudoInner_symm v w

lemma eq_zero_of_pseudoInner_eq_zero {v : E} (h : ∀ w : E, pseudoInner v w = 0) : v = 0 :=
  pseudoInner_nondegenerate v h

lemma eq_zero_of_pseudoInner_right_eq_zero {w : E} (h : ∀ v : E, pseudoInner v w = 0) : w = 0 :=
  pseudoInner_nondegenerate w fun v ↦ (pseudoInner_comm w v).trans (h v)

@[simp] lemma pseudoInner_zero_left (w : E) : pseudoInner (0 : E) w = 0 := by
  simp [pseudoInner]

@[simp] lemma pseudoInner_zero_right (v : E) : pseudoInner v (0 : E) = 0 := by
  simp [pseudoInner]

lemma pseudoInner_add_left (u v w : E) :
    pseudoInner (u + v) w = pseudoInner u w + pseudoInner v w := by
  simp [pseudoInner]

lemma pseudoInner_add_right (u v w : E) :
    pseudoInner u (v + w) = pseudoInner u v + pseudoInner u w := by
  simp [pseudoInner]

lemma pseudoInner_smul_left (c : ℝ) (v w : E) :
    pseudoInner (c • v) w = c * pseudoInner v w := by
  simp [pseudoInner]

lemma pseudoInner_smul_right (c : ℝ) (v w : E) :
    pseudoInner v (c • w) = c * pseudoInner v w := by
  simp [pseudoInner]

end Basic

/-! ## Riemannian geometry as a special case -/

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Every real inner product space is a pseudo-inner product space: positive definiteness is in
particular nondegeneracy.

Registering this globally is what makes pseudo-Riemannian results subsume the Riemannian ones
instead of duplicating them. -/
noncomputable instance (priority := 100) _root_.InnerProductSpace.toPseudoInnerProductSpace :
    PseudoInnerProductSpace F where
  pseudoInnerSL := innerSL ℝ
  pseudoInner_symm v w := real_inner_comm w v
  pseudoInner_nondegenerate v hv := (inner_self_eq_zero (𝕜 := ℝ)).mp (hv v)

@[simp]
lemma pseudoInner_eq_inner (v w : F) : pseudoInner v w = inner ℝ v w := rfl

end InnerProduct

/-! ## The associated bilinear and quadratic forms -/

section Forms

variable [PseudoInnerProductSpace E]

variable (E) in
/-- The pseudo-inner product as a `LinearMap.BilinForm`, forgetting continuity. -/
noncomputable def toBilinForm : LinearMap.BilinForm ℝ E :=
  (PseudoInnerProductSpace.pseudoInnerSL (E := E)).toBilinForm

@[simp]
lemma toBilinForm_apply (v w : E) : toBilinForm E v w = pseudoInner v w := rfl

lemma toBilinForm_isSymm : (toBilinForm E).IsSymm :=
  ⟨fun v w ↦ by simpa using (pseudoInner_comm v w)⟩

lemma toBilinForm_nondegenerate : (toBilinForm E).Nondegenerate := by
  constructor
  · intro v hv
    exact eq_zero_of_pseudoInner_eq_zero fun w ↦ by simpa using hv w
  · intro w hw
    exact eq_zero_of_pseudoInner_right_eq_zero fun v ↦ by simpa using hw v

/-! ### Index lowering -/

variable (E) in
/-- Index lowering `♭ : v ↦ pseudoInner v ·`, as a continuous linear map `E →L[ℝ] E⋆`.

Definitionally the pseudo-inner product itself; the name records the geometric role. -/
abbrev flatL : E →L[ℝ] (E →L[ℝ] ℝ) := PseudoInnerProductSpace.pseudoInnerSL

@[simp]
lemma flatL_apply (v w : E) : flatL E v w = pseudoInner v w := rfl

lemma flatL_injective : Function.Injective (flatL E) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  exact eq_zero_of_pseudoInner_eq_zero fun w ↦ by
    simpa using congrFun (congrArg (fun f : E →L[ℝ] ℝ ↦ (f : E → ℝ)) hv) w

variable (E) in
/-- The quadratic form `v ↦ pseudoInner v v`. Its `QuadraticForm.sigNeg` is the index. -/
noncomputable def toQuadraticForm : QuadraticForm ℝ E :=
  (PseudoInnerProductSpace.pseudoInnerSL (E := E)).toQuadraticForm

@[simp]
lemma toQuadraticForm_apply (v : E) : toQuadraticForm E v = pseudoInner v v := rfl

end Forms

/-! ## Musical isomorphisms -/

section Dual

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E] [FiniteDimensional ℝ E]

variable (E) in
/-- On a finite-dimensional Hausdorff real topological vector space, the continuous dual `E⋆`
has the same dimension as `E`. -/
lemma finrank_dual_eq : finrank ℝ (E →L[ℝ] ℝ) = finrank ℝ E := by
  have h : (E →L[ℝ] ℝ) ≃ₗ[ℝ] Module.Dual ℝ E :=
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).symm
  rw [h.finrank_eq, Subspace.dual_finrank_eq]

end Dual

section Musical

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
  [FiniteDimensional ℝ E] [PseudoInnerProductSpace E]

lemma flatL_surjective : Function.Surjective (flatL E) :=
  (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_dual_eq E).symm).mp flatL_injective

lemma flatL_bijective : Function.Bijective (flatL E) :=
  ⟨flatL_injective, flatL_surjective⟩

variable (E) in
/-- The musical isomorphism `♭ : E ≃L[ℝ] E⋆`. -/
noncomputable def flatEquiv : E ≃L[ℝ] (E →L[ℝ] ℝ) :=
  LinearEquiv.toContinuousLinearEquiv <|
    LinearEquiv.ofBijective (flatL E).toLinearMap flatL_bijective

@[simp]
lemma flatEquiv_apply (v w : E) : flatEquiv E v w = pseudoInner v w := rfl

variable (E) in
/-- The musical isomorphism `♯ : E⋆ ≃L[ℝ] E`, inverse to `♭`. -/
noncomputable def sharpEquiv : (E →L[ℝ] ℝ) ≃L[ℝ] E := (flatEquiv E).symm

variable (E) in
/-- Index raising `♯ : E⋆ →L[ℝ] E`, as a continuous linear map. -/
noncomputable def sharpL : (E →L[ℝ] ℝ) →L[ℝ] E := (sharpEquiv E).toContinuousLinearMap

lemma sharpL_apply (ω : E →L[ℝ] ℝ) : sharpL E ω = sharpEquiv E ω := rfl

@[simp]
lemma sharpL_flatL (v : E) : sharpL E (flatL E v) = v :=
  (flatEquiv E).symm_apply_apply v

@[simp]
lemma flatL_sharpL (ω : E →L[ℝ] ℝ) : flatL E (sharpL E ω) = ω :=
  (flatEquiv E).apply_symm_apply ω

/-- Pairing with a raised covector is evaluation. -/
@[simp]
lemma pseudoInner_sharpL_right (v : E) (ω : E →L[ℝ] ℝ) :
    pseudoInner v (sharpL E ω) = ω v := by
  rw [pseudoInner_comm]
  exact congrFun (congrArg (fun f : E →L[ℝ] ℝ ↦ (f : E → ℝ)) (flatL_sharpL ω)) v

/-- Pairing with a raised covector is evaluation. -/
@[simp]
lemma pseudoInner_sharpL_left (v : E) (ω : E →L[ℝ] ℝ) :
    pseudoInner (sharpL E ω) v = ω v := by
  rw [pseudoInner_comm]; exact pseudoInner_sharpL_right v ω

/-! ### The induced form on the dual -/

variable (E) in
/-- The form induced on `E⋆` by raising both indices, `(ω₁, ω₂) ↦ ω₁ (ω₂♯)`.

For a metric tensor this is the inverse metric `g^{ab}`. -/
noncomputable def dualPseudoInnerSL : (E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E →L[ℝ] ℝ) (F' := (E →L[ℝ] ℝ) →L[ℝ] ℝ)
    { toFun := fun ω : E →L[ℝ] ℝ ↦ ω.comp (sharpL E)
      map_add' := fun ω₁ ω₂ ↦ by ext ω; simp
      map_smul' := fun c ω ↦ by ext ω'; simp }

@[simp]
lemma dualPseudoInnerSL_apply (ω₁ ω₂ : E →L[ℝ] ℝ) :
    dualPseudoInnerSL E ω₁ ω₂ = ω₁ (sharpL E ω₂) := rfl

lemma dualPseudoInnerSL_eq_pseudoInner_sharpL (ω₁ ω₂ : E →L[ℝ] ℝ) :
    dualPseudoInnerSL E ω₁ ω₂ = pseudoInner (sharpL E ω₁) (sharpL E ω₂) := by
  rw [dualPseudoInnerSL_apply, pseudoInner_sharpL_left]

lemma dualPseudoInnerSL_symm (ω₁ ω₂ : E →L[ℝ] ℝ) :
    dualPseudoInnerSL E ω₁ ω₂ = dualPseudoInnerSL E ω₂ ω₁ := by
  simp only [dualPseudoInnerSL_eq_pseudoInner_sharpL]
  exact pseudoInner_comm _ _

lemma dualPseudoInnerSL_nondegenerate (ω : E →L[ℝ] ℝ)
    (h : ∀ η : E →L[ℝ] ℝ, dualPseudoInnerSL E ω η = 0) : ω = 0 := by
  ext v
  simpa only [dualPseudoInnerSL_apply, sharpL_flatL, zero_apply]
    using h (flatL E v)

variable (E) in
/-- `E⋆` with the inverse form. Deliberately a `def`: as an instance it would let typeclass
inference loop through iterated duals. -/
@[reducible] noncomputable def dual : PseudoInnerProductSpace (E →L[ℝ] ℝ) where
  pseudoInnerSL := dualPseudoInnerSL E
  pseudoInner_symm := dualPseudoInnerSL_symm
  pseudoInner_nondegenerate := dualPseudoInnerSL_nondegenerate

end Musical

end PseudoInnerProductSpace
