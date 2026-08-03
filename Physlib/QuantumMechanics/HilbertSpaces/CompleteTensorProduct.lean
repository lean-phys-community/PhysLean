/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Normed.Operator.Extend
/-!

# Complete tensor product

-/

@[expose] public section

noncomputable section

open UniformSpace
open scoped InnerProductSpace TensorProduct

/-!
## A. Definition
-/

/-- The _completion_ of the tensor product of two inner product spaces `E` and `F` over `𝕜`.
  By construction this produces a Hilbert space. The localized notations are `E ⊗ₕ F`
  and `E ⊗ₕ[𝕜] F`, accessed by `open scoped CompleteTensorProduct`. -/
def CompleteTensorProduct (𝕜 : Type*) [RCLike 𝕜]
    (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] : Type _ := Completion (E ⊗[𝕜] F)
deriving NormedAddCommGroup, InnerProductSpace 𝕜, CompleteSpace

@[inherit_doc CompleteTensorProduct]
scoped[CompleteTensorProduct] infixl:100 " ⊗ₕ " => CompleteTensorProduct _

@[inherit_doc]
scoped[CompleteTensorProduct]
notation:100 E:100 " ⊗ₕ[" 𝕜 "] " F:101 => CompleteTensorProduct 𝕜 E F

namespace CompleteTensorProduct

/-!
## B. Nontrivial
-/

section Nontrivial

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Nontrivial E]
variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Nontrivial F]

instance _root_.TensorProduct.instNontrivial : Nontrivial (E ⊗[𝕜] F) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    obtain ⟨y, hy⟩ := exists_ne (0 : F)
    exact ⟨x ⊗ₜ y, 0, norm_pos_iff.mp (by simp [hx, hy])⟩

instance instNontrivial : Nontrivial (E ⊗ₕ[𝕜] F) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E ⊗[𝕜] F)
    exact ⟨Completion.coe' x, 0, fun h ↦ hx <| Completion.coe_eq_zero_iff.mp h⟩

end Nontrivial

/-!
## C. Coercions
-/

section Coercion

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable (c : 𝕜) (x y : E ⊗[𝕜] F)

/-- The map from the tensor product to its completion. -/
@[coe]
def coe' : E ⊗[𝕜] F → E ⊗ₕ[𝕜] F := Completion.coe'

/-- Coercion from `E ⊗[𝕜] F` to its completion. -/
instance : Coe (E ⊗[𝕜] F) (E ⊗ₕ[𝕜] F) := ⟨coe'⟩

lemma denseRange_coe : DenseRange (coe' : E ⊗[𝕜] F → E ⊗ₕ[𝕜] F) := Completion.denseRange_coe

@[norm_cast]
lemma coe_zero : (0 : E ⊗[𝕜] F) = (0 : E ⊗ₕ[𝕜] F) := rfl

variable {x} in
@[simp]
lemma coe_eq_zero_iff : (x : E ⊗ₕ[𝕜] F) = 0 ↔ x = 0 := Completion.coe_eq_zero_iff

@[norm_cast]
lemma coe_neg : (-x : E ⊗[𝕜] F) = (-x : E ⊗ₕ[𝕜] F) := Completion.coe_neg _

@[norm_cast]
lemma coe_sub : (x - y : E ⊗[𝕜] F) = (x - y : E ⊗ₕ[𝕜] F) := Completion.coe_sub _ _

@[norm_cast]
lemma coe_add : (x + y : E ⊗[𝕜] F) = (x + y : E ⊗ₕ[𝕜] F) := Completion.coe_add _ _

@[simp, norm_cast]
lemma coe_smul : (c • x : E ⊗[𝕜] F) = (c • x : E ⊗ₕ[𝕜] F) := Completion.coe_smul _ _

@[simp]
lemma inner_coe : ⟪(x : E ⊗ₕ[𝕜] F), (y : E ⊗ₕ[𝕜] F)⟫_𝕜 = ⟪x, y⟫_𝕜 := Completion.inner_coe _ _

@[simp]
lemma norm_coe : ‖(x : E ⊗ₕ[𝕜] F)‖ = ‖x‖ := Completion.norm_coe _

/-- The canonical embedding of the tensor product into its completion as a linear isometry. -/
def tInclₗᵢ : E ⊗[𝕜] F →ₗᵢ[𝕜] E ⊗ₕ[𝕜] F := Completion.toComplₗᵢ

@[simp]
lemma coe_tInclₗᵢ : ⇑(tInclₗᵢ : E ⊗ F →ₗᵢ[𝕜] E ⊗ₕ F) = coe' := rfl

/-- The canonical embedding of the tensor product into its completion as a continuous linear map. -/
def tInclL : E ⊗[𝕜] F →L[𝕜] E ⊗ₕ[𝕜] F := tInclₗᵢ.toContinuousLinearMap

@[simp]
lemma coe_tInclL : ⇑(tInclL : E ⊗ F →L[𝕜] E ⊗ₕ F) = coe' := rfl

@[simp]
lemma norm_tInclL [Nontrivial E] [Nontrivial F] : ‖(tInclL : E ⊗ F →L[𝕜] E ⊗ₕ F)‖ = 1 :=
  (tInclₗᵢ : E ⊗ F →ₗᵢ[𝕜] E ⊗ₕ F).norm_toContinuousLinearMap

end Coercion
end CompleteTensorProduct
end
