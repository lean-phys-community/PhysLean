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
end CompleteTensorProduct
end
