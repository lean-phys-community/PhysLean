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

end
