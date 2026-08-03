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

/-!
## D. Induction principle
-/

section Induction

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Induction principle for `CompleteTensorProduct` combining those of `Completion`
  and `TensorProduct`. -/
@[elab_as_elim]
lemma induction_on {motive : E ⊗ₕ[𝕜] F → Prop} (z : E ⊗ₕ[𝕜] F)
    (zero : motive 0) (tmul : ∀ (x : E) (y : F), motive (x ⊗ₜ[𝕜] y))
    (add : ∀ x y : E ⊗[𝕜] F, motive x → motive y → motive ↑(x + y))
    (closed : IsClosed {x | motive x}) : motive z :=
  Completion.induction_on z closed fun x ↦ x.induction_on zero tmul add

end Induction

/-!
## D. Commutative
-/

section Commutative

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The complete tensor product of inner product spaces is commutative,
  up to linear isometry equivalence. -/
def comm : E ⊗ₕ[𝕜] F ≃ₗᵢ[𝕜] F ⊗ₕ[𝕜] E :=
  (TensorProduct.comm 𝕜 E F).extendOfIsometry tInclₗᵢ.toLinearMap tInclₗᵢ.toLinearMap
    denseRange_coe denseRange_coe (by simp)

@[simp]
lemma comm_symm : (comm 𝕜 E F).symm = comm 𝕜 F E := rfl

variable {𝕜 E F} in
@[simp]
lemma comm_coe (x : E ⊗[𝕜] F) : comm 𝕜 E F x = TensorProduct.comm 𝕜 E F x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ _

end Commutative

/-!
## E. Associative
-/

section Associative

lemma _root_.TensorProduct.denseRange_map
    {R 𝕜 : Type*} [CommSemiring R] [RCLike 𝕜] {σ₁₂ : R →+* 𝕜} [RingHomSurjective σ₁₂]
    {E : Type*} [AddCommMonoid E] [Module R E] {F : Type*} [AddCommMonoid F] [Module R F]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    {f : E →ₛₗ[σ₁₂] G} (hf : DenseRange f) {g : F →ₛₗ[σ₁₂] H} (hg : DenseRange g) :
    DenseRange (TensorProduct.map f g) := by
  intro x
  change x ∈ (TensorProduct.map f g).range.topologicalClosure
  refine x.induction_on (Submodule.zero_mem _) (fun a b ↦ ?_) (fun _ _ ↦ Submodule.add_mem _)
  refine map_mem_closure₂' (fun u ↦ ?_) (fun v ↦ ?_) (hf a) (hg b) ?_
  · refine Metric.continuous_iff.mpr fun v ε hε ↦ ⟨ε / (1 + ‖u‖), by positivity, fun s hs ↦ ?_⟩
    rw [dist_eq_norm, ← TensorProduct.tmul_sub, TensorProduct.norm_tmul] at *
    refine lt_of_le_of_lt (b := (1 + ‖u‖) * ‖s - v‖) ?_ ?_
    · exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg _)
    · exact (lt_div_iff₀' <| by positivity).mp hs
  · refine Metric.continuous_iff.mpr fun u ε hε ↦ ⟨ε / (1 + ‖v‖), by positivity, fun s hs ↦ ?_⟩
    rw [dist_eq_norm, ← TensorProduct.sub_tmul, TensorProduct.norm_tmul] at *
    refine lt_of_le_of_lt (b := ‖s - u‖ * (1 + ‖v‖)) ?_ ?_
    · exact mul_le_mul_of_nonneg_left (by norm_num) (norm_nonneg _)
    · exact (lt_div_iff₀ <| by positivity).mp hs
  · exact fun _ ⟨u, hu⟩ _ ⟨v, hv⟩ ↦ ⟨u ⊗ₜ v, by simp [hu, hv]⟩

variable (𝕜 : Type*) [RCLike 𝕜]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
variable (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- The compete tensor product of inner product spaces is associative,
  up to linear isometry equivalence. -/
def assoc : E ⊗ₕ[𝕜] F ⊗ₕ[𝕜] G ≃ₗᵢ[𝕜] E ⊗ₕ[𝕜] (F ⊗ₕ[𝕜] G) :=
  (TensorProduct.assoc 𝕜 E F G).extendOfIsometry
    (tInclₗᵢ.comp (tInclₗᵢ.rTensor G)).toLinearMap (tInclₗᵢ.comp (tInclₗᵢ.lTensor E)).toLinearMap
    (by
      rw [LinearIsometry.coe_toLinearMap, LinearIsometry.coe_comp]
      refine DenseRange.comp denseRange_coe ?_ tInclₗᵢ.continuous
      exact TensorProduct.denseRange_map denseRange_coe denseRange_id)
    (by
      rw [LinearIsometry.coe_toLinearMap, LinearIsometry.coe_comp]
      refine DenseRange.comp denseRange_coe ?_ tInclₗᵢ.continuous
      exact TensorProduct.denseRange_map denseRange_id denseRange_coe)
    fun _ ↦ by simp only [LinearIsometry.norm_map', TensorProduct.norm_assoc]

end Associative


end CompleteTensorProduct
end
