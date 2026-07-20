/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import QuantumInfo.ForMathlib.SionMinimax

@[expose] public section

--TODO go elsewhere
attribute [fun_prop] LowerSemicontinuous --UpperSemicontinuous
attribute [fun_prop] LowerSemicontinuousOn --UpperSemicontinuousOn
attribute [fun_prop] LowerSemicontinuous.lowerSemicontinuousOn
attribute [fun_prop] UpperSemicontinuous.upperSemicontinuousOn
attribute [fun_prop] Continuous.lowerSemicontinuous Continuous.upperSemicontinuous

attribute [fun_prop] QuasilinearOn QuasiconvexOn QuasiconcaveOn

attribute [fun_prop] QuasiconvexOn.sup
attribute [fun_prop] QuasiconcaveOn.inf
attribute [fun_prop] QuasiconcaveOn.inf

attribute [fun_prop] ConvexOn ConcaveOn

attribute [fun_prop] ConvexOn.quasiconvexOn ConcaveOn.quasiconcaveOn
attribute [fun_prop] LinearMap.convexOn LinearMap.concaveOn

theorem _root_.IsCompact.exists_isMinOn_lowerSemicontinuousOn {α β : Type*}
  [LinearOrder α] [TopologicalSpace α] [TopologicalSpace β] [ClosedIicTopology α]
  {s : Set β} (hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : LowerSemicontinuousOn f s) :
    ∃ x ∈ s, IsMinOn f s x :=
  hf.exists_isMinOn ne_s hs

@[fun_prop]
theorem LinearMap.quasilinearOn {E β 𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [PartialOrder β] [AddCommMonoid β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) :
    QuasilinearOn 𝕜 s f :=
  ⟨(f.convexOn hs).quasiconvexOn, (f.concaveOn hs).quasiconcaveOn⟩

@[fun_prop]
theorem LinearMap.quasiconvexOn {E β 𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [PartialOrder β] [AddCommMonoid β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) :
    QuasiconvexOn 𝕜 s f :=
  (f.quasilinearOn hs).left

@[fun_prop]
theorem LinearMap.quasiconcaveOn {E β 𝕜 : Type*} [Semiring 𝕜] [PartialOrder 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]
  [PartialOrder β] [AddCommMonoid β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]
  (f : E →ₗ[𝕜] β) {s : Set E} (hs : Convex 𝕜 s) :
    QuasiconcaveOn 𝕜 s f :=
  (f.quasilinearOn hs).right

--??
theorem continuous_stupid.{u_2, u_1} {M : Type u_1} [inst : NormedAddCommGroup M] [inst_1 : Module ℝ M]
  [inst_3 : ContinuousSMul ℝ M] {N : Type u_2} [inst_4 : NormedAddCommGroup N]
  [inst_5 : Module ℝ N]
  [FiniteDimensional ℝ M]
  (f : N →L[ℝ] M →L[ℝ] ℝ) :
    Continuous fun (x : N × M) ↦ (f x.1) x.2 := by
  have h_sum : Continuous (fun x : N × M ↦
      ∑ i, f x.1 (Module.finBasis ℝ M i) * ((Module.finBasis ℝ M).repr x.2) i) :=
    continuous_finsetSum _ fun i _ ↦ .mul (by fun_prop)
      (((Module.finBasis ℝ M).coord i).continuous_of_finiteDimensional.comp continuous_snd)
  convert h_sum with x
  rw [← (Module.finBasis ℝ M).sum_repr x.2, map_sum]
  simp [mul_comm]

/-- The minimax theorem, at the level of generality we need. For convex, compact, nonempty sets `S`
and `T`in a real topological vector space `M`, and a bilinear function `f` on M, we can exchange
the order of minimizing and maximizing. -/
theorem minimax
  {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  {N : Type*} [NormedAddCommGroup N] [Module ℝ N] [ContinuousAdd N] [ContinuousSMul ℝ N]
  (f : N →L[ℝ] M →L[ℝ] ℝ)
  (S : Set M) (T : Set N) (hS₁ : IsCompact S) (hT₁ : IsCompact T)
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)
    : ⨅ x : T, ⨆ y : S, f x y = ⨆ y : S, ⨅ x : T, f x y := by
  refine sion_minimax (f := (f · ·)) (S := T) (T := S) ?_ hT₁ hT₃ hS₃ ?_ ?_ ?_ hS₂ hT₂ ?_ ?_
  · exact fun y _ => (Continuous.lowerSemicontinuous (by fun_prop)).lowerSemicontinuousOn T
  · exact fun y _ => (Continuous.upperSemicontinuous (by fun_prop)).upperSemicontinuousOn S
  · exact fun y _ => LinearMap.quasiconvexOn (f := LinearMap.flip {
      toFun := fun x ↦ (f x).toLinearMap, map_add' := by simp, map_smul' := by simp} y) hT₂
  · exact fun x _ => LinearMap.quasiconcaveOn _ hS₂
  · rw [← Set.image_prod]
    exact (hT₁.prod hS₁).bddAbove_image (continuous_stupid f).continuousOn
  · rw [← Set.image_prod]
    exact (hT₁.prod hS₁).bddBelow_image (continuous_stupid f).continuousOn

/-- **Von-Neumann's Minimax Theorem**, specialized to bilinear forms. -/
theorem LinearMap.BilinForm.minimax
  {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  (f : LinearMap.BilinForm ℝ M)
  (S : Set M) (T : Set M) (hS₁ : IsCompact S) (hT₁ : IsCompact T)
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)
    : ⨅ x : T, ⨆ y : S, f x y = ⨆ y : S, ⨅ x : T, f x y :=
  _root_.minimax (LinearMap.toContinuousLinearMap {
    toFun := fun x ↦ (f x).toContinuousLinearMap, map_add' := by simp, map_smul' := by simp})
    S T hS₁ hT₁ hS₂ hT₂ hS₃ hT₃

/-- Convenience form of `LinearMap.BilinForm.minimax` with the order inf/sup arguments supplied to f flipped. -/
theorem LinearMap.BilinForm.minimax'
  {M : Type*} [NormedAddCommGroup M] [Module ℝ M] [ContinuousAdd M] [ContinuousSMul ℝ M] [FiniteDimensional ℝ M]
  (f : LinearMap.BilinForm ℝ M)
  (S : Set M) (T : Set M) (hS₁ : IsCompact S) (hT₁ : IsCompact T)
  (hS₂ : Convex ℝ S) (hT₂ : Convex ℝ T) (hS₃ : S.Nonempty) (hT₃ : T.Nonempty)
    : ⨆ x : S, ⨅ y : T, f x y = ⨅ y : T, ⨆ x : S, f x y :=
  (minimax f.flip S T hS₁ hT₁ hS₂ hT₂ hS₃ hT₃).symm
