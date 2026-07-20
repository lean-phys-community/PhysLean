/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Dennj Osele
-/
module

public import QuantumInfo.Channels.Bundled
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Duals of matrix map

Definitions and theorems about the dual of a matrix map. -/

@[expose] public section

noncomputable section
open ComplexOrder
open scoped Kronecker

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
variable {R : Type*} [CommRing R]
variable {𝕜 : Type*} [RCLike 𝕜]

namespace MatrixMap

variable [DecidableEq dIn] [DecidableEq dOut] {M : MatrixMap dIn dOut 𝕜}

--This should be definable with LinearMap.adjoint, but that requires InnerProductSpace stuff
--that is currently causing issues and pains (tried `open scoped Frobenius`).

/-- The dual of a map between matrices, defined by `Tr[A M(B)] = Tr[(dual M)(A) B]`. Sometimes
 called the adjoint of the map instead. -/
@[irreducible]
def dual (M : MatrixMap dIn dOut R) : MatrixMap dOut dIn R :=
  let coordDual :=
    let iso1 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
    let iso2 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
    iso1 ∘ₗ LinearMap.dualMap M ∘ₗ iso2
  (Matrix.transposeLinearEquiv dIn dIn R R).toLinearMap ∘ₗ coordDual ∘ₗ
    (Matrix.transposeLinearEquiv dOut dOut R R).toLinearMap

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem Dual.trace_eq (M : MatrixMap dIn dOut R) (A : Matrix dIn dIn R) (B : Matrix dOut dOut R) :
    (M A * B).trace = (A * M.dual B).trace := by
  have hDualIn (X Y : Matrix dIn dIn R) :
      ((Matrix.stdBasis R dIn dIn).toDualEquiv Y.transpose) X = (X * Y).trace := by
    simp [Module.Basis.toDualEquiv_apply, Module.Basis.toDual, Matrix.trace, Matrix.mul_apply,
      Matrix.stdBasis, Fintype.sum_prod_type, mul_comm]
  have hDualOut (X Y : Matrix dOut dOut R) :
      ((Matrix.stdBasis R dOut dOut).toDualEquiv Y.transpose) X = (X * Y).trace := by
    simp [Module.Basis.toDualEquiv_apply, Module.Basis.toDual, Matrix.trace, Matrix.mul_apply,
      Matrix.stdBasis, Fintype.sum_prod_type, mul_comm]
  rw [← hDualOut (M A) B, ← hDualIn A (M.dual B)]
  simp [dual]

--all properties below should provable just from `inner_eq`, since the definition of `dual` itself
-- is pretty hairy (and maybe could be improved...)

/-- The dual of a `IsHermitianPreserving` map also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving.dual {M : MatrixMap dIn dOut ℂ} (h : M.IsHermitianPreserving) :
    M.dual.IsHermitianPreserving := by
  have key (y : Matrix dIn dIn ℂ) :
      M (Matrix.conjTranspose y) = Matrix.conjTranspose (M y) := by
    obtain ⟨a, b, ha, hb, rfl⟩ :
        ∃ a b : Matrix dIn dIn ℂ, a.IsHermitian ∧ b.IsHermitian ∧ a + Complex.I • b = y :=
      ⟨_, _, (realPart y).2, (imaginaryPart y).2, realPart_add_I_smul_imaginaryPart y⟩
    simp [map_add, map_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
      ha.eq, hb.eq, (h ha).eq, (h hb).eq]
  intro x hx
  refine Matrix.ext_iff_trace_mul_left.mpr fun A => ?_
  have h1 := congrArg star (Dual.trace_eq M A.conjTranspose x)
  simp only [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, ← key, hx.eq] at h1
  rw [Matrix.trace_mul_comm, Dual.trace_eq] at h1
  exact (Matrix.trace_mul_comm A _).trans h1.symm

open MatrixOrder
--TODO Cleanup, find home, abstract out to HermitianMats...?
theorem _root_.Matrix.PosSemidef.trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  open scoped Matrix in
  obtain ⟨C, rfl⟩ : ∃ C : Matrix n n 𝕜, B = Cᴴ * C :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.nonneg_iff_posSemidef.mpr hB)
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem IsPositive.dual {M : MatrixMap dIn dOut ℂ} (h : M.IsPositive) : M.dual.IsPositive := by
  intro x hx
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨IsHermitianPreserving.dual h.IsHermitianPreserving hx.1, fun v => ?_⟩
  have h0 := (h (Matrix.posSemidef_vecMulVec_self_star v)).trace_mul_nonneg hx
  rwa [Dual.trace_eq, Matrix.vecMulVec_mul, Matrix.trace_vecMulVec, dotProduct_comm,
    ← Matrix.dotProduct_mulVec] at h0

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem dual_Unital (h : M.IsTracePreserving) : M.dual.Unital := by
  refine Matrix.ext_iff_trace_mul_left.mpr fun A => ?_
  rw [← Dual.trace_eq, Matrix.mul_one, Matrix.mul_one, h A]

alias IsTracePreserving.dual := dual_Unital

/--
If two matrix maps satisfy the trace duality property, they are equal.
-/
lemma dual_unique
    (M : MatrixMap dIn dOut 𝕜) (M' : MatrixMap dOut dIn 𝕜)
    (h : ∀ A B, (M A * B).trace = (A * M' B).trace) : M.dual = M' :=
  LinearMap.ext fun B => Matrix.ext_iff_trace_mul_left.mpr fun A =>
    (Dual.trace_eq M A B).symm.trans (h A B)

/--
The Choi matrix of the dual map is the transpose of the reindexed Choi matrix of the original map.
-/
lemma dual_choi_matrix (M : MatrixMap dIn dOut 𝕜) :
    M.dual.choi_matrix = (M.choi_matrix.transpose).reindex (Equiv.prodComm dOut dIn) (Equiv.prodComm dOut dIn) := by
  ext ⟨j₁, i₁⟩ ⟨j₂, i₂⟩
  simpa [choi_matrix, Matrix.trace_single_mul, Matrix.trace_mul_single] using
    (Dual.trace_eq M (Matrix.single j₂ j₁ 1) (Matrix.single i₁ i₂ 1)).symm

/--
If the Choi matrix of a map is positive semidefinite, then the Choi matrix of its dual is also
positive semidefinite.
-/
lemma dual_choi_matrix_posSemidef_of_posSemidef (M : MatrixMap dIn dOut 𝕜) (h : M.choi_matrix.PosSemidef) :
    M.dual.choi_matrix.PosSemidef := by
  rw [dual_choi_matrix, Matrix.reindex_apply]
  exact h.transpose.submatrix _

/--
The dual of the identity map is the identity map.
-/
lemma dual_id : (MatrixMap.id dIn 𝕜).dual = MatrixMap.id dIn 𝕜 :=
  dual_unique _ _ fun _ _ => rfl

private theorem matrix_mem_span_kronecker {A C : Type*} [Fintype A] [Fintype C]
    [DecidableEq A] [DecidableEq C] (X : Matrix (A × C) (A × C) 𝕜) :
    X ∈ Submodule.span 𝕜
      (Set.range (fun p : (Matrix A A 𝕜 × Matrix C C 𝕜) => p.1 ⊗ₖ p.2)) := by
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun ⟨a₁, c₁⟩ _ =>
    Submodule.sum_mem _ fun ⟨a₂, c₂⟩ _ => ?_
  rw [show Matrix.single (a₁, c₁) (a₂, c₂) (X (a₁, c₁) (a₂, c₂)) =
      X (a₁, c₁) (a₂, c₂) • ((Matrix.single a₁ a₂ 1 : Matrix A A 𝕜) ⊗ₖ
        (Matrix.single c₁ c₂ 1 : Matrix C C 𝕜)) by
    simp [Matrix.single_kronecker_single, Matrix.smul_single]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(_, _), rfl⟩)

/--
The dual of a Kronecker product of maps is the Kronecker product of their duals.
-/
lemma dual_kron {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (M : MatrixMap A B 𝕜) (N : MatrixMap C D 𝕜) :
    (M ⊗ₖₘ N).dual = M.dual ⊗ₖₘ N.dual := by
  refine dual_unique _ _ fun X Y => ?_
  induction matrix_mem_span_kronecker X, matrix_mem_span_kronecker Y using
    Submodule.span_induction₂ with
  | mem_mem X Y hX hY =>
      obtain ⟨⟨x₁, x₂⟩, rfl⟩ := hX
      obtain ⟨⟨y₁, y₂⟩, rfl⟩ := hY
      simp [MatrixMap.kron_map_of_kron_state, ← Matrix.mul_kronecker_mul,
        Matrix.trace_kronecker, Dual.trace_eq M x₁ y₁, Dual.trace_eq N x₂ y₂]
  | zero_left => simp
  | zero_right => simp
  | add_left X₁ X₂ Y _ _ _ h₁ h₂ => simpa [map_add, Matrix.add_mul] using congrArg₂ (· + ·) h₁ h₂
  | add_right X Y₁ Y₂ _ _ _ h₁ h₂ => simpa [map_add, Matrix.mul_add] using congrArg₂ (· + ·) h₁ h₂
  | smul_left a X Y _ _ h => simpa [map_smul, smul_mul_assoc] using congrArg (a • ·) h
  | smul_right a X Y _ _ h => simpa [map_smul, Matrix.mul_smul] using congrArg (a • ·) h

--The dual of a CompletelyPositive map is always CP, more generally it's k-positive
-- see Lemma 3.1 of https://www.math.uwaterloo.ca/~krdavids/Preprints/CDPRpositivereal.pdf
theorem IsCompletelyPositive.dual {M : MatrixMap dIn dOut ℂ} (h : M.IsCompletelyPositive) : M.dual.IsCompletelyPositive := by
  intro n
  simpa [dual_kron, dual_id] using IsPositive.dual (h n)

/--
The composition of the dual of the inverse of the dual basis isomorphism with the dual basis
isomorphism is the evaluation map.
-/
lemma Module.Basis.dualMap_toDualEquiv_symm_comp_toDualEquiv {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] (b : Module.Basis ι R M) :
    b.toDualEquiv.symm.toLinearMap.dualMap ∘ₗ b.toDualEquiv.toLinearMap = (Module.evalEquiv R M).toLinearMap := by
  ext x f
  obtain ⟨g, rfl⟩ := b.toDualEquiv.surjective f
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.dualMap_apply, LinearEquiv.symm_apply_apply]
  simp [Module.Basis.toDual, mul_comm]

/--
The composition of the inverse of the dual basis isomorphism with the dual of the dual basis
isomorphism is the inverse of the evaluation map.
-/
lemma Module.Basis.toDualEquiv_symm_comp_dualMap_toDualEquiv {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] (b : Module.Basis ι R M) :
    b.toDualEquiv.symm.toLinearMap ∘ₗ b.toDualEquiv.toLinearMap.dualMap = (Module.evalEquiv R M).symm.toLinearMap := by
  ext f
  obtain ⟨y, rfl⟩ := (Module.evalEquiv R M).surjective f
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_eq]
  ext x
  simp [Module.Basis.toDual, Module.evalEquiv, Module.Dual.eval, mul_comm]

@[simp]
theorem dual_dual : M.dual.dual = M :=
  dual_unique _ _ fun A B => by
    rw [Matrix.trace_mul_comm, ← Dual.trace_eq, Matrix.trace_mul_comm]

end MatrixMap

namespace CPTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def dual (M : CPTPMap dIn dOut) : CPUMap dOut dIn where
  toLinearMap := M.map.dual
  unital := M.TP.dual
  cp := .dual M.cp

theorem dual_pos (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.dual T :=
  M.dual.pos_Hermitian hT

/-- The dual of a CPTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem dual.PTP_POVM (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.dual T ∧ M.dual T ≤ 1) :=
  ⟨M.dual.pos_Hermitian hT.1, by simpa using ContinuousOrderHomClass.map_monotone M.dual hT.2⟩

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_Dual (ℰ : CPTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.dual T) :=
  congr(Complex.re $(MatrixMap.Dual.trace_eq ℰ.map ρ.m T.mat))

end CPTPMap

section hermDual

set_option backward.isDefEq.respectTransparency false in
--PULLOUT to Bundled.lean. Also use this to improve the definitions in POVM.lean.
def HPMap.ofHermitianMat {dOut : Type*} (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) : HPMap dIn dOut where
  toFun x := f (realPart x) + Complex.I • f (imaginaryPart x)
  map_add' x y := by
    simp only [map_add, HermitianMat.mat_add, smul_add]
    abel
  map_smul' c m := by
    ext i j
    simp [realPart_smul, imaginaryPart_smul, Complex.ext_iff]
    constructor <;> ring
  HP _ h := (HermitianMat.H _).add (by simp [IsSelfAdjoint.imaginaryPart h])

set_option backward.isDefEq.respectTransparency false in
omit [Fintype dOut] in
--PULLOUT
@[simp]
theorem HPMap.linearMap_ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    LinearMapClass.linearMap (HPMap.ofHermitianMat f) = f := by
  ext1 ⟨x, hx⟩
  ext1
  simp [ofHermitianMat, HPMap.apply_hermitianMat_eq, HPMap.map,
    (show IsSelfAdjoint x from hx).imaginaryPart]
  exact congrArg _ (congrArg _ (selfAdjoint.realPart_coe (x := ⟨x, hx⟩)))

--PULLOUT
omit [Fintype dOut] in
@[simp]
theorem HPMap.ofHermitianMat_linearMap (f : HPMap dIn dOut ℂ) :
    ofHermitianMat (LinearMapClass.linearMap f) = f := by
  ext x : 2
  simp only [map, ofHermitianMat, instFunLike, LinearMap.coe_coe, HermitianMat.val_eq_coe,
    HermitianMat.mat_mk, LinearMap.coe_mk, AddHom.coe_mk, ← map_smul, ← map_add]
  exact congrArg _ (realPart_add_I_smul_imaginaryPart x)


variable (f : HPMap dIn dOut) (A : HermitianMat dIn ℂ)

--Can define one for HPMap's that has 'easier' definitional properties, uses the inner product
--structure, doesn't go through Module.Basis the same way. Requires the equivalence between ℝ-linear
--maps of HermitianMats and ℂ-linear maps of matrices.
def HPMap.hermDual : HPMap dOut dIn :=
  HPMap.ofHermitianMat (LinearMapClass.linearMap f).adjoint

@[simp]
theorem HPMap.hermDual_hermDual : f.hermDual.hermDual = f := by
  simp [hermDual]

open RealInnerProductSpace

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem HPMap.inner_hermDual (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ := by
  change ⟪(LinearMapClass.linearMap f) A, B⟫ = ⟪A, (LinearMapClass.linearMap f.hermDual) B⟫
  rw [hermDual, ← LinearMap.adjoint_inner_right, HPMap.linearMap_ofHermitianMat]

/-- Version of `HPMap.inner_hermDual` that uses HermitiaMat.inner directly. TODO cleanup -/
theorem HPMap.inner_hermDual' (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ :=
  HPMap.inner_hermDual f A B

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem MatrixMap.IsPositive.hermDual (h : MatrixMap.IsPositive f.map) : f.hermDual.map.IsPositive := by
  intro x hx
  change Matrix.PosSemidef (f.hermDual ⟨x, hx.1⟩).mat
  classical
  rw [← HermitianMat.zero_le_iff, HermitianMat.nonneg_iff_inner_nonneg]
  intro y hy
  rw [HPMap.inner_hermDual, HPMap.hermDual_hermDual]
  exact HermitianMat.inner_ge_zero (HermitianMat.zero_le_iff.mpr hx)
    (HermitianMat.zero_le_iff.mpr (h (HermitianMat.zero_le_iff.mp hy)))

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem HPMap.hermDual_Unital [DecidableEq dIn] [DecidableEq dOut] (h : MatrixMap.IsTracePreserving f.map) :
    f.hermDual.map.Unital := by
  --todo: make this is an accessible 'constructor' for Unital
  refine HermitianMat.ext_iff.mp (?_ : f.hermDual 1 = 1)
  open RealInnerProductSpace in
  refine ext_inner_left ℝ fun v => ?_
  rw [← HPMap.inner_hermDual, HermitianMat.inner_one, HermitianMat.inner_one] --TODO Inner.inner
  exact congr(Complex.re $(h v)) --TODO: HPMap with IsTracePreserving give the HermitianMat.trace version

alias MatrixMap.IsTracePreserving.hermDual := HPMap.hermDual_Unital

namespace PTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def hermDual (M : PTPMap dIn dOut) : PUMap dOut dIn where
  toHPMap := M.toHPMap.hermDual
  pos := M.pos.hermDual
  unital := M.TP.hermDual

theorem hermDual_pos (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.hermDual T :=
  M.hermDual.pos_Hermitian hT

/-- The dual of a PTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem hermDual.PTP_POVM (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.hermDual T ∧ M.hermDual T ≤ 1) :=
  ⟨M.hermDual.pos_Hermitian hT.1,
    by simpa using ContinuousOrderHomClass.map_monotone M.hermDual hT.2⟩

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_hermDual (ℰ : PTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.hermDual T) :=
  HPMap.inner_hermDual' _ _ _

end PTPMap

end hermDual
