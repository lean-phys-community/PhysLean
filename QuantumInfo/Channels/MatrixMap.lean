/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Module.LinearMap.Basic
public import QuantumInfo.ForMathlib.ContinuousLinearMap
public import QuantumInfo.ForMathlib.ComplexLaplaceTransform
public import QuantumInfo.ForMathlib.ContinuousSup
public import QuantumInfo.ForMathlib.Filter
public import QuantumInfo.ForMathlib.HermitianMat
public import QuantumInfo.ForMathlib.Isometry
public import QuantumInfo.ForMathlib.LinearEquiv
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.Minimax
public import QuantumInfo.ForMathlib.Misc
public import QuantumInfo.ForMathlib.Unitary
public import QuantumInfo.States.Pure.Braket
public import QuantumInfo.States.Mixed.MState

/-! # Linear maps of matrices

This file works with `MatrixMap`s, that is, linear maps from square matrices to square matrices.
Although this is just a shorthand for `Matrix A A R →ₗ[R] Matrix B B R`, there are several
concepts that specifically make sense in this context.

 * `toMatrix` is the rectangular "transfer matrix", where matrix multiplication commutes with map
   composition.
 * `choi_matrix` is the square "Choi matrix", see `MatrixMap.choi_PSD_iff_CP_map` for example usage
 * `kron` is the Kronecker product of matrix maps
 * `IsTracePreserving` states the trace of the output is always equal to the trace of the input.

We provide simp lemmas for relating these facts, prove basic facts e.g. composition and identity,
and some facts about `IsTracePreserving` maps.
-/

@[expose] public section

/-- A `MatrixMap` is a linear map between squares matrices of size A to size B, over R. -/
abbrev MatrixMap (A B R : Type*) [Semiring R] := Matrix A A R →ₗ[R] Matrix B B R

variable {A B C D E F R : Type*} [Fintype A] [DecidableEq A]

namespace MatrixMap
section matrix

variable [Semiring R]

variable (A R) in
/-- Alias of LinearMap.id, but specifically as a MatrixMap. -/
@[reducible]
def id : MatrixMap A A R := LinearMap.id

/-- Choi matrix of a given linear matrix map. Note that this is defined even for things that
  aren't CPTP, it's just rarely talked about in those contexts. This is the inverse of
  `MatrixMap.of_choi_matrix`. Compare with `MatrixMap.toMatrix`, which gives the transfer matrix. -/
def choi_matrix (M : MatrixMap A B R) : Matrix (B × A) (B × A) R :=
  fun (j₁,i₁) (j₂,i₂) ↦ M (Matrix.single i₁ i₂ 1) j₁ j₂

/-- Given the Choi matrix, generate the corresponding R-linear map between matrices as a
MatrixMap. This is the inverse of `MatrixMap.choi_matrix`. -/
def of_choi_matrix (M : Matrix (B × A) (B × A) R) : MatrixMap A B R where
  toFun X := fun b₁ b₂ ↦ ∑ (a₁ : A), ∑ (a₂ : A), X a₁ a₂ * M (b₁, a₁) (b₂, a₂)
  map_add' x y := by funext b₁ b₂; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r x := by
    funext b₁ b₂
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc]

/-- Proves that `MatrixMap.of_choi_matrix` and `MatrixMap.choi_matrix` inverses. -/
@[simp]
theorem map_choi_inv (M : Matrix (B × A) (B × A) R) : choi_matrix (of_choi_matrix M) = M := by
  ext ⟨i₁,i₂⟩ ⟨j₁,j₂⟩
  simp [of_choi_matrix, choi_matrix, Matrix.single, ite_and]

/-- Proves that `MatrixMap.choi_matrix` and `MatrixMap.of_choi_matrix` inverses. -/
@[simp]
theorem choi_map_inv (M : MatrixMap A B R) : of_choi_matrix (choi_matrix M) = M := by
  refine Matrix.ext_linearMap (R := R) fun i j => LinearMap.ext fun x => ?_
  ext b₁ b₂
  rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.singleLinearMap_apply,
    show Matrix.single i j x = x • Matrix.single i j 1 by simp, map_smul, map_smul]
  simp [of_choi_matrix, choi_matrix, Matrix.single, ite_and]

/-- The correspondence induced by `MatrixMap.of_choi_matrix` is injective. -/
theorem choi_matrix_inj : Function.Injective (@choi_matrix A B R _ _) :=
  Function.LeftInverse.injective choi_map_inv


variable {R : Type*} [CommSemiring R]

/-- The linear equivalence between linear maps of matrices,and Choi matrices.-/
@[simps]
def choi_equiv : MatrixMap A B R ≃ₗ[R] Matrix (B × A) (B × A) R where
  toFun := choi_matrix
  invFun := of_choi_matrix
  left_inv _ := by simp
  right_inv _ := by simp
  map_add' _ _ := by ext; simp [choi_matrix]
  map_smul' _ _ := by ext; simp [choi_matrix]

/-- The linear equivalence between MatrixMap's and transfer matrices on a larger space.
Compare with `MatrixMap.choi_matrix`, which gives the Choi matrix instead of the transfer matrix. -/
noncomputable def toMatrix [Fintype B] : MatrixMap A B R ≃ₗ[R] Matrix (B × B) (A × A) R :=
  LinearMap.toMatrix (Matrix.stdBasis R A A) (Matrix.stdBasis R B B)

/-- Multiplication of transfer matrices, `MatrixMap.toMatrix`, is equivalent to composition of maps. -/
theorem toMatrix_comp [Fintype B] [Fintype C] [DecidableEq B] (M₁ : MatrixMap A B R) (M₂ : MatrixMap B C R) : toMatrix (M₂ ∘ₗ M₁) = (toMatrix M₂) * (toMatrix M₁) :=
  LinearMap.toMatrix_comp _ _ _ M₂ M₁

end matrix

section kraus

variable [Star R] [CommSemiring R]
variable {κ : Type*} [Fintype κ]

/-- Construct a matrix map out of families of matrices M N : Σ → Matrix B A R
indexed by κ via X ↦ ∑ k : κ, (M k) * X * (N k)ᴴ -/
def of_kraus (M N : κ → Matrix B A R) : MatrixMap A B R :=
  ∑ k : κ, {
    toFun X := M k * X * (N k).conjTranspose
    map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
    map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
  }

end kraus

section kraus_exists

variable [CommSemiring R] [StarRing R] [Fintype B]

theorem exists_kraus (Φ : MatrixMap A B R) :
    ∃ r : ℕ, ∃ (M N : Fin r → Matrix B A R), Φ = of_kraus M N := by
  classical
  let K := ((B × A) × A) × B
  let M₀ : K → Matrix B A R := fun (((b, a₁), a₂), b₂) =>
    Matrix.single b a₁ (Φ (Matrix.single a₁ a₂ (1 : R)) b b₂)
  let N₀ : K → Matrix B A R := fun (((_, _), a₂), b₂) => Matrix.single b₂ a₂ (1 : R)
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin _).symm
  refine ⟨Fintype.card K, M₀ ∘ e, N₀ ∘ e, choi_matrix_inj ?_⟩
  ext ⟨j₁, i₁⟩ ⟨j₂, i₂⟩
  simp only [choi_matrix, of_kraus, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Function.comp_apply]
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_prod_type]
  simp [M₀, N₀, Matrix.sum_apply, Matrix.mul_apply, Matrix.single, ite_and, apply_ite]

end kraus_exists

section submatrix

variable {A B : Type*} (R : Type*) [Semiring R]

/-- The `MatrixMap` corresponding to applying a `submatrix` operation on each side. -/
@[simps]
def submatrix (f : B → A) : MatrixMap A B R where
  toFun x := x.submatrix f f
  map_add' := by simp [Matrix.submatrix_add]
  map_smul' := by simp [Matrix.submatrix_smul]

@[simp]
theorem submatrix_id : submatrix R _root_.id = id A R := by
  ext1; simp

@[simp]
theorem submatrix_comp (f : C → B) (g : B → A) :
    submatrix R f ∘ₗ submatrix R g = submatrix R (g ∘ f) := by
  ext1; simp

end submatrix

section kron
open Kronecker

variable {A B C D R : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [DecidableEq A] [DecidableEq C]

/-- The Kronecker product of MatrixMaps. Defined here using `TensorProduct.map M₁ M₂`, with
  appropriate reindexing operations and `LinearMap.toMatrix`/`Matrix.toLin`. Notation `⊗ₖₘ`. -/
noncomputable def kron [CommSemiring R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) : MatrixMap (A × C) (B × D) R :=
  let h₁ := (LinearMap.toMatrix (Module.Basis.tensorProduct  (Matrix.stdBasis R A A) (Matrix.stdBasis R C C))
      (Module.Basis.tensorProduct  (Matrix.stdBasis R B B) (Matrix.stdBasis R D D)))
    (TensorProduct.map M₁ M₂);
  let r₁ := Equiv.prodProdProdComm B B D D;
  let r₂ := Equiv.prodProdProdComm A A C C;
  let h₂ := Matrix.reindex r₁ r₂ h₁;
  Matrix.toLin (Matrix.stdBasis R (A × C) (A × C)) (Matrix.stdBasis R (B × D) (B × D)) h₂

scoped[MatrixMap] infixl:100 " ⊗ₖₘ " => MatrixMap.kron

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 60000 in
/-- The extensional definition of the Kronecker product `MatrixMap.kron`, in terms of the entries of
  its image. -/
theorem kron_def [CommSemiring R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) (M : Matrix (A × C) (A × C) R) :
    (M₁ ⊗ₖₘ M₂) M (b₁, d₁) (b₂, d₂) = ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂,
      (M₁ (Matrix.single a₁ a₂ 1) b₁ b₂) * (M₂ (Matrix.single c₁ c₂ 1) d₁ d₂) * (M (a₁, c₁) (a₂, c₂)) := by
  classical
  obtain ⟨hB, hD⟩ : (∀ (X : Matrix B B R) (p : B × B), (Matrix.stdBasis R B B).repr X p = X p.1 p.2)
      ∧ ∀ (X : Matrix D D R) (p : D × D), (Matrix.stdBasis R D D).repr X p = X p.1 p.2 := by
    constructor <;> intro X p <;>
      simp [Matrix.stdBasis, Module.Basis.map_repr, Module.Basis.repr_reindex, Pi.basis_repr]
  induction M using Matrix.induction_on' with
  | h_zero => simp
  | h_add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | h_std_basis i j x =>
    obtain ⟨a₁, c₁⟩ := i
    obtain ⟨a₂, c₂⟩ := j
    simp only [kron]
    rw [show Matrix.single (a₁, c₁) (a₂, c₂) x = x • Matrix.single (a₁, c₁) (a₂, c₂) 1 by simp,
      ← Matrix.stdBasis_eq_single (R := R), map_smul, Matrix.toLin_self]
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.prodProdProdComm_symm, Equiv.prodProdProdComm_apply, LinearMap.toMatrix_apply,
      Module.Basis.tensorProduct_apply, TensorProduct.map_tmul,
      Module.Basis.tensorProduct_repr_tmul_apply, hB, hD, Matrix.stdBasis_eq_single]
    simp [Matrix.single, ite_and, Fintype.sum_prod_type, Matrix.stdBasis_eq_single]
    ring

section kron_lemmas
variable [CommSemiring R]

theorem add_kron (ML₁ ML₂ : MatrixMap A B R) (MR : MatrixMap C D R) : (ML₁ + ML₂) ⊗ₖₘ MR = ML₁ ⊗ₖₘ MR + ML₂ ⊗ₖₘ MR := by
  simp [kron, TensorProduct.map_add_left, Matrix.submatrix_add]

theorem kron_add (ML : MatrixMap A B R) (MR₁ MR₂ : MatrixMap C D R) : ML ⊗ₖₘ (MR₁ + MR₂) = ML ⊗ₖₘ MR₁ + ML ⊗ₖₘ  MR₂ := by
  simp [kron, TensorProduct.map_add_right, Matrix.submatrix_add]

theorem smul_kron (r : R) (ML : MatrixMap A B R) (MR : MatrixMap C D R) : (r • ML) ⊗ₖₘ MR = r • (ML ⊗ₖₘ MR) := by
  simp [kron, TensorProduct.map_smul_left, Matrix.submatrix_smul]

theorem kron_smul (r : R) (ML : MatrixMap A B R) (MR : MatrixMap C D R) : ML ⊗ₖₘ (r • MR) = r • (ML ⊗ₖₘ MR) := by
  simp [kron, TensorProduct.map_smul_right, Matrix.submatrix_smul]

@[simp]
theorem zero_kron (MR : MatrixMap C D R) : (0 : MatrixMap A B R) ⊗ₖₘ MR = 0 := by
  simp [kron]

@[simp]
theorem kron_zero (ML : MatrixMap A B R) : ML ⊗ₖₘ (0 : MatrixMap C D R) = 0 := by
  simp [kron]

variable [DecidableEq B] in
theorem kron_id_id : (id A R ⊗ₖₘ id B R) = id (A × B) R := by
  simp [kron]

variable {Dl₁ Dl₂ Dl₃ Dr₁ Dr₂ Dr₃ : Type*}
  [Fintype Dl₁] [Fintype Dl₂] [Fintype Dl₃] [Fintype Dr₁] [Fintype Dr₂] [Fintype Dr₃]
  [DecidableEq Dl₁] [DecidableEq Dl₂] [DecidableEq Dr₁] [DecidableEq Dr₂] in
/-- For maps L₁, L₂, R₁, and R₂, the product (L₂ ∘ₗ L₁) ⊗ₖₘ (R₂ ∘ₗ R₁) = (L₂ ⊗ₖₘ R₂) ∘ₗ (L₁ ⊗ₖₘ R₁) -/
theorem kron_comp_distrib (L₁ : MatrixMap Dl₁ Dl₂ R) (L₂ : MatrixMap Dl₂ Dl₃ R) (R₁ : MatrixMap Dr₁ Dr₂ R)
    (R₂ : MatrixMap Dr₂ Dr₃ R) : (L₂ ∘ₗ L₁) ⊗ₖₘ (R₂ ∘ₗ R₁) = (L₂ ⊗ₖₘ R₂) ∘ₗ (L₁ ⊗ₖₘ R₁) := by
  simp [kron, TensorProduct.map_comp, ← Matrix.toLin_mul, Matrix.submatrix_mul_equiv, ← LinearMap.toMatrix_comp]

end kron_lemmas

-- /-- The canonical tensor product on linear maps between matrices, where a map from
--   M[A,B] to M[C,D] is given by M[A×C,B×D]. This tensor product acts independently on
--   Kronecker products and gives Kronecker products as outputs. -/
--   def matrixMap_kron (M₁ : Matrix (A₁ × B₁) (C₁ × D₁) R) (M₂ : Matrix (A₂ × B₂) (C₂ × D₂) R) :
--   Matrix ((A₁ × A₂) × (B₁ × B₂)) ((C₁ × C₂) × (D₁ × D₂)) R := Matrix.of fun ((a₁, a₂), (b₁, b₂))
--   ((c₁, c₂), (d₁, d₂)) ↦ (M₁ (a₁, b₁) (c₁, d₁)) * (M₂ (a₂, b₂) (c₂, d₂))

/-- The operational definition of the Kronecker product `MatrixMap.kron`, that it maps a Kronecker
  product of inputs to the Kronecker product of outputs. It is the unique bilinear map doing so. -/
theorem kron_map_of_kron_state [CommRing R] (M₁ : MatrixMap A B R) (M₂ : MatrixMap C D R) (MA : Matrix A A R) (MC : Matrix C C R) : (M₁ ⊗ₖₘ M₂) (MA ⊗ₖ MC) = (M₁ MA) ⊗ₖ (M₂ MC) := by
  induction MA using Matrix.induction_on' with
  | h_zero => simp
  | h_add p q hp hq => simp [Matrix.add_kronecker, map_add, hp, hq]
  | h_std_basis a₁ a₂ x =>
    induction MC using Matrix.induction_on' with
    | h_zero => simp
    | h_add p q hp hq => simp [Matrix.kronecker_add, map_add, hp, hq]
    | h_std_basis c₁ c₂ y =>
      ext ⟨b₁, d₁⟩ ⟨b₂, d₂⟩
      rw [Matrix.single_kronecker_single, kron_def,
        show Matrix.single a₁ a₂ x = x • Matrix.single a₁ a₂ 1 by simp,
        show Matrix.single c₁ c₂ y = y • Matrix.single c₁ c₂ 1 by simp, map_smul, map_smul]
      simp [Matrix.single, ite_and]
      ring

theorem choi_matrix_state_rep {B : Type*} [Fintype B] [Nonempty A] (M : MatrixMap A B ℂ) :
    M.choi_matrix = (↑(Fintype.card (α := A)) : ℂ) • (M ⊗ₖₘ (LinearMap.id : MatrixMap A A ℂ)) (MState.pure (Ket.MES A)).m := by
  ext ⟨b, a⟩ ⟨b', a'⟩
  simp [Matrix.smul_apply, kron_def, choi_matrix, Ket.MES, Ket.apply, Matrix.single, ite_and,
    apply_ite]
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (Fintype.card A).cast_nonneg']
  field_simp
  norm_cast

theorem submatrix_kron_submatrix [CommSemiring R] (f : B → A) (g : D → C) :
    submatrix R f ⊗ₖₘ submatrix R g = submatrix R (Prod.map f g) := by
  ext m ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  simp [kron_def, Prod.map, Matrix.single, ite_and]

theorem submatrix_kron_id [CommSemiring R] (f : B → A) :
    submatrix R f ⊗ₖₘ id C R = submatrix R (Prod.map f _root_.id) := by
  simp [← submatrix_kron_submatrix]

theorem id_kron_submatrix [CommSemiring R] (f : B → A) :
    id C R ⊗ₖₘ submatrix R f = submatrix R (Prod.map _root_.id f) := by
  simp [← submatrix_kron_submatrix]

end kron

section pi
variable {R : Type*} [CommSemiring R]
variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable {dI : ι → Type v} [∀i, Fintype (dI i)] [∀i, DecidableEq (dI i)]
variable {dO : ι → Type w} [∀i, Fintype (dO i)] [∀i, DecidableEq (dO i)]

/-- Finite Pi-type tensor product of MatrixMaps. Defined as `PiTensorProduct.tprod` of the
  underlying Linear maps. Notation `⨂ₜₘ[R] i, f i`, eventually. -/
noncomputable def piProd (Λi : ∀ i, MatrixMap (dI i) (dO i) R) : MatrixMap (∀i, dI i) (∀i, dO i) R :=
  Matrix.toLin
    (Matrix.stdBasis R ((i:ι) → dI i) ((i:ι) → dI i))
    (Matrix.stdBasis R ((i:ι) → dO i) ((i:ι) → dO i))
    (Matrix.reindex (Equiv.arrowProdEquivProdArrow _ dO dO)
      (Equiv.arrowProdEquivProdArrow _ dI dI)
      (LinearMap.toMatrix
        (_root_.Basis.piTensorProduct (fun i ↦ Matrix.stdBasis R (dI i) (dI i)))
        (_root_.Basis.piTensorProduct (fun i ↦ Matrix.stdBasis R (dO i) (dO i)))
        (PiTensorProduct.map Λi)))

theorem choi_matrix_piProd (Λi : ∀ i, MatrixMap (dI i) (dO i) R) :
    (MatrixMap.piProd Λi).choi_matrix =
      Matrix.reindex
        (Equiv.arrowProdEquivProdArrow ι dO dI)
        (Equiv.arrowProdEquivProdArrow ι dO dI)
        (Matrix.piProd (fun i => (Λi i).choi_matrix)) := by
  ext x y
  simp [MatrixMap.choi_matrix, Matrix.piProd]
  rw [MatrixMap.piProd, ← Matrix.stdBasis_eq_single (R := R) x.2 y.2,
    Matrix.toLin_self, Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [Matrix.smul_apply, Matrix.stdBasis_eq_single, Matrix.single, Matrix.of_apply,
    ite_and, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp [Matrix.reindex_apply, LinearMap.toMatrix_apply, Matrix.stdBasis, Matrix.single, ite_and,
    ← Matrix.single_eq_of_single_single]

-- notation3:100 "⨂ₜₘ "(...)", "r:(scoped f => tprod R f) => r
-- syntax (name := bigsum) "∑ " bigOpBinders ("with " term)? ", " term:67 : term

/--
Composition of `MatrixMap.piProd` maps distributes over the tensor product.
-/
theorem piProd_comp
  {d₁ d₂ d₃ : ι → Type*}
  [∀ i, Fintype (d₁ i)] [∀ i, DecidableEq (d₁ i)]
  [∀ i, Fintype (d₂ i)] [∀ i, DecidableEq (d₂ i)]
  [∀ i, Fintype (d₃ i)] [∀ i, DecidableEq (d₃ i)]
  (Λ₁ : ∀ i, MatrixMap (d₁ i) (d₂ i) R) (Λ₂ : ∀ i, MatrixMap (d₂ i) (d₃ i) R) :
    piProd (fun i ↦ (Λ₂ i) ∘ₗ (Λ₁ i)) = (piProd Λ₂) ∘ₗ (piProd Λ₁) := by
  simp [piProd, PiTensorProduct.map_comp, ← Matrix.toLin_mul, ← LinearMap.toMatrix_comp]

@[simp]
theorem piProd_id :
    piProd (fun i ↦ (LinearMap.id : MatrixMap (dI i) (dI i) R)) = LinearMap.id := by
  simp [piProd, PiTensorProduct.map_id, Matrix.submatrix_one_equiv]

end pi
