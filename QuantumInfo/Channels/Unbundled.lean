/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.MatrixMap
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-! # Properties of Matrix Maps

Building on `MatrixMap`s, this defines the properties: `IsTracePreserving`, `Unital`,
`IsHermitianPreserving`, `IsPositive` and `IsCompletelyPositive`. They have basic facts
such as closure under composition, addition, and scaling.

These are the *unbundled* versions, which just state the relevant properties of a given `MatrixMap`.
The bundled versions are `HPMap`, `UnitalMap`, `TPMap`, `PMap`, and `CPMap` respectively, given
in Bundled.lean.
-/

@[expose] public section

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator CStarAlgebra

namespace MatrixMap

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable {κ 𝕜 : Type*} [Fintype κ] [RCLike 𝕜]

section tp

variable {R : Type*} [Semiring R]
variable {M : MatrixMap A B R} {M₂ : MatrixMap B C R}

/-- A linear matrix map is *trace preserving* if trace of the output equals trace of the input. -/
def IsTracePreserving (M : MatrixMap A B R) : Prop :=
  ∀ (x : Matrix A A R), (M x).trace = x.trace

/-- A map is trace preserving iff the partial trace of the Choi matrix is the identity. -/
theorem IsTracePreserving_iff_trace_choi [DecidableEq A] (M : MatrixMap A B R) : M.IsTracePreserving
    ↔ M.choi_matrix.traceLeft = 1 := by
  constructor
  · intro h
    ext a₁ a₂
    replace h := h (Matrix.single a₁ a₂ 1)
    simp only [Matrix.trace, Matrix.diag] at h
    simp [Matrix.traceLeft, choi_matrix, h, Matrix.single_apply, Matrix.one_apply, eq_comm]
    split_ifs with hc <;> simp [hc, Finset.filter_and, Finset.filter_eq]
  · intro h X
    replace h := fun (a₁ a₂ : A) ↦ congrFun₂ h a₁ a₂
    simp [Matrix.traceLeft, Matrix.trace] at h ⊢
    rw [← M.choi_map_inv, of_choi_matrix]
    dsimp
    rw [Finset.sum_comm_cycle, Finset.sum_comm_cycle]
    simp [← Finset.mul_sum, h, Matrix.one_apply]

namespace IsTracePreserving

/-- Simp lemma: the trace of the image of a IsTracePreserving map is the same as the original
trace. -/
@[simp]
theorem apply_trace (h : M.IsTracePreserving) (ρ : Matrix A A R)
    : (M ρ).trace = ρ.trace :=
  h ρ

/-- The trace of a Choi matrix of a TP map is the cardinality of the input space. -/
theorem trace_choi [DecidableEq A] (h : M.IsTracePreserving) :
    M.choi_matrix.trace = (Finset.univ (α := A)).card := by
  rw [← Matrix.traceLeft_trace, (IsTracePreserving_iff_trace_choi M).mp h,
    Matrix.trace_one, Finset.card_univ]

/-- The composition of IsTracePreserving maps is also trace preserving. -/
theorem comp (h₁ : M.IsTracePreserving) (h₂ : M₂.IsTracePreserving) :
    IsTracePreserving (M₂ ∘ₗ M) :=
  fun x ↦ (h₂ _).trans (h₁ x)

/-- The identity MatrixMap IsTracePreserving. -/
@[simp]
theorem id : (id A R).IsTracePreserving :=
  fun _ ↦ rfl

variable {R : Type*} [CommSemiring R] in
/-- Unit linear combinations of IsTracePreserving maps are IsTracePreserving. -/
theorem unit_linear {M₁ M₂ : MatrixMap A B R} {x y : R}
    (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) (hxy : x + y = 1) :
    (x • M₁ + y • M₂).IsTracePreserving := by
  rw [IsTracePreserving] at h₁ h₂ ⊢
  simp [h₁, h₂, ← add_mul, hxy]

variable {R : Type*} [CommSemiring R] [DecidableEq C] [DecidableEq A] in
/-- The kronecker product of IsTracePreserving maps is also trace preserving. -/
theorem kron {M₁ : MatrixMap A B R} {M₂ : MatrixMap C D R} (h₁ : M₁.IsTracePreserving) (h₂ : M₂.IsTracePreserving) :
    (M₁ ⊗ₖₘ M₂).IsTracePreserving := by
  intro x
  simp_rw [Matrix.trace, Matrix.diag]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [kron_def]
  have h_simp : ∑ x_1, ∑ x_2, ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂,
    M₁ (Matrix.single a₁ a₂ 1) x_1 x_1 * M₂ (Matrix.single c₁ c₂ 1) x_2 x_2 * x (a₁, c₁) (a₂, c₂) =
      ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂, (if a₁ = a₂ then 1 else 0) * (if c₁ = c₂ then 1 else 0) * x (a₁, c₁) (a₂, c₂) := by
    --Sort the sum into AACCBD order
    simp only [@Finset.sum_comm A _ D, @Finset.sum_comm A _ B, @Finset.sum_comm C _ B, @Finset.sum_comm C _ D]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    congr! 8 with a₁ _ a₂ _ c₁ _ c₂ _
    · exact (h₁ _).trans (by split_ifs with h <;> simp [h, Matrix.trace_single_eq_of_ne])
    · exact (h₂ _).trans (by split_ifs with h <;> simp [h, Matrix.trace_single_eq_of_ne])
  simp [h_simp]

section piProd

variable {ι : Type u} [DecidableEq ι] [Fintype ι]
variable {dI : ι → Type v} [∀ i, Fintype (dI i)] [∀ i, DecidableEq (dI i)]
variable {dO : ι → Type w} [∀ i, Fintype (dO i)] [∀ i, DecidableEq (dO i)]
variable {R : Type*} [CommSemiring R]

/-- The `MatrixMap.piProd` product of IsTracePreserving maps is also trace preserving. -/
theorem piProd {Λi : ∀ i, MatrixMap (dI i) (dO i) R} (h₁ : ∀ i, (Λi i).IsTracePreserving) :
    (MatrixMap.piProd Λi).IsTracePreserving := by
  rw [IsTracePreserving_iff_trace_choi, MatrixMap.choi_matrix_piProd]
  ext f g
  have htrace := fun i =>
    congrFun₂ ((IsTracePreserving_iff_trace_choi (Λi i)).1 (h₁ i)) (f i) (g i)
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.one_apply] at htrace
  have hprod := (Fintype.prod_sum (f := fun i x => (Λi i).choi_matrix (x, f i) (x, g i))).symm
  simp [Matrix.traceLeft, Matrix.piProd, Matrix.reindex_apply, Matrix.one_apply, funext_iff,
    hprod, htrace, Finset.prod_boole]

end piProd

variable {S : Type*} [CommSemiring S] [Star S] [DecidableEq A] in
/-- The channel X ↦ ∑ k : κ, (M k) * X * (N k)ᴴ formed by Kraus operators M, N : κ → Matrix B A R
is trace-preserving if ∑ k : κ, (N k)ᴴ * (M k) = 1 -/
theorem of_kraus_isTracePreserving
  (M N : κ → Matrix B A S)
  (hTP : (∑ k, (N k).conjTranspose * (M k)) = 1) :
  (MatrixMap.of_kraus M N).IsTracePreserving := by
  intro x
  simp only [of_kraus, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_cycle (B := x), ← Matrix.trace_sum, ← Finset.sum_mul, hTP, one_mul]

/-- `MatrixMap.submatrix` is trace-preserving when the function is an equivalence. -/
theorem submatrix (e : A ≃ B) : (MatrixMap.submatrix R e).IsTracePreserving := by
  intro; simp

end IsTracePreserving
end tp


section unital

variable [DecidableEq A] [DecidableEq B] [Semiring R]

/-- A linear matrix map is *unital* if it preserves the identity. -/
def Unital (M : MatrixMap A B R) : Prop :=
  M 1 = 1

namespace Unital

variable {M : MatrixMap A B R}

omit [Fintype A] [Fintype B]

@[simp]
theorem map_1 (h : M.Unital) : M 1 = 1 :=
  h

/-- The identity `MatrixMap` is `Unital`. -/
@[simp]
theorem id : (id A R).Unital :=
  rfl

--TODO: Closed under composition, kronecker products, it's iff M.choi_matrix.traceLeft = 1...

end Unital
end unital

variable {A B C R : Type*}

open Kronecker
open TensorProduct

open ComplexOrder
variable [RCLike R]

/-- A linear matrix map is *Hermitian preserving* if it maps `IsHermitian` matrices to `IsHermitian`.-/
def IsHermitianPreserving (M : MatrixMap A B R) : Prop :=
  ∀⦃x⦄, x.IsHermitian → (M x).IsHermitian

/-- A linear matrix map is *positive* if it maps `PosSemidef` matrices to `PosSemidef`.-/
def IsPositive [Fintype A] [Fintype B] (M : MatrixMap A B R) : Prop :=
  ∀⦃x⦄, x.PosSemidef → (M x).PosSemidef

/-- A linear matrix map is *completely positive* if, for any integer n, the tensor product
with `I(n)` is positive. -/
def IsCompletelyPositive [Fintype A] [Fintype B] [DecidableEq A] (M : MatrixMap A B R) : Prop :=
  ∀ (n : ℕ), (M ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) R)).IsPositive

namespace IsHermitianPreserving

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsHermitianPreserving. -/
theorem id : (id A R).IsPositive :=
  fun _ h ↦ h

/-- The composition of IsHermitianPreserving maps is also Hermitian preserving. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R}
    (h₁ : M₁.IsHermitianPreserving) (h₂ : M₂.IsHermitianPreserving) : IsHermitianPreserving (M₂ ∘ₗ M₁) :=
  fun _ h ↦ h₂ (h₁ h)

end IsHermitianPreserving

namespace IsPositive
variable [Fintype A] [Fintype B] [Fintype C]

/- Every `MatrixMap` that `IsPositive` is also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving {M : MatrixMap A B R}
    (hM : IsPositive M) : IsHermitianPreserving M := by
  intro x hx
  let xH : HermitianMat _ _ := ⟨x, hx⟩
  classical --because PosPart requires DecidableEq
  have hSub := (hM (HermitianMat.zero_le_iff.mp xH.posPart_nonneg)).isHermitian.sub
    (hM (HermitianMat.zero_le_iff.mp xH.negPart_nonneg)).isHermitian
  rw [← map_sub] at hSub
  convert ← hSub
  exact HermitianMat.ext_iff.1 (HermitianMat.posPart_add_negPart xH)

/-- The composition of IsPositive maps is also positive. -/
theorem comp {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsPositive)
    (h₂ : M₂.IsPositive) : IsPositive (M₂ ∘ₗ M₁) :=
  fun _ h ↦ h₂ (h₁ h)

variable {A : Type*} [Fintype A] in
/-- The identity MatrixMap IsPositive. -/
@[simp]
theorem id : (id A R).IsPositive :=
  fun _ h ↦ h

/-- Sums of IsPositive maps are IsPositive. -/
theorem add {M₁ M₂ : MatrixMap A B R} (h₁ : M₁.IsPositive) (h₂ : M₂.IsPositive) :
    (M₁ + M₂).IsPositive :=
  fun _ h ↦ Matrix.PosSemidef.add (h₁ h) (h₂ h)

/-- Nonnegative scalings of IsPositive maps are IsPositive. -/
theorem smul {M : MatrixMap A B R} (hM : M.IsPositive) {x : R} (hx : 0 ≤ x) :
    (x • M).IsPositive :=
  fun _ h ↦ (hM h).smul hx

end IsPositive

namespace IsCompletelyPositive
variable [Fintype A] [Fintype B] [Fintype C] [DecidableEq A]

/-- Definition of a CP map, but with `Fintype T` in the definition instead of a `Fin n`. -/
theorem of_Fintype  {M : MatrixMap A B R} (h : IsCompletelyPositive M)
    (T : Type*) [Fintype T] [DecidableEq T] :
    (M.kron (LinearMap.id : MatrixMap T T R)).IsPositive := by
  obtain ⟨n, ⟨e⟩⟩ : ∃ n : ℕ, Nonempty (T ≃ Fin n) :=
    Finite.exists_equiv_fin T
  have key : M ⊗ₖₘ (LinearMap.id : MatrixMap T T R) =
      MatrixMap.submatrix R (Prod.map _root_.id ⇑e) ∘ₗ
        (M ⊗ₖₘ (LinearMap.id : MatrixMap (Fin n) (Fin n) R)) ∘ₗ
        MatrixMap.submatrix R (Prod.map _root_.id ⇑e.symm) := by
    classical
    rw [← id_kron_submatrix, ← id_kron_submatrix, ← kron_comp_distrib, ← kron_comp_distrib]
    simp [MatrixMap.id]
  intro x hx
  rw [key]
  exact ((h n) (hx.submatrix _)).submatrix _

/- Every `MatrixMap` that `IsCompletelyPositive` also `IsPositiveMap`. -/
theorem IsPositive {M : MatrixMap A B R}
    (hM : IsCompletelyPositive M) : IsPositive M := by
  intro x hx
  have h := (hM 1 (hx.kronecker Matrix.PosSemidef.one)).submatrix fun b : B => (b, 0)
  rw [kron_map_of_kron_state] at h
  convert h using 1
  ext b b'
  simp

/-- The composition of IsCompletelyPositive maps is also completely positive. -/
theorem comp [DecidableEq B] {M₁ : MatrixMap A B R} {M₂ : MatrixMap B C R} (h₁ : M₁.IsCompletelyPositive)
    (h₂ : M₂.IsCompletelyPositive) : IsCompletelyPositive (M₂ ∘ₗ M₁) := by
  --sketch: (M₂ ∘ₗ M₁) ⊗ₖₘ id[n] = (M₂ ⊗ₖₘ id[n]) ∘ₗ (M₁ ⊗ₖₘ id[n]), which is a composition of positive maps.
  intro n
  rw [← LinearMap.id_comp (LinearMap.id : MatrixMap (Fin n) (Fin n) R), kron_comp_distrib]
  exact (h₁ n).comp (h₂ n)

/-- The identity MatrixMap IsCompletelyPositive. -/
@[simp]
theorem id : (id A R).IsCompletelyPositive := by
  intro n ρ h
  rwa [show LinearMap.id = MatrixMap.id (Fin n) R from rfl, kron_id_id]

/-- Sums of IsCompletelyPositive maps are IsCompletelyPositive. -/
theorem add {M₁ M₂ : MatrixMap A B R} (h₁ : M₁.IsCompletelyPositive) (h₂ : M₂.IsCompletelyPositive) :
    (M₁ + M₂).IsCompletelyPositive :=
  fun n _ h ↦ by
  simp only [add_kron, LinearMap.add_apply]
  exact Matrix.PosSemidef.add (h₁ n h) (h₂ n h)

/-- Nonnegative scalings of `IsCompletelyPositive` maps are `IsCompletelyPositive`. -/
theorem smul {M : MatrixMap A B R} (hM : M.IsCompletelyPositive) {x : R} (hx : 0 ≤ x) :
    (x • M).IsCompletelyPositive :=
  fun n ρ h ↦ by
    rw [MatrixMap.smul_kron]
    exact (hM n h).smul hx

variable (A B) in
/-- The zero map `IsCompletelyPositive`. -/
theorem zero : (0 : MatrixMap A B R).IsCompletelyPositive :=
  fun _ _ _ ↦ by simpa using Matrix.PosSemidef.zero

/-- A finite sum of completely positive maps is completely positive. -/
theorem finset_sum {ι : Type*} [Fintype ι] {m : ι → MatrixMap A B R} (hm : ∀ i, (m i).IsCompletelyPositive) :
    (∑ i, m i).IsCompletelyPositive :=
  Finset.sum_induction m _ (fun _ _ ↦ add) (.zero A B) (by simpa)

end IsCompletelyPositive

variable [Fintype A] [Fintype B] [Fintype C] [DecidableEq A]
variable {d : Type*} [Fintype d]

open MatrixOrder

/-- The map that takes M and returns M ⊗ₖ C, where C is positive semidefinite, is a completely
  positive map. -/
theorem kron_kronecker_const {C : Matrix d d R} (h : C.PosSemidef) {h₁ h₂ : _} : IsCompletelyPositive
    (⟨⟨fun M => M ⊗ₖ C, h₁⟩, h₂⟩ : MatrixMap A (A × d) R) := by
  intros n x hx
  convert (hx.kronecker h).submatrix
    (fun (⟨⟨a, d'⟩, n'⟩ : (A × d) × Fin n) => ⟨⟨a, n'⟩, d'⟩) using 1
  ext ⟨⟨a, d₁⟩, n₁⟩ ⟨⟨a', d₂⟩, n₂⟩
  erw [MatrixMap.kron_def]
  simp [Matrix.single, ite_and, mul_comm]

omit [Fintype B] in
theorem choi_of_kraus (K : κ → Matrix B A 𝕜) :
    (MatrixMap.of_kraus K K).choi_matrix = ∑ k, Matrix.vecMulVec (fun (x : B × A) => K k x.1 x.2) (fun (x : B × A) => star (K k x.1 x.2)) := by
  ext ⟨b₁, a₁⟩ ⟨b₂, a₂⟩
  simp [MatrixMap.choi_matrix, MatrixMap.of_kraus, Matrix.sum_apply, Matrix.mul_apply,
    Matrix.single, Matrix.vecMulVec, ite_and]

/-- The linear map of conjugating a matrix by another, `x → y * x * yᴴ`. -/
@[simps]
def _root_.MatrixMap.conj (y : Matrix B A R) : MatrixMap A B R where
  toFun x := y * x * y.conjTranspose
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq A] in
theorem conj_isPositive (M : Matrix B A 𝕜) : (conj M).IsPositive :=
  fun _ hX => hX.mul_mul_conjTranspose_same M

omit [DecidableEq A] in
theorem IsPositive_sum {ι : Type*} [Fintype ι] (f : ι → MatrixMap A B ℂ) (h : ∀ i, (f i).IsPositive) :
    (∑ i, f i).IsPositive :=
  Finset.sum_induction f _ (fun _ _ ↦ IsPositive.add)
    (fun _ _ ↦ by simpa using Matrix.PosSemidef.zero) fun i _ ↦ h i

omit [DecidableEq A] in
theorem of_kraus_isPositive (K : κ → Matrix B A ℂ) :
    (of_kraus K K).IsPositive := by
  rw [of_kraus]
  exact IsPositive_sum _ fun k => conj_isPositive (K k)

theorem conj_kron (M : Matrix B A 𝕜) (N : Matrix D C 𝕜) [DecidableEq C] :
    conj M ⊗ₖₘ conj N = conj (M ⊗ₖ N) := by
  refine (Matrix.stdBasis 𝕜 (A × C) (A × C)).ext fun ⟨⟨a, c⟩, a', c'⟩ => ?_
  rw [Matrix.stdBasis_eq_single, ← one_mul (1 : 𝕜), ← Matrix.single_kronecker_single,
    kron_map_of_kron_state]
  simp [Matrix.mul_kronecker_mul, Matrix.single_kronecker_single, Matrix.conjTranspose_kronecker,
    Matrix.mul_assoc]

theorem congruence_one_eq_id : conj (1 : Matrix A A ℂ) = MatrixMap.id A ℂ :=
  LinearMap.ext fun x => by simp [conj]

theorem congruence_CP {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (M : Matrix B A 𝕜) : (conj M).IsCompletelyPositive := by
  intro n
  rw [show (LinearMap.id : MatrixMap (Fin n) (Fin n) 𝕜) = conj 1 from
    LinearMap.ext fun x => by simp, conj_kron]
  exact conj_isPositive _

theorem IsCompletelyPositive_sum {ι : Type*} [Fintype ι] (f : ι → MatrixMap A B ℂ) (h : ∀ i, (f i).IsCompletelyPositive) :
    (∑ i, f i).IsCompletelyPositive :=
  IsCompletelyPositive.finset_sum h

omit [Fintype B] [DecidableEq A] in
theorem of_kraus_eq_sum_conj (K : κ → Matrix B A 𝕜) :
    of_kraus K K = ∑ k, conj (K k) := by
  ext
  simp [MatrixMap.of_kraus, conj]

theorem of_kraus_CP (K : κ → Matrix B A 𝕜) : (of_kraus K K).IsCompletelyPositive := by
  classical
  rw [of_kraus_eq_sum_conj]
  exact IsCompletelyPositive.finset_sum fun k ↦ congruence_CP (K k)

theorem exists_kraus_of_choi_PSD
    (C : Matrix (B × A) (B × A) 𝕜) (hC : C.PosSemidef) :
    ∃ (K : (B × A) → Matrix B A 𝕜), C = (MatrixMap.of_kraus K K).choi_matrix := by
  classical
  use fun k i j => ( hC.1.eigenvectorUnitary.val : Matrix _ _ 𝕜 ) (i, j) k * ( hC.1.eigenvalues k |> RCLike.ofReal |> Real.sqrt)
  convert Matrix.IsHermitian.spectral_theorem hC.1 using 1;
  ext i j
  simp [choi_of_kraus, Matrix.mul_apply, Matrix.vecMulVec, Matrix.sum_apply, Matrix.diagonal]
  refine Finset.sum_congr rfl fun _ _ => ?_
  rw [mul_mul_mul_comm, ← RCLike.ofReal_mul, Real.mul_self_sqrt (hC.eigenvalues_nonneg _)]
  ring

/-
The Choi matrix of M is the image of the unnormalized maximally entangled state projector under M ⊗ id.
-/
theorem choi_matrix_eq_map_proj (M : MatrixMap A B R) :
    M.choi_matrix = (M ⊗ₖₘ MatrixMap.id A R) (Matrix.vecMulVec (fun (x : A × A) => if x.1 = x.2 then 1 else 0) (fun (x : A × A) => star (if x.1 = x.2 then 1 else 0))) := by
  ext ⟨b₁, d₁⟩ ⟨b₂, d₂⟩
  rw [MatrixMap.kron_def]
  simp [MatrixMap.choi_matrix, Matrix.single, Matrix.vecMulVec, MatrixMap.id, ite_and]

/-- Choi's theorem on completely positive maps: A map `IsCompletelyPositive` iff its Choi Matrix is PSD. -/
theorem choi_PSD_iff_CP_map (M : MatrixMap A B R) :
    M.IsCompletelyPositive ↔ M.choi_matrix.PosSemidef := by
  refine ⟨fun hcp => ?_, fun h_psd => ?_⟩
  · rw [MatrixMap.choi_matrix_eq_map_proj]
    exact hcp.of_Fintype A (Matrix.PosSemidef.outer_self_conj _)
  · obtain ⟨K, hK⟩ := exists_kraus_of_choi_PSD M.choi_matrix h_psd
    rw [choi_matrix_inj hK]
    exact of_kraus_CP K

omit [Fintype B] [DecidableEq A] in
theorem conj_eq_mulRightLinearMap_comp_mulRightLinearMap (y : Matrix B A R) :
    conj y = mulRightLinearMap B R y.conjTranspose ∘ₗ mulLeftLinearMap A R y := by
  ext1; simp

set_option backward.isDefEq.respectTransparency false in
/-- The act of conjugating (not necessarily by a unitary, just by any matrix at all) is completely positive. -/
theorem conj_isCompletelyPositive (M : Matrix B A R) : (conj M).IsCompletelyPositive := by
  classical
  exact congruence_CP M

/-- `MatrixMap.submatrix` is completely positive -/
theorem IsCompletelyPositive.submatrix (f : B → A) : (MatrixMap.submatrix R f).IsCompletelyPositive := by
  convert conj_isCompletelyPositive (Matrix.submatrix (α := R) 1 f _root_.id : Matrix B A R)
  ext1 m
  simp [m.submatrix_eq_mul_mul]

/-- The channel X ↦ ∑ k : κ, (M k) * X * (M k)ᴴ formed by Kraus operators M : κ → Matrix B A R
is completely positive -/
theorem of_kraus_isCompletelyPositive (M : κ → Matrix B A R) :
    (of_kraus M M).IsCompletelyPositive := by
  rw [of_kraus]
  exact IsCompletelyPositive.finset_sum (fun i ↦ conj_isCompletelyPositive (M i))

omit [Fintype B] [DecidableEq A] in
/--
The Choi matrix of a map in symmetric Kraus form is a sum of rank-1 projectors.
-/
theorem choi_of_kraus_R [DecidableEq A] (K : κ → Matrix B A 𝕜) :
    (of_kraus K K).choi_matrix = ∑ k, Matrix.vecMulVec (fun (x : B × A) => K k x.1 x.2) (fun (x : B × A) => star (K k x.1 x.2)) := by
  exact choi_of_kraus K

/-
The Choi matrix of M is the result of applying M \otimes I to the unnormalized maximally entangled state (Choi matrix of identity).
-/
variable {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [RCLike R]

theorem choi_eq_kron_id_apply_choi_id (M : MatrixMap A B R) :
    M.choi_matrix = (M ⊗ₖₘ MatrixMap.id A R) ((MatrixMap.id A R).choi_matrix) := by
  ext ⟨j₁, a₁⟩ ⟨j₂, a₂⟩ : 2
  rw [MatrixMap.kron_def]
  simp [choi_matrix, MatrixMap.id, Matrix.single, ite_and]

/-
The Choi matrix of the identity map is positive semidefinite.
-/
theorem choi_id_is_PSD {A R : Type*} [Fintype A] [DecidableEq A] [RCLike R] :
    (MatrixMap.id A R).choi_matrix.PosSemidef := by
  convert Matrix.PosSemidef.outer_self_conj fun p : A × A => if p.1 = p.2 then (1 : R) else 0
  ext ⟨i, j⟩ ⟨k, l⟩
  simp [MatrixMap.choi_matrix, MatrixMap.id, Matrix.single, Matrix.vecMulVec]
  aesop

/-
If a map is completely positive, its Choi matrix is positive semidefinite.
-/
theorem is_CP_implies_choi_PSD {A B R : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [RCLike R] (M : MatrixMap A B R) (hCP : M.IsCompletelyPositive) :
    M.choi_matrix.PosSemidef := by
  rw [choi_eq_kron_id_apply_choi_id]
  exact MatrixMap.IsCompletelyPositive.of_Fintype hCP A choi_id_is_PSD

theorem IsCompletelyPositive.exists_kraus (Φ : MatrixMap A B R) (hCP : Φ.IsCompletelyPositive) :
    ∃ (M : (B × A) → Matrix B A R), Φ = of_kraus M M := by
  obtain ⟨K, hK⟩ := exists_kraus_of_choi_PSD Φ.choi_matrix ((choi_PSD_iff_CP_map Φ).mp hCP)
  exact ⟨K, choi_matrix_inj hK⟩

open scoped MatrixOrder in
/-- Kadison-Schwarz for completely positive subunital matrix maps. -/
theorem cp_subunital_kadison_schwarz {M : MatrixMap A B ℂ} [DecidableEq B]
    (hM : M.IsCompletelyPositive) (hM1 : M 1 ≤ (1 : Matrix B B ℂ))
    (X : Matrix A A ℂ) :
    (M X)ᴴ * M X ≤ M (Xᴴ * X) := by
  have hblock :
      (Matrix.fromBlocks (M 1) (M X) ((M X)ᴴ) (M (Xᴴ * X))).PosSemidef := by
    classical
    obtain ⟨K, rfl⟩ := MatrixMap.IsCompletelyPositive.exists_kraus _ hM
    rw [MatrixMap.of_kraus_eq_sum_conj]
    convert Matrix.posSemidef_sum Finset.univ (fun k _ => by
      simpa [MatrixMap.conj, Matrix.mul_assoc] using
        Matrix.fromBlocks_gram_posSemidef (X * (K k)ᴴ) (K k)ᴴ) using 1
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.conjTranspose_sum,
        Matrix.mul_assoc]
  have hgap_block :
      (Matrix.fromBlocks (1 - M 1) 0 0 (0 : Matrix B B ℂ)).PosSemidef := by
    obtain ⟨Y, hY⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      (show (0 : Matrix B B ℂ) ≤ 1 - M 1 by simpa [sub_nonneg] using hM1)
    simpa [← Matrix.star_eq_conjTranspose, ← hY] using
      Matrix.fromBlocks_gram_posSemidef (0 : Matrix B B ℂ) Y
  have hsum :
      (Matrix.fromBlocks (1 : Matrix B B ℂ) (M X) ((M X)ᴴ) (M (Xᴴ * X))).PosSemidef := by
    simpa [Matrix.fromBlocks_add] using hblock.add hgap_block
  letI : Invertible (1 : Matrix B B ℂ) := invertibleOne
  rw [← sub_nonneg]
  exact Matrix.nonneg_iff_posSemidef.mpr (by simpa using
    (Matrix.PosDef.fromBlocks₁₁ (M X) (M (Xᴴ * X)) Matrix.PosDef.one).mp hsum)

open scoped MatrixOrder in
/-- A positive subunital matrix map is contractive on positive inputs. -/
theorem positive_subunital_norm_apply_le {M : MatrixMap A B ℂ} [DecidableEq B]
    (hM : M.IsPositive) (hM1 : M 1 ≤ (1 : Matrix B B ℂ))
    {X : Matrix A A ℂ} (hX : 0 ≤ X) :
    ‖M X‖ ≤ ‖X‖ := by
  let eA := Matrix.toEuclideanCLM (n := A) (𝕜 := ℂ)
  let eB := Matrix.toEuclideanCLM (n := B) (𝕜 := ℂ)
  have hXle : X ≤ ‖X‖ • (1 : Matrix A A ℂ) := by
    refine (map_le_map_iff eA).mp ?_
    have h := IsSelfAdjoint.le_algebraMap_norm_self (IsSelfAdjoint.of_nonneg (map_nonneg eA hX))
    have hs : algebraMap ℝ (EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) ‖eA X‖ =
        eA (‖X‖ • (1 : Matrix A A ℂ)) := by
      rw [Algebra.algebraMap_eq_smul_one]
      ext x i
      change (((‖X‖ : ℂ) • x).ofLp i) =
        (((‖X‖ : ℂ) • (1 : Matrix A A ℂ)) *ᵥ x.ofLp) i
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, WithLp.ofLp_smul]
    exact h.trans_eq hs
  have hMX_le : M X ≤ ‖X‖ • (1 : Matrix B B ℂ) :=
    (show M X ≤ ‖X‖ • M 1 by
      simpa [sub_nonneg, map_sub, map_smul] using
        (hM (by exact hXle :
          (‖X‖ • (1 : Matrix A A ℂ) - X).PosSemidef)).nonneg).trans
      (smul_le_smul_of_nonneg_left hM1 (norm_nonneg X))
  have hMX_nn : 0 ≤ M X := (hM (by simpa [Matrix.nonneg_iff_posSemidef] using hX)).nonneg
  have hone : ‖(1 : Matrix B B ℂ)‖ ≤ 1 := by
    rcases subsingleton_or_nontrivial (Matrix B B ℂ) with h | h
    · simp [Subsingleton.elim (1 : Matrix B B ℂ) 0]
    · exact CStarRing.norm_one.le
  refine (CStarAlgebra.norm_le_norm_of_nonneg_of_le (map_nonneg eB hMX_nn)
    ((map_le_map_iff eB).mpr hMX_le)).trans ?_
  change ‖‖X‖ • (1 : Matrix B B ℂ)‖ ≤ ‖X‖
  rw [show (‖X‖ • (1 : Matrix B B ℂ)) = ((‖X‖ : ℂ) • (1 : Matrix B B ℂ)) by ext; simp, norm_smul]
  simpa using mul_le_mul_of_nonneg_left hone (norm_nonneg X)

open scoped MatrixOrder in
/-- A completely positive subunital matrix map is contractive in operator norm. -/
theorem cp_subunital_opNorm_le_one {M : MatrixMap A B ℂ} [DecidableEq B]
    (hM : M.IsCompletelyPositive) (hM1 : M 1 ≤ (1 : Matrix B B ℂ))
    (X : Matrix A A ℂ) :
    ‖M X‖ ≤ ‖X‖ := by
  refine (sq_le_sq₀ (norm_nonneg (M X)) (norm_nonneg X)).mp ?_
  simp only [sq, ← CStarRing.norm_star_mul_self, Matrix.star_eq_conjTranspose]
  let e := Matrix.toEuclideanCLM (n := B) (𝕜 := ℂ)
  exact (CStarAlgebra.norm_le_norm_of_nonneg_of_le
      (map_nonneg e (star_mul_self_nonneg (M X)))
      ((map_le_map_iff e).mpr (cp_subunital_kadison_schwarz hM hM1 X))).trans
    (positive_subunital_norm_apply_le hM.IsPositive hM1 (star_mul_self_nonneg X))

/--
The Kronecker product of two Kraus maps is the Kraus map of the Kronecker products of the operators.
-/
theorem kron_of_kraus {A B C D R : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq C] [CommSemiring R] [StarRing R] [SMulCommClass R R R]
    {κ ι : Type*} [Fintype κ] [Fintype ι]
    (M : κ → Matrix B A R) (N : ι → Matrix D C R) :
    of_kraus M M ⊗ₖₘ of_kraus N N =
    of_kraus (fun (k : κ × ι) => M k.1 ⊗ₖ N k.2) (fun k => M k.1 ⊗ₖ N k.2) := by
  apply MatrixMap.choi_matrix_inj
  ext ⟨ b, a ⟩ ⟨ d, c ⟩
  simp only [of_kraus] ;
  simp only [choi_matrix, LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply]
  rw [ MatrixMap.kron_def ]
  simp only [LinearMap.coe_sum, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply,
    Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    star_mul'] ;
  simp only [Matrix.single, Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite, not_and,
    Finset.sum_const_zero, add_zero, ne_eq];
  simp only [Finset.sum_sigma', Finset.univ_sigma_univ];
  simp only [mul_comm, Finset.mul_sum, Finset.sum_sigma', mul_left_comm, mul_assoc];
  refine Finset.sum_bij ( fun x _ => ⟨ ⟨ ⟨ x.snd.snd.fst.fst, x.snd.fst.fst.fst ⟩, x.snd.snd.fst.snd, x.snd.fst.fst.snd ⟩, x.snd.snd.snd, x.snd.fst.snd ⟩ ) ?_ ?_ ?_ ?_
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, and_imp]
    grind
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, Sigma.mk.injEq,
      Prod.mk.injEq, heq_eq_eq, and_imp]
    grind
  · simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, exists_prop,
      Sigma.exists, existsAndEq, and_true, exists_and_left, and_imp]
    grind
  · simp

namespace IsCompletelyPositive

/-- The Kronecker product of IsCompletelyPositive maps is also completely positive. -/
theorem kron {D : Type*} [DecidableEq C] [Fintype D] {M₁ : MatrixMap A B R} {M₂ : MatrixMap C D R}
    (h₁ : M₁.IsCompletelyPositive) (h₂ : M₂.IsCompletelyPositive) : IsCompletelyPositive (M₁ ⊗ₖₘ M₂) := by
  obtain ⟨K₁, rfl⟩ := exists_kraus M₁ h₁
  obtain ⟨K₂, rfl⟩ := exists_kraus M₂ h₂
  rw [kron_of_kraus K₁ K₂]
  apply of_kraus_isCompletelyPositive

section piProd

variable {ι : Type u} [DecidableEq ι] [fι : Fintype ι]
variable {dI : ι → Type v} [∀i, Fintype (dI i)] [∀i, DecidableEq (dI i)]
variable {dO : ι → Type w} [∀i, Fintype (dO i)] [∀i, DecidableEq (dO i)]

/-- The `MatrixMap.piProd` product of IsCompletelyPositive maps is also completely positive. -/
theorem piProd {Λi : ∀ i, MatrixMap (dI i) (dO i) R} (h₁ : ∀ i, (Λi i).IsCompletelyPositive) :
    IsCompletelyPositive (MatrixMap.piProd Λi) := by
  rw [choi_PSD_iff_CP_map, MatrixMap.choi_matrix_piProd]
  convert! Matrix.PosSemidef.submatrix
    (Matrix.PosSemidef.piProd (fun i => (choi_PSD_iff_CP_map (Λi i)).1 (h₁ i)))
    (Equiv.arrowProdEquivProdArrow ι dO dI).symm using 1

end piProd

end IsCompletelyPositive

end MatrixMap
