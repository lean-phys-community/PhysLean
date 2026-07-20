/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati
-/
module

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
public import QuantumInfo.ClassicalInfo.Distribution

/-!
Finite dimensional quantum pure states, bra and kets. Mixed states are `MState` in that file.

These could be done with a Hilbert space of Fintype, which would look like
```lean4
(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
```
or by choosing a particular `Basis` and asserting it is `Fintype`. But frankly it seems easier to
mostly focus on the basis-dependent notion of `Matrix`, which has the added benefit of an obvious
"classical" interpretation (as the basis elements, or diagonal elements of a mixed state). In that
sense, this quantum theory comes with the a particular classical theory always preferred.
-/

@[expose] public section

noncomputable section

open Classical
open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

section
variable (d : Type*) [Fintype d]

/-- A ket as a vector of unit norm. We follow the convention in `Matrix` of vectors as simple functions
 from a Fintype. Kets are distinctly not a vector space in our notion, as they represent only normalized
 states and so cannot (in general) be added or scaled. -/
structure Ket where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1
  --TODO: change to `vec : EuclideanSpace ℂ d` / `normalized' : ‖vec‖ = 1`

/-- A bra is identical in definition to a `Ket`, but are separate to avoid complex conjugation confusion.
 They can be interconverted with the adjoint: `Ket.to_bra` and `Bra.to_ket` -/
structure Bra where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 =1

end section

namespace Braket

scoped notation:max "〈" ψ:90 "∣" => (ψ : Bra _)

scoped notation:max "∣" ψ:90 "〉" => (ψ : Ket _)

variable {d : Type*} [Fintype d]

instance instFunLikeKet : FunLike (Ket d) d ℂ where
  coe ψ := ψ.vec
  coe_injective _ _ h := by rwa [Ket.mk.injEq]

lemma _root_.Ket.coe_fun_eq (ψ : Ket d) : (ψ : d → ℂ) = ψ.vec := rfl

instance instFunLikeBra : FunLike (Bra d) d ℂ where
  coe ψ := ψ.vec
  coe_injective _ _ h := by rwa [Bra.mk.injEq]

lemma _root_.Bra.coe_fun_eq (ψ : Bra d) : (ψ : d → ℂ) = ψ.vec := rfl

def dot (ξ : Bra d) (ψ : Ket d) : ℂ := ∑ x, (ξ x) * (ψ x)

scoped notation "〈" ξ:90 "‖" ψ:90 "〉" => dot (ξ : Bra _) (ψ : Ket _)

theorem dot_eq_dotProduct (ψ : Bra d) (φ : Ket d) :〈ψ‖φ〉= dotProduct (m := d) ψ φ :=
  rfl

end Braket

section braket
open Braket

variable {d : Type*} [Fintype d]

theorem Ket.apply (ψ : Ket d) (i : d) : ψ i = ψ.vec i :=
  rfl

theorem Bra.apply (ψ : Bra d) (i : d) : ψ i = ψ.vec i :=
  rfl

@[ext]
theorem Ket.ext {ξ ψ : Ket d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h

@[ext]
theorem Bra.ext {ξ ψ : Bra d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h

theorem Ket.normalized (ψ : Ket d) : ∑ x, Complex.normSq (ψ x) = 1 :=
  ψ.normalized' ▸ Finset.sum_congr rfl fun x _ => Complex.normSq_eq_norm_sq (ψ x)

theorem Bra.normalized (ψ : Bra d) : ∑ x, Complex.normSq (ψ x) = 1 :=
  ψ.normalized' ▸ Finset.sum_congr rfl fun x _ => Complex.normSq_eq_norm_sq (ψ x)

/-- Any Bra can be turned into a Ket by conjugating the elements. -/
@[coe]
def Ket.to_bra (ψ : Ket d) : Bra d :=
  ⟨conj ψ, by simpa [Ket.apply] using ψ.2⟩

/-- Any Ket can be turned into a Bra by conjugating the elements. -/
@[coe]
def Bra.to_ket (ψ : Bra d) : Ket d :=
  ⟨conj ψ, by simpa [Bra.apply] using ψ.2⟩

instance instBraOfKet : Coe (Ket d) (Bra d) := ⟨Ket.to_bra⟩

instance instKetOfBra : Coe (Bra d) (Ket d) := ⟨Bra.to_ket⟩

@[simp]
theorem Bra.eq_conj (ψ : Ket d) (x : d) :〈ψ∣ x = conj (∣ψ〉 x) :=
  rfl

theorem Bra.apply' (ψ : Ket d) (i : d) : 〈ψ∣ i = conj (ψ.vec i) :=
  rfl

theorem Ket.exists_ne_zero (ψ : Ket d) : ∃ x, ψ x ≠ 0 := by
  by_contra h
  push Not at h
  simpa [h] using ψ.normalized

theorem Bra.exists_ne_zero (ψ : Bra d) : ∃ x, ψ x ≠ 0 := by
  by_contra h
  push Not at h
  simpa [h] using ψ.normalized

/-- Create a ket out of a vector given it has a nonzero component -/
def Ket.normalize (v : d → ℂ) (h : ∃ x, v x ≠ 0) : Ket d :=
  { vec := fun x ↦ v x / √(∑ x : d, ‖v x‖ ^ 2),
    normalized' := by
      obtain ⟨a, ha⟩ := h
      have hS : 0 < ∑ x, ‖v x‖ ^ 2 :=
        Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ a, by positivity⟩
      simp [div_pow, ← Finset.sum_div, Real.sq_sqrt hS.le, hS.ne']
  }

/-- A ket is already normalized -/
theorem Ket.normalize_ket_eq_self (ψ : Ket d) : Ket.normalize (ψ.vec) (Ket.exists_ne_zero ψ) = ψ := by
  ext x
  simp [normalize, apply, ψ.normalized']

/-- Create a bra out of a vector given it has a nonzero component -/
def Bra.normalize (v : d → ℂ) (h : ∃ x, v x ≠ 0) : Bra d :=
  { vec := fun x ↦ v x / √(∑ x : d, ‖v x‖ ^ 2),
    normalized' := by
      obtain ⟨a, ha⟩ := h
      have hS : 0 < ∑ x, ‖v x‖ ^ 2 :=
        Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ a, by positivity⟩
      simp [div_pow, ← Finset.sum_div, Real.sq_sqrt hS.le, hS.ne']
  }

/-- A bra is already normalized -/
def Bra.normalize_ket_eq_self (ψ : Bra d) : Bra.normalize (ψ.vec) (Bra.exists_ne_zero ψ) = ψ := by
  ext x
  simp [normalize, apply, ψ.normalized']

/-- Ket form by the superposition of all elements in `d`.
Commonly denoted by |+⟩, especially for qubits -/
def uniform_superposition [hdne : Nonempty d] : Ket d := by
  let f : d → ℂ := fun _ ↦ 1
  have hfnezero : ∃ x, f x ≠ 0 := by
    obtain ⟨i⟩ := hdne
    use i
    simp only [f, ne_eq, one_ne_zero, not_false_eq_true]
  exact Ket.normalize f hfnezero

/-- There exists a ket for every nonempty `d`.
Here, we use the uniform superposition -/
instance instInhabited [Nonempty d] : Inhabited (Ket d) where
  default := uniform_superposition

/-- Construct the Ket corresponding to a basis vector, with a +1 phase. -/
def Ket.basis (i : d) : Ket d :=
  ⟨fun j ↦ if i = j then 1 else 0, by simp [apply_ite]⟩

/-- Construct the Bra corresponding to a basis vector, with a +1 phase. -/
def Bra.basis (i : d) : Bra d :=
  ⟨fun j ↦ if i = j then 1 else 0, by simp [apply_ite]⟩

/-- A Bra can be viewed as a function from Ket's to ℂ. -/
instance instFunLikeBraket : FunLike (Bra d) (Ket d) ℂ where
  coe ξ := dot ξ
  coe_injective x y h := by
    ext i
    simpa [Ket.basis, dot, Ket.apply] using congrFun h (Ket.basis i)

/-- The inner product of any state with itself is 1. -/
@[simp]
theorem Braket.dot_self_eq_one (ψ : Ket d) :〈ψ‖ψ〉= 1 := by
  simpa [dot, ← Complex.normSq_eq_conj_mul_self] using congr(Complex.ofReal $ψ.normalized)

/-- Swapping the arguments conjugates the bra-ket product:
    `⟨ψ₂|ψ₁⟩ = conj(⟨ψ₁|ψ₂⟩)`. -/
lemma Braket.dot_swap_conj (ψ₁ ψ₂ : Ket d) :
    〈ψ₂‖ψ₁〉 = starRingEnd ℂ 〈ψ₁‖ψ₂〉 := by
  simp [Braket.dot, mul_comm]

section prod
variable {d d₁ d₂ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂]

/-- The outer product of two kets, creating an unentangled state. -/
def Ket.prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : Ket (d₁ × d₂) where
  vec := fun (i,j) ↦ ψ₁ i * ψ₂ j
  normalized' := by
    simp [Fintype.sum_prod_type, ← Complex.normSq_eq_norm_sq, mul_pow,
      ← Finset.mul_sum, ψ₁.normalized, ψ₂.normalized]

infixl:100 " ⊗ᵠ " => Ket.prod

/-- A Ket is a product if it's `Ket.prod` of two kets. -/
def Ket.IsProd (ψ : Ket (d₁ × d₂)) : Prop := ∃ ξ φ, ψ = ξ ⊗ᵠ φ

/-- A Ket is entangled if it's not `Ket.prod` of two kets. -/
def Ket.IsEntangled (ψ : Ket (d₁ × d₂)) : Prop := ¬ψ.IsProd

/-- `Ket.prod` states are product states. -/
@[simp]
theorem Ket.IsProd_prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : (ψ₁.prod ψ₂).IsProd :=
  ⟨ψ₁, ψ₂, rfl⟩

/-- `Ket.prod` states are not entangled states. -/
@[simp]
theorem Ket.not_IsEntangled_prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : ¬(ψ₁.prod ψ₂).IsEntangled :=
  (· (ψ₁.IsProd_prod ψ₂))

/-- A ket is a product state iff its components are cross-multiplicative. -/
theorem Ket.IsProd_iff_mul_eq_mul (ψ : Ket (d₁ × d₂)) : ψ.IsProd ↔
    ∀ i₁ i₂ j₁ j₂, ψ (i₁,j₁)  * ψ (i₂,j₂) = ψ (i₁,j₂) * ψ (i₂,j₁) := by
  constructor
  · rintro ⟨ξ,φ,rfl⟩ i₁ i₂ j₁ j₂
    simp only [prod, apply]
    ring_nf
  · intro hcrossm
    obtain ⟨⟨a, b⟩, hab⟩ := Ket.exists_ne_zero ψ
    have hn : ‖ψ (a, b)‖ ≠ 0 := by simpa using hab
    have hS₁ : 0 < ∑ i, ‖ψ (i, b)‖ ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, Finset.mem_univ a, by positivity⟩
    have hS₂ : 0 < ∑ j, ‖ψ (a, j)‖ ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨b, Finset.mem_univ b, by positivity⟩
    have hmul : √(∑ i, ‖ψ (i, b)‖ ^ 2) * √(∑ j, ‖ψ (a, j)‖ ^ 2) = ‖ψ (a, b)‖ := by
      rw [← Real.sqrt_mul hS₁.le, ← Real.sqrt_sq (norm_nonneg (ψ (a, b)))]
      congr 1
      simp_rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type', ← mul_pow, ← norm_mul]
      calc ∑ p : d₁ × d₂, ‖ψ (p.1, b) * ψ (a, p.2)‖ ^ 2
          = ∑ p : d₁ × d₂, ‖ψ (a, b) * ψ (p.1, p.2)‖ ^ 2 :=
            Finset.sum_congr rfl fun p _ => by rw [hcrossm p.1 a b p.2, mul_comm]
        _ = ‖ψ (a, b)‖ ^ 2 := by simp [mul_pow, ← Finset.mul_sum, apply, ψ.normalized']
    refine ⟨⟨fun x => ‖ψ (a, b)‖ / ψ (a, b) * (ψ (x, b) / √(∑ i, ‖ψ (i, b)‖ ^ 2)), ?_⟩,
        ⟨fun y => ψ (a, y) / √(∑ j, ‖ψ (a, j)‖ ^ 2), ?_⟩, ?_⟩
    · simp [div_pow, Real.sq_sqrt hS₁.le, ← Finset.sum_div, div_self, hn, hS₁.ne']
    · simp [div_pow, Real.sq_sqrt hS₂.le, ← Finset.sum_div, hS₂.ne']
    · ext ⟨x, y⟩
      have key := hcrossm x a y b
      have hsqrt : (√(∑ i, ‖ψ (i, b)‖ ^ 2) * √(∑ j, ‖ψ (a, j)‖ ^ 2) : ℂ) = ‖ψ (a, b)‖ := by
        exact_mod_cast congrArg Complex.ofReal hmul
      have h₁ : (√(∑ i, ‖ψ (i, b)‖ ^ 2) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hS₁).ne'
      have h₂ : (√(∑ j, ‖ψ (a, j)‖ ^ 2) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr hS₂).ne'
      simp only [prod, apply] at key hsqrt h₁ h₂ hab ⊢
      field_simp
      linear_combination (ψ.vec (x, y) * ψ.vec (a, b)) * hsqrt + (‖ψ.vec (a, b)‖ : ℂ) * key
end prod

section mes
/-- The Maximally Entangled State, or MES, on a d×d system. In principle there are many, this
is specifically the MES with an all-positive phase. For instance on `d := Fin 2`, this is the
Bell state. -/
def Ket.MES (d) [Fintype d] [Nonempty d] : Ket (d × d) where
  vec := fun (i,j) ↦ if i = j then 1 / Real.sqrt (Fintype.card (α := d)) else 0
  normalized' := by
    simp [apply_ite, Fintype.sum_prod_type]

/-- On any space of dimension at least two, the maximally entangled state `MES` is entangled. -/
theorem Ket.MES_isEntangled [Nontrivial d] : (Ket.MES d).IsEntangled := by
  obtain ⟨x, y, h⟩ := exists_pair_ne d
  simp only [IsEntangled, IsProd_iff_mul_eq_mul, not_forall]
  exact ⟨x, y, x, y, by simp [MES, apply, h]⟩

/-- The transpose trick -/
theorem transposeTrick {d} [Fintype d] [Nonempty d] [DecidableEq d] {M : Matrix d d ℂ} :
    (M ⊗ₖ 1) *ᵥ (Ket.MES d).vec = (1 ⊗ₖ M.transpose) *ᵥ (Ket.MES d).vec := by
  ext ⟨i₁, i₂⟩
  simp [Ket.MES, Matrix.mulVec, dotProduct, Matrix.kroneckerMap, Matrix.one_apply,
    Fintype.sum_prod_type, mul_ite, ite_mul, Finset.sum_ite_eq]

end mes

section equiv

/-- The equivalence relation on `Ket` where two kets equivalent if they are equal up to a
global phase, i.e. `∃ z, ‖z‖ = 1 ∧ a.vec = z • b.vec -/
def Ket.PhaseEquiv : Setoid (Ket d) where
  r a b := ∃ z : ℂ, ‖z‖ = 1 ∧ a.vec = z • b.vec
  iseqv := {
    refl := fun x ↦ ⟨1, by simp⟩,
    symm := fun ⟨z,h₁,h₂⟩ ↦ ⟨conj z,
      by simp [h₁],
      by simp [h₁, h₂, smul_smul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]⟩,
    trans := fun ⟨z₁,h₁₁,h₁₂⟩ ⟨z₂,h₂₁,h₂₂⟩ ↦ ⟨z₁ * z₂,
      by simp [h₁₁, h₂₁],
      by simp [h₁₂, h₂₂, smul_smul]⟩
  }

variable (d) in
/-- The type of `Ket`s up to a global phase equivalence, as given by `Ket.PhaseEquiv`.
In particular, `MState`s really only care about a KetUpToPhase, and not Kets themselves. -/
def KetUpToPhase :=
  @Quotient (Ket d) Ket.PhaseEquiv

/-- Construct a `KetUpToPhase` from a `Ket`. -/
def KetUpToPhase.mk (ψ : Ket d) : KetUpToPhase d :=
  @Quotient.mk _ Ket.PhaseEquiv ψ

/-- Lift a function on `Ket d` to `KetUpToPhase d`, given that it respects phase equivalence. -/
def KetUpToPhase.lift {α : Sort*} (f : Ket d → α)
    (hf : ∀ ψ φ, Ket.PhaseEquiv.r ψ φ → f ψ = f φ) : KetUpToPhase d → α :=
  @Quotient.lift _ _ Ket.PhaseEquiv f hf

@[simp]
theorem KetUpToPhase.lift_mk {α : Sort*} (f : Ket d → α)
    (hf : ∀ ψ φ, Ket.PhaseEquiv.r ψ φ → f ψ = f φ) (ψ : Ket d) :
    KetUpToPhase.lift f hf (KetUpToPhase.mk ψ) = f ψ := rfl

theorem KetUpToPhase.ind {p : KetUpToPhase d → Prop}
    (h : ∀ ψ : Ket d, p (KetUpToPhase.mk ψ)) : ∀ q, p q :=
  @Quotient.ind _ Ket.PhaseEquiv p h

theorem KetUpToPhase.surjective_mk : Function.Surjective (KetUpToPhase.mk (d := d)) :=
  Quotient.mk_surjective

end equiv

/-! ## Norm bounds -/

section norm_bounds
open Braket

variable {d : Type*} [Fintype d]

private def ketToEuclidean (ψ : Ket d) : EuclideanSpace ℂ d :=
  (WithLp.equiv 2 _).symm ψ.vec

private lemma ketToEuclidean_norm (ψ : Ket d) : ‖ketToEuclidean ψ‖ = 1 := by
  simp [EuclideanSpace.norm_eq, ketToEuclidean, ψ.normalized']

private lemma dot_eq_euclidean_inner (ψ₁ ψ₂ : Ket d) :
    〈ψ₁‖ψ₂〉 = @inner ℂ (EuclideanSpace ℂ d) _
      (ketToEuclidean ψ₁) (ketToEuclidean ψ₂) := by
  simp [dot, ketToEuclidean, PiLp.inner_apply, RCLike.inner_apply, Ket.apply, mul_comm]

/-- The bra-ket product of normalized states has norm at most 1 (Cauchy-Schwarz). -/
lemma Braket.norm_dot_le_one (ψ₁ ψ₂ : Ket d) : ‖〈ψ₁‖ψ₂〉‖ ≤ 1 := by
  rw [dot_eq_euclidean_inner]
  simpa [ketToEuclidean_norm] using norm_inner_le_norm (ketToEuclidean ψ₁) (ketToEuclidean ψ₂)

end norm_bounds

end braket
