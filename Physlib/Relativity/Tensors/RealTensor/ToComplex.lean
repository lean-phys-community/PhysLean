/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Nikolai Kashcheev
-/
module

public import Physlib.Relativity.Tensors.ComplexTensor.Basic
public import Physlib.Meta.Sorry
/-!

# Complex Lorentz tensors from real Lorentz tensors

## i. Overview

In this module we describe how to pass from real Lorentz tensors to complex Lorentz tensors
in a functorial way.
Specifically, we construct a canonical equivariant semilinear map

* `toComplex : ℝT(3, c) →ₛₗ[Complex.ofRealHom] ℂT(colorToComplex ∘ c)`

which is compatible with the natural operations on tensors (permutations of
indices, tensor products, contractions and evaluations).

## ii. Key results

The main definitions and statements are:

* `colorToComplex` upgrades the colour of a real Lorentz tensor to the
  corresponding complex Lorentz colour.
* `TensorSpecies.Tensor.ComponentIdx.complexify` transports component indices
  along `colorToComplex`.
* `toComplex` is the basic semilinear map from real to complex Lorentz tensors.
* `toComplex_basis` and `toComplex_pure_basisVector` show that `toComplex`
  sends basis tensors to basis tensors.
* `toComplex_eq_zero_iff` and `toComplex_injective` show that `toComplex` is
  injective.
* `toComplex_equivariant` states that `toComplex` is equivariant for the action
  of the complexified Lorentz group.
* `permT_toComplex`, `prodT_toComplex`, `contrT_toComplex` and `evalT_toComplex`
  express that `toComplex` commutes with the basic tensor operations.

## iii. Table of contents

* A. Colours and component indices
* B. The semilinear map `toComplex`
  * B.1. Expression in the tensor basis
  * B.2. Behaviour on basis vectors and injectivity
  * B.3. Equivariance under the Lorentz action
* C. Compatibility with permutations: `permT`
* D. Compatibility with tensor products: `prodT`
* E. Compatibility with contraction: `contrT`
* F. Compatibility with evaluation: `evalT`

## iv. References

The general formalism of Lorentz tensors and their operations is developed in
other parts of the library; here we only specialise to the passage from real to
complex Lorentz tensors.

-/

@[expose] public section

namespace realLorentzTensor

open Module TensorSpecies
open Tensor
open complexLorentzTensor

/-!

## A. Colours and component indices

We first explain how the Lorentz colour data and component indices for real
tensors are transported to the complex setting.

-/

/-- The map from colors of real Lorentz tensors to complex Lorentz tensors. -/
def colorToComplex (c : realLorentzTensor.Color) : complexLorentzTensor.Color :=
  match c with
  | .up => .up
  | .down => .down

lemma repDim_colorToComplex {c : realLorentzTensor.Color} :
    complexLorentzTensor.repDim (colorToComplex c) = 4 := by
  cases c <;> simp [colorToComplex]

/-- `simp` helper: reduce `match c j` after a case split on `c j`
  (avoids dependent `rw` / `Pi.smul_apply`). -/
lemma colorToComplex_match_up {n} {c : Fin n → realLorentzTensor.Color} {j}
    (hc : c j = realLorentzTensor.Color.up) :
    (match c j with
      | .up => complexLorentzTensor.Color.up
      | .down => complexLorentzTensor.Color.down)
      = complexLorentzTensor.Color.up := by
  rw [hc]

lemma colorToComplex_match_down {n} {c : Fin n → realLorentzTensor.Color} {j}
    (hc : c j = realLorentzTensor.Color.down) :
    (match c j with
      | .up => complexLorentzTensor.Color.up
      | .down => complexLorentzTensor.Color.down)
      = complexLorentzTensor.Color.down := by
  rw [hc]

lemma colorToComplex_comp_eq_match {n} (c : Fin n → realLorentzTensor.Color) (j : Fin n) :
    (colorToComplex ∘ c) j =
      (match c j with
        | .up => complexLorentzTensor.Color.up
        | .down => complexLorentzTensor.Color.down) := by
  rcases hc : c j with _ | _ <;> simp [colorToComplex, hc, Function.comp_apply]

/-- The complexification of the component index of a real Lorentz tensor to
  a complex Lorentz tensor. -/
noncomputable def _root_.TensorSpecies.Tensor.ComponentIdx.complexify {n}
    {c : Fin n → realLorentzTensor.Color} :
    ComponentIdx (S := realLorentzTensor) c ≃
      ComponentIdx (S := complexLorentzTensor) (colorToComplex ∘ c) where
  toFun b := fun j => Fin.cast repDim_colorToComplex.symm (finSumFinEquiv (b j))
  invFun i := fun j => finSumFinEquiv.symm <| Fin.cast repDim_colorToComplex (i j)
  left_inv i := by simp
  right_inv i := by simp

@[simp]
lemma ComponentIdx.complexify_apply {n} {c : Fin n → realLorentzTensor.Color}
    (f : ComponentIdx (S := realLorentzTensor) c) (j : Fin n) :
    (ComponentIdx.complexify f) j = Fin.cast repDim_colorToComplex.symm (finSumFinEquiv (f j)) :=
  rfl

@[simp]
lemma ComponentIdx.complexify_toFun_apply {n} {c : Fin n → realLorentzTensor.Color}
    (f : ComponentIdx (S := realLorentzTensor) c) (j : Fin n) :
    (ComponentIdx.complexify.toFun f) j = (ComponentIdx.complexify f) j :=
  rfl

/-!

## B. The semilinear map `toComplex`

We now define the basic semilinear map from real Lorentz tensors to complex
Lorentz tensors. It is characterised by sending the standard tensor basis on
the real side to the corresponding basis on the complex side, and is therefore
determined by the behaviour on components.

-/

/-- The semilinear map from real Lorentz tensors to complex Lorentz tensors,
  defined through basis. -/
noncomputable def toComplex {n} {c : Fin n → realLorentzTensor.Color} :
    ℝT(3, c) →ₛₗ[Complex.ofRealHom] ℂT(colorToComplex ∘ c) where
  toFun v := ∑ i, (Tensor.basis (S := realLorentzTensor) c).repr v i •
    Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) i.complexify
  map_smul' c v := by
    simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.ofRealHom_eq_coe]
    rw [Finset.smul_sum]
    congr
    funext i
    rw [← smul_smul]
    rfl
  map_add' c v := by
    simp only [map_add, Finsupp.coe_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    congr
    funext i
    simp [add_smul]

lemma toComplex_eq_sum_basis {n} (c : Fin n → realLorentzTensor.Color) (v : ℝT(3, c)) :
    toComplex v = ∑ i, (Tensor.basis (S := realLorentzTensor) c).repr v
      (ComponentIdx.complexify.symm i) •
      Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) i := by
  simp only [toComplex, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Equiv.sum_comp ComponentIdx.complexify]
  simp

/-- The representation of `toComplex v` in the complexified basis equals
  the real representation coerced to complex. -/
lemma toComplex_repr {n} {c : Fin n → realLorentzTensor.Color}
    (v : ℝT(3, c)) (i : ComponentIdx (S := realLorentzTensor) c) :
    (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)).repr
      (toComplex v) i.complexify =
    ↑((Tensor.basis (S := realLorentzTensor) c).repr v i) := by
  -- Expand toComplex v in the complexified basis
  rw [toComplex_eq_sum_basis]
  -- `repr` commutes with finite sums of tensors; then push the Finsupp evaluation into the sum
  rw [map_sum]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply]
  -- The sum has only one non-zero term (when k = i.complexify)
  rw [Fintype.sum_eq_single i.complexify]
  · -- Case k = i.complexify: show the term equals ↑(repr v i)
    have hsmul :
        ((Tensor.basis (S := realLorentzTensor) c).repr v
            (ComponentIdx.complexify.symm (ComponentIdx.complexify i))) •
          Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)
            (ComponentIdx.complexify i) =
        (↑((Tensor.basis (S := realLorentzTensor) c).repr v
            (ComponentIdx.complexify.symm (ComponentIdx.complexify i))) : ℂ) •
          Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)
            (ComponentIdx.complexify i) :=
      (Complex.coe_smul _ _).symm
    rw [hsmul]
    have hm :=
      LinearEquiv.map_smul
        (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)).repr
        (↑((Tensor.basis (S := realLorentzTensor) c).repr v
            (ComponentIdx.complexify.symm (ComponentIdx.complexify i))) : ℂ)
        (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)
          (ComponentIdx.complexify i))
    simp_rw [hm]
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Basis.repr_self, Finsupp.single_apply]
    simp only [Equiv.symm_apply_apply ComponentIdx.complexify, ite_true, mul_one]
  · -- Case k ≠ i.complexify: show the term equals 0
    intro k hk
    have hsmul :
        ((Tensor.basis (S := realLorentzTensor) c).repr v (ComponentIdx.complexify.symm k)) •
          Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) k =
        (↑((Tensor.basis (S := realLorentzTensor) c).repr v (ComponentIdx.complexify.symm k)) : ℂ) •
          Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) k :=
      (Complex.coe_smul _ _).symm
    rw [hsmul]
    have hm :=
      LinearEquiv.map_smul (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)).repr
        (↑((Tensor.basis (S := realLorentzTensor) c).repr v (ComponentIdx.complexify.symm k)) : ℂ)
        (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c) k)
    simp_rw [hm]
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Basis.repr_self, Finsupp.single_apply]
    split_ifs with h
    · exfalso
      exact hk h
    · rw [mul_zero]

/-- `toComplex` sends basis elements to basis elements. -/
@[simp]
lemma toComplex_basis {n} {c : Fin n → realLorentzTensor.Color}
    (i : ComponentIdx (S := realLorentzTensor) c) :
    toComplex (c := c) ((Tensor.basis (S := realLorentzTensor) c) i) =
      (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)) i.complexify := by
  classical
  simp only [toComplex, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Basis.repr_self]
  simp_rw [Finsupp.single_apply]
  -- collapse the sum: only the `i`-term survives
  refine (Fintype.sum_eq_single i ?_).trans ?_
  · intro j hj
    have hij : i ≠ j := Ne.symm hj
    simp [hij]
  · -- now the remaining term is the `i`-term
    simp

/-- `toComplex` on a pure basis vector. -/
@[simp]
lemma toComplex_pure_basisVector {n} {c : Fin n → realLorentzTensor.Color}
    (b : ComponentIdx (S := realLorentzTensor) c) :
    toComplex (c := c) (Pure.basisVector c b |>.toTensor)
      =
    (Pure.basisVector (colorToComplex ∘ c) b.complexify).toTensor := by
  classical
  -- rewrite pure basis vector back to tensor basis, use `toComplex_basis`, then rewrite back
  rw [← Tensor.basis_apply (S := realLorentzTensor) (c := c) b]
  rw [toComplex_basis (c := c) b]
  rw [Tensor.basis_apply (S := complexLorentzTensor) (c := (colorToComplex ∘ c)) b.complexify]

lemma toComplex_map_smul {n} (c : Fin n → realLorentzTensor.Color) (r : ℝ) (t : ℝT(3, c)) :
    toComplex (c := c) (r • t) = (Complex.ofReal r) • toComplex (c := c) t :=
  (toComplex (c := c)).map_smulₛₗ r t

@[simp]
lemma toComplex_eq_zero_iff {n} (c : Fin n → realLorentzTensor.Color) (v : ℝT(3, c)) :
    toComplex v = 0 ↔ v = 0 := by
  rw [toComplex_eq_sum_basis]
  have h1 : LinearIndependent ℂ
      (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c)) :=
    Basis.linearIndependent _
  rw [Fintype.linearIndependent_iff] at h1
  constructor
  · intro h
    apply (Tensor.basis (S := realLorentzTensor) c).repr.injective
    ext i
    have h2 := h1 (fun i => ((Tensor.basis c).repr v) (ComponentIdx.complexify.symm i)) h
      i.complexify
    simpa using h2
  · intro h
    subst h
    simp

/-- The map `toComplex` is injective. -/
lemma toComplex_injective {n} (c : Fin n → realLorentzTensor.Color) :
    Function.Injective (toComplex (c := c)) :=
  (injective_iff_map_eq_zero' toComplex).mpr (fun v => toComplex_eq_zero_iff c v)

open Matrix
open MatrixGroups
open CategoryTheory
open complexLorentzTensor
open Lorentz.SL2C
/-!

## pure
-/

/-- For a given color, the map turning a real Lorentz vector into a complex one. -/
noncomputable def toComplexVector (c : realLorentzTensor.Color) :
  realLorentzTensor.modules 3 c →ₛₗ[Complex.ofRealHom] complexLorentzTensor.modules
    (colorToComplex c) where
  toFun v := match c with
    | Color.up => ∑ i, ((Lorentz.contrBasis 3).repr v i) •
      Lorentz.complexContrBasisFin4 (finSumFinEquiv i)
    | Color.down => ∑ i, ((Lorentz.coBasis 3).repr v i) •
      Lorentz.complexCoBasisFin4 (finSumFinEquiv i)
  map_add' v1 v2 := by
    match c with
    | Color.up =>
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, Nat.reduceAdd, ← Finset.sum_add_distrib]
      congr
      funext x
      rw [add_smul]
      rfl
    | Color.down =>
      simp only [map_add, Finsupp.coe_add, Pi.add_apply, Nat.reduceAdd, ← Finset.sum_add_distrib]
      congr
      funext x
      rw [add_smul]
      rfl
  map_smul' r v := by
    match c with
    | Color.up =>
      simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.reduceAdd,
        Complex.ofRealHom_eq_coe, Complex.coe_smul]
      rw [Finset.smul_sum]
      congr
      funext x
      rw [← smul_smul]
      rfl
    | Color.down =>
      simp only [map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.reduceAdd,
        Complex.ofRealHom_eq_coe, Complex.coe_smul]
      rw [Finset.smul_sum]
      congr
      funext x
      rw [← smul_smul]
      rfl

/-- The function which turns a real pure tensor into a complex one. -/
noncomputable def toComplexPure {c : Fin n → Color} (p : Pure realLorentzTensor c) :
    Pure complexLorentzTensor (colorToComplex ∘ c) := fun i =>
  toComplexVector (c i) (p i)

lemma toComplexPure_component {c : Fin n → Color} (p : Pure realLorentzTensor c)
    (φ : ComponentIdx c) : (toComplexPure p).component (ComponentIdx.complexify φ) =
      p.component φ := by
  simp [Pure.component, toComplexPure]
  congr
  funext x
  generalize φ x = φx at *
  generalize p x = px at *
  clear φ p
  generalize_proofs h1 h2 h3
  let b (c : Color) : Basis (Fin (complexLorentzTensor.repDim (colorToComplex c))) ℂ
      (complexLorentzTensor.modules (colorToComplex c)) :=
    match colorToComplex c with
    | Color.upL => Fermion.leftBasis
    | Color.downL => Fermion.altLeftBasis
    | Color.upR => Fermion.rightBasis
    | Color.downR => Fermion.altRightBasis
    | complexLorentzTensor.Color.up => Lorentz.complexContrBasisFin4
    | complexLorentzTensor.Color.down => Lorentz.complexCoBasisFin4
  let b' (c : Color) : Basis (Fin 1 ⊕ Fin 3) ℝ (realLorentzTensor.modules 3 c) :=
    (match c with
      | Color.up => Lorentz.contrBasis
      | Color.down => Lorentz.coBasis : Basis (Fin 1 ⊕ Fin 3) ℝ (realLorentzTensor.modules 3 c))
  let P (c : Color) (px : realLorentzTensor.modules 3 c) (φx : Fin 1 ⊕ Fin 3)
    (h2 : 4 = repDim (colorToComplex c)) : Prop :=
    ((b c).repr
      (toComplexVector c px))
    (Fin.cast h2 (finSumFinEquiv φx)) =
  ↑(((b' c).repr
        px)
      φx)
  suffices h : P (c x) px φx h2 by exact h
  generalize c x = c at *
  fin_cases c
  · simp only [colorToComplex, toComplexVector, Nat.reduceAdd, Fin.cast_eq_self, P, b, b']
    trans (∑ x, (Lorentz.complexContrBasisFin4.repr ((Lorentz.contrBasis.repr px) x •
        Lorentz.complexContrBasisFin4 (finSumFinEquiv x))))
      (finSumFinEquiv φx)
    · simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Nat.reduceAdd, Finsupp.coe_add, Finsupp.coe_finsetSum, Pi.add_apply,
      Finset.sum_apply]
      rfl
    simp [- Fintype.sum_sum_type, Lorentz.complexContrBasisFin4]
    trans ∑ x, (((Lorentz.contrBasis.repr px) x • Lorentz.complexContrBasis.repr
      (Lorentz.complexContrBasis x) φx))
    · simp [Basis.repr_self, Complex.real_smul]
      rfl
    simp [- Fintype.sum_sum_type, Finsupp.single_apply]
  · simp only [colorToComplex, toComplexVector, Nat.reduceAdd, Fin.cast_eq_self, P, b, b']
    trans (∑ x, (Lorentz.complexCoBasisFin4.repr ((Lorentz.coBasis.repr px) x •
      Lorentz.complexCoBasisFin4 (finSumFinEquiv x))))
      (finSumFinEquiv φx)
    · simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
      Finset.sum_singleton, Nat.reduceAdd, Finsupp.coe_add, Finsupp.coe_finsetSum, Pi.add_apply,
      Finset.sum_apply]
      rfl
    simp [- Fintype.sum_sum_type, Lorentz.complexCoBasisFin4]
    trans ∑ x, (((Lorentz.coBasis.repr px) x •
      Lorentz.complexCoBasis.repr (Lorentz.complexCoBasis x) φx))
    · simp [Basis.repr_self, Complex.real_smul]
      rfl
    simp [- Fintype.sum_sum_type, Finsupp.single_apply]

@[sorryful]
lemma actionP_toComplexPure {n : ℕ } (c : Fin n → Color) (p : Pure realLorentzTensor c)
    (Λ : SL(2, ℂ)) :
    Λ • toComplexPure p = toComplexPure (toLorentzGroup Λ • p) := by
  ext i
  simp [Pure.actionP_eq, toComplexPure]
  let b (c : Color) : Representation ℂ _ (complexLorentzTensor.modules (colorToComplex c)) :=
    match colorToComplex c with
    | Color.upL => Fermion.leftHandedRep
    | Color.downL => Fermion.altLeftHandedRep
    | Color.upR => Fermion.rightHandedRep
    | Color.downR => Fermion.altRightHandedRep
    | complexLorentzTensor.Color.up => Lorentz.ContrℂModule.SL2CRep
    | complexLorentzTensor.Color.down => Lorentz.CoℂModule.SL2CRep
  let b' (c : Color) : Representation ℝ _ (realLorentzTensor.modules 3 c) :=
    (match c with
    | Color.up => Lorentz.ContrMod.rep
    | Color.down => Lorentz.CoMod.rep)
  let P (c : Color) (px : realLorentzTensor.modules 3 c) : Prop :=
    b c Λ (toComplexVector c px) = toComplexVector c (b' c (toLorentzGroup Λ) px)
  change P (c i) (p i)
  generalize p i = p at *
  generalize c i = c at *
  fin_cases c
  · simp_all [P, b, b', colorToComplex]
    calc _ = (Lorentz.ContrℂModule.SL2CRep Λ) (∑ i, ((Lorentz.contrBasis 3).repr p i) •
      Lorentz.complexContrBasisFin4 (finSumFinEquiv i)) := by rfl
        _ = (∑ i, (Lorentz.ContrℂModule.SL2CRep Λ) (((Lorentz.contrBasis 3).repr p i) •
          (Lorentz.complexContrBasisFin4 (finSumFinEquiv i)))) := by
          simp only [Nat.reduceAdd, map_sum]
        _ = (∑ i, (Lorentz.ContrℂModule.SL2CRep Λ) (((Lorentz.contrBasis 3).repr p i : ℂ) •
          (Lorentz.complexContrBasisFin4 (finSumFinEquiv i)))) := by rfl
        _ = (∑ i, (((Lorentz.contrBasis 3).repr p i : ℂ) •
            (Lorentz.ContrℂModule.SL2CRep Λ)
            (Lorentz.complexContrBasisFin4 (finSumFinEquiv i)))) := by
          congr
          funext x
          rw [map_smul]
    sorry
  · simp_all [P, b, b', colorToComplex]
    sorry

lemma toComplex_pure {n : ℕ} (c : Fin n → Color) (p : Pure realLorentzTensor c) :
    toComplex p.toTensor = (toComplexPure p).toTensor := by
  apply (Tensor.basis _).repr.injective
  ext φ
  obtain ⟨φ, rfl⟩ := TensorSpecies.Tensor.ComponentIdx.complexify.surjective φ
  rw [basis_repr_pure, toComplex_repr, toComplexPure_component]
  simp

/-!

### B.3. Equivariance under the Lorentz action

Finally we record that `toComplex` is equivariant for the natural action of
`SL(2, ℂ)` (and hence the induced Lorentz action) on tensors.

-/

set_option backward.isDefEq.respectTransparency false in
/-- The map `toComplex` is equivariant. -/
@[sorryful]
lemma toComplex_equivariant {n} {c : Fin n → realLorentzTensor.Color}
    (v : ℝT(3, c)) (Λ : SL(2, ℂ)) :
    Λ • (toComplex v) = toComplex (Lorentz.SL2C.toLorentzGroup Λ • v) := by
  induction' v using induction_on_pure with p r t h t1 t2
  · simp only
    rw [actionT_pure, toComplex_pure, actionT_pure, actionP_toComplexPure, toComplex_pure]
  · simp
    rw [← h]
    change Λ • (r : ℂ) • toComplex t = _
    rw [actionT_smul]
    rfl
  · simp_all

/-!

## C. Compatibility with permutations: `permT`

We first show that complexification is compatible with permutation of tensor
slots. On colours this is encoded in the `PermCond` predicate, and on tensors
by the operator `permT`.

-/

/-- The `PermCond` condition is preserved under `colorToComplex`. -/
@[simp] lemma permCond_colorToComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) :
    PermCond (colorToComplex ∘ c) (colorToComplex ∘ c1) σ := by
  refine And.intro h.1 ?_
  intro i
  simpa [Function.comp_apply] using congrArg colorToComplex (h.2 i)

/-- `permT` sends basis vectors to basis vectors. -/
@[simp] lemma permT_basis_real {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ)
    (b : ComponentIdx (S := realLorentzTensor) c) :
    permT (S := realLorentzTensor) σ h ((Tensor.basis (S := realLorentzTensor) c) b)
    = (Tensor.basis (S := realLorentzTensor) c1)
      (fun j => b (σ j)) := by
  classical
  simp [Tensor.basis_apply, permT_pure, Pure.permP_basisVector]

@[simp] lemma permT_basis_complex {n m : ℕ}
    {c : Fin n → complexLorentzTensor.Color} {c1 : Fin m → complexLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ)
    (b : ComponentIdx (S := complexLorentzTensor) c) :
    permT (S := complexLorentzTensor) σ h ((Tensor.basis (S := complexLorentzTensor) c) b)
      =
    (Tensor.basis (S := complexLorentzTensor) c1)
      (fun j => Fin.cast
        (by
          -- from the color agreement we get the repDim agreement
          -- if one has `h.2 j : c1 j = c (σ j)`, then replace it with `(h.2 j).symm`
          simpa using congrArg (fun col => complexLorentzTensor.repDim col) (h.2 j))
        (b (σ j))) := by
  classical
  simp [Tensor.basis_apply, permT_pure, Pure.permP_basisVector, basisIdxCongr_eq_cast]

/-- The map `toComplex` commutes with permT. -/
lemma permT_toComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color}
    {c1 : Fin m → realLorentzTensor.Color}
    {σ : Fin m → Fin n} (h : PermCond c c1 σ) (t : ℝT(3, c)) :
    toComplex (permT (S := realLorentzTensor) σ h t)
      =
    permT (S := complexLorentzTensor) σ (permCond_colorToComplex (c := c) (c1 := c1) h)
      (toComplex (c := c) t) := by
  classical
  let h' : PermCond (colorToComplex ∘ c) (colorToComplex ∘ c1) σ :=
    permCond_colorToComplex (c := c) (c1 := c1) h
  let P : ℝT(3, c) → Prop := fun t =>
    toComplex (permT (S := realLorentzTensor) σ h t)
      =
    permT (S := complexLorentzTensor) σ h' (toComplex (c := c) t)
  change P t
  apply induction_on_basis
  · intro b
    dsimp [P, h']

    -- permT on (real/complex) basis + toComplex on basis
    simp (config := { failIfUnchanged := false })
      [permT_basis_real, permT_basis_complex, toComplex_basis]

    -- index equality
    apply congrArg (Tensor.basis (S := complexLorentzTensor) (colorToComplex ∘ c1))
    funext j
    simp [TensorSpecies.Tensor.ComponentIdx.complexify, colorToComplex, Function.comp_apply]
  · simp [P]
  · intro r t ht
    dsimp [P] at ht ⊢
    refine (by
      simp [map_smul, ht])
  · intro t1 t2 h1 h2
    dsimp [P] at h1 h2 ⊢
    refine (by
      simp [map_add, h1, h2])

/-!

### D. Compatibility with tensor products: `prodT`

-/

/-- `colorToComplex` commutes with `Fin.append` (as functions). -/
@[simp]
lemma colorToComplex_append {n m : ℕ}
    (c : Fin n → realLorentzTensor.Color) (c1 : Fin m → realLorentzTensor.Color) :
    (colorToComplex ∘ Fin.append c c1) = Fin.append (colorToComplex ∘ c) (colorToComplex ∘ c1) := by
  funext x
  -- breaking down x : Fin (n+m) into left/right parts
  refine Fin.addCases (fun i => ?_) (fun j => ?_) x
  · -- left case: x = castAdd m i
    -- here `simp` should expand `Fin.append` on castAdd
    simp [Fin.append, Function.comp_apply]
  · -- right case: x = natAdd n j
    simp [Fin.append, Function.comp_apply]

lemma permCond_prodTColorToComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color} :
    PermCond (Fin.append (colorToComplex ∘ c) (colorToComplex ∘ c1))
      (colorToComplex ∘ Fin.append c c1)
      (id : Fin (n + m) → Fin (n + m)) := by
  -- For `σ = id`, `PermCond.on_id` reduces the goal to pointwise color equality.
  -- Here that equality is exactly `colorToComplex_append`.
  apply (PermCond.on_id
    (c := Fin.append (colorToComplex ∘ c) (colorToComplex ∘ c1))
    (c1 := colorToComplex ∘ Fin.append c c1)).2
  intro x
  -- `colorToComplex_append` states the two color functions are extensionally equal,
  -- but with the sides reversed, so we use its symmetric form.
  have hx := congrArg (fun f => f x)
    (colorToComplex_append (c := c) (c1 := c1)).symm
  simpa [Function.comp_apply] using hx

/-- `prodT` on the complex side, with colors written as `colorToComplex ∘ Fin.append ...`.
This is `prodT` followed by a cast using `colorToComplex_append`. -/
noncomputable def prodTColorToComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color} :
    ℂT(colorToComplex ∘ c) → ℂT(colorToComplex ∘ c1) → ℂT(colorToComplex ∘ Fin.append c c1) :=
  fun x y =>
    permT (S := complexLorentzTensor) (σ := (id : Fin (n + m) → Fin (n + m)))
      (permCond_prodTColorToComplex (c := c) (c1 := c1))
      (prodT (S := complexLorentzTensor) x y)

private lemma cast_componentIdx_apply {n : ℕ} {c c' : Fin n → complexLorentzTensor.Color}
    (h : c' = c) (f : ComponentIdx (S := complexLorentzTensor) c') (x : Fin n) :
    (cast (congr_arg ComponentIdx h) f) x =
      Fin.cast (congr_arg (fun c => complexLorentzTensor.repDim (c x)) h) (f x) := by
  subst h
  rfl

@[simp]
private lemma cast_componentIdx_eq_fun {n : ℕ}
    {c c' : Fin n → complexLorentzTensor.Color}
    (h : c' = c) (f : ComponentIdx (S := complexLorentzTensor) c') :
    cast (congr_arg ComponentIdx h) f =
      (fun x =>
        Fin.cast (congr_arg (fun col => complexLorentzTensor.repDim (col x)) h) (f x)) := by
  funext x
  exact cast_componentIdx_apply (c := c) (c' := c') h f x

/-- `complexify` commutes with `prod` of component indices. -/
@[simp]
lemma complexify_prod {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color} {c1 : Fin m → realLorentzTensor.Color}
    (b : ComponentIdx (S := realLorentzTensor) c)
    (b1 : ComponentIdx (S := realLorentzTensor) c1) :
    ComponentIdx.complexify (c := Fin.append c c1) (ComponentIdx.prod.symm (b, b1))
      =
    cast (congr_arg ComponentIdx (colorToComplex_append c c1).symm)
      (ComponentIdx.prod.symm (ComponentIdx.complexify (c := c) b,
        ComponentIdx.complexify (c := c1) b1)) := by
  ext x
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective x
  cases i with
  | inl i =>
    rw [ComponentIdx.complexify_apply]
    simp [ComponentIdx.prod]
    erw [basisIdxCongr_eq_cast]
    simp
  | inr j =>
    rw [ComponentIdx.complexify_apply]
    simp [ComponentIdx.prod]
    erw [basisIdxCongr_eq_cast]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The map `toComplex` commutes with prodT. -/
lemma prodT_toComplex {n m : ℕ}
    {c : Fin n → realLorentzTensor.Color}
    {c1 : Fin m → realLorentzTensor.Color}
    (t : ℝT(3, c)) (t1 : ℝT(3, c1)) :
    toComplex (c := Fin.append c c1) (prodT (S := realLorentzTensor) t t1)
      =
    prodTColorToComplex (c := c) (c1 := c1)
      (toComplex (c := c) t) (toComplex (c := c1) t1) := by
  classical
  -- Induction on the first tensor using the tensor basis.
  let P : ℝT(3, c) → Prop := fun t =>
    ∀ t1 : ℝT(3, c1),
      toComplex (c := Fin.append c c1) (prodT (S := realLorentzTensor) t t1)
        =
      prodTColorToComplex (c := c) (c1 := c1)
        (toComplex (c := c) t) (toComplex (c := c1) t1)
  have hP : P t := by
    -- `induction_on_basis` over the first tensor.
    apply
      induction_on_basis
        (c := c)
        (P := P)
        (t := t)
    · -- basis case for the first tensor and we must show the property for all `t1`
      intro b t1
      -- Define the property on the second tensor, with the first fixed to a basis vector.
      let P1 : ℝT(3, c1) → Prop := fun t1' =>
        toComplex (c := Fin.append c c1)
            (prodT (S := realLorentzTensor)
              ((Tensor.basis (S := realLorentzTensor) c) b) t1')
          =
        prodTColorToComplex (c := c) (c1 := c1)
          (toComplex (c := c) ((Tensor.basis (S := realLorentzTensor) c) b))
          (toComplex (c := c1) t1')
      have hP1 : P1 t1 := by
        -- Induction on the second tensor using the tensor basis.
        apply
          induction_on_basis
            (c := c1)
            (P := P1)
            (t := t1)
        · -- basis case for the second tensor
          intro b1
          -- Unfold `P1` and compute both sides explicitly on pure basis tensors.
          dsimp [P1]
          simp (config := { failIfUnchanged := false })
            [prodTColorToComplex,
            prodT_pure,
            permT_pure,
            Pure.prodP_basisVector,
            Pure.permP_basisVector,
            Tensor.basis_apply,
            toComplex_pure_basisVector,
            colorToComplex_append,
            basisIdxCongr_eq_cast]
        · -- zero tensor in the second argument
          simp [P1, prodTColorToComplex]
        · -- scalar multiplication in the second argument
          intro r t1' ht'
          dsimp [P1] at ht' ⊢
          refine (by
            simp [map_smul, ht', prodTColorToComplex])
        · -- addition in the second argument
          intro t1' t2' h1 h2
          dsimp [P1] at h1 h2 ⊢
          refine (by
            simp [map_add, h1, h2, prodTColorToComplex])
      -- Apply the resulting property to `t1`.
      exact hP1
    · -- zero tensor in the first argument
      intro t1
      simp [prodTColorToComplex]
    · -- scalar multiplication in the first argument
      intro r t ht t1
      dsimp [P] at ht ⊢
      refine (by
        simp [map_smul, ht, prodTColorToComplex])
    · -- addition in the first argument
      intro t1 t2 h1 h2 t1'
      dsimp [P] at h1 h2 ⊢
      refine (by
        simp [map_add, h1 t1', h2 t1', prodTColorToComplex])
  -- Apply the resulting property to `t1`.
  exact hP t1

/-!

### E. Compatibility with contraction: `contrT`

-/

/-- `τ` commutes with `colorToComplex` on the Lorentz `up/down` colors. -/
@[simp]
lemma tau_colorToComplex (x : realLorentzTensor.Color) :
    (complexLorentzTensor).τ (colorToComplex x) = colorToComplex ((realLorentzTensor).τ x) := by
  cases x <;> rfl

/-- `complexify` commutes with precomposition by `succSuccAbove`.
  We use `fun k => b (Fin.succSuccAbove i j k)` and direct application
  `(ComponentIdx.complexify b) (Fin.succSuccAbove i j m)` rather than composition so that
  dependent `ComponentIdx` types unify correctly (avoiding `Function.comp` type mismatch). -/
@[simp]
lemma ComponentIdx.complexify_comp_succSuccAbove
    {n : ℕ} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} (b : ComponentIdx (S := realLorentzTensor) c) (m : Fin n) :
    (ComponentIdx.complexify (c := c ∘ Fin.succSuccAbove i j)
      (fun k => b (Fin.succSuccAbove i j k))) m =
    (ComponentIdx.complexify (c := c) b) (Fin.succSuccAbove i j m) := by
  simp only [ComponentIdx.complexify_apply, Function.comp_apply]

/-- For a real basis vector, `toComplex(contrP(basisVector c b))` equals
  `contrP(basisVector (colorToComplex ∘ c) (complexify b))` (complex species). -/
lemma toComplex_contrP_basisVector {n : ℕ} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} (h : i ≠ j ∧ (realLorentzTensor).τ (c i) = c j)
    (b : ComponentIdx (S := realLorentzTensor) c) :
    toComplex (c := c ∘ Fin.succSuccAbove i j)
      (Pure.contrP (S := realLorentzTensor) i j h (Pure.basisVector c b))
      =
    Pure.contrP (S := complexLorentzTensor) i j
      (by
        simpa [Function.comp_apply] using And.intro h.1
          (by simpa [tau_colorToComplex] using congrArg colorToComplex h.2))
      (Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b)) := by
  let c' := c ∘ Fin.succSuccAbove i j
  simp only [Pure.contrP]
  rw [toComplex_map_smul c' (Pure.contrPCoeff i j h (Pure.basisVector c b))
    ((Pure.dropPair i j h.1 (Pure.basisVector c b)).toTensor),
    Pure.dropPair_basisVector (c := c),
    ← Tensor.basis_apply (S := realLorentzTensor) c' (fun k => b (Fin.succSuccAbove i j k)),
    toComplex_basis (c := c') (i := fun k => b (Fin.succSuccAbove i j k))]
  congr 1
  · -- contrPCoeff: real and complex both equal 0 or 1 with same condition
    rw [contrPCoeff_basis, complexLorentzTensor.contrPCoeff_basis]
    simp only [Function.comp_apply, ComponentIdx.complexify_apply, Nat.reduceAdd, Fin.cast_cast,
      Fin.cast_inj, EmbeddingLike.apply_eq_iff_eq]
    simp_all only [ne_eq]
    obtain ⟨left, right⟩ := h
    split
    next h => simp_all only [Complex.ofReal_one]
    next h => simp_all only [Complex.ofReal_zero]
  · -- complexify(fun k => b (succSuccAbove k)) = (complexify b) ∘ succSuccAbove
    rw [Pure.dropPair_basisVector]
    rw [← Tensor.basis_apply]
    refine congr_arg _ (funext fun m => ComponentIdx.complexify_comp_succSuccAbove b m)

set_option backward.isDefEq.respectTransparency false in
/-- The map `toComplex` commutes with `contrT`. -/
lemma contrT_toComplex {n : ℕ}
    {c : Fin (n + 1 + 1) → realLorentzTensor.Color} {i j : Fin (n + 1 + 1)}
    (h : i ≠ j ∧ (realLorentzTensor).τ (c i) = c j) (t : ℝT(3, c)) :
    toComplex (c := c ∘ Fin.succSuccAbove i j) (contrT (S := realLorentzTensor) n i j h t)
      =
    contrT (S := complexLorentzTensor) n i j (by
        simpa [Function.comp_apply] using
          And.intro h.1 (by
            simpa [tau_colorToComplex] using congrArg colorToComplex h.2))
      (toComplex (c := c) t) := by
  classical
  -- We prove the statement by induction on the tensor `t` using the tensor basis.
  -- After contracting two indices, the resulting colour function lives on `Fin n`.
  let c' : Fin n → realLorentzTensor.Color := c ∘ Fin.succSuccAbove i j
  have hP :
      ∀ t : ℝT(3, c),
        toComplex (c := c') (contrT (S := realLorentzTensor) n i j h t) =
          contrT (S := complexLorentzTensor) n i j
            (by
              -- transport the colour relation along `colorToComplex`
              simpa [Function.comp_apply] using
                And.intro h.1
                  (by
                    simpa [tau_colorToComplex] using congrArg colorToComplex h.2))
            (toComplex (c := c) t) := by
    intro t
    -- Work with the property as a predicate for `induction_on_basis`.
    let P : ℝT(3, c) → Prop := fun t =>
      toComplex (c := c') (contrT (S := realLorentzTensor) n i j h t) =
        contrT (S := complexLorentzTensor) n i j
          (by
            simpa [Function.comp_apply] using
              And.intro h.1
                (by
                  simpa [tau_colorToComplex] using congrArg colorToComplex h.2))
          (toComplex (c := c) t)
    have hP' : P t := by
      -- `induction_on_basis` over the tensor `t`.
      apply
        induction_on_basis
          (c := c)
          (P := P)
          (t := t)
      · -- basis case
        intro b
        -- (Tensor.basis c) b = (Pure.basisVector c b).toTensor;
        -- then equate both sides via toComplex_contrP_basisVector.
        rw [Tensor.basis_apply (S := realLorentzTensor) c b]
        show toComplex (c := c')
            (contrT (S := realLorentzTensor) n i j h ((Pure.basisVector c b).toTensor))
          = contrT (S := complexLorentzTensor) n i j _
            (toComplex (c := c) ((Pure.basisVector c b).toTensor))
        rw [contrT_pure (S := realLorentzTensor) (p := Pure.basisVector c b),
          toComplex_pure_basisVector (c := c) b,
          contrT_pure (S := complexLorentzTensor)
            (p := Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b))]
        exact toComplex_contrP_basisVector h b
      · -- zero tensor
        dsimp [P]
        simp
      · -- scalar multiplication
        intro r t ht
        dsimp [P] at ht ⊢
        refine (by
          simp [map_smul, ht])
      · -- addition
        intro t1 t2 h1 h2
        dsimp [P] at h1 h2 ⊢
        refine (by
          simp [map_add, h1, h2])
    exact hP'
  exact hP t

/-!

### F. Compatibility with evaluation: `evalT`

-/

/-- `complexify` commutes with precomposition by `succAbove`. -/
@[simp]
lemma ComponentIdx.complexify_comp_succAbove
    {n : ℕ} {c : Fin (n + 1) → realLorentzTensor.Color} (i : Fin (n + 1))
    (b : ComponentIdx (S := realLorentzTensor) c) (m : Fin n) :
    (ComponentIdx.complexify (c := c ∘ i.succAbove) (fun k => b (i.succAbove k))) m =
    (ComponentIdx.complexify (c := c) b) (i.succAbove m) := by
  simp only [ComponentIdx.complexify_apply, Function.comp_apply]

/-- Convert an evaluation index from the real repDim to the complex repDim. -/
noncomputable def evalIdxToComplex {n : ℕ}
    {c : Fin (n + 1) → realLorentzTensor.Color} (i : Fin (n + 1))
    (b : Fin 1 ⊕ Fin 3) : Fin (complexLorentzTensor.repDim ((colorToComplex ∘ c) i)) :=
  Fin.cast repDim_colorToComplex.symm (finSumFinEquiv b)

/-- `evalT` on the complex side, but with output colors as `colorToComplex ∘ (c ∘ i.succAbove)`.
Implemented via `permT (σ := id) (by simp)` as a transport. -/
noncomputable def evalTColorToComplex {n : ℕ}
    {c : Fin (n + 1) → realLorentzTensor.Color} (i : Fin (n + 1))
    (b : Fin 1 ⊕ Fin 3) :
    ℂT(colorToComplex ∘ c) → ℂT(colorToComplex ∘ (c ∘ i.succAbove)) :=
  fun t =>
    permT (S := complexLorentzTensor) (σ := (id : Fin n → Fin n))
      (by
        -- transport ((colorToComplex ∘ c) ∘ i.succAbove) and (colorToComplex ∘ (c ∘ i.succAbove))
        simp [Function.comp_apply])
      ((TensorSpecies.Tensor.evalT (S := complexLorentzTensor) (c := (colorToComplex ∘ c))
          i (evalIdxToComplex (c := c) i b)) t)

set_option backward.isDefEq.respectTransparency false in
/-- For a real basis vector, `toComplex(evalP(basisVector c b))` equals
  `evalP(basisVector (colorToComplex ∘ c) (complexify b))` (complex species). -/
lemma toComplex_evalP_basisVector {n : ℕ} {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin 1 ⊕ Fin 3)
    (b' : ComponentIdx (S := realLorentzTensor) c) :
    toComplex (c := c ∘ i.succAbove)
      (Pure.evalP (S := realLorentzTensor) i b (Pure.basisVector c b'))
      =
    permT (S := complexLorentzTensor) (σ := (id : Fin n → Fin n))
      (by simp [Function.comp_apply])
      (Pure.evalP (S := complexLorentzTensor) i (evalIdxToComplex (c := c) i b)
        (Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b'))) := by
  simp only [Pure.evalP]
  have hdrop : (Pure.basisVector c b').drop i =
    Pure.basisVector (c ∘ i.succAbove) (fun k => b' (i.succAbove k)) := by
    ext j; simp only [Pure.drop, Pure.basisVector, Function.comp_apply]
  rw [hdrop, toComplex_map_smul (c ∘ i.succAbove) (Pure.evalPCoeff i b (Pure.basisVector c b'))
    ((Pure.basisVector (c ∘ i.succAbove)) (fun k => b' (i.succAbove k)) |>.toTensor)]
  · -- evalPCoeff: real and complex match; then tensor equality
    simp only [Pure.evalPCoeff, Pure.basisVector, Basis.repr_self, Finsupp.single_apply,
      ComponentIdx.complexify_apply, evalIdxToComplex]
    · by_cases h : b' i = b
      · simp [h]
        have hdrop' : (Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b')).drop i =
          Pure.basisVector (colorToComplex ∘ (c ∘ i.succAbove))
            (ComponentIdx.complexify (c := c ∘ i.succAbove) (fun k => b' (i.succAbove k))) := by
          ext j; simp only [Pure.drop, Pure.basisVector, ComponentIdx.complexify_apply,
            Function.comp_apply]
        rw [hdrop']
        exact (permT_id_self (S := complexLorentzTensor) (c := colorToComplex ∘ (c ∘ i.succAbove))
          (t := (Pure.basisVector (colorToComplex ∘ (c ∘ i.succAbove))
            (ComponentIdx.complexify (c := c ∘ i.succAbove) (fun k => b'
              (i.succAbove k)))).toTensor)).symm
      · simp [h]

/-- The map `toComplex` commutes with `evalT`. -/
lemma evalT_toComplex {n : ℕ}
    {c : Fin (n + 1) → realLorentzTensor.Color}
    (i : Fin (n + 1)) (b : Fin 1 ⊕ Fin 3) (t : ℝT(3, c)) :
    toComplex (c := c ∘ i.succAbove)
        ((TensorSpecies.Tensor.evalT (S := realLorentzTensor) (c := c) i b) t)
      =
    evalTColorToComplex (c := c) i b (toComplex (c := c) t) := by
  classical
  let c' := c ∘ i.succAbove
  let P : ℝT(3, c) → Prop := fun t =>
    toComplex (c := c')
      ((TensorSpecies.Tensor.evalT (S := realLorentzTensor) (c := c) i b) t) =
    evalTColorToComplex (c := c) i b (toComplex (c := c) t)
  have hP : ∀ t, P t := by
    intro t
    apply induction_on_basis (c := c) (P := P) (t := t)
    · intro b'
      rw [Tensor.basis_apply (S := realLorentzTensor) c b']
      simp only [evalTColorToComplex, P]
      rw [evalT_pure (S := realLorentzTensor) (p := Pure.basisVector c b'),
        toComplex_pure_basisVector (c := c) b',
        evalT_pure (S := complexLorentzTensor)
          (p := Pure.basisVector (colorToComplex ∘ c) (ComponentIdx.complexify b'))]
      exact toComplex_evalP_basisVector i b b'
    · dsimp [P]
      simp only [evalTColorToComplex, map_zero]
    · intro r t' ht'
      dsimp [P] at ht' ⊢
      rw [LinearMap.map_smul, toComplex_map_smul (c ∘ i.succAbove) r
        ((evalT (S := realLorentzTensor) i b) t'),
        ht', toComplex_map_smul (c := c) r t']
      simp only [evalTColorToComplex, LinearMap.map_smul]
    · intro t1 t2 h1 h2
      dsimp [P] at h1 h2 ⊢
      rw [LinearMap.map_add, map_add, h1, h2]
      simp only [evalTColorToComplex, LinearMap.map_add]
  exact hP t

end realLorentzTensor
