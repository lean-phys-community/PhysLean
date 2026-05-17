/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Metrics.Pre
public import Physlib.Relativity.Tensors.Contraction.Basis
public import Physlib.Relativity.Tensors.Elab
meta import Mathlib.Tactic.Cases
/-!

## Real Lorentz tensors

Within this directory `Pre` is used to denote that the definitions are preliminary and
which are used to define `realLorentzTensor`.

-/

@[expose] public section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open MonoidalCategory

namespace realLorentzTensor

/-- The colors associated with complex representations of SL(2, ℂ) of interest to physics. -/
inductive Color
  /-- The color associated with contravariant Lorentz vectors. -/
  | up : Color
  /-- The color associated with covariant Lorentz vectors. -/
  | down : Color

/-- Color for complex Lorentz tensors is decidable. -/
instance : DecidableEq Color := fun x y =>
  match x, y with
  | Color.up, Color.up => isTrue rfl
  | Color.down, Color.down => isTrue rfl
  /- The false -/
  | Color.up, Color.down => isFalse fun h => Color.noConfusion h
  | Color.down, Color.up => isFalse fun h => Color.noConfusion h

end realLorentzTensor

noncomputable section
open realLorentzTensor in
/-- The tensor structure for complex Lorentz tensors. -/
def realLorentzTensor (d : ℕ := 3) : TensorSpecies ℝ realLorentzTensor.Color
    (LorentzGroup d) (fun _ => Fin 1 ⊕ Fin d) where
  FD := Discrete.functor fun c =>
    match c with
    | Color.up => Lorentz.Contr d
    | Color.down => Lorentz.Co d
  τ := fun c =>
    match c with
    | Color.up => Color.down
    | Color.down => Color.up
  τ_involution c := by
    match c with
    | Color.up => rfl
    | Color.down => rfl
  contr := Discrete.natTrans fun c =>
    match c with
    | Discrete.mk Color.up => Lorentz.contrCoContract
    | Discrete.mk Color.down => Lorentz.coContrContract
  metric := Discrete.natTrans fun c =>
    match c with
    | Discrete.mk Color.up => Lorentz.preContrMetric d
    | Discrete.mk Color.down => Lorentz.preCoMetric d
  unit := Discrete.natTrans fun c =>
    match c with
    | Discrete.mk Color.up => Lorentz.preCoContrUnit d
    | Discrete.mk Color.down => Lorentz.preContrCoUnit d
  basis := fun c =>
    match c with
    | Color.up => Lorentz.contrBasis d
    | Color.down => Lorentz.coBasis d
  contr_tmul_symm := fun c =>
    match c with
    | Color.up => Lorentz.contrCoContract_tmul_symm
    | Color.down => Lorentz.coContrContract_tmul_symm
  contr_unit := fun c =>
    match c with
    | Color.up => Lorentz.contr_preCoContrUnit
    | Color.down => Lorentz.contr_preContrCoUnit
  unit_symm := fun c =>
    match c with
    | Color.up => Lorentz.preCoContrUnit_symm
    | Color.down => Lorentz.preContrCoUnit_symm
  contr_metric := fun c =>
    match c with
    | Color.up => Lorentz.contrCoContract_apply_metric
    | Color.down => Lorentz.coContrContract_apply_metric

namespace realLorentzTensor

/-- Notation for a real Lorentz tensor. -/
syntax (name := realLorentzTensorSyntax) "ℝT[" term,* "]" : term

macro_rules
  | `(ℝT[$termDim:term, $term:term, $terms:term,*]) =>
      `(((realLorentzTensor $termDim).Tensor (vecCons $term ![$terms,*])))
  | `(ℝT[$termDim:term, $term:term]) =>
    `(((realLorentzTensor $termDim).Tensor (vecCons $term ![])))
  | `(ℝT[$termDim:term]) =>`(((realLorentzTensor $termDim).Tensor (vecEmpty)))
  | `(ℝT[]) =>`(((realLorentzTensor 3).Tensor (vecEmpty)))

set_option quotPrecheck false in
/-- Notation for a real Lorentz tensor. -/
scoped[realLorentzTensor] notation "ℝT(" d "," c ")" =>
  (realLorentzTensor d).Tensor c

/-!

## Basis and discrete functor objects

These re-express fields of `realLorentzTensor d` in terms of `Lorentz` data.

-/



@[simp]
lemma basisIdxCongr_eq_refl {d : ℕ} {c1 c2 : realLorentzTensor.Color} (h : c1 = c2) :
    TensorSpecies.basisIdxCongr (basisIdx := fun _ => Fin 1 ⊕ Fin d) h = Equiv.refl _ := by
  rfl


lemma basisIdxCongr_apply {d : ℕ} {c1 c2 : realLorentzTensor.Color} (h : c1 = c2)
    (i : Fin 1 ⊕ Fin d) :
    TensorSpecies.basisIdxCongr (basisIdx := fun _ => Fin 1 ⊕ Fin d) h i = i := by
  simp

lemma basis_eq_contrBasis {d : ℕ} :
    (realLorentzTensor d).basis Color.up = Lorentz.contrBasis (d := d) := rfl

lemma basis_eq_coBasis {d : ℕ} :
    (realLorentzTensor d).basis Color.down = Lorentz.coBasis (d := d) := rfl

lemma FD_obj_up {d : ℕ} :
    (realLorentzTensor d).FD.obj { as := Color.up } = Lorentz.Contr d := rfl

lemma FD_obj_down {d : ℕ} :
    (realLorentzTensor d).FD.obj { as := Color.down } = Lorentz.Co d := rfl

/-!

## Simplifying τ

-/

@[simp]
lemma τ_up_eq_down {d : ℕ} : (realLorentzTensor d).τ Color.up = Color.down := rfl

@[simp]
lemma τ_down_eq_up {d : ℕ} : (realLorentzTensor d).τ Color.down = Color.up := rfl

/-!

## Simplification of contractions with respect to basis

-/

open TensorSpecies

set_option backward.isDefEq.respectTransparency false in
lemma contr_basis {d : ℕ} {c : realLorentzTensor.Color}
    (i : Fin 1 ⊕ Fin d)
    (j : Fin 1 ⊕ Fin d) :
    (realLorentzTensor d).castToField
      (((realLorentzTensor d).contr.app (Discrete.mk c)).hom
      ((realLorentzTensor d).basis c i ⊗ₜ
      (realLorentzTensor d).basis ((realLorentzTensor d).τ c) j))
      = (if i = j then 1 else 0) := by
  match c with
  | .up =>
    change Lorentz.contrCoContract.hom
      (Lorentz.contrBasis d i ⊗ₜ Lorentz.coBasis d j) = _
    rw [Lorentz.contrCoContract_hom_tmul]
    simp only [Rep.tensorUnit_V, Lorentz.contrBasis_toFin1dℝ, Lorentz.coBasis_toFin1dℝ,
      dotProduct_single, mul_one]
    rw [Pi.single_apply]
    refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
    simp only [eq_comm]
  | .down =>
    change Lorentz.coContrContract.hom
      (Lorentz.coBasis d i ⊗ₜ Lorentz.contrBasis d j) = _
    rw [Lorentz.coContrContract_hom_tmul]
    simp only [Rep.tensorUnit_V, Lorentz.coBasis_toFin1dℝ, Lorentz.contrBasis_toFin1dℝ,
      dotProduct_single, mul_one]
    rw [Pi.single_apply]
    refine ite_congr ?_ (congrFun rfl) (congrFun rfl)
    simp only [eq_comm]

open Tensor
lemma contrT_basis_repr_apply_eq_dropPairSection {n d: ℕ}
    {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)} (h : i ≠ j ∧ (realLorentzTensor d).τ (c i) = c j)
    (t : ℝT(d, c)) (b : ComponentIdx (c ∘ Pure.dropPairEmb i j)) :
    (basis (c ∘ Pure.dropPairEmb i j)).repr (contrT n i j h t) b =
    ∑ (x : b.DropPairSection),
    ((basis c).repr t x.1) *
    if (x.1 i) = (x.1 j) then 1 else 0 := by
  rw [contrT_basis_repr_apply]
  congr
  funext x
  congr 1
  rw [contr_basis]
  rfl

open ComponentIdx in
lemma contrT_basis_repr_apply_eq_fin {n d: ℕ} {c : Fin (n + 1 + 1) → realLorentzTensor.Color}
    {i j : Fin (n + 1 + 1)}
    {h : i ≠ j ∧ (realLorentzTensor d).τ (c i) = c j}
    (t : ℝT(d,c)) (b : ComponentIdx (c ∘ Pure.dropPairEmb i j)) :
    (basis (c ∘ Pure.dropPairEmb i j)).repr (contrT n i j h t) b =
    ∑ (x : Fin 1 ⊕ Fin d),
    ((basis c).repr t
    (DropPairSection.ofFinEquiv h.1 b ⟨x, x⟩)) := by
  rw [contrT_basis_repr_apply_eq_sum_fin]
  congr
  funext x
  rw [Finset.sum_eq_single (x)]
  · rw [contr_basis]
    simp
  · intro y _ hy
    rw [contr_basis, if_neg]
    · simp_all
    · simp only [basisIdxCongr_apply]
      exact Ne.symm hy
  · simp

/-!

## Contractions and to Field

-/

attribute [-simp] Fintype.sum_sum_type

lemma contrPCoeff_basis {d n : ℕ} {c : Fin n → realLorentzTensor.Color} (i j : Fin n)
    (hij : i ≠ j ∧ (realLorentzTensor d).τ (c i) = c j)
    (b : ComponentIdx (S := realLorentzTensor d) c) :
    Pure.contrPCoeff i j hij (Pure.basisVector c b) = if b i = b j then 1 else 0 := by
  simp only [Pure.contrPCoeff, Monoidal.tensorUnit_obj, Rep.tensorUnit_V, Rep.tensorUnit_ρ,
    Functor.comp_obj, Discrete.functor_obj_eq_as, Function.comp_apply, Pure.basisVector]
  generalize b i = b1 at *
  generalize b j = b2 at *
  suffices h : ∀ c, ∀ c1,  (hc : (realLorentzTensor d).τ c = c1) →
    (realLorentzTensor d).castToField ((ConcreteCategory.hom
    ((realLorentzTensor d).contr.app { as :=c }))
    (((realLorentzTensor d).basis c) b1 ⊗ₜ[ℝ]
      (ConcreteCategory.hom ((realLorentzTensor d).FD.map (eqToHom (by simp_all))))
      (((realLorentzTensor d).basis c1) b2))) =
    if b1 = b2 then 1 else 0 by
    exact h (c i) (c j) hij.2
  rintro c c1 rfl
  exact contr_basis _ _

lemma contrT_eq_sum_evalT {n} {d} (c : Fin (n + 1 + 1) → Color) (i j : Fin (n + 1 + 1))
    (h : i ≠ j ∧ (realLorentzTensor d).τ (c i) = c j) (t : ℝT(d, c)) :
    contrT n i j h t =  ∑ (μ : Fin 1 ⊕ Fin d), permT id (by
      simp [Pure.dropPairEmb_eq_predAbove h.1])
     (evalT ((Fin.predAbove 0 i).predAbove j) μ (evalT i μ t)) := by
  induction' t using Tensor.induction_on_basis with b r t h t1 t2 h1 h2
  · rw [contrT_basis]
    simp only [ contrPCoeff_basis, ite_smul, one_smul, zero_smul]
    conv_rhs =>
      enter [2, μ];
      simp only [evalT_basis, Fin.zero_succAbove, apply_ite, Fin.succ_zero_eq_one, map_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    have h0 : i.succAbove ((Fin.predAbove 0 i).predAbove j) = j := by
      rcases i.eq_zero_or_eq_succ with rfl | ⟨k, rfl⟩
      · exact Fin.succAbove_predAbove (Ne.symm h.1)
      · rw [Fin.predAbove_zero_succ]
        exact Fin.succ_succAbove_predAbove (Ne.symm h.1)
    rw [h0]
    split_ifs with h₁ _ h₂
    · rw [permT_basis]
      congr
      ext x
      simp only [Function.comp_apply, ComponentIdx.dropPair, id_eq, basisIdxCongr_eq_refl,
        Equiv.refl_apply]
      rw [Pure.dropPairEmb_eq_predAbove h.1]
    · symm at h₁; contradiction
    · symm at h₂; contradiction
    · rfl
  · simp
  · simp [Finset.smul_sum, h]
  · simp [h1, h2, Finset.sum_add_distrib]

lemma contrT_toField {d} (c : Fin 2 → Color)
    (h : 0 ≠ 1 ∧ (realLorentzTensor d).τ (c 0) = c 1) (t : ℝT(d, c)) :
    (contrT 0 0 1 h t).toField = ∑ (μ : Fin 1 ⊕ Fin d), {t | [μ] [μ]}ᵀ.toField := by
  rw [contrT_eq_sum_evalT, map_sum, Tensorial.self_toTensor_apply]
  congr
  ext μ
  simp only [toField_permT]
  rfl

end realLorentzTensor
end
