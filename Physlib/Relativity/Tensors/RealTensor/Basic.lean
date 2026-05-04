/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Metrics.Pre
public import Physlib.Relativity.Tensors.Contraction.Basis
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
lemma basisIdxCongr_apply {d : ℕ} {c1 c2 : realLorentzTensor.Color} (h : c1 = c2)
    (i : Fin 1 ⊕ Fin d) :
    TensorSpecies.basisIdxCongr (basisIdx := fun _ => Fin 1 ⊕ Fin d) h i = i := by
  rfl

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

end realLorentzTensor
end
