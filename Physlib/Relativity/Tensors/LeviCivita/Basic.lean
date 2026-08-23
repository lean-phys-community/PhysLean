/-
Copyright (c) 2026 Robert Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Sneiderman
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Basic
public import Physlib.Relativity.Tensors.UnitTensor
public import Physlib.Meta.Sorry
public import Physlib.Relativity.Tensors.OfInt
public import Physlib.Mathematics.LeviCivita.Basic
public import Physlib.Mathematics.KroneckerDelta.Contraction
public import Physlib.Relativity.Tensors.RealTensor.Metrics.Basic
/-!

# The Levi-Civita tensor as a real Lorentz tensor

## i. Overview

This file defines the rank-four Levi-Civita tensor `εᵘᵛᵖᵟ` as a real Lorentz tensor in
`d = 3` spatial dimensions, with `ε⁰¹²³ = 1`, and proves its antisymmetry under each
adjacent transposition of indices.

The component on a multi-index `f` is the generalized Kronecker delta of `f` against the
identity, i.e. the sign of `f` when `f` is a permutation and `0` otherwise. The integer
components are carried by `TensorSpecies.Tensor.TensorInt.toTensor`.

## ii. Key results

- `leviCivita` : the rank-four Levi-Civita tensor `ε4`, with `ε⁰¹²³ = 1`.
- `leviCivita_basis_repr_apply` : its standard-basis components as a generalized Kronecker delta.
- `leviCivita_basis_repr_eq_leviCivitaSymbol` : its standard-basis components as the
  general-dimension Levi-Civita symbol `leviCivitaSymbol` at `ι = Fin 4`.
- `leviCivita_antisymm`, `leviCivita_antisymm_mid`, `leviCivita_antisymm_last` : antisymmetry
  under each adjacent transposition of the indices.

## iii. Table of contents

- A. Definition
- B. Components in the standard basis
- C. Antisymmetry

## iv. References

-/

@[expose] public section

open Matrix
open MatrixGroups
open TensorProduct
noncomputable section

namespace realLorentzTensor
open TensorSpecies
open Tensor
open KroneckerDelta

/-!

## A. Definition

-/

/-- The Levi-Civita tensor `εᵘᵛᵖᵟ` as a real Lorentz tensor in `d = 3`, with `ε⁰¹²³ = 1`.

The component on a multi-index `f` is the generalized Kronecker delta of `f` against the
identity, i.e. the sign of `f` when `f` is a permutation and `0` otherwise. -/
noncomputable def leviCivita : ℝT[3, .up, .up, .up, .up] :=
  TensorInt.toTensor (S := realLorentzTensor 3)
    (c := ![Color.up, Color.up, Color.up, Color.up]) fun f =>
    generalizedKroneckerDelta (fun i => finSumFinEquiv (f i)) (id : Fin 4 → Fin 4)

/-- The Levi-Civita tensor `εᵘᵛᵖᵟ` as a real Lorentz tensor. -/
scoped[realLorentzTensor] notation "ε4" => leviCivita

/-- The `TensorInt.toTensor` form of the Levi-Civita tensor. -/
lemma leviCivita_eq_ofInt : ε4 =
    TensorInt.toTensor (S := realLorentzTensor 3)
    (c := ![Color.up, Color.up, Color.up, Color.up]) fun f =>
    generalizedKroneckerDelta (fun i => finSumFinEquiv (f i)) (id : Fin 4 → Fin 4) :=
  rfl

/-- The Euclidean Levi-Civita symbol `ε_{ijkl}` in dimension 4. -/
def _root_.euclidLeviCivita (g : Fin 4 → Fin 4) : ℝ :=
  generalizedKroneckerDelta g (id : Fin 4 → Fin 4)

/-- The Euclidean Levi-Civita symbol in dimension 4 is the general-dimension
Levi-Civita symbol `leviCivitaSymbol` at `ι = Fin 4`, carried to the reals. -/
lemma _root_.euclidLeviCivita_eq_leviCivitaSymbol (g : Fin 4 → Fin 4) :
    euclidLeviCivita g = (leviCivitaSymbol g : ℝ) :=
  rfl

/-!

## B. Components in the standard basis

-/

/-- The components of the Levi-Civita tensor in the standard basis are the generalized
Kronecker delta of the multi-index against the identity. -/
lemma leviCivita_basis_repr_apply
    (b : ComponentIdx (S := realLorentzTensor 3) ![Color.up, Color.up, Color.up, Color.up]) :
    (Tensor.basis _).repr ε4 b
      = (generalizedKroneckerDelta (fun i => finSumFinEquiv (b i)) (id : Fin 4 → Fin 4) : ℝ) := by
  rw [leviCivita_eq_ofInt, TensorInt.basis_repr_apply]

/-- The components of the Levi-Civita tensor in the standard basis are the
general-dimension Levi-Civita symbol `leviCivitaSymbol` of the multi-index at
`ι = Fin 4`. -/
lemma leviCivita_basis_repr_eq_leviCivitaSymbol
    (b : ComponentIdx (S := realLorentzTensor 3) ![Color.up, Color.up, Color.up, Color.up]) :
    (Tensor.basis _).repr ε4 b
      = (leviCivitaSymbol (fun i => finSumFinEquiv (b i)) : ℝ) :=
  leviCivita_basis_repr_apply b

/-- The Levi-Civita tensor vanishes on any multi-index with a repeated value: if two distinct
index positions `i ≠ j` carry the same basis index, the component is zero. -/
lemma leviCivita_basis_repr_eq_zero_of_eq
    {b : ComponentIdx (S := realLorentzTensor 3) ![Color.up, Color.up, Color.up, Color.up]}
    {i j : Fin 4} (hij : i ≠ j) (h : b i = b j) :
    (Tensor.basis _).repr ε4 b = 0 := by
  rw [leviCivita_basis_repr_apply]
  have hdet : generalizedKroneckerDelta (fun i => finSumFinEquiv (b i))
      (id : Fin 4 → Fin 4) = 0 := by
    rw [show generalizedKroneckerDelta (fun i => finSumFinEquiv (b i)) (id : Fin 4 → Fin 4)
          = Matrix.det (fun a c => ((kroneckerDelta (finSumFinEquiv (b a)) (id c) : ℕ) : ℤ))
          from rfl]
    refine Matrix.det_zero_of_row_eq hij (funext fun c => ?_)
    rw [congrArg (⇑finSumFinEquiv) h]
  rw [hdet, Int.cast_zero]

/-!

## C. Antisymmetry

-/

/-- The Levi-Civita tensor is antisymmetric in its first two indices
`{ε4 | μ ν ρ σ = - ε4 | ν μ ρ σ}ᵀ`. -/
lemma leviCivita_antisymm : {ε4 | μ ν ρ σ = - (ε4 | ν μ ρ σ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply, leviCivita_eq_ofInt, TensorInt.basis_repr_apply,
    map_neg, Finsupp.neg_apply, TensorInt.basis_repr_apply, ← Int.cast_neg]
  congr 1
  rw [← generalizedKroneckerDelta_swap _ _ (Fin.zero_ne_one (n := 2))]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The Levi-Civita tensor is antisymmetric in its middle two indices
`{ε4 | μ ν ρ σ = - ε4 | μ ρ ν σ}ᵀ`. -/
lemma leviCivita_antisymm_mid : {ε4 | μ ν ρ σ = - (ε4 | μ ρ ν σ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply, leviCivita_eq_ofInt, TensorInt.basis_repr_apply,
    map_neg, Finsupp.neg_apply, TensorInt.basis_repr_apply, ← Int.cast_neg]
  congr 1
  rw [← generalizedKroneckerDelta_swap _ _ (show (1 : Fin 4) ≠ 2 by decide)]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The Levi-Civita tensor is antisymmetric in its last two indices
`{ε4 | μ ν ρ σ = - ε4 | μ ν σ ρ}ᵀ`. -/
lemma leviCivita_antisymm_last : {ε4 | μ ν ρ σ = - (ε4 | μ ν σ ρ)}ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  rw [permT_basis_repr_symm_apply, leviCivita_eq_ofInt, TensorInt.basis_repr_apply,
    map_neg, Finsupp.neg_apply, TensorInt.basis_repr_apply, ← Int.cast_neg]
  congr 1
  rw [← generalizedKroneckerDelta_swap _ _ (show (2 : Fin 4) ≠ 3 by decide)]
  congr 1
  funext i
  fin_cases i <;> rfl

open TensorSpecies Tensor

/-!

## D. Component-level API used by the contraction identities

-/

lemma ofFinEquiv_apply_succSuccAbove {k' : Type} [CommRing k'] {C G : Type} [Group G]
    {V : C → Type} [∀ c, AddCommGroup (V c)] [∀ c, Module k' (V c)]
    {basisIdx : C → Type} [∀ c, Fintype (basisIdx c)] [∀ c, DecidableEq (basisIdx c)]
    {rep : (c : C) → Representation k' G (V c)}
    {bb : (c : C) → Module.Basis (basisIdx c) k' (V c)}
    {S : TensorSpecies k' C G V basisIdx rep bb}
    {n : ℕ} {c : Fin (n+1+1) → C} {i j : Fin (n+1+1)} (hij : i ≠ j)
    (b : ComponentIdx (S := S) (c ∘ Fin.succSuccAbove i j))
    (x : basisIdx (c i) × basisIdx (c j)) (m : Fin n) :
    (ComponentIdx.DropPairSection.ofFinEquiv (S := S) hij b x).1 (Fin.succSuccAbove i j m)
      = b m :=
  (ComponentIdx.DropPairSection.mem_iff_apply_succSuccAbove_eq _ _).mp
    (ComponentIdx.DropPairSection.ofFinEquiv (S := S) hij b x).2 m

lemma crossToEnd_basis_repr {d nA nB : ℕ} {cA : Fin (nA+1) → Color} {cB : Fin (nB+1) → Color}
    (i : Fin (nA+1)) (j : Fin (nB+1)) (hc : (realLorentzTensor d).τ (cA i) = cB j)
    (t : ℝT(d, cA)) (M : ℝT(d, cB))
    (b : ComponentIdx (S := realLorentzTensor d)
      (Fin.append (cA ∘ i.succAbove) (cB ∘ j.succAbove))) :
    (Tensor.basis _).repr (crossToEnd i j hc t M) b
      = ∑ x : Fin 1 ⊕ Fin d,
          (Tensor.basis cA).repr t (i.insertNth x (fun m => b (Fin.castAdd nB m)))
          * (Tensor.basis cB).repr M (j.insertNth x (fun m => b (Fin.natAdd nA m))) := by
  rw [crossToEnd]
  simp only [LinearMap.compr₂_apply, LinearMap.comp_apply]
  rw [permT_basis_repr_symm_apply, contrT_basis_repr_apply_eq_fin]
  conv_lhs => enter [2, x]; rw [permT_basis_repr_symm_apply, prodT_basis_repr_apply]
  simp only [basisIdxCongr_eq_refl, Equiv.refl_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [ComponentIdx.prod, Equiv.coe_fn_mk, basisIdxCongr_eq_refl, Equiv.refl_apply]
  congr 1
  · congr 1
    funext m
    rw [IsReindexing.inv_cast_eq]
    induction m using Fin.succAboveCases (i := i) with
    | x =>
      rw [Fin.insertNth_apply_same]
      exact ComponentIdx.DropPairSection.ofFinEquiv_apply_fst _ _ _
    | p k =>
      rw [Fin.insertNth_apply_succAbove]
      conv_lhs => rw [← Fin.succSuccAbove_castAdd_natAdd_apply_castAdd i j k]
      simp only [Fin.cast_cast, Fin.cast_eq_self]
      rw [ofFinEquiv_apply_succSuccAbove]
      simp only [basisIdxCongr_eq_refl, Equiv.refl_apply]
      exact congrArg b (IsReindexing.inv_id_eq _ _)
  · congr 1
    funext m
    rw [IsReindexing.inv_cast_eq]
    induction m using Fin.succAboveCases (i := j) with
    | x =>
      rw [Fin.insertNth_apply_same]
      exact ComponentIdx.DropPairSection.ofFinEquiv_apply_snd _ _ _
    | p k =>
      rw [Fin.insertNth_apply_succAbove]
      conv_lhs => rw [← Fin.succSuccAbove_castAdd_natAdd_apply_natAdd i j k]
      simp only [Fin.cast_cast, Fin.cast_eq_self]
      rw [ofFinEquiv_apply_succSuccAbove]
      simp only [basisIdxCongr_eq_refl, Equiv.refl_apply]
      exact congrArg b (IsReindexing.inv_id_eq _ _)

lemma crossToSlot_basis_repr {d nA : ℕ} {c : Fin (nA+1) → Color} {cM : Fin 2 → Color}
    (i : Fin (nA+1)) (j : Fin 2) (hc : (realLorentzTensor d).τ (c i) = cM j)
    (M : ℝT(d, cM)) (t : ℝT(d, c))
    (b : ComponentIdx (S := realLorentzTensor d)
      (Function.update c i (cM (j.succAbove 0)))) :
    (Tensor.basis _).repr (crossToSlot i j hc M t) b
      = ∑ x : Fin 1 ⊕ Fin d,
          (Tensor.basis c).repr t (i.insertNth x (fun m => b (i.succAbove m)))
          * (Tensor.basis cM).repr M (j.insertNth x (fun _ => b i)) := by
  rw [crossToSlot_eq_crossToEnd, permT_basis_repr_symm_apply, crossToEnd_basis_repr]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [basisIdxCongr_eq_refl, Equiv.refl_apply]
  congr 2
  · funext m
    induction m using Fin.succAboveCases (i := i) with
    | x => rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
    | p k =>
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      refine congrArg b ?_
      rw [IsReindexing.inv_equiv_symm_eq, ← Fin.append_succAbove_const_eq_cycleIcc i,
        Fin.append_left]
  · funext m
    induction m using Fin.succAboveCases (i := j) with
    | x => rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same]
    | p k =>
      rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]
      refine congrArg b ?_
      rw [IsReindexing.inv_equiv_symm_eq, ← Fin.append_succAbove_const_eq_cycleIcc i,
        Fin.append_right]

lemma metricTensor_repr_apply {d : ℕ} (cc : Color)
    (b : ComponentIdx (S := realLorentzTensor d) ![cc, cc]) :
    (Tensor.basis _).repr (metricTensor (S := realLorentzTensor d) cc) b
      = minkowskiMatrix (b 0) (b 1) := by
  match cc with
  | Color.up => exact contrMetric_repr_apply_eq_minkowskiMatrix b
  | Color.down => exact coMetric_repr_apply_eq_minkowskiMatrix b

set_option backward.isDefEq.respectTransparency false in
lemma toDualMapAtIndex_basis_repr {d nA : ℕ} {c : Fin (nA+1) → Color}
    (i : Fin (nA+1)) (t : ℝT(d, c))
    (b : ComponentIdx (S := realLorentzTensor d)
      (Function.update c i ((realLorentzTensor d).τ (c i)))) :
    (Tensor.basis _).repr (Tensor.toDualMapAtIndex (S := realLorentzTensor d) i t) b
      = ∑ x : Fin 1 ⊕ Fin d,
          (Tensor.basis c).repr t (i.insertNth x (fun m => b (i.succAbove m)))
          * minkowskiMatrix x (b i) := by
  have h := crossToSlot_basis_repr (d := d) i (0 : Fin 2) (rfl)
      (metricTensor (S := realLorentzTensor d) ((realLorentzTensor d).τ (c i))) t b
  refine h.trans (Finset.sum_congr rfl fun x _ => ?_)
  congr 1
  rw [metricTensor_repr_apply]
  congr 1

open ComponentIdx.DropPairSection in
lemma section_chain {cA cB : Fin 4 → Color}
    (h1 : (0 : Fin (0+1+1)) ≠ 1) (h2 : (1 : Fin (2+1+1)) ≠ 3)
    (h3 : (2 : Fin (4+1+1)) ≠ 5) (h4 : (3 : Fin (6+1+1)) ≠ 7)
    (x x1 x2 x3 : Fin 1 ⊕ Fin 3) :
    ((ofFinEquiv (S := realLorentzTensor 3) (c := Fin.append cA cB) h4
        ((ofFinEquiv h3
            ((ofFinEquiv h2
                ((ofFinEquiv h1 (fun j => j.elim0) (x, x)).1) (x1, x1)).1) (x2, x2)).1)
          (x3, x3)).1 : Fin (6+1+1) → Fin 1 ⊕ Fin 3)
      = ![x, x1, x2, x3, x, x1, x2, x3] := by
  funext m
  fin_cases m <;> rfl

lemma prod_fst_vec {cA cB : Fin 4 → Color} (y0 y1 y2 y3 y4 y5 y6 y7 : Fin 1 ⊕ Fin 3) :
    (((ComponentIdx.prod (S := realLorentzTensor 3) (c := cA) (c1 := cB))
        (![y0,y1,y2,y3,y4,y5,y6,y7] : Fin (4+4) → Fin 1 ⊕ Fin 3)).1 :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![y0,y1,y2,y3] := by
  funext m; fin_cases m <;> rfl

lemma prod_snd_vec {cA cB : Fin 4 → Color} (y0 y1 y2 y3 y4 y5 y6 y7 : Fin 1 ⊕ Fin 3) :
    (((ComponentIdx.prod (S := realLorentzTensor 3) (c := cA) (c1 := cB))
        (![y0,y1,y2,y3,y4,y5,y6,y7] : Fin (4+4) → Fin 1 ⊕ Fin 3)).2 :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![y4,y5,y6,y7] := by
  funext m; fin_cases m <;> rfl

section Nest
variable (x x1 x2 x3 y0 y1 y2 y3 : Fin 1 ⊕ Fin 3)

lemma nest3 : (Fin.insertNth (3 : Fin (3+1)) y3
    (fun m => ![x, x1, x2, x3] (Fin.succAbove 3 m)) : Fin 4 → Fin 1 ⊕ Fin 3)
      = ![x, x1, x2, y3] := by
  funext m; fin_cases m <;> rfl

lemma nest2 : (Fin.insertNth (2 : Fin (3+1)) y2
    (fun m => (![x, x1, x2, y3] : Fin 4 → Fin 1 ⊕ Fin 3) (Fin.succAbove 2 m)) :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![x, x1, y2, y3] := by
  funext m; fin_cases m <;> rfl

lemma nest1 : (Fin.insertNth (1 : Fin (3+1)) y1
    (fun m => (![x, x1, y2, y3] : Fin 4 → Fin 1 ⊕ Fin 3) (Fin.succAbove 1 m)) :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![x, y1, y2, y3] := by
  funext m; fin_cases m <;> rfl

lemma nest0 : (Fin.insertNth (0 : Fin (3+1)) y0
    (fun m => (![x, y1, y2, y3] : Fin 4 → Fin 1 ⊕ Fin 3) (Fin.succAbove 0 m)) :
      Fin 4 → Fin 1 ⊕ Fin 3) = ![y0, y1, y2, y3] := by
  funext m; fin_cases m <;> rfl

end Nest

lemma vec4_0 {a b c e : Fin 1 ⊕ Fin 3} :
    (![a,b,c,e] : Fin 4 → Fin 1 ⊕ Fin 3) 0 = a := rfl
lemma vec4_1 {a b c e : Fin 1 ⊕ Fin 3} :
    (![a,b,c,e] : Fin 4 → Fin 1 ⊕ Fin 3) 1 = b := rfl
lemma vec4_2 {a b c e : Fin 1 ⊕ Fin 3} :
    (![a,b,c,e] : Fin 4 → Fin 1 ⊕ Fin 3) 2 = c := rfl
lemma vec4_3 {a b c e : Fin 1 ⊕ Fin 3} :
    (![a,b,c,e] : Fin 4 → Fin 1 ⊕ Fin 3) 3 = e := rfl

lemma sum_mul_eta {d : ℕ} (f : (Fin 1 ⊕ Fin d) → ℝ) (y : Fin 1 ⊕ Fin d) :
    ∑ z : Fin 1 ⊕ Fin d, f z * minkowskiMatrix z y = f y * minkowskiMatrix y y := by
  refine Finset.sum_eq_single y (fun z _ hz => ?_) (fun h => absurd (Finset.mem_univ y) h)
  rw [minkowskiMatrix.off_diag_zero hz, mul_zero]

/-- Bundling four independent basis indices into one component index. -/
def vec4Equiv :
    ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3))
      ≃ (Fin 4 → Fin 1 ⊕ Fin 3) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  invFun v := (v 0, v 1, v 2, v 3)
  left_inv p := rfl
  right_inv v := by funext m; fin_cases m <;> rfl

/-- Bundling three independent basis indices into one component index. -/
def vec3Equiv :
    ((Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3) × (Fin 1 ⊕ Fin 3)) ≃ (Fin 3 → Fin 1 ⊕ Fin 3) where
  toFun p := ![p.1, p.2.1, p.2.2]
  invFun v := (v 0, v 1, v 2)
  left_inv p := rfl
  right_inv v := by funext m; fin_cases m <;> rfl

lemma sum4_eq {M : Type} [AddCommMonoid M] (F : (Fin 4 → Fin 1 ⊕ Fin 3) → M) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3, ∑ x3 : Fin 1 ⊕ Fin 3,
        F ![x, x1, x2, x3]
      = ∑ v : Fin 4 → Fin 1 ⊕ Fin 3, F v := by
  rw [← Equiv.sum_comp vec4Equiv F]
  simp only [Fintype.sum_prod_type]
  rfl

lemma sum_reindex_finSumFinEquiv {M : Type} [AddCommMonoid M] (F : (Fin 4 → Fin 4) → M) :
    ∑ v : Fin 4 → Fin 1 ⊕ Fin 3, F (fun i => finSumFinEquiv (v i))
      = ∑ g : Fin 4 → Fin 4, F g := by
  exact Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin 4))
    (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4)) _ _ (fun _ => rfl)

lemma prod_eta_diag_of_injective {v : Fin 4 → Fin 1 ⊕ Fin 3} (hv : Function.Injective v) :
    minkowskiMatrix (v 0) (v 0) * minkowskiMatrix (v 1) (v 1) *
      minkowskiMatrix (v 2) (v 2) * minkowskiMatrix (v 3) (v 3) = -1 := by
  have hbij : Function.Bijective v :=
    (Fintype.bijective_iff_injective_and_card v).mpr ⟨hv, by simp⟩
  have h1 : ∏ i : Fin 4, minkowskiMatrix (v i) (v i)
      = ∏ y : Fin 1 ⊕ Fin 3, minkowskiMatrix y y :=
    Equiv.prod_comp (Equiv.ofBijective v hbij) (fun y => minkowskiMatrix y y)
  rw [Fin.prod_univ_four] at h1
  rw [h1]
  rw [Fintype.prod_sum_type]
  simp only [minkowskiMatrix.inr_i_inr_i, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num

open KroneckerDelta in
/-- Abbreviation for the summand of the fully contracted epsilon-epsilon sum. -/
noncomputable def epsEtaSummand (v : Fin 4 → Fin 1 ⊕ Fin 3) : ℝ :=
  ((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ) *
    (((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
      * minkowskiMatrix (v 0) (v 0) * minkowskiMatrix (v 1) (v 1)
      * minkowskiMatrix (v 2) (v 2) * minkowskiMatrix (v 3) (v 3))

open KroneckerDelta in
lemma epsEtaSummand_eq (v : Fin 4 → Fin 1 ⊕ Fin 3) : epsEtaSummand v =
    - (((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
      * ((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) : ℝ)) := by
  rw [epsEtaSummand]
  by_cases hA : generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
      (id : Fin 4 → Fin 4) = 0
  · rw [hA]; norm_num
  · have hinj : Function.Injective (fun i => finSumFinEquiv (v i)) := by
      by_contra hni
      exact hA (leviCivitaSymbol_eq_zero_of_not_injective hni)
    have hv : Function.Injective v := Function.Injective.of_comp hinj
    have hp := prod_eta_diag_of_injective hv
    linear_combination
      (((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) : ℝ) *
        ((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) : ℝ)) * hp

open KroneckerDelta in
lemma sum_epsEtaSummand : ∑ v : Fin 4 → Fin 1 ⊕ Fin 3, epsEtaSummand v = -24 := by
  have hsum : ∑ v : Fin 4 → Fin 1 ⊕ Fin 3,
      (generalizedKroneckerDelta (fun i => finSumFinEquiv (v i)) (id : Fin 4 → Fin 4)
        * generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) = 24 := by
    rw [sum_reindex_finSumFinEquiv (fun g => generalizedKroneckerDelta g (id : Fin 4 → Fin 4)
      * generalizedKroneckerDelta g (id : Fin 4 → Fin 4))]
    exact sum_generalizedKroneckerDelta_mul_self
  have h : (∑ v : Fin 4 → Fin 1 ⊕ Fin 3,
      (((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
          (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * ((generalizedKroneckerDelta (fun i => finSumFinEquiv (v i))
            (id : Fin 4 → Fin 4) : ℤ) : ℝ))) = 24 := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hsum
  rw [Finset.sum_congr rfl (fun v _ => epsEtaSummand_eq v), Finset.sum_neg_distrib, h]

set_option backward.isDefEq.respectTransparency false in
lemma unitTensor_down_repr {d : ℕ}
    (b : ComponentIdx (S := realLorentzTensor d) ![Color.up, Color.down]) :
    (Tensor.basis _).repr (unitTensor (S := realLorentzTensor d) Color.down) b
      = if b 0 = b 1 then 1 else 0 := by
  rw [unitTensor, fromConstPair,
    show ((realLorentzTensor d).unit Color.down) (1 : ℝ) = Lorentz.preContrCoUnitVal d from
      Lorentz.preContrCoUnit_apply_one]
  simp only [τ_down_eq_up]
  rw [fromPairT_basis_repr, Lorentz.preContrCoUnitVal_expand_tmul]
  simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply,
    Module.Basis.tensorProduct_repr_tmul_apply, Module.Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]
  rw [Finset.sum_eq_single (b 0)] <;> aesop

open ComponentIdx.DropPairSection in
lemma section_chain3 {cA cB : Fin 4 → Color}
    (h1 : (0 : Fin (2+1+1)) ≠ 2) (h2 : (1 : Fin (4+1+1)) ≠ 4) (h3 : (2 : Fin (6+1+1)) ≠ 6)
    (b : Fin 2 → Fin 1 ⊕ Fin 3) (x x1 x2 : Fin 1 ⊕ Fin 3) :
    ((ofFinEquiv (S := realLorentzTensor 3) (c := Fin.append cA cB) h3
        ((ofFinEquiv h2 ((ofFinEquiv h1 b (x, x)).1) (x1, x1)).1) (x2, x2)).1 :
      Fin (6+1+1) → Fin 1 ⊕ Fin 3)
      = ![x, x1, x2, b 0, x, x1, x2, b 1] := by
  funext m
  fin_cases m <;> rfl

open KroneckerDelta in
lemma eps_rotate (a b c y : Fin 1 ⊕ Fin 3) :
    generalizedKroneckerDelta
        (fun i => finSumFinEquiv ((![a,b,c,y] : Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4)
      = - generalizedKroneckerDelta
        (fun i => finSumFinEquiv ((![y,a,b,c] : Fin 4 → Fin 1 ⊕ Fin 3) i))
          (id : Fin 4 → Fin 4) := by
  have hg : (fun i => finSumFinEquiv ((![a,b,c,y] : Fin 4 → Fin 1 ⊕ Fin 3) i))
      = (((fun i => finSumFinEquiv ((![y,a,b,c] : Fin 4 → Fin 1 ⊕ Fin 3) i))
          ∘ ⇑(Equiv.swap (0 : Fin 4) 1)) ∘ ⇑(Equiv.swap (1 : Fin 4) 2))
          ∘ ⇑(Equiv.swap (2 : Fin 4) 3) := by
    funext i; fin_cases i <;> rfl
  rw [hg, generalizedKroneckerDelta_swap _ _ (show (2:Fin 4) ≠ 3 by decide),
    generalizedKroneckerDelta_swap _ _ (show (1:Fin 4) ≠ 2 by decide),
    generalizedKroneckerDelta_swap _ _ (show (0:Fin 4) ≠ 1 by decide)]
  ring

lemma sum3_eq' {M : Type} [AddCommMonoid M]
    (F : (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → (Fin 1 ⊕ Fin 3) → M) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3, F x x1 x2
      = ∑ w : Fin 3 → Fin 1 ⊕ Fin 3, F (w 0) (w 1) (w 2) := by
  rw [← Equiv.sum_comp vec3Equiv (fun w => F (w 0) (w 1) (w 2))]
  simp only [Fintype.sum_prod_type]
  rfl

lemma cons_vec (y : Fin 1 ⊕ Fin 3) (w : Fin 3 → Fin 1 ⊕ Fin 3) :
    (fun i => finSumFinEquiv ((![y, w 0, w 1, w 2] : Fin 4 → Fin 1 ⊕ Fin 3) i))
      = Fin.cons (finSumFinEquiv y) (fun i => finSumFinEquiv (w i)) := by
  funext i; fin_cases i <;> rfl

lemma sum_reindex3 {M : Type} [AddCommMonoid M] (F : (Fin 3 → Fin 4) → M) :
    ∑ w : Fin 3 → Fin 1 ⊕ Fin 3, F (fun i => finSumFinEquiv (w i))
      = ∑ h : Fin 3 → Fin 4, F h :=
  Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin 3))
    (finSumFinEquiv : (Fin 1 ⊕ Fin 3) ≃ Fin 4)) _ _ (fun _ => rfl)

open KroneckerDelta in
lemma eps_eta_three (a b c y0 y1 : Fin 1 ⊕ Fin 3) :
    ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y0] :
        Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
      * (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y1] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * minkowskiMatrix a a * minkowskiMatrix b b * minkowskiMatrix c c
        * minkowskiMatrix y1 y1)
      = - (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)) := by
  by_cases hA : generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y1] :
      Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) = 0
  · rw [hA]; norm_num
  · have hinj : Function.Injective
        (fun i => finSumFinEquiv ((![a,b,c,y1] : Fin 4 → Fin 1 ⊕ Fin 3) i)) := by
      by_contra hni
      exact hA (leviCivitaSymbol_eq_zero_of_not_injective hni)
    have hv : Function.Injective (![a,b,c,y1] : Fin 4 → Fin 1 ⊕ Fin 3) :=
      Function.Injective.of_comp hinj
    have hp := prod_eta_diag_of_injective hv
    simp only [vec4_0, vec4_1, vec4_2, vec4_3] at hp
    linear_combination
      (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ) *
        ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![a,b,c,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)) * hp

open KroneckerDelta in
lemma sum_eps_three (y0 y1 : Fin 1 ⊕ Fin 3) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3,
      ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
          * minkowskiMatrix x x * minkowskiMatrix x1 x1 * minkowskiMatrix x2 x2
          * minkowskiMatrix y1 y1)
      = -6 * (if y0 = y1 then 1 else 0) := by
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun x2 _ => eps_eta_three x x1 x2 y0 y1]
  simp only [Finset.sum_neg_distrib]
  have hZ : ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3,
      (generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4)
        * generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4))
      = 6 * ((kroneckerDelta (finSumFinEquiv y0) (finSumFinEquiv y1) : ℕ) : ℤ) := by
    rw [sum3_eq' (fun x x1 x2 => generalizedKroneckerDelta (fun i =>
        finSumFinEquiv ((![x, x1, x2, y0] : Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4)
      * generalizedKroneckerDelta (fun i =>
        finSumFinEquiv ((![x, x1, x2, y1] : Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4))]
    rw [Finset.sum_congr rfl fun w _ => by
      rw [eps_rotate (w 0) (w 1) (w 2) y0, eps_rotate (w 0) (w 1) (w 2) y1,
        cons_vec y0 w, cons_vec y1 w]]
    simp only [neg_mul_neg]
    rw [sum_reindex3 (fun h => generalizedKroneckerDelta (Fin.cons (finSumFinEquiv y0) h)
        (id : Fin 4 → Fin 4)
      * generalizedKroneckerDelta (Fin.cons (finSumFinEquiv y1) h) (id : Fin 4 → Fin 4))]
    exact sum_generalizedKroneckerDelta_mul_cons _ _
  have hR : ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3,
      (((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y1] :
            Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ))
      = 6 * (if y0 = y1 then 1 else 0) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hZ
    push_cast at this
    rw [this]
    by_cases hy : y0 = y1
    · rw [hy]; simp [KroneckerDelta.eq_one_of_same]
    · rw [if_neg hy, KroneckerDelta.eq_zero_of_ne (fun hc => hy (finSumFinEquiv.injective hc))]
      norm_num
  rw [hR]
  ring

open KroneckerDelta in
lemma sum_eps_three' (y0 y1 : Fin 1 ⊕ Fin 3) :
    ∑ x : Fin 1 ⊕ Fin 3, ∑ x1 : Fin 1 ⊕ Fin 3, ∑ x2 : Fin 1 ⊕ Fin 3,
      ((generalizedKroneckerDelta (fun i => finSumFinEquiv ((![x,x1,x2,y0] :
          Fin 4 → Fin 1 ⊕ Fin 3) i)) (id : Fin 4 → Fin 4) : ℤ) : ℝ)
        * (((Tensor.basis ![Color.up, Color.up, Color.up, Color.up]).repr ε4)
            (![x,x1,x2,y1] : Fin 4 → Fin 1 ⊕ Fin 3)
          * minkowskiMatrix x x * minkowskiMatrix x1 x1 * minkowskiMatrix x2 x2
          * minkowskiMatrix y1 y1)
      = -6 * (if y0 = y1 then 1 else 0) := by
  rw [← sum_eps_three y0 y1]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun x2 _ => ?_
  rw [leviCivita_basis_repr_apply]

/-!

## E. The epsilon-epsilon contraction identities

-/

lemma leviCivita_contract_three : {ε4 | μ ν ρ σ ⊗ ε4 | τ(μ) τ(ν) τ(ρ) τ(τ) =
    (-6) • unitTensor (S := realLorentzTensor) Color.down | σ τ }ᵀ := by
  apply (Tensor.basis _).repr.injective
  ext b
  simp only [contrT_basis_repr_apply_eq_fin, prodT_basis_repr_apply,
    toDualMapAtIndex_basis_repr, leviCivita_basis_repr_apply,
    permT_basis_repr_symm_apply,
    section_chain3, prod_fst_vec, prod_snd_vec, nest3, nest2, nest1, nest0,
    vec4_0, vec4_1, vec4_2, vec4_3, sum_mul_eta]
  simp only [map_zsmul, Finsupp.coe_smul, Pi.smul_apply, zsmul_eq_mul,
    basisIdxCongr_eq_refl, Equiv.refl_apply, unitTensor_down_repr]
  rw [IsReindexing.inv_eq_self_of_pointwise_eq _ (by decide),
    IsReindexing.inv_eq_self_of_pointwise_eq _ (by decide), sum_eps_three' (b 0) (b 1)]
  norm_num

-- `checkType` linter: whnf on this tensor-notation statement exceeds the
-- linter's 200k-heartbeat budget (since the v4.32.0 bump; still the case on
-- v4.33.0). The proof itself elaborates within the default budget.
@[nolint checkType]
lemma leviCivita_contract_self :
    {ε4 | μ ν ρ σ ⊗ ε4 | τ(μ) τ(ν) τ(ρ) τ(σ)}ᵀ.toField = - 24 := by
  rw [Tensor.toField_eq_repr]
  simp only [contrT_basis_repr_apply_eq_fin, prodT_basis_repr_apply,
    toDualMapAtIndex_basis_repr, leviCivita_basis_repr_apply,
    section_chain, prod_fst_vec, prod_snd_vec, nest3, nest2, nest1, nest0]
  simp only [vec4_0, vec4_1, vec4_2, vec4_3, sum_mul_eta]
  rw [← sum_epsEtaSummand, ← sum4_eq epsEtaSummand]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun x2 _ => Finset.sum_congr rfl fun x3 _ => ?_
  rw [epsEtaSummand, leviCivita_basis_repr_apply]
  simp only [vec4_0, vec4_1, vec4_2, vec4_3]
end realLorentzTensor
