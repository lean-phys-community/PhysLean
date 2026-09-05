/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Relativity.LorentzGroup.Invariants.IsQuadLorentz
public meta import Mathlib.Data.Fintype.Sum
public meta import Mathlib.Data.Fintype.Pi
/-!
# Lorentz invariants of three four-vector indices

`IsTriLorentz repLorentz T` says that a family `T`, indexed by three four-vector
indices and valued in a module `B` carrying a representation of `SL(2,ℂ)`, transforms
as a tensor `T^{μ₁ μ₂ μ₃}`.

Three indices admit no invariant contraction at all: the metric ties two indices and the
Levi-Civita symbol four, so an odd number of indices can be tied by neither. The main
theorem `eq_zero_of_invariant` says accordingly that every Lorentz invariant in the span
of the components is zero.

The proof needs neither the sieve nor the certificate polynomial of the two- and
four-index cases, because one axis already does all the work. Along a spatial axis the
four light-cone directions carry boost weights `2`, `-2`, `0` and `0`, and the two of
weight zero are the two directions transverse to both time and that axis. A light-cone
multi-index of total weight zero therefore has its `+2` and `-2` slots in bijection, so
an odd number of its three slots is transverse. The half turn about the axis is the
Lorentz transformation fixing time and the axis and negating the two transverse
directions, so it acts on such a multi-index by `(-1)` to an odd power, namely by `-1`.
An invariant has boost weight zero, hence is a combination of these multi-indices, hence
is negated by the half turn; being invariant it is also fixed by it, and so is zero.

The section headings tell the story: the half turn about an axis and its sign on the
light-cone directions (A), triple Lorentz tensors and the span of their components (B),
the light-cone basis along one axis grading that span by boost weight (C), the
weight-zero part of a generator (D), the half turn negating every invariant (E), which
then also holds modulo a Lorentz-stable submodule (F).
-/

@[expose] public section

namespace Lorentz

open TensorProduct Matrix MatrixGroups SL2C BoostWeight
open IsQuadLorentz (eq_component_zero_of_mem_boostWeightSubmodule
  mem_boostWeightSubmodule_zero_of_invariant quotRep quotRep_mkQ)

/-!

## A. The half turn about a spatial axis

The half turn about the axis `i` is the rotation by `π` about it: it fixes time and the
axis itself and negates the two transverse directions. On the light-cone basis along the
same axis it is therefore diagonal, with sign `1` on the two directions of boost weight
`±2` and sign `-1` on the two transverse ones.

-/

namespace SL2C

/-- The half turn about the axis `i`: the rotation by `π` about the `i`-th spatial
  axis, written in `SL(2,ℂ)`. -/
noncomputable def halfTurn : Fin 3 → SL(2,ℂ)
  | 0 => ⟨!![0, -Complex.I; -Complex.I, 0], by
      rw [Matrix.det_fin_two_of]
      simp [Complex.I_mul_I]⟩
  | 1 => ⟨!![0, -1; 1, 0], by
      rw [Matrix.det_fin_two_of]
      simp⟩
  | 2 => ⟨!![-Complex.I, 0; 0, Complex.I], by
      rw [Matrix.det_fin_two_of]
      simp [Complex.I_mul_I]⟩

/-- The matrix entries of the half turn about the `x`-axis. -/
@[simp] lemma halfTurn_zero_apply (j k : Fin 2) :
    (halfTurn 0).1 j k = (!![0, -Complex.I; -Complex.I, 0]) j k := rfl

/-- The matrix entries of the half turn about the `y`-axis. -/
@[simp] lemma halfTurn_one_apply (j k : Fin 2) :
    (halfTurn 1).1 j k = (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) j k := rfl

/-- The matrix entries of the half turn about the `z`-axis. -/
@[simp] lemma halfTurn_two_apply (j k : Fin 2) :
    (halfTurn 2).1 j k = (!![-Complex.I, 0; 0, Complex.I]) j k := rfl

/-- The Lorentz matrix of the half turn about the axis `i` is diagonal: it fixes the
  time direction and the axis, and negates the two transverse directions. -/
lemma toLorentzGroup_halfTurn_apply (i : Fin 3) (a b : Fin 1 ⊕ Fin 3) :
    (toLorentzGroup (halfTurn i)).1 a b =
      if a = b then (if b = Sum.inl 0 ∨ b = Sum.inr i then 1 else -1) else 0 := by
  refine Complex.ofReal_injective ?_
  rw [toLorentzGroup_eq_trace, PauliMatrix.trace_pauliSelfAdjoint'_mul_apply]
  fin_cases i <;>
    rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [PauliMatrix.pauliSelfAdjoint', PauliMatrix.pauliMatrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Complex.ext_iff]

end SL2C

/-- The sign by which the half turn about an axis acts on each of the four light-cone
  directions along that axis: `1` on the two of boost weight `±2`, `-1` on the two
  transverse ones. -/
def lightConeSign (κ : Fin 4) : ℤ := if κ = 0 ∨ κ = 1 then 1 else -1

/-- The half turn about the axis `i` acts on each light-cone direction along that axis
  by its sign. -/
lemma sum_halfTurn_lightConeCoeff (i : Fin 3) (κ : Fin 4) (ν : Fin 1 ⊕ Fin 3) :
    ∑ μ : Fin 1 ⊕ Fin 3, lightConeCoeff i κ μ *
        (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 ν μ : ℝ) : ℂ)
      = ((lightConeSign κ : ℤ) : ℂ) * lightConeCoeff i κ ν := by
  simp only [SL2C.toLorentzGroup_halfTurn_apply]
  rcases ν with a | j
  · rw [Subsingleton.elim a 0]
    fin_cases i <;> fin_cases κ <;>
      simp [lightConeCoeff, lightConeSign, Fintype.sum_sum_type]
  · fin_cases i <;> fin_cases j <;> fin_cases κ <;>
      simp [lightConeCoeff, lightConeSign, Fintype.sum_sum_type]

/-- The scalar behind the action of the half turn on a light-cone multi-index: the half
  turn acts slot by slot, so the product of the per-slot signs factors out. -/
lemma sum_prod_halfTurn_lightConeCoeff (i : Fin 3) {n : ℕ} (c : Fin n → Fin 4)
    (a : Fin n → Fin 1 ⊕ Fin 3) :
    ∑ d : Fin n → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) *
        (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) (d j) : ℝ) : ℂ))
      = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) * ∏ j, lightConeCoeff i (c j) (a j) := by
  calc ∑ d : Fin n → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) *
        (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) (d j) : ℝ) : ℂ))
      = ∑ d : Fin n → Fin 1 ⊕ Fin 3, ∏ j, (lightConeCoeff i (c j) (d j) *
          (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) (d j) : ℝ) : ℂ)) :=
        Finset.sum_congr rfl fun d _ => (Finset.prod_mul_distrib).symm
    _ = ∏ j, ∑ μ : Fin 1 ⊕ Fin 3, (lightConeCoeff i (c j) μ *
          (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j) μ : ℝ) : ℂ)) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    _ = ∏ j, (((lightConeSign (c j) : ℤ) : ℂ) * lightConeCoeff i (c j) (a j)) :=
        Finset.prod_congr rfl fun j _ => sum_halfTurn_lightConeCoeff i (c j) (a j)
    _ = (∏ j, ((lightConeSign (c j) : ℤ) : ℂ)) * ∏ j, lightConeCoeff i (c j) (a j) :=
        Finset.prod_mul_distrib
    _ = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) * ∏ j, lightConeCoeff i (c j) (a j) := by
        push_cast
        rfl

/-- A light-cone multi-index of three slots and total boost weight zero has an odd
  number of transverse slots, so the half turn acts on it by `-1`. -/
lemma prod_lightConeSign_of_sum_lightConeWeight_eq_zero (c : Fin 3 → Fin 4)
    (hc : (∑ j, lightConeWeight (c j)) = 0) : ∏ j, lightConeSign (c j) = -1 := by
  revert c
  decide

/-!

## B. Triple Lorentz tensors and the span of their components

The hypothesis on the family and the space its components span, which is where the
invariants to be classified live.

-/

/-- A family `T` of elements of `B`, indexed by three four-vector indices, transforms as
  a tensor `T^{μ₁ μ₂ μ₃}` under the representation `repLorentz` of `SL(2,ℂ)`. -/
structure IsTriLorentz (B : Type*) [AddCommMonoid B] [Module ℂ B]
    (repLorentz : Representation ℂ SL(2,ℂ) B)
    (T : (Fin 3 → (Fin 1 ⊕ Fin 3)) → B) : Prop where
  repLorentz_T : ∀ (g : SL(2,ℂ)) l,
    repLorentz g (T l) = ∑ (a : Fin 3 → Fin 1 ⊕ Fin 3),
    (∏ (i : Fin 3), (((SL2C.toLorentzGroup g).1 (a i) (l i) : ℝ) : ℂ)) • T a

namespace IsTriLorentz
set_option linter.unusedVariables false

variable {B : Type*} [AddCommGroup B] [Module ℂ B]
  {repLorentz : Representation ℂ SL(2,ℂ) B}
  {T : (Fin 3 → (Fin 1 ⊕ Fin 3)) → B}
  (hT : IsTriLorentz B repLorentz T)

/-- The span of all the components. -/
def span (hT : IsTriLorentz B repLorentz T) : Submodule ℂ B := ⨆ d, ℂ ∙ T d

/-- The span of the components is exactly the set of linear combinations of them. -/
lemma mem_span_iff (x : B) :
    x ∈ hT.span ↔ ∃ (c : (Fin 3 → (Fin 1 ⊕ Fin 3)) → ℂ), x = ∑ d, c d • T d := by
  constructor
  · intro hx
    rw [span] at hx
    refine Submodule.iSup_induction
      (motive := fun y => ∃ c : (Fin 3 → (Fin 1 ⊕ Fin 3)) → ℂ, y = ∑ d, c d • T d)
      (fun d => ℂ ∙ T d) hx ?_ ?_ ?_
    · intro d y hy
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨fun e => if e = d then a else 0, ?_⟩
      simp [ite_smul, Finset.sum_ite_eq']
    · exact ⟨0, by simp⟩
    · rintro y z ⟨c₁, rfl⟩ ⟨c₂, rfl⟩
      exact ⟨c₁ + c₂, by simp [add_smul, Finset.sum_add_distrib]⟩
  · rintro ⟨c, rfl⟩
    exact sum_mem fun d _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-!

## C. The light-cone basis along one axis

Along a spatial axis `i` the coordinate components recombine into the light-cone
components `lightCone i c`, which span the same space, are homogeneous of boost weight
`∑ j, lightConeWeight (c j)`, and are negated by the half turn about the axis exactly
when an odd number of their slots is transverse.

-/

/-- The axis-`i` light-cone component of `T` at the light-cone multi-index `c`. -/
noncomputable def lightCone (hT : IsTriLorentz B repLorentz T) (i : Fin 3)
    (c : Fin 3 → Fin 4) : B :=
  ∑ d : Fin 3 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (d j)) • T d

/-- Each light-cone component lies in the span of the coordinate components. -/
lemma lightCone_mem_span (i : Fin 3) (c : Fin 3 → Fin 4) : hT.lightCone i c ∈ hT.span :=
  sum_mem fun d _ => Submodule.smul_mem _ _
    (Submodule.mem_iSup_of_mem d (Submodule.mem_span_singleton_self _))

/-- Each generator is recovered from the light-cone components along any axis. -/
lemma eq_sum_lightCone (i : Fin 3) (d : Fin 3 → Fin 1 ⊕ Fin 3) :
    T d = ∑ c : Fin 3 → Fin 4,
      (∏ j, lightConeCoeffInv i (d j) (c j)) • hT.lightCone i c := by
  calc T d = ∑ e : Fin 3 → Fin 1 ⊕ Fin 3,
        (∑ c : Fin 3 → Fin 4, (∏ j, lightConeCoeffInv i (d j) (c j)) *
          (∏ j, lightConeCoeff i (c j) (e j))) • T e := by
        simp only [sum_prod_lightConeCoeffInv, ite_smul, one_smul, zero_smul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
    _ = _ := by
        simp only [lightCone, Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]

/-- The light-cone components along any axis span the same space as the components. -/
lemma span_eq_lightCone (hT : IsTriLorentz B repLorentz T) (i : Fin 3) :
    hT.span = ⨆ c, ℂ ∙ hT.lightCone i c := by
  rw [span]
  refine le_antisymm (iSup_le fun d => ?_) (iSup_le fun c => ?_)
  · rw [Submodule.span_singleton_le_iff_mem, hT.eq_sum_lightCone i d]
    exact sum_mem fun c _ => Submodule.smul_mem _ _
      (Submodule.mem_iSup_of_mem c (Submodule.mem_span_singleton_self _))
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hT.lightCone_mem_span i c

/-- The light-cone components are boost eigenvectors: along axis `i` the component at
  `c` has boost weight the total light-cone weight of `c`. -/
lemma lightCone_mem_boostWeightSubmodule (i : Fin 3) (c : Fin 3 → Fin 4) :
    hT.lightCone i c ∈ boostWeightSubmodule repLorentz i (∑ j, lightConeWeight (c j)) := by
  refine mem_boostWeightSubmodule.2 fun t ht => ?_
  have hstep : ∀ x : Fin 3 → Fin 1 ⊕ Fin 3,
      (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.boostAxis i t ht) (T x)
        = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3,
            ((∏ j, lightConeCoeff i (c j) (x j)) *
              (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
                (x j) : ℝ) : ℂ))) • T a := by
    intro x
    rw [hT.repLorentz_T, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  calc repLorentz (SL2C.boostAxis i t ht) (hT.lightCone i c)
      = ∑ x : Fin 3 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.boostAxis i t ht) (T x) := by
        simp only [lightCone, map_sum, map_smul]
    _ = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3,
          (∑ x : Fin 3 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) *
            (∏ j, (((SL2C.toLorentzGroup (SL2C.boostAxis i t ht)).1 (a j)
              (x j) : ℝ) : ℂ))) • T a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3, (((t : ℝ) : ℂ) ^ (∑ j, lightConeWeight (c j)) *
          (∏ j, lightConeCoeff i (c j) (a j))) • T a := by
        refine Finset.sum_congr rfl fun a _ => ?_
        congr 1
        exact sum_prod_lightConeCoeff i c a ht
    _ = (algebraMap ℝ ℂ) t ^ (∑ j, lightConeWeight (c j)) • hT.lightCone i c := by
        rw [show (algebraMap ℝ ℂ) t = ((t : ℝ) : ℂ) from rfl, lightCone, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => (smul_smul _ _ _).symm

/-- The half turn about the axis `i` acts on the light-cone component at `c` by the
  product of the signs of its slots. -/
lemma repLorentz_halfTurn_lightCone (i : Fin 3) (c : Fin 3 → Fin 4) :
    repLorentz (SL2C.halfTurn i) (hT.lightCone i c)
      = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) • hT.lightCone i c := by
  have hstep : ∀ x : Fin 3 → Fin 1 ⊕ Fin 3,
      (∏ j, lightConeCoeff i (c j) (x j)) • repLorentz (SL2C.halfTurn i) (T x)
        = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3,
            ((∏ j, lightConeCoeff i (c j) (x j)) *
              (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j)
                (x j) : ℝ) : ℂ))) • T a := by
    intro x
    rw [hT.repLorentz_T, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_smul _ _ _
  calc repLorentz (SL2C.halfTurn i) (hT.lightCone i c)
      = ∑ x : Fin 3 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) •
          repLorentz (SL2C.halfTurn i) (T x) := by
        simp only [lightCone, map_sum, map_smul]
    _ = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3,
          (∑ x : Fin 3 → Fin 1 ⊕ Fin 3, (∏ j, lightConeCoeff i (c j) (x j)) *
            (∏ j, (((SL2C.toLorentzGroup (SL2C.halfTurn i)).1 (a j)
              (x j) : ℝ) : ℂ))) • T a := by
        simp only [hstep]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => (Finset.sum_smul).symm
    _ = ∑ a : Fin 3 → Fin 1 ⊕ Fin 3, (((∏ j, lightConeSign (c j) : ℤ) : ℂ) *
          (∏ j, lightConeCoeff i (c j) (a j))) • T a :=
        Finset.sum_congr rfl fun a _ => by
          rw [sum_prod_halfTurn_lightConeCoeff i c a]
    _ = ((∏ j, lightConeSign (c j) : ℤ) : ℂ) • hT.lightCone i c := by
        rw [lightCone, Finset.smul_sum]
        exact Finset.sum_congr rfl fun a _ => (smul_smul _ _ _).symm

/-!

## D. The weight-zero part of a generator

Each generator `T e` is the sum of its boost-weight components `monoComponent i e m`,
and an element of the span of weight zero along the axis `i` is the corresponding
combination of the weight-zero ones alone. Those are built from light-cone multi-indices
of total weight zero, so the half turn about the axis negates them.

-/

/-- The axis-`i` weight-`m` component of the generator `T e`: the weight-`m` partial
  sum of `eq_sum_lightCone`. -/
noncomputable def monoComponent (i : Fin 3) (e : Fin 3 → Fin 1 ⊕ Fin 3) (m : ℤ) : B :=
  ∑ c ∈ Finset.univ.filter (fun c : Fin 3 → Fin 4 => (∑ s, lightConeWeight (c s)) = m),
    (∏ s, lightConeCoeffInv i (e s) (c s)) • hT.lightCone i c

/-- The weight components are homogeneous of the stated weight. -/
lemma monoComponent_mem_boostWeightSubmodule (i : Fin 3) (e : Fin 3 → Fin 1 ⊕ Fin 3)
    (m : ℤ) : hT.monoComponent i e m ∈ boostWeightSubmodule repLorentz i m := by
  refine sum_mem fun c hc => Submodule.smul_mem _ _ ?_
  exact (show (∑ s, lightConeWeight (c s)) = m from (Finset.mem_filter.1 hc).2) ▸
    hT.lightCone_mem_boostWeightSubmodule i c

/-- The total light-cone weight of three slots is one of the seven even numbers between
  `-6` and `6`. -/
lemma sum_lightConeWeight_mem (c : Fin 3 → Fin 4) :
    (∑ s, lightConeWeight (c s)) ∈ ({-6, -4, -2, 0, 2, 4, 6} : Finset ℤ) := by
  revert c
  decide

/-- A component is the sum of its weight components over the seven possible weights. -/
lemma eq_sum_monoComponent_univ (i : Fin 3) (e : Fin 3 → Fin 1 ⊕ Fin 3) :
    T e = ∑ m ∈ ({-6, -4, -2, 0, 2, 4, 6} : Finset ℤ), hT.monoComponent i e m := by
  rw [hT.eq_sum_lightCone i e]
  exact (Finset.sum_fiberwise_of_maps_to (fun c _ => sum_lightConeWeight_mem c) _).symm

include hT in
/-- The weight-zero round along one axis: an element of weight zero along axis `i`
  expanded in the generators re-expands in their weight-zero components alone. -/
lemma eq_sum_monoComponent_zero (i : Fin 3) {x : B}
    (c : (Fin 3 → Fin 1 ⊕ Fin 3) → ℂ) (hx : x = ∑ e, c e • T e)
    (hw : x ∈ boostWeightSubmodule repLorentz i 0) :
    x = ∑ e, c e • hT.monoComponent i e 0 := by
  have hsum : x = ∑ m ∈ ({-6, -4, -2, 0, 2, 4, 6} : Finset ℤ),
      ∑ e, c e • hT.monoComponent i e m := by
    rw [hx]
    calc ∑ e, c e • T e
        = ∑ e, c e • ∑ m ∈ ({-6, -4, -2, 0, 2, 4, 6} : Finset ℤ),
            hT.monoComponent i e m :=
          Finset.sum_congr rfl fun e _ => by rw [← hT.eq_sum_monoComponent_univ i e]
      _ = _ := by
          simp only [Finset.smul_sum]
          exact Finset.sum_comm
  exact eq_component_zero_of_mem_boostWeightSubmodule
    (w := fun m => ∑ e, c e • hT.monoComponent i e m) hw
    (fun m _ => sum_mem fun e _ => Submodule.smul_mem _ _
      (hT.monoComponent_mem_boostWeightSubmodule i e m))
    (by decide) hsum

/-- The half turn about the axis `i` negates the weight-zero component of a generator:
  every light-cone multi-index contributing to it has an odd number of transverse
  slots. -/
lemma repLorentz_halfTurn_monoComponent_zero (i : Fin 3) (e : Fin 3 → Fin 1 ⊕ Fin 3) :
    repLorentz (SL2C.halfTurn i) (hT.monoComponent i e 0) = -hT.monoComponent i e 0 := by
  rw [monoComponent, map_sum, ← neg_one_smul (R := ℂ), Finset.smul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [map_smul, hT.repLorentz_halfTurn_lightCone i c,
    prod_lightConeSign_of_sum_lightConeWeight_eq_zero c (Finset.mem_filter.1 hc).2,
    smul_smul, smul_smul]
  norm_num [mul_comm]

/-!

## E. The classification of the Lorentz invariants

One axis suffices. An invariant has boost weight zero along it, so section D writes it
through the weight-zero components alone, and the half turn about that same axis negates
those. The invariant is therefore both fixed and negated by one Lorentz transformation,
and so is zero.

-/

include hT in
/-- The classification of the Lorentz invariants: three four-vector indices carry no
  invariant contraction, so every element of the span of the components fixed by the
  Lorentz group is zero. -/
theorem eq_zero_of_invariant {x : B} (hx : x ∈ hT.span)
    (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x = 0 := by
  obtain ⟨c, hc⟩ := (hT.mem_span_iff x).1 hx
  have hw := mem_boostWeightSubmodule_zero_of_invariant (repLorentz := repLorentz) hinv
  have h0 : x = ∑ e, c e • hT.monoComponent 2 e 0 :=
    hT.eq_sum_monoComponent_zero 2 c hc (hw 2)
  have hneg : repLorentz (SL2C.halfTurn 2) x = -x := by
    calc repLorentz (SL2C.halfTurn 2) x
        = ∑ e, c e • repLorentz (SL2C.halfTurn 2) (hT.monoComponent 2 e 0) := by
          conv_lhs => rw [h0]
          rw [map_sum]
          exact Finset.sum_congr rfl fun e _ => map_smul _ _ _
      _ = ∑ e, c e • -hT.monoComponent 2 e 0 :=
          Finset.sum_congr rfl fun e _ => by
            rw [hT.repLorentz_halfTurn_monoComponent_zero 2 e]
      _ = -x := by
          rw [h0]
          simp
  have hself : x = -x := by
    conv_lhs => rw [← hinv (SL2C.halfTurn 2)]
    exact hneg
  have htwo : (2 : ℂ) • x = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.2 hself
  simpa using htwo

/-!

## F. The classification modulo a Lorentz-stable submodule

A Lorentz-stable submodule can be divided out: the quotient representation carries the
images of the components as a triple Lorentz tensor again, so the classification applies
verbatim in the quotient and lifts to a classification modulo the submodule. The
quotient representation itself is the one built in `IsQuadLorentz`.

-/

include hT in
/-- The images of the components in the quotient by a Lorentz-stable submodule again
  form a triple Lorentz tensor. -/
lemma isTriLorentz_quotRep (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S) :
    IsTriLorentz (B ⧸ S) (quotRep (repLorentz := repLorentz) S hS)
      (fun l => S.mkQ (T l)) where
  repLorentz_T g l := by
    rw [quotRep_mkQ, hT.repLorentz_T g l, map_sum]
    exact Finset.sum_congr rfl fun a _ => map_smul _ _ _

include hT in
/-- The classification of the Lorentz invariants modulo a stable submodule: an element
  of the span of the components together with a Lorentz-stable submodule `S`, fixed by
  the Lorentz group, already lies in `S`. -/
lemma mem_of_invariant_of_mem_sup {x : B} (S : Submodule ℂ B)
    (hS : ∀ g : SL(2,ℂ), ∀ y ∈ S, repLorentz g y ∈ S)
    (hx : x ∈ hT.span ⊔ S) (hinv : ∀ g : SL(2,ℂ), repLorentz g x = x) : x ∈ S := by
  have hT' := hT.isTriLorentz_quotRep S hS
  have hmk : S.mkQ x ∈ hT'.span := by
    obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, hc⟩ := (hT.mem_span_iff u).1 hu
    refine (hT'.mem_span_iff _).2 ⟨c, ?_⟩
    rw [← huz, map_add, show S.mkQ z = 0 from (Submodule.Quotient.mk_eq_zero S).2 hz,
      add_zero, hc, map_sum]
    exact Finset.sum_congr rfl fun d _ => map_smul _ _ _
  have hinv' : ∀ g : SL(2,ℂ),
      quotRep (repLorentz := repLorentz) S hS g (S.mkQ x) = S.mkQ x := by
    intro g
    rw [quotRep_mkQ, hinv g]
  have hzero := hT'.eq_zero_of_invariant hmk hinv'
  rwa [← Submodule.ker_mkQ S, LinearMap.mem_ker]

end IsTriLorentz

end Lorentz
